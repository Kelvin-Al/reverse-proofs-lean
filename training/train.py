"""Train a small linear policy for one-step reverse propositional proofs."""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import shutil
import sys
from tempfile import TemporaryDirectory

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT / "experiments"
sys.path.insert(0, str(EXPERIMENTS / "reverse_proof_generator"))
from experiment import Lean, edge_source, proof_source
from formulas import parse_formula, render, shape, size


ACTIONS = ("exact", "intro", "apply", "constructor", "left", "right", "cases")
FEATURES = (
    "bias", "empty", "one_goal", "extra_goals", "locals", "target_size",
    "target_and", "target_or", "target_imp", "shared_context", "can_apply",
    "can_merge_cases", "can_join", "last_local_or",
)
ATOMS = tuple("PQRS")


def parse_state(state):
    goals = []
    for goal in state:
        context, target = map(str.strip, goal.split("|"))
        locals_ = tuple((name.strip(), parse_formula(typ)) for name, typ in
                        (item.split(":") for item in context.split(",") if item))
        goals.append((locals_, parse_formula(target)))
    return tuple(goals)


def render_state(state):
    return [f"{','.join(f'{name}:{render(typ)}' for name, typ in context)} | {render(target)}"
            for context, target in state]


def theorem_key(target):
    names = {}
    return shape(target, lambda atom: names.setdefault(atom, len(names)))


def dataset(method_names):
    traces = []
    for source in ("reverse_proof_generator", "controlled_reverse_proofs"):
        path = EXPERIMENTS / source / "results.json"
        methods = json.loads(path.read_text(encoding="utf-8"))["methods"]
        for method in method_names:
            for name, lane in methods[method].items():
                if not lane["proof"]["ok"]:
                    continue
                states = [parse_state(state) for state in lane["states"]]
                if states[0] or len(states) != len(lane["edges"]) + 1:
                    raise ValueError(f"inconsistent trace {source}/{method}/{name}")
                rows = []
                for current, predecessor, edge in zip(states, states[1:], lane["edges"]):
                    if not edge["ok"] or predecessor != parse_state(edge["proposed_state"]):
                        raise ValueError(f"unverified or inconsistent edge in {source}/{method}/{name}")
                    rows.append((current, edge["tactic"], predecessor))
                traces.append((f"{source}/{method}/{name}", theorem_key(states[-1][0][1]), rows))
    return traces


def split_traces(traces):
    keys = {key for _, key, _ in traces}
    keys = sorted(keys, key=lambda key: sha256(repr(key).encode()).digest())
    heldout = set(keys[:max(1, len(keys) // 4)])
    return ([trace for trace in traces if trace[1] not in heldout],
            [trace for trace in traces if trace[1] in heldout])


def root(formula):
    return formula[0] if isinstance(formula, tuple) else None


def candidates(state):
    """Propose bounded inverse moves using only the current state."""
    moves = {action: [] for action in ACTIONS}

    def add(action, tactic, context, target, consumed):
        if size(target) <= 12 and all(size(typ) <= 12 for _, typ in context):
            moves[action].append((tactic, ((context, target), *state[consumed:])))

    if not state:
        for atom in ATOMS:
            add("exact", "exact h0", (("h0", atom),), atom, 0)
        return moves

    context, target = state[0]
    if len(state) < 3:
        # Reuse the first goal's context, or vary its final branch hypothesis.
        contexts = [context]
        if context:
            name, typ = context[-1]
            contexts.extend((*context[:-1], (name, atom)) for atom in ATOMS if atom != typ)
        for local_context in contexts:
            for name, typ in local_context:
                add("exact", f"exact {name}", local_context, typ, 0)
                if root(typ) == "∧":
                    add("exact", f"exact {name}.left", local_context, typ[1], 0)
                    add("exact", f"exact {name}.right", local_context, typ[2], 0)

    if context:
        name, typ = context[-1]
        add("intro", f"intro {name}", context[:-1], ("→", typ, target), 1)
    for name, typ in context:
        if root(typ) == "→" and typ[1] == target:
            add("apply", f"apply {name}", context, typ[2], 1)
    for atom in ATOMS:
        add("left", "left", context, ("∨", target, atom), 1)
        add("right", "right", context, ("∨", atom, target), 1)

    if len(state) >= 2:
        other, other_target = state[1]
        if context == other:
            add("constructor", "constructor", context, ("∧", target, other_target), 2)
        if (context and other and target == other_target and context[:-1] == other[:-1]
                and context[-1][0] == other[-1][0] and context[-1][1] != other[-1][1]):
            branch, left = context[-1]
            used = {name for name, _ in context}
            name = next((f"h{i}" for i in range(10) if f"h{i}" not in used), None)
            if name is not None:
                merged = (*context[:-1], (name, ("∨", left, other[-1][1])))
                add("cases", f"cases {name} <;> rename_i {branch}", merged, target, 2)
    return moves


def features(state):
    if not state:
        return [1, 1, *([0] * (len(FEATURES) - 2))]
    context, target = state[0]
    second_context = state[1][0] if len(state) >= 2 else None
    available = candidates(state)
    return [1, 0, len(state) == 1, min(len(state) - 1, 3), min(len(context), 5),
            size(target) / 12, root(target) == "∧", root(target) == "∨", root(target) == "→",
            second_context is not None and context[:-1] == second_context[:-1],
            bool(available["apply"]), bool(available["cases"]), bool(available["constructor"]),
            bool(context and root(context[-1][1]) == "∨")]


def fit(rows):
    inputs = np.array([features(state) for state, _, _ in rows], dtype=float)
    labels = np.eye(len(ACTIONS))[[ACTIONS.index(tactic.split()[0]) for _, tactic, _ in rows]]
    weights = np.zeros((len(FEATURES), len(ACTIONS)))
    losses = []
    for _ in range(400):
        logits = inputs @ weights
        exp = np.exp(logits - logits.max(axis=1, keepdims=True))
        probabilities = exp / exp.sum(axis=1, keepdims=True)
        losses.append(float(-np.log(probabilities[labels == 1]).mean()))
        gradient = inputs.T @ (probabilities - labels) / len(inputs) + 0.01 * weights
        weights -= 0.2 * gradient
    return weights, {"epochs": len(losses), "initial_loss": losses[0], "last_epoch_loss": losses[-1]}


def ordered(scores):
    return [ACTIONS[index] for index in np.argsort(-scores, kind="stable")]


def evaluate(rows, training_rows, score, lean, tag):
    seen = set(training_rows)
    counts = Counter()
    predictions = []
    for index, (state, reference, reference_predecessor) in enumerate(rows):
        action = reference.split()[0]
        ranking = ordered(score(state))
        options = candidates(state)
        available = [family for family in ranking if options[family]]
        tactic, predecessor = options[available[0]][0]
        source = edge_source(render_state(predecessor), tactic, render_state(state))
        result = lean.check(f"{tag}_{index}", source)
        novel = (state, reference, reference_predecessor) not in seen
        counts.update({"steps": 1, "novel_steps": novel, "top1": ranking[0] == action,
                       "top3": action in ranking[:3], "novel_top1": novel and ranking[0] == action,
                       "decoder_covers_family": action in available, "masked_top1": available[0] == action,
                       "lean_accepted": result["ok"], "novel_lean_accepted": novel and result["ok"]})
        predictions.append({"current": render_state(state), "reference": reference,
                            "reference_predecessor": render_state(reference_predecessor), "novel": novel,
                            "ranking": ranking, "tactic": tactic, "predecessor": render_state(predecessor),
                            "lean": result})
    return {"counts": dict(counts), "predictions": predictions}


def rollout(score, lean, tag, known_theorems, seeds=range(12)):
    results = []
    for seed in seeds:
        rng = np.random.default_rng(seed)
        states = [()]
        tactics = []
        outcome = {"seed": seed, "reverse_steps": [],
                   "lean": {"ok": False, "diagnostic": "step budget exhausted"}}
        for _ in range(8):
            state = states[-1]
            options = candidates(state)
            choices = [(tactic, before) for action in ordered(score(state))
                       for tactic, before in options[action]
                       if before not in states and (len(tactics) >= 3 or not closed(before))]
            if not choices:
                outcome["lean"]["diagnostic"] = "no candidate"
                break
            family = choices[0][0].split()[0]
            first_family = [move for move in choices if move[0].split()[0] == family]
            tactic, before = first_family[rng.integers(len(first_family))]
            outcome["reverse_steps"].append({"tactic": tactic, "predecessor": render_state(before)})
            tactics.append(tactic)
            states.append(before)
            if closed(before):
                target = before[0][1]
                source = proof_source(render(target), tactics[::-1], [render_state(s) for s in states[::-1]])
                result = lean.check(f"{tag}_rollout_{seed}", source, proof=True)
                key = theorem_key(target)
                outcome.update(target=render(target), key=key, novel_theorem=key not in known_theorems,
                               tactics=tactics[::-1], lean=result)
                break
        results.append(outcome)
    return results


def closed(state):
    return len(state) == 1 and not state[0][0]


def write_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean 4.19.0 executable")
    parser.add_argument("--rules-only", action="store_true", help="use only hand-written rule traces")
    parser.add_argument("--output", type=Path, required=True, help="new directory for this run")
    args = parser.parse_args()
    executable = shutil.which(args.lean)
    if executable is None:
        parser.error(f"Lean executable not found: {args.lean}")
    methods = ("rules",) if args.rules_only else ("llm_reverse", "rules")
    traces = dataset(methods)
    train, test = split_traces(traces)
    training_rows = [row for _, _, rows in train for row in rows]
    test_rows = [row for _, _, rows in test for row in rows]
    weights, fit_report = fit(training_rows)
    frequencies = Counter(tactic.split()[0] for _, tactic, _ in training_rows)
    prior = np.array([frequencies[action] for action in ACTIONS])
    policies = {"frequency": lambda state: prior, "trained": lambda state: features(state) @ weights}
    args.output.mkdir(parents=True, exist_ok=False)
    write_json(args.output / "model.json", {"features": FEATURES, "actions": ACTIONS,
                                             "weights": weights.tolist(), "frequency": prior.tolist()})
    report = {"parameters": weights.size, "methods": methods, "fit": fit_report,
              "train": {"traces": [name for name, _, _ in train], "steps": len(training_rows)},
              "holdout": {"traces": [name for name, _, _ in test], "steps": len(test_rows)}}
    print(json.dumps(report), flush=True)
    with TemporaryDirectory(dir=args.output.resolve()) as temp:
        lean = Lean(str(Path(executable).resolve()), Path(temp))
        report["lean"] = lean.version
        for tag, score in policies.items():
            results = evaluate(test_rows, training_rows, score, lean, tag)
            rollouts = rollout(score, lean, tag, {key for _, key, _ in traces})
            verified = [run for run in rollouts if run["lean"]["ok"]]
            report[tag] = {**results["counts"], "rollouts": len(rollouts), "proved": len(verified),
                           "distinct_novel_theorems": len({run["key"] for run in verified if run["novel_theorem"]})}
            write_json(args.output / f"{tag}.json", {**results, "rollouts": rollouts})
    write_json(args.output / "summary.json", report)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
