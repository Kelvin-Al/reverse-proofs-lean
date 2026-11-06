"""Compare greedy and bounded reverse search with a frozen linear policy."""

import argparse
from collections import Counter
from heapq import heappop, heappush
import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

import numpy as np

from train import (
    ACTIONS, FEATURES, Lean, candidates, closed, dataset, edge_source, features, ordered,
    parse_formula, proof_source, render, render_state, rollout, shape, theorem_key, write_json,
)


MIN_STEPS = 4
MAX_STEPS = 8
NODE_BUDGET = 64


def state_key(state):
    names = {}

    def normalize(formula):
        return shape(formula, lambda atom: names.setdefault(atom, len(names)))

    return tuple((tuple((name, normalize(typ)) for name, typ in context), normalize(target))
                 for context, target in state)


def steps_to_close(state):
    # Each merge removes one goal. Only an intro can reduce the maximum context length.
    return max(len(state) - 1, 0) + max((len(context) for context, _ in state), default=0)


def search(score, lean, tag, seed, emitted):
    rng = np.random.default_rng(seed)
    queue = []
    best_rank = {}

    def push(states, tactics, rank_cost):
        depth = len(tactics)
        remaining = steps_to_close(states[-1])
        if depth + remaining > MAX_STEPS:
            return
        key = (depth, state_key(states[-1]))
        if key in best_rank and best_rank[key] <= rank_cost:
            return
        best_rank[key] = rank_cost
        priority = max(MIN_STEPS, depth + remaining) + rank_cost / 2
        heappush(queue, (priority, rng.random(), rank_cost, key, states, tactics))

    outcome = {"seed": seed, "popped_nodes": 0, "lean_checks": 0, "rejections": []}

    def verify(states, tactics):
        target = states[-1][0][1]
        key = theorem_key(target)
        forward = tactics[::-1]
        source = proof_source(render(target), forward, [render_state(s) for s in reversed(states)])
        outcome["lean_checks"] += 1
        result = lean.check(f"{tag}_{seed}_{outcome['lean_checks']}", source, proof=True)
        if result["ok"]:
            outcome.update(target=render(target), key=key, tactics=forward, lean=result,
                           reverse_steps=[{"tactic": tactic, "predecessor": render_state(state)}
                                          for tactic, state in zip(tactics, states[1:])])
            emitted.add(key)
            return True
        outcome["rejections"].append(result)
        return False

    push(((),), (), 0)
    duplicate = None
    while queue and outcome["popped_nodes"] < NODE_BUDGET:
        _, _, rank_cost, key, states, tactics = heappop(queue)
        if best_rank[key] != rank_cost:
            continue
        outcome["popped_nodes"] += 1
        state = states[-1]
        if closed(state):
            if theorem_key(state[0][1]) in emitted:
                if duplicate is None:
                    duplicate = (states, tactics)
            elif verify(states, tactics):
                return outcome
            continue
        if len(tactics) == MAX_STEPS:
            continue
        options = candidates(state)
        families = [action for action in ordered(score(state)) if options[action]]
        for rank, action in enumerate(families):
            for tactic, before in options[action]:
                if before in states or (closed(before) and len(tactics) + 1 < MIN_STEPS):
                    continue
                push((*states, before), (*tactics, tactic), rank_cost + rank)

    if duplicate is not None and verify(*duplicate):
        return outcome
    outcome["lean"] = {"ok": False, "diagnostic": "node budget exhausted" if queue else "no remaining candidate"}
    return outcome


def summarize(runs, known):
    proved = [run for run in runs if run["lean"]["ok"]]
    targets = [parse_formula(run["target"]) for run in proved]
    keys = {theorem_key(target) for target in targets}
    return {
        "attempts": len(runs), "proved": len(proved), "theorems_up_to_renaming": len(keys),
        "novel_theorems_up_to_renaming": len(keys - known),
        "connective_skeletons": len({shape(target, lambda _: "atom") for target in targets}),
        "proofs_with_cases": sum(any(tactic.startswith("cases ") for tactic in run["tactics"]) for run in proved),
        "failures": dict(Counter(run["lean"]["diagnostic"] for run in runs if not run["lean"]["ok"])),
    }


def diagnose(runs):
    failures = [run for run in runs if not run["lean"]["ok"]]
    return {
        "failed_seeds": [run["seed"] for run in failures],
        "three_goals_after_step_3": sum(len(run["reverse_steps"]) >= 3 and
                                       len(run["reverse_steps"][2]["predecessor"]) == 3 for run in failures),
        "goal_counts_at_stop": dict(Counter(len(run["reverse_steps"][-1]["predecessor"])
                                            for run in failures if run["reverse_steps"])),
        "only_injections_after_step_3": sum(len(run["reverse_steps"]) > 3 and
                                            all(step["tactic"] in {"left", "right"}
                                                for step in run["reverse_steps"][3:]) for run in failures),
    }


def audit_failed_steps(runs, lean):
    sources = []
    for run in runs:
        if run["lean"]["ok"]:
            continue
        current = []
        for step in run["reverse_steps"]:
            before = step["predecessor"]
            sources.append(edge_source(before, step["tactic"], current))
            current = before
    if not sources:
        return {"steps": 0, "ok": True}
    # Each source shares its initial import. The examples are independent declarations.
    source = sources[0] + "\n".join(part.split("\n", 1)[1] for part in sources[1:])
    result = lean.check("original_trained_failed_edges", source)
    return {"steps": len(sources), **result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=Path, required=True, help="checkpoint from train.py --rules-only")
    parser.add_argument("--lean", default="lean", help="Lean 4.19.0 executable")
    parser.add_argument("--output", type=Path, required=True, help="new directory for the comparison")
    args = parser.parse_args()
    executable = shutil.which(args.lean)
    if executable is None:
        parser.error(f"Lean executable not found: {args.lean}")
    checkpoint = json.loads(args.model.read_text(encoding="utf-8"))
    if checkpoint["features"] != list(FEATURES) or checkpoint["actions"] != list(ACTIONS):
        parser.error("checkpoint feature or action order differs from train.py")
    weights = np.array(checkpoint["weights"])
    frequency = np.array(checkpoint["frequency"])
    scores = {"frequency": lambda _: frequency, "trained": lambda state: features(state) @ weights}
    known = {key for _, key, _ in dataset(("rules",))}
    suites = {"original": range(12), "fresh": range(100, 112)}
    report = {"parameters": weights.size, "min_steps": MIN_STEPS, "max_steps": MAX_STEPS,
              "node_budget_per_seed": NODE_BUDGET, "suites": {}}
    args.output.mkdir(parents=True, exist_ok=False)
    with TemporaryDirectory(dir=args.output.resolve()) as temp:
        lean = Lean(str(Path(executable).resolve()), Path(temp))
        report["lean"] = lean.version
        for suite, seeds in suites.items():
            report["suites"][suite] = {"seeds": list(seeds)}
            for name, score in scores.items():
                tag = f"{suite}_{name}"
                greedy = rollout(score, lean, f"{tag}_greedy", known, seeds)
                emitted = set()
                searched = [search(score, lean, f"{tag}_search", seed, emitted) for seed in seeds]
                metrics = summarize(searched, known)
                metrics["popped_nodes"] = sum(run["popped_nodes"] for run in searched)
                metrics["lean_checks"] = sum(run["lean_checks"] for run in searched)
                report["suites"][suite][name] = {"greedy": summarize(greedy, known), "search": metrics,
                                                  "greedy_diagnostics": diagnose(greedy)}
                records = {"greedy": greedy, "search": searched}
                if suite == "original" and name == "trained":
                    audit = audit_failed_steps(greedy, lean)
                    records["failed_edge_audit"] = audit
                    report["suites"][suite][name]["failed_edge_audit"] = {
                        "steps": audit["steps"], "ok": audit["ok"],
                    }
                write_json(args.output / f"{tag}.json", records)
                print(f"{tag}: {metrics}", flush=True)
    write_json(args.output / "summary.json", report)


if __name__ == "__main__":
    main()
