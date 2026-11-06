"""Run reverse proof generation rounds and verify all final proofs."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

from formulas import parse_formula, render, shape, size

ROOT = Path(__file__).resolve().parent
LANES = tuple("abcdefgh")
MAX_STEPS = 8
HEADER = ("import Verifier\nset_option autoImplicit false\n"
          "set_option warningAsError true\nset_option linter.unusedVariables false\n")
TACTIC = re.compile(
    r"intro h[0-9]|exact h[0-9](?:\.(?:left|right))*|apply h[0-9]|constructor|left|right|"
    r"cases h[0-9] <;> rename_i h[0-9]"
)


def formula(text):
    tree = parse_formula(text)
    if size(tree) > 12:
        raise ValueError("formula has more than 12 connectives")
    return render(tree)


def encode_state(goals):
    terms = []
    for goal in goals:
        context, target = goal.split("|")
        context = context.strip()
        term = formula(target)
        if context:
            bindings = []
            for item in context.split(","):
                name, typ = map(str.strip, item.split(":"))
                if not re.fullmatch(r"h[0-9]", name) or name in [n for n, _ in bindings]:
                    raise ValueError("invalid or repeated local hypothesis")
                bindings.append((name, formula(typ)))
            term = "(∀ " + " ".join(f"({n} : {t})" for n, t in bindings) + f", {term})"
        terms.append(term)
    return "[" + ", ".join(terms) + "]"


def is_closed(goals):
    return len(goals) == 1 and not goals[0].split("|")[0].strip()


def checked_tactic(tactic):
    if not TACTIC.fullmatch(tactic):
        raise ValueError(f"unsupported tactic {tactic!r}")
    return tactic


def edge_source(before, tactic, after):
    return (HEADER + "example (P Q R S : Prop) : True := by\n"
            f"  probe_edge {encode_state(before)} to {encode_state(after)} "
            f"using {checked_tactic(tactic)}\n  exact True.intro\n")


def proof_source(target, tactics, states=None):
    lines = [HEADER, f"theorem generated (P Q R S : Prop) : {formula(target)} := by\n"]
    for index, tactic in enumerate(tactics):
        if states is not None:
            lines.append(f"  assert_state {encode_state(states[index])}\n")
        lines.append(f"  {checked_tactic(tactic)}\n")
    if states is not None:
        lines.append(f"  assert_state {encode_state(states[-1])}\n")
    return "".join(lines) + "#print axioms generated\n"


class Lean:
    def __init__(self, executable, directory):
        self.exe = executable
        self.directory = directory
        self.env = {**os.environ, "LEAN_PATH": str(directory)}
        for name in ("Verifier.lean", "lean-toolchain"):
            (directory / name).write_bytes((ROOT / name).read_bytes())
        version = self.run(["--version"])
        if version.returncode:
            raise RuntimeError(version.stdout + version.stderr)
        self.version = version.stdout.strip()
        result = self.run(["-o", "Verifier.olean", "Verifier.lean"])
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)

    def run(self, args):
        return subprocess.run([self.exe, *args], cwd=self.directory, env=self.env,
                              text=True, capture_output=True, timeout=30)

    def check(self, name, source, proof=False):
        file = f"{name}.lean"
        (self.directory / file).write_text(source, encoding="utf-8")
        result = self.run([file])
        diagnostic = (result.stdout + result.stderr).strip()
        ok = result.returncode == 0 and (not proof or "does not depend on any axioms" in diagnostic)
        return {"ok": ok, "diagnostic": diagnostic, "source": source}


def read_rounds(directory):
    files = sorted(directory.glob("round_*.json"))
    if [file.name for file in files] != [f"round_{i:02}.json" for i in range(1, len(files)+1)]:
        raise ValueError("round files must be consecutive starting from round_01.json")
    return [json.loads(file.read_text()) for file in files]


def reverse_run(method, rounds, lean, pool):
    lanes = {key: {"states": [[]], "edges": [], "status": "active"} for key in LANES}
    if len(rounds) > MAX_STEPS:
        raise ValueError("too many rounds")
    for step, batch in enumerate(rounds, 1):
        active = {key for key, lane in lanes.items() if lane["status"] == "active"}
        if active != set(batch):
            raise ValueError(f"{method} round {step}: expected {sorted(active)}, got {sorted(batch)}")

        def check(key):
            tactic, before = batch[key]
            after = lanes[key]["states"][-1]
            try:
                if not before:
                    raise ValueError("a predecessor must have at least one goal")
                source = edge_source(before, tactic, after)
            except ValueError as error:
                return {"ok": False, "diagnostic": str(error)}
            return lean.check(f"{method}_{step:02}_{key}", source)

        for key, result in zip(batch, pool.map(check, batch)):
            lane = lanes[key]
            tactic, before = batch[key]
            lane["edges"].append({"tactic": tactic, "proposed_state": before, **result})
            if not result["ok"]:
                lane["status"] = "rejected_edge"
                continue
            lane["states"].append(before)
            if is_closed(before):
                lane["status"] = "closed"

    def replay(item):
        key, lane = item
        if lane["status"] != "closed":
            return
        states = lane["states"][::-1]
        target = states[0][0].split("|")[1].strip()
        tactics = [edge["tactic"] for edge in lane["edges"][::-1]]
        lane["target"] = target
        lane["tactics"] = tactics
        lane["proof"] = lean.check(f"{method}_proof_{key}", proof_source(target, tactics, states), True)

    list(pool.map(replay, lanes.items()))
    return lanes


def direct_run(proposals, lean, pool):
    if set(proposals) != set(LANES):
        raise ValueError("expected eight direct proposals")

    def check(key):
        target, tactics = proposals[key]
        row = {"target": target, "tactics": tactics, "status": "complete"}
        try:
            if not 1 <= len(tactics) <= MAX_STEPS:
                raise ValueError("proof exceeds tactic budget or is empty")
            source = proof_source(target, tactics)
        except ValueError as error:
            return {**row, "proof": {"ok": False, "diagnostic": str(error)}}
        return {**row, "proof": lean.check(f"direct_proof_{key}", source, True)}

    return dict(zip(proposals, pool.map(check, proposals)))


def summarize(lanes):
    valid = [lane for lane in lanes.values() if lane.get("proof", {}).get("ok")]
    trees = [parse_formula(lane["target"]) for lane in valid]
    renamed = set()
    for tree in trees:
        ids = {}
        renamed.add(shape(tree, lambda atom: ids.setdefault(atom, len(ids))))
    return {
        "attempts": len(lanes),
        "proved": len(valid),
        "unique_up_to_renaming": len(renamed),
        "unique_connective_skeletons": len({shape(tree, lambda _: "*") for tree in trees}),
        "proof_lengths": [len(lane["tactics"]) for lane in valid],
        "tactic_families": sorted({t.split()[0] for lane in valid for t in lane["tactics"]}),
        "proofs_with_cases": sum(any(t.startswith("cases ") for t in lane["tactics"]) for lane in valid),
        "accepted_edges": sum(e["ok"] for lane in lanes.values() for e in lane.get("edges", [])),
        "rejected_edges": sum(not e["ok"] for lane in lanes.values() for e in lane.get("edges", [])),
    }


def controls(lean):
    expected = ["h1:P | Q ∨ P", "h1:Q | Q ∨ P"]
    source = lambda after: edge_source(["h0:P ∨ Q | Q ∨ P"], "cases h0 <;> rename_i h1", after)
    checks = {
        "correct_order": lean.check("control_correct", source(expected)),
        "reversed_goals": lean.check("control_wrong", source(expected[::-1])),
    }
    if not checks["correct_order"]["ok"] or checks["reversed_goals"]["ok"]:
        raise RuntimeError(f"unexpected verifier controls: {checks}")
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--gate", action="store_true", help="show active LLM lanes after current rounds")
    parser.add_argument("--output", type=Path, default=ROOT / "results.json")
    args = parser.parse_args()
    executable = args.lean if "/" not in args.lean else str(Path(args.lean).resolve())
    with TemporaryDirectory() as temp, ThreadPoolExecutor(max_workers=4) as pool:
        lean = Lean(executable, Path(temp))
        llm = reverse_run("llm_reverse", read_rounds(ROOT / "llm_rounds"), lean, pool)
        if args.gate:
            print(json.dumps({key: [lane["status"], lane["states"][-1],
                                   [e["diagnostic"] for e in lane["edges"] if not e["ok"]]]
                              for key, lane in llm.items()}, ensure_ascii=False, indent=2))
            return
        from rules import rule_rounds
        rules = reverse_run("rules", rule_rounds(), lean, pool)
        direct = direct_run(json.loads((ROOT / "direct.json").read_text()), lean, pool)
        checks = controls(lean)

    methods = {"llm_reverse": llm, "rules": rules, "llm_direct": direct}
    summary = {name: summarize(lanes) for name, lanes in methods.items()}
    output = {"lean": lean.version, "summary": summary, "methods": methods, "controls": checks}
    args.output.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
