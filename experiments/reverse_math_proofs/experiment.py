"""Replay reverse-generated Lean proofs beyond propositional logic."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
LANES = ("nat_rewrite", "nat_induction", "list_induction", "list_exists", "tree_induction")
MAX_STEPS = 14
HEADER = ("import Verifier\nset_option autoImplicit false\n"
          "set_option warningAsError true\nset_option linter.unusedVariables false\n")

# Single-line terms in the small vocabulary of this pilot. The inputs are frozen proposals.
TERM = re.compile(r"[\w .:+*=()\[\],∀∃→∧<>-]+")
FORBIDDEN = re.compile(r"\b(?:by|sorry|admit|unsafe|run_tac)\b")
SIMPLE = re.compile(r"rfl|constructor|intro h[0-9]|induct_(?:nat|list|tree) h[0-9] as(?: h[0-9]){2,5}")


def term(text):
    text = text.strip()
    if not TERM.fullmatch(text) or "--" in text or FORBIDDEN.search(text):
        raise ValueError(f"unsupported term: {text!r}")
    return text


def encode_state(goals):
    terms = []
    for goal in goals:
        context, target = map(str.strip, goal.split("|"))
        target = term(target)
        if context:
            target = f"(∀ {term(context)}, {target})"
        terms.append(target)
    return "[" + ", ".join(terms) + "]"


def is_closed(goals):
    return len(goals) == 1 and not goals[0].split("|")[0].strip()


def checked_tactic(tactic):
    if SIMPLE.fullmatch(tactic):
        return tactic
    if tactic.startswith("change "):
        return f"change {term(tactic[7:])}"
    if tactic.startswith("rewrite [") and tactic.endswith("]"):
        rule = tactic[9:-1]
        reverse = "← " if rule.startswith("← ") else ""
        return f"rewrite [{reverse}{term(rule[len(reverse):])}]"
    if tactic.startswith("refine ⟨") and tactic.endswith(", ?_⟩"):
        return f"refine ⟨{term(tactic[8:-5])}, ?_⟩"
    raise ValueError(f"unsupported tactic: {tactic!r}")


def edge_source(before, tactic, after):
    return (HEADER + "example : True := by\n"
            f"  probe_edge {encode_state(before)} to {encode_state(after)} "
            f"using {checked_tactic(tactic)}\n  exact True.intro\n")


def proof_source(target, tactics, states):
    lines = [HEADER, f"theorem generated : {term(target)} := by\n"]
    for index, tactic in enumerate(tactics):
        lines.append(f"  assert_state {encode_state(states[index])}\n")
        lines.append(f"  {checked_tactic(tactic)}\n")
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


def new_lanes():
    return {key: {"states": [[]], "edges": [], "status": "active"} for key in LANES}


def check_round(method, step, batch, lanes, lean, pool):
    active = {key for key, lane in lanes.items() if lane["status"] == "active"}
    if active != set(batch):
        raise ValueError(f"{method} round {step}: expected {sorted(active)}, got {sorted(batch)}")

    def check(key):
        tactic, before = batch[key]
        try:
            if not before:
                raise ValueError("a predecessor must have at least one goal")
            source = edge_source(before, tactic, lanes[key]["states"][-1])
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


def controls(lean):
    before = ["(h0 : Nat) | Nat.succ 0 + h0 = Nat.succ (0 + h0)"]
    base = "| Nat.succ 0 + 0 = Nat.succ (0 + 0)"
    step = ("(h1 : Nat) (h2 : Nat.succ 0 + h1 = Nat.succ (0 + h1)) | "
            "Nat.succ 0 + Nat.succ h1 = Nat.succ (0 + Nat.succ h1)")
    tactic = "induct_nat h0 as h1 h2"
    good = lean.check("control_correct_ih", edge_source(before, tactic, [base, step]))
    wrong_ih = step.replace("(h2 : Nat.succ 0 + h1 = Nat.succ (0 + h1))", "(h2 : h1 = h1)")
    bad = lean.check("control_wrong_ih", edge_source(before, tactic, [base, wrong_ih]))
    if not good["ok"] or bad["ok"] or "expected state" not in bad["diagnostic"]:
        raise RuntimeError(f"unexpected induction controls: {good}, {bad}")
    return {"correct_ih": good, "wrong_ih": bad}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--gate-cache", type=Path)
    parser.add_argument("--output", type=Path, default=ROOT / "results.json")
    args = parser.parse_args()
    executable = args.lean if "/" not in args.lean else str(Path(args.lean).resolve())
    rounds = read_rounds(ROOT / "llm_rounds")
    if len(rounds) > MAX_STEPS:
        raise ValueError("too many rounds")
    cache = args.gate_cache
    saved = json.loads(cache.read_text()) if cache and cache.exists() else {"rounds": [], "lanes": new_lanes()}
    if saved["rounds"] != rounds[:len(saved["rounds"])]:
        raise ValueError("the recorded round prefix changed")
    lanes = saved["lanes"]
    with TemporaryDirectory() as temp, ThreadPoolExecutor(max_workers=4) as pool:
        lean = Lean(executable, Path(temp))
        for step in range(len(saved["rounds"]), len(rounds)):
            check_round("math", step + 1, rounds[step], lanes, lean, pool)
        if cache:
            cache.write_text(json.dumps({"rounds": rounds, "lanes": lanes}, ensure_ascii=False))
            print(json.dumps({key: [lane["status"], lane["states"][-1],
                                   [e["diagnostic"] for e in lane["edges"] if not e["ok"]]]
                              for key, lane in lanes.items()}, ensure_ascii=False))
            return
        for key, lane in lanes.items():
            if lane["status"] == "closed":
                states = lane["states"][::-1]
                target = states[0][0].split("|")[1].strip()
                tactics = [edge["tactic"] for edge in lane["edges"][::-1]]
                lane["target"] = target
                lane["tactics"] = tactics
                lane["proof"] = lean.check(key, proof_source(target, tactics, states), True)
        checks = controls(lean)
    summary = {key: {"verified_edges": sum(edge["ok"] for edge in lane["edges"]),
                     "rejected_edges": sum(not edge["ok"] for edge in lane["edges"]),
                     "proved": lane.get("proof", {}).get("ok", False)}
               for key, lane in lanes.items()}
    output = {"lean": lean.version, "summary": summary, "lanes": lanes, "controls": checks}
    args.output.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
