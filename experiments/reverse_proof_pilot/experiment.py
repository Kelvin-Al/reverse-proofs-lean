"""Replay one-step reverse proof extensions in Lean 4."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
from statistics import mean
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent
SEEDS = {
    "swap": ("(P ∧ Q) → (Q ∧ P)", "fun h => And.intro h.right h.left"),
    "cases": ("(P ∨ Q) → (P → R) → (Q → R) → R", "fun h f g => Or.elim h f g"),
    "compose": ("(P → Q) → (Q → R) → P → R", "fun f g p => g (f p)"),
}
PRECEDENCE = {"→": 1, "∨": 2, "∧": 3}


def parse_formula(source):
    tokens = iter(re.sub(r"\s", "", source))
    token = next(tokens, None)

    def read(minimum=1):
        nonlocal token
        if token in ("P", "Q", "R", "S"):
            left, token = token, next(tokens, None)
        elif token == "(":
            token = next(tokens, None)
            left = read()
            if token != ")":
                raise ValueError("unclosed parenthesis")
            token = next(tokens, None)
        else:
            raise ValueError("expected a propositional atom")
        while PRECEDENCE.get(token, 0) >= minimum:
            operator, token = token, next(tokens, None)
            left = (operator, left, read(PRECEDENCE[operator]))
        return left

    formula = read()
    if token is not None:
        raise ValueError("unexpected token after formula")
    return formula


def render(formula):
    if isinstance(formula, str):
        return formula
    operator, left, right = formula
    return f"({render(left)} {operator} {render(right)})"


def shape(formula, atoms):
    if isinstance(formula, str):
        return atoms(formula)
    operator, left, right = formula
    return (operator, shape(left, atoms), shape(right, atoms))


def size(formula):
    if isinstance(formula, str):
        return 0
    return 1 + size(formula[1]) + size(formula[2])


def rule_proposals(seed_formula):
    _, left, right = parse_formula(seed_formula)
    a, b, f = render(left), render(right), render(parse_formula(seed_formula))
    return [
        (f"({a} ∧ S) → ({b} ∧ S)", "fun h => And.intro (seed h.left) h.right"),
        (f"(S ∧ {a}) → {b}", "fun h => seed h.right"),
        (f"({a} ∨ {b}) → {b}", "fun h => Or.elim h seed (fun b => b)"),
        (f"{a} → ({b} ∨ S)", "fun h => Or.inl (seed h)"),
        (f"{a} → ({b} → S) → S", "fun h k => k (seed h)"),
        (f"(S → {a}) → S → {b}", "fun k s => seed (k s)"),
        (f"{a} → ({b} ∧ {a})", "fun h => And.intro (seed h) h"),
        (f"({f} → S) → S", "fun k => k seed"),
    ]


# These deliberately small lexical constraints keep proposals as pure proof terms.
TERM_TOKEN = re.compile(
    r"seed|fun|And\.(?:intro|left|right)|Or\.(?:inl|inr|elim)|"
    r"[a-z](?:\.(?:left|right))*|[()]|=>"
)


def replay_source(target, term, seed_formula, seed_proof):
    separated = term.replace("(", " ( ").replace(")", " ) ").replace("=>", " => ")
    tokens = separated.split()
    if tokens.count("seed") != 1 or not all(TERM_TOKEN.fullmatch(t) for t in tokens):
        raise ValueError("term must use one seed and the supported proof-term tokens")
    hole = f"(show {render(parse_formula(seed_formula))} from ?_)"
    wrapper = " ".join(hole if t == "seed" else t for t in tokens)
    return (
        "import Lean\nset_option autoImplicit false\n"
        "set_option warningAsError true\nset_option linter.unusedVariables false\n"
        f"theorem candidate (P Q R S : Prop) : {render(target)} := by\n"
        f"  refine ({wrapper})\n"
        f"  guard_target =ₛ {render(parse_formula(seed_formula))}\n"
        f"  exact {seed_proof}\n"
        "#print axioms candidate\n"
    )


def verify(task, lean, directory, seed_override=None):
    method, seed_name, index, target, term = task
    row = {"method": method, "seed": seed_name, "index": index,
           "target": target, "term": term}
    try:
        formula = parse_formula(target)
        if size(formula) > 12:
            raise ValueError("formula exceeds 12 connectives")
        seed_formula, seed_proof = seed_override or SEEDS[seed_name]
        source = replay_source(formula, term, seed_formula, seed_proof)
    except ValueError as error:
        return {**row, "accepted": False, "diagnostic": str(error)}

    file = directory / f"{method}_{seed_name}_{index}.lean"
    file.write_text(source, encoding="utf-8")
    try:
        result = subprocess.run(
            [lean, str(file)], cwd=ROOT, capture_output=True, text=True, timeout=30
        )
    except subprocess.TimeoutExpired:
        return {**row, "accepted": False, "diagnostic": "Lean timed out"}
    diagnostic = (result.stdout + result.stderr).strip().replace(str(file), file.name)
    accepted = result.returncode == 0 and "does not depend on any axioms" in diagnostic
    return {**row, "accepted": accepted, "diagnostic": diagnostic, "lean_source": source}


def summarize(rows):
    good = [row for row in rows if row["accepted"]]
    formulas = [parse_formula(row["target"]) for row in good]
    renamed = set()
    for formula in formulas:
        atom_ids = {}
        renamed.add(shape(formula, lambda atom: atom_ids.setdefault(atom, len(atom_ids))))
    return {
        "attempts": len(rows), "accepted": len(good),
        "unique_up_to_atom_renaming": len(renamed),
        "unique_connective_skeletons": len({shape(f, lambda _: "*") for f in formulas}),
        "mean_connectives": round(mean(map(size, formulas)), 2) if formulas else None,
    }


def skeletons(rows, method):
    return {shape(parse_formula(row["target"]), lambda _: "*")
            for row in rows if row["accepted"] and row["method"] == method}


def instantiation_probe(lean, directory):
    # Post-hoc check excluded from the frozen comparison. Change only the seed type.
    task = ("probe", "cases", 1, "((P → R) ∧ (Q → S)) → (P ∨ Q) → (R ∨ S)",
            "fun h d => seed d (fun p => Or.inl (h.left p)) (fun q => Or.inr (h.right q))")
    seed_formula, seed_proof = SEEDS["cases"]
    specialized = (seed_formula.replace("R", "(R ∨ S)"), seed_proof)
    return {
        "fixed_seed": verify(task, lean, directory),
        "instantiated_seed": verify((*task[:2], 2, *task[3:]), lean, directory, specialized),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--proposals", type=Path, default=ROOT / "llm_proposals.json")
    parser.add_argument("--output", type=Path, default=ROOT / "results.json")
    args = parser.parse_args()
    lean = args.lean if "/" not in args.lean else str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, "--version"], cwd=ROOT, text=True).strip()
    proposal_bytes = args.proposals.read_bytes()
    proposals = json.loads(proposal_bytes)
    if set(proposals) != set(SEEDS) or any(len(batch) != 8 for batch in proposals.values()):
        parser.error("expected exactly eight proposals for each of swap, cases, compose")

    tasks = []
    for seed_name, (formula, _) in SEEDS.items():
        for method, batch in (("rules", rule_proposals(formula)), ("llm", proposals[seed_name])):
            tasks.extend((method, seed_name, i, *pair) for i, pair in enumerate(batch, 1))
    controls = [
        ("control", "swap", 1, "(P ∧ Q) → (Q ∧ P)", "seed"),
        ("control", "swap", 2, "P → Q", "seed"),
    ]
    with TemporaryDirectory() as temp, ThreadPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(lambda task: verify(task, lean, Path(temp)), tasks + controls))
        probe = instantiation_probe(lean, Path(temp))
    candidates, control_rows = rows[:-2], rows[-2:]
    if [row["accepted"] for row in control_rows] != [True, False]:
        raise RuntimeError(f"unexpected control result: {control_rows!r}")

    summary = {}
    for method in ("rules", "llm"):
        group = [row for row in candidates if row["method"] == method]
        summary[method] = {
            "overall": summarize(group),
            "by_seed": {name: summarize([row for row in group if row["seed"] == name])
                        for name in SEEDS},
        }
    rule_shapes, llm_shapes = (skeletons(candidates, method) for method in ("rules", "llm"))
    summary["connective_skeleton_overlap"] = {
        "shared": len(rule_shapes & llm_shapes),
        "rules_only": len(rule_shapes - llm_shapes),
        "llm_only": len(llm_shapes - rule_shapes),
    }
    results = {
        "lean": version,
        "proposals_sha256": hashlib.sha256(proposal_bytes).hexdigest(),
        "summary": summary, "controls": control_rows, "candidates": candidates,
        "post_hoc_instantiation_probe": probe,
    }
    args.output.write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
