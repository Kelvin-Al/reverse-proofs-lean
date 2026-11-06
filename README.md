# Reverse Proofs in Lean

A proof-of-concept for generating a theorem and its proof together. The generator starts from an empty goal list, proposes a predecessor proof state and a tactic, and asks Lean to check that running the tactic produces the current state. Once the trace reaches a closed theorem statement, Lean replays the tactics in forward order and checks the complete proof.

The initial pilot used existing proof fragments. The later experiments start from an empty goal list with no supplied theorem statement or seed proof. They cover propositional logic, specified case-split structures, natural-number arithmetic, lists, and a custom binary tree.

## Reproduce the experiments

Install Python 3.10+ and Lean 4.19.0. The pinned Lean version is recorded in `lean-toolchain`. No Python packages or mathlib installation are required.

Run an experiment from the repository root:

```sh
python3 experiments/reverse_math_proofs/experiment.py
```

Use `--lean /absolute/path/to/lean` to select a Lean binary explicitly. Use `--output /path/to/results.json` to keep the included result snapshot separate from your run. Each script replays the recorded candidates against Lean. The snapshot records the checked Lean source, proof traces, and diagnostics.

| Experiment | What it checks | Recorded outcome |
|---|---|---|
| [Seed-based pilot](experiments/reverse_proof_pilot/README.md) | Extend a given proof fragment by one step | 24/24 rule candidates and 23/24 LLM candidates passed |
| [Generation from empty](experiments/reverse_proof_generator/PROTOCOL.md) | Generate complete propositional statements and proofs | 8/8 in each of three groups. The reverse LLM traces had 43 verified transitions |
| [Controlled branching](experiments/controlled_reverse_proofs/PROTOCOL.md) | Satisfy nested case-split requirements and use the branch hypotheses | 6/6 in each of three groups. The reverse LLM traces had 60 verified transitions |
| [Mathematical examples](experiments/reverse_math_proofs/PROTOCOL.md) | Generate proofs with rewriting, induction, and existential witnesses | 5 complete proofs and 40 verified transitions |

See [Generated.lean](experiments/reverse_math_proofs/Generated.lean) for the five resulting Lean declarations. They cover an arithmetic rearrangement, an identity proved by induction on a natural number, the interaction of list mapping and concatenation, a list existence statement with an explicit witness, and preservation of node count under binary-tree mirroring.

The recorded LLM proposals came from a prompted dialogue model. The scripts reproduce validation of those proposals. The examples are small and include familiar results. The experiments demonstrate the feasibility of this workflow within the tested fragments.

## Small learned policy

The [training baseline](training/README.md) fits 98 weights from scratch to rank inverse tactic families. It uses the verified propositional traces and checks the decoded steps and complete proofs with Lean.

See [DISCUSSION.md](DISCUSSION.md) for the draft discussion on proof-state representation and reverse generation.
