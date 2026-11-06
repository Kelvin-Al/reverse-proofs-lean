import Lean

open Lean Meta Elab Tactic

private def propVars : List Name := [`P, `Q, `R, `S]

private def goalLocals (ctx : LocalContext) : Array Expr :=
  ctx.foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail || propVars.contains decl.userName then acc
    else acc.push decl.toExpr

-- Count only the explicit, named hypotheses encoded by the state serializer.
private def stateBinders : Expr → List Name
  | .forallE name _ body _ =>
      if name.toString.startsWith "h" then name :: stateBinders body else []
  | _ => []

private def elabStates (types : Array (TSyntax `term)) : TacticM (Array Expr) :=
  if types.isEmpty then pure #[] else withMainContext do
    types.mapM fun type => elabTermEnsuringType type (some (.sort .zero))

private def checkStates (expected : Array Expr) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  unless goals.length == expected.size do
    throwError "expected {expected.size} goals, got {goals.length}"
  for (goal, type) in goals.zip expected.toList do
    goal.withContext do
      let locals := goalLocals (← getLCtx)
      let names ← locals.toList.mapM fun expr => return (← expr.fvarId!.getDecl).userName
      unless names == stateBinders type do
        throwError "expected hypotheses {stateBinders type}, got {names}"
      let actual ← mkForallFVars locals (← goal.getType)
      unless ← isDefEq actual type do
        throwError "expected state {type}, got {actual}"

elab "assert_state " "[" expected:term,* "]" : tactic => do
  checkStates (← elabStates expected.getElems)

elab "probe_edge " "[" before:term,* "]" " to " "[" after:term,* "]" " using " tac:tactic : tactic => do
  let initial ← elabStates before.getElems
  let expected ← elabStates after.getElems
  let original ← getGoals
  let created ← withMainContext do
    initial.toList.mapM fun type => do
      let root ← mkFreshExprSyntheticOpaqueMVar type
      return (← root.mvarId!.introNP (stateBinders type).length).2
  setGoals created
  evalTactic tac
  checkStates expected
  setGoals original
