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

private abbrev BranchPath := List Bool

private structure BranchWitness where
  goal : MVarId
  hyp : FVarId

private def freshBranchHyp (parent : LocalContext) (goal : MVarId) : TacticM Expr :=
  goal.withContext do
    let introduced := (goalLocals (← getLCtx)).filter fun expr =>
      (parent.find? expr.fvarId!).isNone
    unless introduced.size == 1 do
      throwError "contract: expected exactly one new branch hypothesis"
    return introduced[0]!

-- A case node is addressed by its case ancestry; other tactics preserve that ancestry.
elab "check_structure " kind:ident " [" tactics:tactic,* "]" : tactic => do
  let mut frontier : List BranchPath := [[]]
  let mut splitPaths : List BranchPath := []
  let mut witnesses : Array BranchWitness := #[]
  for tac in tactics.getElems do
    let goal :: tail ← getUnsolvedGoals | throwError "contract: no goal for tactic"
    let path :: pending := frontier | throwError "contract: missing goal ancestry"
    let parent := (← goal.getDecl).lctx
    evalTactic tac
    let after ← getUnsolvedGoals
    unless after.length >= tail.length && after.drop (after.length - tail.length) == tail do
      throwError "contract: a tactic changed a pending goal"
    let children := after.take (after.length - tail.length)
    if tac.raw.getKind == `Lean.Parser.Tactic.«tactic_<;>_» then
      -- The Python grammar permits the combinator only in 'cases ... <;> rename_i ...'.
      let [left, right] := children | throwError "contract: cases must create two goals"
      if splitPaths.contains path then
        throwError "contract: multiple case splits at one ancestry"
      let leftHyp ← freshBranchHyp parent left
      let rightHyp ← freshBranchHyp parent right
      let leftTy ← left.withContext (inferType leftHyp)
      let rightTy ← right.withContext (inferType rightHyp)
      if ← withMainContext (isDefEq leftTy rightTy) then
        throwError "contract: identical alternatives"
      splitPaths := splitPaths ++ [path]
      witnesses := witnesses.push ⟨left, leftHyp.fvarId!⟩ |>.push ⟨right, rightHyp.fvarId!⟩
      frontier := [path ++ [false], path ++ [true]] ++ pending
    else
      frontier := List.replicate children.length path ++ pending
  unless (← getUnsolvedGoals).isEmpty do
    throwError "contract: unclosed proof"
  let valid :=
    if kind.getId == `chain then
      splitPaths.length == 2 && splitPaths.contains [] &&
        (splitPaths.contains [false] || splitPaths.contains [true])
    else if kind.getId == `balanced then
      splitPaths.length == 3 && splitPaths.contains [] &&
        splitPaths.contains [false] && splitPaths.contains [true]
    else false
  unless valid do
    throwError "contract: case tree has paths {splitPaths}"
  for witness in witnesses do
    let some value ← getExprMVarAssignment? witness.goal
      | throwError "contract: no proof term for branch"
    let term ← instantiateMVars value
    unless (Expr.fvar witness.hyp).occurs term do
      throwError "contract: a branch hypothesis was unused"
