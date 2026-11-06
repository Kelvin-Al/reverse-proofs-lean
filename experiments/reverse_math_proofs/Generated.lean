import Verifier
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false

theorem nat_rewrite : ∀ a b c : Nat, (a + b) + c = (a + c) + b := by
  intro h0
  intro h1
  intro h2
  rewrite [Nat.add_assoc h0 h1 h2]
  rewrite [Nat.add_comm h1 h2]
  rewrite [← Nat.add_assoc h0 h2 h1]
  rfl
#print axioms nat_rewrite

theorem nat_induction : ∀ a b : Nat, Nat.succ a + b = Nat.succ (a + b) := by
  intro h0
  intro h3
  induct_nat h3 as h1 h2
  rfl
  change Nat.succ (Nat.succ h0 + h1) = Nat.succ (Nat.succ (h0 + h1))
  rewrite [h2]
  rfl
#print axioms nat_induction

theorem list_induction : ∀ (α β : Type) (f : α → β) (xs ys : List α), List.map f (xs ++ ys) = List.map f xs ++ List.map f ys := by
  intro h0
  intro h1
  intro h2
  intro h3
  intro h4
  induct_list h3 as h5 h6 h7
  rfl
  change h2 h5 :: List.map h2 (h6 ++ h4) = h2 h5 :: (List.map h2 h6 ++ List.map h2 h4)
  rewrite [h7]
  rfl
#print axioms list_induction

theorem list_exists : ∀ (α : Type) (x : α) (xs : List α), ∃ ys : List α, List.length ys = Nat.succ (List.length xs) ∧ List.tail ys = xs := by
  intro h0
  intro h1
  intro h2
  refine ⟨h1 :: h2, ?_⟩
  constructor
  rfl
  rfl
#print axioms list_exists

theorem tree_induction : ∀ (α : Type) (t : PilotTree α), PilotTree.nodes (PilotTree.mirror t) = PilotTree.nodes t := by
  intro h0
  intro h1
  induct_tree h1 as h2 h3 h4 h5 h6
  rfl
  change 1 + (PilotTree.nodes (PilotTree.mirror h4) + PilotTree.nodes (PilotTree.mirror h3)) = 1 + (PilotTree.nodes h3 + PilotTree.nodes h4)
  rewrite [h6]
  rewrite [h5]
  rewrite [Nat.add_comm (PilotTree.nodes h4) (PilotTree.nodes h3)]
  rfl
#print axioms tree_induction
