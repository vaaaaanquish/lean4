import Lean

/-!
Tests `Elab.parallelKernelCheck`: theorem proofs are checked by the kernel on separate tasks, later
declarations do not wait for these checks, and a proof rejected by the kernel is still reported.
Also tests `Elab.memoizeKernelCheck`, which skips the check of a theorem that repeats an accepted
one but must not skip it for a rejected one.
-/

open Lean Elab Tactic

theorem ok₁ (a : Nat) : a + 0 = a := by omega

theorem ok₂ (a : Nat) : 0 + a + 0 = a := by
  have := ok₁ a
  omega

/-- Closes the goal with a term of the wrong type, which only the kernel notices. -/
elab "bogus_proof" : tactic => do
  (← getMainGoal).assign (mkConst ``True.intro)

/--
error: (kernel) declaration type mismatch, 'bad' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
theorem bad : False := by bogus_proof

-- The statement of `bad` is available even though its proof was rejected.
theorem usesBad : 1 = 2 := bad.elim

/--
error: (kernel) declaration type mismatch, 'badSeq' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
set_option Elab.parallelKernelCheck false in
theorem badSeq : False := by bogus_proof

/--
error: (kernel) application type mismatch
  ⟨trivial, fun x => True.intro⟩
argument has type
  False → True
but function has type
  (False → False) → True ∧ (False → False)
-/
#guard_msgs in
theorem badNested : True ∧ (False → False) := ⟨trivial, fun _ => by bogus_proof⟩

/-- info: 'ok₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ok₂

-- Identical statements and proofs referring to imported constants only: the second check is skipped.
theorem dup₁ (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
theorem dup₂ (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega

set_option Elab.memoizeKernelCheck false in
theorem dup₃ (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega

/--
error: (kernel) declaration type mismatch, 'badDup₁' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
theorem badDup₁ : False := by bogus_proof

-- A rejected proof is not memoized, so its repetition is rejected as well.
/--
error: (kernel) declaration type mismatch, 'badDup₂' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
theorem badDup₂ : False := by bogus_proof

/-- info: 'badDup₂' depends on axioms: [badDup₂] -/
#guard_msgs in
#print axioms badDup₂
