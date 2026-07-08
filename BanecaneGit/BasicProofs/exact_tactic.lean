/-
If our hypothesis contains the proof, exact tactic lets us use it to prove the theorem
-/
theorem one_eq_succ_zero : Nat.succ 0 = 1 := rfl
example (h : Nat.succ 0 ≤ 2) : 1 ≤ 2 := by
  rw[ one_eq_succ_zero] at h --at tells Lean to apply the tactic at h
  -- which in this case is our hypothesis
  exact h -- Now our hypothesis is exactly 1 ≤ 2, so exact h tactic
  --uses it to prove the example/ theorem

  /-
  Below is a more sofisticated example of this
  We prove that x + 1 = y + 1 → x = y
  -/

example (x y : Nat): x + 1 = y + 1 → x = y := by
  intro h --introduces a variable that we can manipulate
  repeat rw [← one_eq_succ_zero] at h
  rw [ Nat.add_succ, Nat.add_succ, Nat.add_zero, Nat.add_zero] at h
  rw[Nat.succ_inj] at h
  exact h

/-
Next we will see how to prove 0 ≠ 1
In lean we usually we have the axiom which says succ n ≠ 0 ∀ n ∈ Nat
-/
#check Nat.succ_ne_zero --Can be thought of as a tactic
--So if we have a witness to the type 0 =1 , we can apply Nat.succ_ne_zero to it
#print Nat.succ_ne_zero

example ( h : 0 = 1) : False := by
  rw[← one_eq_succ_zero] at h
  grind only
-- come back and complete the proof without grind.
