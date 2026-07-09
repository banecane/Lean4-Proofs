import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

example (a b : Nat) : a + b = b + a := by
  linarith
