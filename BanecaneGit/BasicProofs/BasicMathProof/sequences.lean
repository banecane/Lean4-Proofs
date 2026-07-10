import Mathlib

-- First, we define the standard mathematical definition of a sequence limit:
-- For every epsilon > 0, there is a starting index N, such that all subsequent terms are within epsilon of l.
def convergesTo (l : ℝ) (u : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε


-- PROOF 1: Constant sequence converges to its constant value
example (h : ∀ n, u n = l) : convergesTo l u := by
  unfold convergesTo
  -- Goal is now: ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

  intro ε he
  -- `intro` strips away the universal quantifier (∀ ε) and the implication (ε > 0).
  -- Context now has: (ε : ℝ) and (he : ε > 0)
  -- New Goal: ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

  use 0
  -- We instantiate the existential quantifier (∃ N) with 0.
  -- New Goal: ∀ n ≥ 0, |u n - l| ≤ ε

  intro m hm
  -- `intro` pulls out the next arbitrary index `m` and the hypothesis `hm : m ≥ 0`.
  -- Context now has: (m : ℕ) and (hm : m ≥ 0)
  -- New Goal: |u m - l| ≤ ε

  rw [h]
  -- We rewrite using our hypothesis `h : ∀ n, u n = l` specialized to `m`.
  -- The term `u m` becomes `l`.
  -- New Goal: |l - l| ≤ ε

  simp
  -- `simp` reduces `|l - l|` to `|0|`, and then to `0`.
  -- New Goal: 0 ≤ ε

  linarith
  -- Linear arithmetic closes the goal because our context contains `he : ε > 0`, which implies `0 ≤ ε`.


-- PROOF 2: If a sequence converges to l > 0, its terms eventually stay above l/2
example (h : convergesTo l u) (hl : l > 0) :
  ∃ N, ∀ n ≥ N, (u n) ≥ l/2 := by

  unfold convergesTo at h
  -- This unpacks the definition inside our hypothesis.
  -- Context now has: h : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

  specialize h (l/2) (by positivity)
  -- We pin down the universal quantifier in `h` by setting ε = l/2.
  -- `by positivity` instantly proves the required side-condition that `l/2 > 0` since `hl : l > 0`.
  -- Context updates to: h : ∃ N, ∀ n ≥ N, |u n - l| ≤ l/2

  rcases h with ⟨m, hm⟩
  -- We destruct the existential hypothesis `h`.
  -- It gives us a specific witness index `m` and a new hypothesis `hm`.
  -- Context now has: (m : ℕ) and (hm : ∀ n ≥ m, |u n - l| ≤ l/2)

  use m
  -- We choose this exact same `m` to fulfill the existential requirement of our main goal.
  -- New Goal: ∀ n ≥ m, u n ≥ l/2

  intro p hp
  -- We introduce an arbitrary index `p` that is past our threshold.
  -- Context now has: (p : ℕ) and (hp : p ≥ m)
  -- New Goal: u p ≥ l/2

  specialize hm p hp
  -- We feed our specific index `p` and our proof `hp` into the local rule `hm`.
  -- Context updates to: hm : |u p - l| ≤ l/2

  grind
  -- `grind` automatically splits the absolute value inequality `|x| ≤ y` into
  -- `-y ≤ x` and `x ≤ y` (specifically `-l/2 ≤ u p - l`), handles the arithmetic,
  -- and finishes the proof.
