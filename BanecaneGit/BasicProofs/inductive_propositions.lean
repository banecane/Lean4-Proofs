-- we will use inductive type to define even Nat

inductive IsEven : Nat → Prop where
  | IsEven : IsEven 0
  | AddToEven {n} (h : IsEven n ) : IsEven (n+2)

open IsEven


theorem ZeroIsEven : IsEven 0 := by apply IsEven.IsEven

theorem TwoIsEven : IsEven 2 := by apply AddToEven ZeroIsEven

theorem FourIsEven : IsEven 4:= by apply AddToEven TwoIsEven


-- Next we wanna prove that any number of the form 2*n is even.


theorem Two_n_IsEven ( n : Nat )( k : Nat) ( h : ∃ k ∈ Nat, n = 2*k ) : IsEven n  := by
  induction n with
    | zero =>
