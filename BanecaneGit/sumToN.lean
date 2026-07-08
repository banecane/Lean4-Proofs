/-
We define a function to find the sum of first n
numbers and then prove an exact formula
-/

def sumToN ( n : Nat) : Nat :=
  match n with
    | 0 => 0
    | m + 1 => sumToN m + ( m + 1)
#check sumToN --is a function from Nat → Nat\
#eval sumToN 10 -- 55

/-
Now we will prove that the sum of first n natural numbers is
n*(n +1)/2
-/
theorem sumToN_proof (n : Nat) : 2*sumToN n = n*(n+1) := by
  induction n with
    | zero => rw[Nat.add_zero, Nat.zero_mul,sumToN,Nat.mul_zero]
    | succ k ih => rw[sumToN, Nat.mul_add, ih]; grind

/-
see the basic structure of an induction argument
 | zero => tells us that we will prove the base claim
 | succ k ih => prove the induction step where our hypothesis is
 represented by ih, so in this case its
  ih : 2*sumToN k = k * (k + 1)
  We can use it in our proof as an proof, like we did by passing it
  as an proof to rw ( called the re write tactic)
-/
