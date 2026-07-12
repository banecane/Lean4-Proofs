-- we will understand how a proof works under the hood.
/-
First thing to understand is that a prop of type A → B just means that we have a function
from type A to type B, So if I have a proof of A then we can get a proof of B using this function


Now if you want to prove any mathematical theorem or proposition in lean, what all the proof do
is build this long chain of functions / implications such that your proof reduces to showing a term
of some other simple prop exists. These simple props are taken as axioms and so the existence of
a therm of that type is gauranteed by the axiom itself. Then this long  chain of implications / maps gives
us a term of the type of our original proposition.

A₁ → A₂ → ··· → A_n
where A₁ is the axiom and so we get the  proof of A_n. (dependent type theory)


for example if we wanna show the following prop:
∀ a: Nat, ∀ b: Nat, a + b = b + a
first of all by currying, this can be seen as function of type Nat → Nat → Prop

first strategy would be to specialise, take some arbitrary a and b
then we would be done if we can show that a term of the type Prop exists.
ie a + b = b + a
again then you use the inductive type of equality in lean to reduce this further to
basic axioms and thus you get a term of this type. ( term is exactly the proof)


--------------------------------------------------------------------------------
Why a term is considered a proof in Dependent Type Theory?
We take a simple example, suppose we wanna prove that
∃ x :Nat , 1 + x = 3
we can first specialise to some arbitrary m.
so then our goal becomes 1 + m = 3
which can be reduced to m = 2. That is we have to a term of this type exists. But
this is ensured from the inductive type of Nat. That is if n is a Nat
then Nat.succ ( n )  is also a Nat.
(this can be thought of as an axiom)
so, we see that showing that a term of type  m =2 exists actually gives us a proof
of ∃ x : Nat, 1 + x = 3.
---------------------------------------------------------------------------------

////////   THIS IS MY UNDERSTANDING AS OF NOW   /////////

-/
