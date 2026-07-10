

/-
Monad itself is a typeclass
It may appear like a category but its a slightly different structure
Monad is strucutre that is a commmon abstraction for
  - List, other collections
  - Option, Except: error/ no answer
  - State
  - Long running comuptations Task/ Future / Promise
  - Side Effects
  - Id ( trick )

Common Structure:
  - Function α → m α which takes Type → Type eg. α to List α
  - Pure: α → m α
  - Map : Given a f : α → β, get m α → m β
  - flat Map : Given f : α → m β , get m α → m β

It Enables :
  - do notations
  - mutable variables
  - while loop
  - imperative programming
-/
#check Monad
-- in Python the 'for' comprehension is a monadic construction

/-!
##List as a Monad
-/
namespace ListMonad
#check List -- List is a function from Type to Type ie. List : α → List α

--Second ingredient
/-
a singleton list is a function from α → List α
-/

def pure {α : Type} ( x: α ) : List α := [x]

-- Next is the Map function
#check List.map  -- f : α → β, then we can define a pointwise function from List α → List β
#eval List.map ( fun(s : String) => s.length  ) [ "hello" , "world", "lean"]
--we can also use the dot '.' notation to run he above command too

#eval ["hello", "world", "lean"].map ( fun s => s.length )

#check List.flatMap
#eval List.range 5 --this is a map from Nat → List Nat
/-
flatMap composed with pure returns map function
-/
#eval [1 , 3, 4].map ( List.range )
#eval [1,2,3].flatMap ( List.range)

#eval List.flatMap ( fun (s : String) => List.range s.length ) [ "hello", "World", "Lean"]


def pairs {α β : Type} ( l1 : List α )( l2 : List β ) : List ( α × β ) :=
  l1.flatMap ( fun x => l2.map ( fun y => (x, y)))

#eval pairs [1,2] [ 3,4]

end ListMonad

--Option Monad
-- helps when your function sometimes can throw a null exception and error for example the half? function below
namespace optionMonad
#print Option
#check Option.map

#eval some 3 |>.map (fun x => x + 1) -- some 3 is something of type option Nat, look at #print Option

#eval none |>.map ( fun x => x + 1)

def half? : Nat → Option Nat
  | 0 => some 0
  | 1 => none
  | n + 2 => half? n |>.map ( fun x => x + 1)

#check half?
#eval half? 34

def threeHalfs? ( n : Nat) : Option Nat :=
  (half? n).map ( fun x => x * 3 )

#eval threeHalfs? 10

def threeHalfs'? (n : Nat) : Option Nat := do
  let x ← half? n
  return x*3

def quarter? ( n : Nat) : Option Nat := do
  let x ← half? n
  let y ← half? x
  return y
-- we implicitly used flat map here, here x has type Option Nat but half? takes Nat as an argument, so flatMap maps some n to n so
-- half? some n is same as half? n
end optionMonad

--State Monad
namespace stateMonad

def slowFib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | m + 1 => slowFib ( m ) + slowFib ( m -1 )

#eval slowFib 33

open Std
variable ( σ : Type)
#check StateM σ

--apply StateM to implement an effecient fibM
-- do notation works for monads?? and Id Monad lets you use do notation to write imperative code in lean
-- homotopy type theory
-- think of state as a hidden variable like in minecraft the world you generate depends on the seed, so the seed in
--some sense is a state and our output depends on the state!!



















end stateMonad
