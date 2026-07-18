import Mathlib


namespace banecane
/-
Today our goal is to implement a BST in Lean and then use to implement Tree Sort
Finally we will prove that Tree sort actually sorts the list.
-/
variable {α : Type} [LinearOrder α]
inductive BST (α : Type) where
  | null : BST α
  | cons : α → BST α → BST α → BST α

--structure is exactly given by
-- parent node -> left child -> right child

--inserts a new element into the BST
def insert (bs : BST α) (val : α) : BST α  :=
  match bs with
    | BST.null => BST.cons val ( BST.null ) ( BST.null )
    | BST.cons h ( b1 ) ( b2 ) => if( h > val ) then
        BST.cons h ( insert b1 val ) ( b2 )
      else
        BST.cons h ( b1 ) ( insert b2 val )


variable (x : BST Nat := BST.null)

#check x
def y :=  insert ( insert ( insert ( insert ( insert x 4 ) 6 ) 1 ) 7 ) 5
#eval y


-- converts a list into a BST
def list_to_BST (ls : List α) (bs : BST α) : BST α  :=
  match ls with
    | List.nil => bs
    | List.cons h ( l1 ) => list_to_BST l1 ( insert bs h )

#check list_to_BST

def xs := [ 1,4,3,2,6,9,8,7]
#eval xs
def test := list_to_BST xs BST.null
#eval test

-- We will implement a tree sort algorithm now
--in order traversal of BST
def BST_to_list (bs : BST α) : List α  :=
  match bs with
    | BST.null => List.nil
    | BST.cons h b1 b2 => List.append (BST_to_list b1)  (  h :: (BST_to_list b2))


def test2 := BST_to_list test
#check List.append

#eval test2

/-
Now we will try to give a proof that tree sort actually sorts the list
-/


--First we need to define what a sorted list is

inductive sorted : List α → Prop
  | nil : sorted []
  | singleton (x : α ) : sorted [x]
  | step ( x y : α ) ( l : List α ) ( hxy : x ≤ y ) (tail_sorted : sorted (y :: l) )
    : sorted ( x :: y :: l )


-- according to the above definition both [1] and [1,2] are sorted.
example : sorted [1] := sorted.singleton 1
example : sorted [1,2] := sorted.step 1 2 List.nil (by simp) (sorted.singleton 2)

#check sorted.step

--next we need to define what a valid Binary Search Tree is

inductive isBst : BST α → Prop
  | nil : isBst BST.null
  | singleton (h : α ) : isBst (BST.cons h BST.null BST.null)
  | node : sorry


#eval BST.cons 4 BST.null BST.null
end banecane
