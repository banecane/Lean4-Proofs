-- Understanding inductive types in lean

namespace langur
-- my_list : linked list implementation in lean

inductive  my_list ( α : Type ) where
  | nil : my_list α
  | cons : α → my_list α → my_list α

-- we defined nil as the null objective for our inductive type.
-- cons can be thought of as an equivalent to a pointer
/-
In this case its exactly a function which when given a term of type α
gives us a function from one my_list α to another my_list α
-/
#check my_list.nil --defines a null object for our inductive type
#check my_list.cons

def l1 : my_list Nat := my_list.cons 4 ( my_list.cons 8 ( my_list.cons 5 ( my_list.nil)))
#check l1
#eval l1

--function to calculate number of elements in our linked list

def my_list_length { α : Type} ( l : my_list α ) : Nat :=
  match l with
    | my_list.nil => 0
    | my_list.cons (_m : α ) ( xs ) => 1 + ( my_list_length xs)

#check my_list_length
#eval my_list_length l1

--Here we make an axiom similar to the Piano axiom that
-- my_list.cons (h : α ) ( l : my_list α ) ≠ my_list.nil
axiom my_list_cons_not_empty {α : Type}{ h : α } {l : my_list α }: my_list.cons h ( l : my_list α ) ≠ my_list.nil


theorem l1_not_empty : l1 ≠ my_list.nil := by apply my_list_cons_not_empty

--One can try checking what happens if we try to prove that an empty list is not empty

def l2  : my_list Nat := my_list.nil --defines an empty my_list

--theorem l2_not_empty : l2 ≠ my_list.nil := by apply my_list_cons_not_empty  )
--it clearly tells us that based on our axiom the apply tactic does not work this time



--writing a function to delete an element from my_list
-- One advantage of lean is that in these type of functions we can ask the user
-- to provide us the proof that the list is not empty

#check my_list_length l1 ≠ 0
def my_list_delete_element {α : Type}( l : my_list α )(h : l ≠ my_list.nil ) : my_list α :=
  match l with
    | my_list.cons _h ( my_list.nil ) => my_list.nil
    | my_list.cons _h ( xs ) => xs

#eval l1
#eval my_list_delete_element l1 l1_not_empty

--Next we write a program to find the smallest element in my_list
set_option checkBinderAnnotations false
def smallest_in_my_list ( l : my_list Nat ) : Nat :=
  match l with
    | my_list.nil => 1000
    | my_list.cons x ( my_list.nil) => x
    | my_list.cons x ( my_list.cons y ( xs )) => if ( x ≤ smallest_in_my_list ( my_list.cons y ( xs ) ) ) then x else smallest_in_my_list ( (my_list.cons y ( xs)))
-- right now we are not requiring the user to provide the proof that list is not empty because we are working with our own data structure
-- this can be done easily for the inductive type Nat that lean provides as the code is much more cleaner
-- also we can take in any type instead of Nat as long as it has some ordering, though we may have to geneate some type class instance for lean.


#check smallest_in_my_list
#eval smallest_in_my_list l1
#eval smallest_in_my_list ( my_list.cons 1 ( l1 ) )

/-
Future additions: (1) prove that this function gives you the smallest element in the list
  (2) Talk about the .rec function that lean generates for every inductive type

-/



--BINARY TREE
--Next we implement a binary tree in lean
/-
an example of Binary Tree :
         Node
        /    \
      Node   Leaf
      /  \
    Leaf Leaf
-/

inductive my_bin (α : Type) where
  | nil : my_bin α
  | node : α → my_bin α → my_bin α → my_bin α

#print my_bin
-- To understand why this defines a binary tree consider the following example

def b1 : my_bin Nat := my_bin.node 3 (my_bin.nil) (my_bin.node 4 ( my_bin.nil) (my_bin.nil))
def b2 : my_bin Nat := my_bin.node 23 ( b1 ) ( my_bin.node 12 ( my_bin.nil) ( my_bin.nil ))
-- so as you can see while defining we can think of assigning the parent node the value 3

-- we can try to put all the element in a binary tree into a list, which will give some idea of how it looks

def print_bin_tree {α : Type } ( b : my_bin α ) : List α :=
  match b with
    | my_bin.nil => []
    | my_bin.node h ( b_1 ) ( b_2 ) =>  h :: ( List.append ( print_bin_tree b_1 ) ( print_bin_tree b_2))

#check print_bin_tree
#eval print_bin_tree b1
#eval print_bin_tree b2
-- a similar program can calculate the number of elements in a binary tree.
-- we can even write a function to calculate the depth of this binary tree

def depth_bin_tree {α : Type} ( b : my_bin α ) : Nat :=
  match b with
    | my_bin.nil => 0
    | my_bin.node _h ( b_1 ) ( b_2) => if ( depth_bin_tree b_1 ≥ depth_bin_tree b_2 ) then (1 + depth_bin_tree b_1 ) else ( 1 + depth_bin_tree b_2)

#check depth_bin_tree
#eval depth_bin_tree b1
#eval depth_bin_tree b2


open my_bin --my_list to my_bin

def my_list_to_my_bin {α  : Type} ( l : my_list α ) : my_bin α :=
  match l with
    | my_list.nil => nil
    | my_list.cons h ( xs ) => node h ( my_list_to_my_bin ( xs )) ( nil)


#eval print_bin_tree (node 43  ( my_list_to_my_bin l1 ) nil  )
end langur
