(* Implementation and correctness proof of fast mergeable priority queues
   using binomial queues.   Andrew W. Appel, October 2009.

 Required reading:
 "Binomial Queues", Section 9.7 of
  Algorithms 3rd Edition in Java, Parts 1-4:
    Fundamentals, Data Structures, Sorting, and Searching,
  by Robert Sedgewick.  Addison-Wesley, 2002.
  http://www.cs.princeton.edu/~appel/BQ.pdf
*)

(********************************* Preliminaries  *****************************)
Require Import SfLib.  (* SfLib is a module in "Software Foundations" by Pierce et al. *)
Require Import Permutation.
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Definition blt_nat (n m: nat) := ble_nat (S n) m.

Definition bgt_nat (n m : nat) := blt_nat m n.

Ltac inv H := inversion H; clear H; subst.

(****************** Binomial Heaps Implementation ****************************)

Definition key := nat.

Inductive tree : Type :=
|  Node: key -> tree -> tree -> tree
|  Leaf : tree.

(* A priority queue (using the binomial queues data structure)
   is a list of trees.
   The i'th element of the list is either Leaf or it is a
   power-of-2-heap with exactly 2^i nodes.
*)

Definition priqueue := list tree.

Definition emptyQ : priqueue := nil.

Definition smash (t u:  tree) : tree :=
  match t , u with
  |  Node x t1 Leaf, Node y u1 Leaf =>
                   if  bgt_nat x y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf  (* arbitrary bogus tree *)
  end.

Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf        => nil
  | nil, _            => t :: nil
  | Leaf :: q', _  => t :: q'
  | u :: q', Leaf  => u :: q'
  | u :: q', _       => Leaf :: carry q' (smash t u)
 end.

Definition insert (q: priqueue) (x: key) : priqueue :=
     carry q (Node x Leaf Leaf).

(* Do the query "Print fold_left" to see how fold_left works.  *)
Definition queue1 := fold_left insert [3,1,4,1,5,9,2,3,5] emptyQ.

Fixpoint join (p q: priqueue) (c: tree) : priqueue :=
  match p, q, c with
    [], _ , _            => carry q c
  | _, [], _             => carry p c
  | Leaf::p', Leaf::q', _              => c :: join p' q' Leaf
  | Leaf::p', q1::q', Leaf            => q1 :: join p' q' Leaf
  | Leaf::p', q1::q', Node _ _ _  => Leaf :: join p' q' (smash c q1)
  | p1::p', Leaf::q', Leaf            => p1 :: join p' q' Leaf
  | p1::p', Leaf::q',Node _ _ _   => Leaf :: join p' q' (smash c p1)
  | p1::p', q1::q', _                   => c :: join p' q' (smash p1 q1)
 end.

Fixpoint unzip (t: tree) (cont: priqueue -> priqueue) : priqueue :=
  match t with
  |  Node x t1 t2   => unzip t2 (fun q => Node x t1 Leaf  :: cont q)
  | Leaf => cont nil
  end.

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
    Node x t1 Leaf  => unzip t1 (fun u => u)
  | _ => nil   (* bogus value for ill-formed or empty trees *)
  end.

Fixpoint find_max' (current: key) (q: priqueue) : key :=
  match q with
  |  []         => current
  | Leaf::q' => find_max' current q'
  | Node x _ _ :: q' => find_max' (if bgt_nat x current then x else current) q'
  end.

Fixpoint find_max (q: priqueue) : key :=
  match q with
  | [] => O   (* bogus value *)
  | Leaf::q' => find_max q'
  | Node x _ _ :: q' => find_max' x q'
 end.

Fixpoint delete_max_aux (m: key) (p: priqueue) : priqueue * priqueue :=
           match p with
           | Leaf :: p'   => let (j,k) := delete_max_aux m p'  in (Leaf::j, k)
           | Node x t1 Leaf :: p' =>
                   if bgt_nat m x then (let (j,k) := delete_max_aux m p' in (Node x t1 Leaf::j,k))
                   else (Leaf::p', heap_delete_max (Node x t1 Leaf))
           | _ => (nil, nil) (* Bogus value *)
          end.

Definition delete_max (q: priqueue) : priqueue :=
   let m := find_max q
    in let (p',q') := delete_max_aux m q
         in join p' q' Leaf.

(********************** Useful things ************************************************)
(* Make sure you understand the statement of each theorem, because you may
  need to use these theorems in your own proofs.  You probably don't need to
  read and understand the proofs of the theorems.  But you might do that anyway,
  to see examples of what the "omega" tactic can solve. *)

Theorem ble_nat_e: forall n m, true = ble_nat n m -> n <= m.
Proof.
induction n as [|n']; intros.
omega.
destruct m; simpl in H.
inversion H.
apply IHn' in H.
omega.
Qed.

Theorem ble_nat_i: forall n m, n <= m -> true = ble_nat n m.
Proof.
induction n as [|n']; intros; simpl; auto.
destruct m.
elimtype False.
omega.
apply IHn'.
omega.
Qed.

Theorem bgt_nat_e: forall n m, true = bgt_nat n m -> n>m.
Proof.
unfold bgt_nat, blt_nat; intros.
apply ble_nat_e in H. omega.
Qed.

Theorem bgt_nat_i: forall n m, n > m -> true = bgt_nat n m.
Proof.
unfold bgt_nat, blt_nat; intros.
apply ble_nat_i.
omega.
Qed.

Theorem false_bgt_nat_i:  forall n m, n <= m -> false = bgt_nat n m.
Proof.
intros.
remember (bgt_nat n m) as GT; destruct GT; auto.
apply bgt_nat_e in HeqGT.
elimtype False; omega.
Qed.

Theorem false_bgt_nat_e: forall n m, false = bgt_nat n m -> n<=m.
Proof.
intros.
assert (n <= m \/ n > m) by omega.
destruct H0; auto.
apply bgt_nat_i in H0.
rewrite <- H0 in H.
inversion H.
Qed.

(******************************** Theorems about Binomial Queues ************************)

(* t is an a complete binary tree of depth n, with every key <= m *)
Fixpoint pow2heap' (n: nat) (m: key) (t: tree) :=
 match n, m, t with
    0, m, Leaf       => True
  | 0, m, Node _ _ _  => False
  | S _, m,Leaf    => False
  | S n', m, Node k l r  => m >= k /\ pow2heap' n' k l /\ pow2heap' n' m r
 end.

(* t is a power-of-2 heap of depth n *)
Definition pow2heap (n: nat) (t: tree) :=
  match t with
    Node m t1 Leaf => pow2heap' n m t1
  | _ => False
  end.

(* l is the i'th tail of a binomial heap *)
Fixpoint priq'  (i: nat) (l: list tree) : Prop :=
   match l with
  | t :: l' => (t=Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
 end.

(* q is a binomial heap *)
Definition priq (q: priqueue) : Prop := priq' 0 q.

(**********************  START YOUR WORK HERE *************************************)


(* This theorem shows a convenient way of proving theorems involving bgt_nat.
   It's worth studying the proof carefully. *)
Example example:  forall a b c d,
    true = bgt_nat a b ->
    false = bgt_nat c d ->
    true = bgt_nat (a+d) (b+c).
Proof.
intros.
(* Step one: Change hypotheses about bgt_nat to hypotheses about gt.  *)
 apply bgt_nat_e in H. apply false_bgt_nat_e in H0.
(* Step two: Change proof-goal about bgt_nat to proof-goal about gt. *)
apply bgt_nat_i.
(* Step three:  omega tactic can solve proof goals about lt, eq, gt,
  given hypotheses about lt, eq, gt of nats. *)
omega.
 (* Step through this example, and to see the principle of how to
      use the omega tactic. *)
Qed.


(** **** Exercise: 1 star (emptyQ_valid)  *)
Theorem emptyQ_valid: priq emptyQ.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (smash_valid) *)
Theorem smash_valid:
       forall n t u, pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u).
(* FILL IN HERE *) Admitted.
(** [] *)

(*  tree_elems t l    means that the keys in t are the same as the elements of l (with repetition) *)
Inductive tree_elems: tree -> list key -> Prop :=
| tree_elems_leaf: tree_elems Leaf nil
| tree_elems_node:  forall bl br v tl tr b,
           tree_elems tl bl ->
           tree_elems tr br ->
           Permutation b (v::bl++br) ->
           tree_elems (Node v tl tr) b.

(* Notice that we use the "Permutation" relation.  "Permutation l1 l2" means that list l1 is
  some rearrangement of list l2.  In the Coq query window, do "SearchAbout Permutation"
  to learn about all sorts of useful theorems about permutations.  In the next
  proof, I applied Permutation_nil, Permutation_trans, and Permutation_sym.  But you might
  do it a different way.  In other proofs, I also use  Permutation_app, Permutation_app_swap,
  perm_skip, perm_swap, and others that I found with the SearchAbout command. *)

(** **** Exercise: 2 stars (tree_elems_ext) *)
(* Extensionality theorem for the tree_elems relation *)
Theorem tree_elems_ext: forall t e1 e2,
  Permutation e1 e2 -> tree_elems t e1 -> tree_elems t e2.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (permut_example) *)
(* To prove this next example, you'll also want to apply some theorems about the "app"
  function (which is the function behind the ++ notation.  Do "SearchAbout app" in the
  Query window.  My favorites are app_nil_end and app_ass.  *)
Example permut_example:
          forall (a b: list key),  Permutation (5::6::a++b) ((5::b)++(6::a++[])).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (smash_elems) *)
(*  Warning:  This next theorem is time-consuming.
  If you're pressed for time, this is one to leave out!  *)
Theorem smash_elems: forall n t u bt bu,
                     pow2heap n t -> pow2heap n u ->
                     tree_elems t bt -> tree_elems u bu ->
                     tree_elems (smash t u) (bt ++ bu).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (priqueue_elems) *)
(* Make an inductive definition, similar to tree_elems, to relate
  a priority queue  "l"  to a list of all its elements.  *)
Inductive priqueue_elems: list tree -> list key -> Prop :=
             (* FILL IN HERE *)
.
(** [] *)

(** **** Exercise: 2 stars (priqueue_elems_ext) *)
(* To prove priqueue_elems_ext, you should almost be able to cut-and-paste the
   proof of tree_elems_ext, with just a few edits.  *)
Theorem priqueue_elems_ext: forall q e1 e2,
  Permutation e1 e2 -> priqueue_elems q e1 -> priqueue_elems q e2.
(* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 3 stars (carry_valid) *)
Theorem carry_valid:
           forall n q,  priq' n q ->
           forall t, (t=Leaf \/ pow2heap n t) -> priq' n (carry q t).
(* FILL IN HERE *) Admitted.
(** [] *)

(* Here ends the main part of the exercise.
   The rest are "extra challenge" problems,
   which you can do if you have the time and the inclination.  *)

(** **** Exercise: 4 stars (carry_elems) *)
Theorem carry_elems:
      forall n q,  priq' n q ->
      forall t, (t=Leaf \/ pow2heap n t) ->
      forall eq et, priqueue_elems q eq ->
                          tree_elems t et ->
                          priqueue_elems (carry q t) (eq++et).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (insert_valid) *)
Theorem insert_valid: forall q x, priq q -> priq (insert q x).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (insert_elems) *)
Theorem insert_elems:
                  forall q x, priq q ->
                  forall e, priqueue_elems q e ->
                              priqueue_elems (insert q x) (x::e).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (join_valid) *)
Theorem join_valid: forall p q c n, priq' n p -> priq' n q -> (c=Leaf \/ pow2heap n c) -> priq' n (join p q c).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars (join_elems) *)
Theorem join_elems:
                forall p q c n,
                      priq' n p ->
                      priq' n q ->
                      (c=Leaf \/ pow2heap n c) ->
                  forall pe qe ce,
                             priqueue_elems p pe ->
                             priqueue_elems q qe ->
                             tree_elems c ce ->
                              priqueue_elems (join p q c) (ce++pe++qe).
(* FILL IN HERE *) Admitted.
(** [] *)