(* Implementation and proof of Red-Black Trees.  Andrew W. Appel, 2011 *)

(* Required reading:
Red-Black Trees in a Functional Setting, by Chris Okasaki. 
Journal of Functional Programming, 9(4):471-477, July 1999. 
http://www.eecs.usma.edu/webs/people/okasaki/jfp99redblack.pdf

   Optional reading:
Efficient Verified Red-Black Trees, by Andrew W. Appel, September 2011. 
http://www.cs.princeton.edu/~appel/papers/redblack.pdf
*)

(* Normally in Coq one might take the 2 Parameters and 3 Axioms and bundle
   them into a Module Type ORDERED.  Then one would then express 
   SET_OF_ORDERED as a parameterized module type (by ORDERED),
   and the module RedBlackTree as a functor (parameterized module).
   This would be straightforward to do in Coq, but 
   is beyond the scope of this simple tutorial example.
*)


Ltac inv H := inversion H; clear H; subst. 

Inductive order {key} (lt: key -> key -> Prop) (x y : key)  : Type :=
 Lt : lt x y -> order lt x y | Eq: x = y -> order lt x y | Gt: lt y x -> order lt x y.

(* Module Type ORDERED. *)
Parameter key : Set.
Parameter lt: key -> key -> Prop.

Axiom lt_eq_gt: forall x y : key, order lt x y.
Axiom lt_irrefl: forall x, ~ lt x x.
Axiom lt_trans: forall x y z, lt x y -> lt y z -> lt x z.
(* End ORDERED. *)

Lemma lt_dec: forall x y, {lt x y}+{~lt x y}.
Proof.
intros. destruct (lt_eq_gt x y).
left; auto.
right; intro; subst; eapply lt_irrefl; eauto.
right; intro.
contradiction (lt_irrefl x).
apply lt_trans with y; auto.
Qed.

(** **** Exercise: 2 stars (key_eq_dec) *)
Lemma key_eq_dec: forall x y : key, {x=y}+{x<>y}.
(* FILL IN HERE *) Admitted.
(** [] *)

Module Type SET_OF_ORDERED.
  Parameter set : Type.
  Parameter empty : set.
  Parameter member: key -> set -> bool.
  Parameter insert: key -> set -> set.

  Parameter valid : set -> Prop.
  Axiom valid_empty: valid empty.
  Axiom valid_insert: forall x s, valid s -> valid (insert x s).

  Parameter interp: set -> (key -> Prop).
  Axiom interp_empty: forall x, ~ interp empty x.
  Axiom interp_insert: 
      forall x y s, 
             valid s -> 
             ((x=y \/ interp s x) <-> interp (insert y s) x).
  Axiom interp_member: 
    forall x t, 
      valid t -> 
      (member x t = true <-> interp t x).
End SET_OF_ORDERED.

Module RedBlackTree: SET_OF_ORDERED.

 Inductive color := Red | Black.
 Inductive tree  : Type :=
 | E : tree 
 | T: color -> tree -> key -> tree -> tree.

 Fixpoint member (x: key) (t : tree) : bool :=
  match t with
  | E => false
  | T _ tl k tr => if lt_dec x k then member x tl 
                         else if lt_dec k x then member x tr
                         else true
  end.

Definition balance rb t1 k t2 :=
 match rb with Red => T Red t1 k t2
 | _ => 
 match t1 with 
 | T Red (T Red a x b) y c => T Red (T Black a x b) y (T Black c k t2)
 | T Red a x (T Red b y c) => T Red (T Black a x b) y (T Black c k t2)
 | a => match t2 with 
            | T Red (T Red b y c) z d =>  T Red (T Black t1 k b) y (T Black c z d)
            | T Red b y (T Red c z d)  => T Red (T Black t1 k b) y (T Black c z d)
            | _ => T Black t1 k t2
            end
  end
 end.

Definition makeBlack t := 
  match t with 
  | E => E
  | T _ a x b => T Black a x b
  end.

Fixpoint ins x s :=
 match s with 
 | E => T Red E x E
 | T c a y b => if lt_dec x y then balance c (ins x a) y b
                        else if lt_dec y x then balance c a y (ins x b)
                        else T c a x b
 end.

Definition insert x s := makeBlack (ins x s).

(* Now that the program has been defined, it's time to prove its properties.
   A red-black tree has two kinds of properties:
  [searchtree]: the keys in each left subtree are all less than the node's key,
                      and the keys in each right subtree are greater
  [redblack]:  there is the same number of black nodes on any path from
               the root to each leaf; and there are never two red nodes in a row.
  First, we'll treat the [searchtree] property.
*)

(** **** Exercise: 3 stars (ins_not_E) *)
Lemma ins_not_E: forall x s, ins x s <> E.
Proof.
intros. induction s; simpl. intro Hx; inversion Hx.
(* This one is best handled with a bit of proof automation,
  but you can grind it out in a less automated way if you like 
*)
(* FILL IN HERE *) Admitted.
(** [] *)

Definition ltopt (x y : option key) := 
  match x, y with
  | Some x', Some y' => lt x' y'
  | _, _ => True
  end.

Inductive searchtree: tree -> option key -> option key -> Prop :=
 | STE: forall lo hi, searchtree E lo hi
 | STT: forall c tl k tr lo hi,
                searchtree tl lo (Some k) ->
                searchtree tr (Some k) hi ->
                ltopt lo (Some k) ->
                ltopt (Some k) hi ->
                searchtree (T c tl k tr) lo hi.

(** **** Exercise: 3 stars (searchtree_balance) *)
Lemma searchtree_balance:
 forall c  s1 t s2 lo hi, 
   ltopt lo (Some t) -> ltopt (Some t) hi ->
   searchtree s1 lo (Some t) -> searchtree s2 (Some t) hi ->
    searchtree (balance c s1 t s2) lo hi.
Proof.
intros.
unfold balance.
(* This one is really painful to do without some proof automation. 
  You can define a 12-line Ltac , "match goal with [7 clauses]", 
  and then simply repeat the application of that tactic. *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (ins_is_searchtree) *)
Lemma ins_is_searchtree: 
   forall x s lo hi, ltopt lo (Some x) -> ltopt (Some x) hi -> 
                    searchtree s lo hi ->
                    searchtree (ins x s) lo hi.
(* This one is pretty easy, even without proof automation *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (valid) *)

Definition valid (t: tree) := searchtree t None None.

Lemma valid_empty: valid E.
(* FILL IN HERE *) Admitted.

Lemma valid_insert: forall x s, valid s -> valid (insert x s).
(* FILL IN HERE *) Admitted.
(** [] *)

(* We have to call this [interp'] instead of [interp] because
 Coq's matching of Module Types can't match an Inductive to a Parameter,
  it can only match a Definition to a Parameter. *)

(** **** Exercise: 3 stars (interp) *)
Inductive interp': tree -> (key -> Prop) :=
 (* fill in an inductive definition, so that   [interp' s x]  means
  that key [x] is found anywhere within tree [s], without caring
  whether  [s] is a valid searchtree or red-black tree *)
(* FILL IN HERE *)
  .

Lemma interp_empty: forall x, ~ interp' E x.
(* FILL IN HERE *) Admitted.

Lemma member_ok:
  forall x t lo hi, 
    searchtree t lo hi -> 
    if member x t then interp' t x else ~interp' t x.
Proof.
induction 1; intros.
(* FILL IN HERE *) Admitted.

Lemma interp_member:
    forall x t, 
      valid t -> 
      (member x t = true <-> interp' t x).
(* FILL IN HERE *) Admitted.

Lemma interp'_makeBlack:
  forall t x, interp' t x <-> interp' (makeBlack t) x.
(* FILL IN HERE *) Admitted.
(** [] *)

Hint Constructors interp'.

(** **** Exercise: 3 stars (interp'_balance) *)
Lemma interp'_balance:
  forall c tl k tr y, interp' (balance c tl k tr) y <-> interp' (T c tl k tr) y.
(* In this proof it really helps to have some proof automation *)
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (ins_ok) *)
Lemma ins_ok:  
   forall x y t lo hi, 
             searchtree t lo hi -> 
             ((x=y \/ interp' t x) <-> interp' (ins y t) x).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (interp_insert) *)
Lemma interp_insert:
      forall x y s, 
             valid s -> 
             ((x=y \/ interp' s x) <-> interp' (insert y s) x).
(* This one is easy, using previous lemmas ins_ok and interp'_makeBlack *)
(* FILL IN HERE *) Admitted.
(** [] *)

(* The next part of this file is not needed for red-black trees to meet
  their functional specification for _correctness_, but does show that
  they will be _efficient_.  That is, one wants to know that the trees
   are balanced, i.e. that the deepest leaf is no more than twice as far
   from the root as the shallowest leaf.  The predicate "is_redblack" 
   guarantees this; the lemma IsRB_leaf shows that the empty tree
  is balanced, and the lemma insert_is_redblack shows that balance
  is preserved by insertion. 

  This is useful to prove, so we do it; but note that there's no way
  of expressing such efficiency criteria in the specification, i.e. in the 
  Module Type SET_OF_ORDERED.
*)
  
(** **** Exercise: 4 stars (is_redblack) *)
 Inductive is_redblack : tree -> color -> nat -> Prop :=
 | IsRB_leaf: forall c, is_redblack E c 0
 | IsRB_r: forall tl k tr n,
          is_redblack tl Red n ->
          is_redblack tr Red n ->
          is_redblack (T Red tl k tr) Black n
 | IsRB_b: forall c tl k tr n,
          is_redblack tl Black n ->
          is_redblack tr Black n ->
          is_redblack (T Black tl k tr) c (S n).

Lemma is_redblack_toblack:
 forall s n, is_redblack s Red n -> is_redblack s Black n.
(* FILL IN HERE *) Admitted.
Hint Resolve is_redblack_toblack.

Lemma makeblack_fiddle:
  forall s n, is_redblack s Black n -> 
            exists n, is_redblack (makeBlack s) Red n.
(* FILL IN HERE *) Admitted.

Inductive nearly_redblack : tree -> nat -> Prop :=
 (* This predicate expresses, "the tree is a red-black tree, except that
  it's nonempty and it is permitted to have two red nodes in a row at 
  the very root (only)." 
*)
(* FILL IN HERE *)
 .

(* FILL IN HERE *)

Lemma ins_is_redblack:
  forall x s n, 
    (is_redblack s Black n -> nearly_redblack (ins x s) n) /\
    (is_redblack s Red n -> is_redblack (ins x s) Black n).
(* This one is tedious with proof automation, 
   but extremely tedious without proof automation *)
(* FILL IN HERE *) Admitted.

Lemma insert_is_redblack:
  forall x s n, is_redblack s Red n ->
                    exists n', is_redblack (insert x s) Red n'.
(*  Just apply a couple of lemmas:  is_is_redblack and makeblack_fiddle *)
(* FILL IN HERE *) Admitted.
(** [] *)

(* Now, some definitions to match the Module Type *)
Definition set := tree.
Definition empty := E.
Definition interp := interp'.

End RedBlackTree.

(* Tne next 5 lines extract the program into an ML program,
   where lt_dec is implemented as the integer less-than operator.
*)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Constant key => "int".
Extract Constant lt_eq_gt => "(fun _ -> failwith ""AXIOM TO BE REALIZED"")".
Extract Inlined Constant lt_dec => "(<)".
Extraction "redblack.ml" RedBlackTree.

(* The accompanying program test_rb.ml exercises this program
  by building a tree by inserting N random keys, each uniform over
  the range 0..N, then looking up N random keys in that range.
  With N = 1 million, the time on my desktop computer is about 1.5 seconds.

  Usage:  
   ocaml
   #use "redblack.ml";;
   #use "test_rb.ml";;
   test 1000000;;
 *)









