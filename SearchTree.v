(* Binary search trees, with specification and proof of correctness.
  Andrew W. Appel, 2013.
*)

(* IMPORTS *)
Require Import ZArith Permutation Omega List Classical_sets.
Require Import FunctionalExtensionality.
Axiom prop_ext: ClassicalFacts.prop_extensionality.
Implicit Arguments prop_ext.
Open Scope Z.

(* A FEW LEMMAS ABOUT SET UNION, ET CETERA *)
Arguments In {U} A x.
Arguments Union {U} B C x.
Arguments Singleton {U} x x0.
Arguments Empty_set {U} x.

Lemma In_Singleton_iff:
  forall U (x y: U), In (Singleton x) y <-> x=y.
Proof.
  intros. split; intros.
    inversion H. reflexivity.
    subst. constructor.
Qed.

Lemma In_Union_iff:
 forall U (B C: Ensemble U) x,
  In (Union B C) x <-> (In B x \/ In C x).
Proof.
(* FILL IN HERE *) Admitted.

Lemma Union_Empty_set_l: forall U (B: Ensemble U),
  Union Empty_set B = B.
Proof.
intros. extensionality x. apply prop_ext.
(* FILL IN HERE *) Admitted.

Lemma Union_sym:
 forall {U} (B C: Ensemble U), Union B C = Union C B.
Proof.
  intros. extensionality x. apply prop_ext.
(* FILL IN HERE *) Admitted.

Lemma Union_assoc:
  forall {U} (A B C: Ensemble U),
   Union A (Union B C) = Union (Union A B) C.
Proof.
(* FILL IN HERE *) Admitted.

(*  PROGRAM FOR BINARY SEARCH TREES *)

Inductive tree  : Type :=
 | E : tree
 | T: tree -> Z -> tree -> tree.

Fixpoint member (x: Z) (t : tree) : bool :=
  match t with
  | E => false
  | T tl k tr => if Z.ltb x k then member x tl
                         else if Z.ltb k x then member x tr
                         else true
  end.

Fixpoint insert (x: Z) (s: tree) :=
 match s with
 | E => T E x E
 | T a y b => if Z.ltb x y then T (insert x a) y b
                        else if Z.ltb y x then T a y (insert x b)
                        else T a x b
 end.

(* SPECIFICATIONS AND PROOF *)


Inductive SearchTree: tree -> Prop :=
(* Getting this right is the most important part of the work,
 *   and it's not completely obvious.
 *)
(* FILL IN HERE *).

Inductive Contents:  Ensemble Z -> tree -> Prop :=
| Ct_E: Contents Empty_set E
(* FILL IN HERE *).



Theorem member_spec:
  forall k cts t,
    SearchTree t ->
    Contents cts t ->
    (In cts k <->  member k t = true).
Proof.
(* FILL IN HERE *) Admitted.

Theorem insert_contents:
 forall k t cts,
    SearchTree t ->
    Contents cts t ->
    Contents (Union (Singleton k) cts) (insert k t).
Proof.
(* FILL IN HERE *) Admitted.

Theorem insert_searchtree:
  forall k t,
   SearchTree t -> SearchTree (insert k t).
Proof.
(* FILL IN HERE *) Admitted.
