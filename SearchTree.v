(* Binary search trees, with specification and proof of correctness.
  Andrew W. Appel, 2013.
*)

(* IMPORTS *)
Require Import ZArith Permutation Omega List Classical_sets.
Require Import FunctionalExtensionality.
Require Export CpdtTactics.
Axiom prop_ext: ClassicalFacts.prop_extensionality.
Implicit Arguments prop_ext.
Open Scope Z.

Ltac inv H := inversion H; subst; clear H.
Ltac appinv t H := apply t in H; inv H.

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
  intros. split.
    intros. inversion H.
      left. apply H0.
      right. apply H0.
    intros. inversion H.
      apply Union_introl. apply H0.
      apply Union_intror. apply H0.
Qed.

Lemma Union_Empty_set_l: forall U (B: Ensemble U),
  Union Empty_set B = B.
Proof.
  intros. extensionality x. apply prop_ext.
  split; intros.
    inversion H; subst. apply Empty_set_ind. apply H0. apply H0.
    apply Union_intror. apply H.
Qed.

Lemma Union_sym:
 forall {U} (B C: Ensemble U), Union B C = Union C B.
Proof.
  intros. extensionality x. apply prop_ext.
  split; intros; inversion H; subst.
  - apply Union_intror. apply H0.
  - apply Union_introl. apply H0.
  - apply Union_intror. apply H0.
  - apply Union_introl. apply H0.
Qed.

Lemma Union_assoc:
  forall {U} (A B C: Ensemble U),
   Union A (Union B C) = Union (Union A B) C.
Proof.
  intros. extensionality x. apply prop_ext.
  split; intros; inversion H; subst.
  - apply Union_introl. apply Union_introl. apply H0.
  - inversion H0; subst.
    apply Union_introl. apply Union_intror. apply H1.
    apply Union_intror. apply H1.
  - inversion H0; subst.
    apply Union_introl. apply H1.
    apply Union_intror. apply Union_introl. apply H1.
  - apply Union_intror. apply Union_intror. apply H0.
Qed.

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

Inductive OccursTree : Z -> tree -> Prop :=
  | occ_root n a b : OccursTree n (T a n b)
  | occ_left n a b : forall p, OccursTree n a -> OccursTree n (T a p b)
  | occ_right n a b : forall p, OccursTree n b -> OccursTree n (T a p b).

Hint Constructors OccursTree.

Definition all_lt (n : Z) (t : tree) := forall x, OccursTree x t -> x < n.
Definition all_gt (n : Z) (t : tree) := forall x, OccursTree x t -> x > n.

Hint Extern 1 (all_lt _ _) => unfold all_lt; intros.
Hint Extern 1 (all_gt _ _) => unfold all_gt; intros.

Inductive SearchTree: tree -> Prop :=
(* Getting this right is the most important part of the work,
 *   and it's not completely obvious.
 *)
  | bst_empty : SearchTree E
  | bst_node n a b : SearchTree a -> SearchTree b
                       -> all_lt n a -> all_gt n b
                       -> SearchTree (T a n b).

Hint Constructors SearchTree.

Inductive Contents: Ensemble Z -> tree -> Prop :=
| Ct_E: Contents Empty_set E
| Ct_U A B l x r: Contents A l -> Contents B r
    -> Contents (Union A B) (T l x r).

Theorem member_or: forall k z t1 t2,
  member k (T t1 z t2) = true -> member k t1 = true \/ member k t2 = true \/ k = z.
Proof.
  intros. inversion H.
  destruct (k <? z) eqn:Heqe;
    [ apply Z.ltb_lt in Heqe | apply Z.ltb_nlt in Heqe ].
  - left. reflexivity.
  - destruct (z <? k) eqn:Heqe2;
      [ apply Z.ltb_lt in Heqe2 | apply Z.ltb_nlt in Heqe2 ].
    right. left. reflexivity.
    inversion H. crush.
Qed.

Theorem member_spec:
  forall k t, SearchTree t -> (member k t = true <-> OccursTree k t).
Proof.
  intros. split; induction t; intros; simpl.
  - crush.
  - inv H. appinv member_or H0; crush.
  - inversion H0.
  - destruct (k <? z) eqn:Heqe;
      [ apply Z.ltb_lt in Heqe | apply Z.ltb_nlt in Heqe ].
    + inv H. inv H0; crush.
      apply H7 in H2. omega.
    + destruct (z <? k) eqn:Heqe2;
        [ apply Z.ltb_lt in Heqe2 | apply Z.ltb_nlt in Heqe2 ].
      * inv H. inv H0; crush.
      * crush.
Qed.

Theorem member_spec_orig:
  forall k cts t,
    SearchTree t ->
    Contents cts t ->
    (In cts k <->  member k t = true).
Proof.
  intros. split; intros; induction t; crush.
    inv H. inv H0. inv H1.
  destruct (k <? z) eqn:Heqe;
    [ apply Z.ltb_lt in Heqe | apply Z.ltb_nlt in Heqe ].
    apply IHt1. inv H. crush.
Abort.

Theorem insert_occurstree:
  forall k x t, OccursTree x t -> OccursTree x (insert k t).
Proof.
  intros.
  induction t; intros. crush.
  simpl. destruct (k <? z) eqn:Heqe;
      [ apply Z.ltb_lt in Heqe | apply Z.ltb_nlt in Heqe ].
    inv H; crush.
  destruct (z <? k) eqn:Heqe2;
      [ apply Z.ltb_lt in Heqe2 | apply Z.ltb_nlt in Heqe2 ].
    inv H; crush.
  assert (k = z). omega.
  rewrite H0. crush.
Qed.

Theorem insert_contents:
 forall k t cts,
    SearchTree t ->
    Contents cts t ->
    Contents (Union (Singleton k) cts) (insert k t).
Proof.
  intros.
  generalize dependent k.
  induction t.
    constructor; crush.
    inv H0. inv H.
Abort.

Theorem insert_searchtree:
  forall k t, SearchTree t -> SearchTree (insert k t).
Proof.
  intros.
  induction t; intros; crush.
    inv H; crush.
    constructor; crush; simpl.
      unfold all_lt. intros. inv H.
    unfold all_gt. intros. inv H.
  inv H; crush.
  destruct (k <? z) eqn:Heqe;
    [ apply Z.ltb_lt in Heqe | apply Z.ltb_nlt in Heqe ].
    constructor; crush.
    unfold all_lt. intros.
    unfold all_lt in *.
    unfold all_gt in *.
    apply H5.
    apply member_spec. auto.
    admit.
  destruct (z <? k) eqn:Heqe2;
    [ apply Z.ltb_lt in Heqe2 | apply Z.ltb_nlt in Heqe2 ].
    constructor; crush.
    unfold all_gt. intros.
    unfold all_lt in *.
    unfold all_gt in *.
    apply H6.
    apply member_spec. auto.
    admit.
  constructor; crush.
  unfold all_lt in *.
  unfold all_gt in *.
  apply Znot_lt_ge in Heqe.
  apply Znot_lt_ge in Heqe2.
  intros.
Abort.