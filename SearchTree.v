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

Lemma Union_refl: forall {U} (A: Ensemble U), Union A A = A.
Proof.
  intros. extensionality x. apply prop_ext.
  split; intros.
    destruct H; apply H.
  constructor. apply H.
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

Fixpoint allb (R : Z -> Z -> bool) (x: Z) (s: tree) : bool :=
  match s with
    | E => true
    | T l n r => andb (R x n) (andb (allb R x l) (allb R x r))
  end.

Inductive SearchTree: tree -> Prop :=
  | st_empty : SearchTree E
  | st_node l n r : SearchTree l -> allb Z.gtb n l = true
                 -> SearchTree r -> allb Z.ltb n r = true
                 -> SearchTree (T l n r).

Inductive Contents:  Ensemble Z -> tree -> Prop :=
  | Ct_E: Contents Empty_set E
  | Ct_U lset l n rset r: Contents lset l
             -> Contents rset r
             -> Contents (Union (Singleton n) (Union lset rset)) (T l n r).

Ltac inv H := inversion H; subst; clear H.

Lemma allb_split : forall R n l1 z l2,
  allb R n (T l1 z l2) = true
    -> R n z = true /\ allb R n l1 = true /\ allb R n l2 = true.
Proof.
  intros.
  apply Bool.andb_true_iff in H. inversion H.
  apply Bool.andb_true_iff in H1. inversion H1.
  intuition.
Qed.

Lemma allb_ltb_spec : forall R cts l n k,
  Contents cts l -> In cts k -> allb R n l = true -> R n k = true.
Proof.
  intros.
  generalize dependent cts.
  induction l; intros; inv H. inv H0.
  apply allb_split in H1.
  inversion H1. inversion H2.
  inv H0; inv H6.
  - assumption.
  - apply IHl1 with (cts := lset); try assumption.
  - apply IHl2 with (cts := rset); try assumption.
Qed.

Lemma ltb_antisym : forall k n, (k <? n) = false -> (n <? k) = false -> n = k.
Proof.
  intros.
  apply Z.ltb_ge in H.
  apply Z.ltb_ge in H0.
  omega.
Qed.

Theorem member_spec:
  forall k cts t,
    SearchTree t ->
    Contents cts t ->
    (In cts k <-> member k t = true).
Proof.
  split; intros.
  - induction H0; inv H1; simpl; inv H; inv H0.
    + rewrite Z.ltb_irrefl; reflexivity.
    + destruct (k <? n) eqn:Heqe.
        apply IHContents1; assumption.
      pose (allb_ltb_spec Z.gtb lset l n k H0_ H H5).
      rewrite Z.gtb_ltb in e.
      rewrite Heqe in e. inversion e.
    + destruct (k <? n) eqn:Heqe.
        pose (allb_ltb_spec Z.ltb rset r n k H0_0 H H7).
        apply Z.ltb_lt in Heqe.
        apply Z.ltb_lt in e. omega.
      destruct (n <? k) eqn:Heqe2.
        apply IHContents2; assumption.
      reflexivity.
  - induction H0; inv H1; simpl; inv H.
    apply In_Union_iff.
    destruct (k <? n) eqn:Heqe.
      right. apply In_Union_iff. left.
      apply IHContents1; assumption.
    destruct (n <? k) eqn:Heqe2.
      right. apply In_Union_iff. right.
      apply IHContents2; assumption.
    left. apply In_Singleton_iff.
    apply ltb_antisym; assumption.
Qed.

Theorem insert_contents:
 forall k t cts,
    SearchTree t ->
    Contents cts t ->
    Contents (Union (Singleton k) cts) (insert k t).
Proof.
  intros.
  induction H0. simpl.
    replace (@Empty_set Z) with (@Union Z Empty_set Empty_set).
      repeat constructor.
    apply Union_refl.
  simpl.
  inv H.
  destruct (k <? n) eqn:Heqe.
    replace (Union (Singleton k) (Union (Singleton n) (Union lset rset)))
      with (Union (Singleton n) (Union (Union (Singleton k) lset) rset)).
      constructor.
        apply IHContents1; assumption.
      assumption.
    rewrite Union_sym.
    repeat rewrite <- Union_assoc. f_equal.
    rewrite (Union_sym rset).
    repeat rewrite <- Union_assoc. f_equal.
    rewrite Union_sym. reflexivity.
  destruct (n <? k) eqn:Heqe2.
    replace (Union (Singleton k) (Union (Singleton n) (Union lset rset)))
      with (Union (Singleton n) (Union lset (Union (Singleton k) rset))).
      constructor. assumption.
      apply IHContents2; assumption.
    repeat rewrite <- Union_assoc.
    rewrite Union_sym.
    repeat rewrite <- Union_assoc.
    rewrite Union_sym.
    repeat rewrite <- Union_assoc. f_equal.
    rewrite Union_sym.
    repeat rewrite <- Union_assoc. reflexivity.
  pose (ltb_antisym _ _ Heqe Heqe2). rewrite e.
  replace (Union (Singleton k) (Union (Singleton k) (Union lset rset)))
    with (Union (Singleton k) (Union lset rset)).
    constructor; assumption.
  repeat rewrite Union_assoc.
  rewrite Union_refl. reflexivity.
Qed.

Lemma allb_impl : forall R z t k,
  allb R z t = true -> R z k = true -> allb R z (insert k t) = true.
Proof.
  intros.
  induction t; simpl.
    apply Bool.andb_true_iff.
    split. assumption.
    reflexivity.
  inv H.
  apply Bool.andb_true_iff in H2.
  inversion H2.
  apply Bool.andb_true_iff in H1.
  inversion H1.
  destruct (k <? z0) eqn:Heqe; simpl.
    f_equal. f_equal.
    specialize (IHt1 H3).
    rewrite IHt1. auto.
  destruct (z0 <? k) eqn:Heqe2; simpl.
    f_equal. f_equal.
    specialize (IHt2 H4).
    rewrite IHt2. auto.
  pose (ltb_antisym _ _ Heqe Heqe2). rewrite e.
  reflexivity.
Qed.

Theorem insert_searchtree:
  forall k t,
   SearchTree t -> SearchTree (insert k t).
Proof.
  intros.
  induction t; simpl.
    constructor; auto.
  inv H.
  destruct (k <? z) eqn:Heqe.
    constructor; auto.
    apply allb_impl with (R := Z.gtb).
      assumption.
    rewrite Z.gtb_ltb.
    assumption.
  destruct (z <? k) eqn:Heqe2.
    constructor; auto.
    apply allb_impl with (R := Z.ltb).
    assumption. assumption.
  constructor; auto;
  pose (ltb_antisym _ _ Heqe Heqe2);
  rewrite <- e;
  assumption.
Qed.