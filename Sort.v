(* Implementation and correctness proof for insertion sort.
  Andrew W. Appel, January 2010. *)

Require Import Permutation.
Require Import SfLib.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Theorem ble_nat_refl: forall m, ble_nat m m = true.
Proof.
  intros. induction m as [| m'].
  Case "m = 0".
  reflexivity.
  Case "m = S m'".
  apply IHm'.
Qed.

Theorem ble_nat_i: forall n m, n <= m -> ble_nat n m = true.
Proof.
induction n as [|n']; intros; simpl; auto.
destruct m.
elimtype False.
omega.
apply IHn'.
omega.
Qed.

Theorem false_ble_nat_i:  forall n m, n > m -> ble_nat n m = false.
Proof.
intros.
remember (ble_nat n m) as p; destruct p; auto.
symmetry in Heqp; apply ble_nat_true in Heqp; elimtype False; omega.
Qed.

Theorem false_ble_nat_e: forall n m, ble_nat n m = false -> n > m.
Proof.
intros.
assert (n <= m \/ n > m) by omega.
destruct H0; auto.
apply ble_nat_i in H0.
rewrite H0 in H.
inversion H.
Qed.

(* PART I.   Prove correctness of functional program for insertion sort  *)

Fixpoint insert (i:nat) (l: list nat) :=
  match l with
  | nil => i::nil
  | h::t => if ble_nat i h then i::h::t else h :: insert i t
 end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => insert h (sort t)
end.

Example sort_pi: sort [3,1,4,1,5,9,2,6,5,3,5] = [1,1,2,3,3,4,5,5,5,6,9].
Proof.
simpl.
reflexivity.
Qed.

(** **** Exercise: 3 stars *)

(* Prove an auxiliary lemma insert_perm, useful for proving sort_perm.
  You may want to get into the proof of sort_perm first, to see what you'll need.  *)
Theorem insert_perm_l: forall l i, Permutation (i::l) (insert i l).
Proof.
  intros. induction l as [| x xs].
  reflexivity.
  simpl. destruct (ble_nat i x).
    reflexivity.
    rewrite <- IHxs. apply perm_swap.
Qed.

Theorem insert_perm: forall l l' i,
  Permutation l l' -> Permutation (i::l) (insert i l').
Proof.
  intros. destruct l' as [| y ys].
    simpl. apply perm_skip. apply H.
    destruct l.
      apply Permutation_nil in H. rewrite H. reflexivity.
      rewrite H. apply insert_perm_l.
Qed.

(** **** Exercise: 3 stars *)
(* Now prove the main theorem. *)
Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros. induction l as [| x xs].
    reflexivity.
    apply insert_perm. assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars *)
(* Define an inductive predicate "sorted" that tells whether a list of nats is in nondecreasing order.
   Then prove that "sort" produces a sorted list.
*)
Inductive sorted: list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_cons1 x : sorted [x]
  | sorted_cons x y l : sorted (y::l) -> ble_nat x y = true -> sorted (x::y::l).

Theorem sorted_zero: forall l, sorted l -> sorted (0 :: l).
Proof.
  intros. induction l as [| x xs].
    apply sorted_cons1.
    inversion H.
      apply sorted_cons.
        apply sorted_cons1.
        reflexivity.
      rewrite H1.
      apply sorted_cons.
        apply H.
        reflexivity.
Qed.

Theorem sorted_rest: forall l i, sorted (i :: l) -> sorted l.
Proof.
  intros. induction l as [| x xs].
    apply sorted_nil.
    inversion H. apply H2.
Qed.

Theorem ble_nat_flip: forall i x, ble_nat i x = false -> ble_nat x i = true.
Proof.
  intros. generalize dependent x.
  induction i as [| i'].
  Case "i = 0".
  destruct x.
    reflexivity.
    intros. inversion H.
  Case "i = S i'".
  induction x.
    reflexivity.
    intros. simpl. apply IHi'.
    inversion H. reflexivity.
Qed.

Theorem insert_sorted: forall l i, sorted l -> sorted (insert i l).
Proof.
  intros.
  induction l as [| x xs].
    simpl. constructor.
    simpl. destruct (ble_nat i x) eqn:Heqe.
      constructor. assumption. assumption.
      inversion H; subst.
        simpl. constructor. constructor.
          apply ble_nat_flip. apply Heqe.
        simpl. simpl in IHxs.
        simpl. destruct (ble_nat i y) eqn:Heqe2.
          constructor.
          constructor. apply H2. apply Heqe2.
          apply ble_nat_flip. apply Heqe.
          constructor. apply IHxs. apply H2. apply H3.
Qed.

(* You may want to first prove an auxiliary lemma about inserting an element
   into a sorted list.  *)
Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intros. induction l as [| x xs].
    apply sorted_nil.
    apply insert_sorted. apply IHxs.
Qed.
(** [] *)
