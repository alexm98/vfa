(* Selection sort, with specification and proof of correctness.
  Andrew W. Appel, 2013.
  By the way, you should never use selection sort in real life.
  If you want a simple but reasonably efficient
  quadratic-time sorting algorithm, use insertion sort.
  And of course, you NEVER use bubble sort.  Everybody knows that!
  https://www.youtube.com/watch?v=k4RRi_ntQc8
*)

Require Import Permutation.
Require Import SfLib.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

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

(* The selection-sort program  *)

Fixpoint select (i: nat) (l: list nat) : nat * list nat :=
match l with
|  nil => (i, nil)
|  h::t => if ble_nat i h
               then let (j, l') := select i t in (j, h::l')
               else let (j,l') := select h t in (j, i::l')
end.

Fixpoint selsort l n :=
match l, n with
| i::r, S n' => let (j,r') := select i r
               in j :: selsort r' n'
| _, _ => nil
end.

Definition selection_sort l := selsort l (length l).


Example sort_pi: selection_sort [3,1,4,1,5,9,2,6,5,3,5] = [1,1,2,3,3,4,5,5,5,6,9].
Proof.
unfold selection_sort.
simpl.
reflexivity.
Qed.

Lemma perm_2nd: forall l l' (x y z : nat),
  Permutation (x :: l) (z :: l') -> Permutation (x :: y :: l) (z :: y :: l').
Proof.
  intros.
  rewrite perm_swap. apply Permutation_sym.
  rewrite perm_swap. apply Permutation_sym.
  apply perm_skip. assumption.
Qed.

Lemma select_perm: forall i l,
  let (j,r) := select i l in Permutation (i::l) (j::r).
Proof.
  intros. generalize dependent i.
  induction l as [| x xs]; intros; simpl.
    repeat constructor.
    destruct (ble_nat i x).
      specialize (IHxs i). destruct (select i xs).
        apply perm_2nd. apply IHxs.
      specialize (IHxs x). destruct (select x xs).
        rewrite perm_swap. apply perm_2nd. apply IHxs.
Qed.

Lemma selsort_perm:
  forall n l, length l = n -> Permutation l (selsort l n).
Proof.
  intros. generalize dependent l.
  induction n; destruct l; intros; subst; simpl.
  - reflexivity.
  - inversion H.
  - constructor.
  - assert (SP := select_perm n0 l).
    destruct (select n0 l).
    eapply Permutation_trans; [ apply SP |].
    constructor.
    apply Permutation_length in SP. simpl in SP. inversion SP.
    apply IHn. simpl in H. rewrite <- H1. inversion H. reflexivity.
Qed.

Theorem selection_sort_perm: forall l, Permutation l (selection_sort l).
Proof.
  induction l. reflexivity. apply selsort_perm. reflexivity.
Qed.