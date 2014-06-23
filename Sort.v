(* Implementation and correctness proof for insertion sort.
  Andrew W. Appel, January 2010. *)

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
(* FILL IN HERE *)

(** **** Exercise: 3 stars *)
(* Now prove the main theorem. *)
Theorem sort_perm: forall l, Permutation l (sort l).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars *)
(* Define an inductive predicate "sorted" that tells whether a list of nats is in nondecreasing order.
   Then prove that "sort" produces a sorted list.
*)
Inductive sorted: list nat -> Prop := 
 (* FILL IN HERE *)
.

(* You may want to first prove an auxiliary lemma about inserting an element
   into a sorted list.  *)
Theorem sort_sorted: forall l, sorted (sort l).
(* FILL IN HERE *) Admitted.
(** [] *)
