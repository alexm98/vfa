(* Implementation and correctness proofs for unrolled lists.
   Andrew W. Appel, October 2010.

 Required reading:
 Unrolling Lists, by Zhong Shao, John H. Reppy, and Andrew W. Appel.
 Proc. 1994 ACM Conf. on Lisp and Functional Programming, June 1994.
 http://www.cs.princeton.edu/~appel/papers/unrolling-lists.pdf
*)

Require Import Permutation.
Require Import SfLib.
Definition admit {T: Type} : T.  Admitted.

(** **** Exercise: 1 star (problem_1) *)
(* Write a function [decreasing] such that it passes
  the following unit  tests (and similar ones for all numbers). *)

Fixpoint decreasing {B} (f: nat -> B -> B) (base: B) (n: nat) : B :=
  match n with
    | O => base
    | S n' => f n (decreasing f base n')
  end.

Example decreasing4: forall B (f: nat -> B -> B) x,
               decreasing f x 4 = f 4 (f 3 (f 2 (f 1 x))).
Proof. reflexivity. Qed.

Example decreasing3: decreasing (@cons nat) nil 3 = 3::2::1::nil.
Proof. reflexivity. Qed.
Example decreasing0:  forall B (f: nat->B->B) (x:B), decreasing f x 0 = x.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star (problem_2) *)
(* The following function is in the Coq standard library.
 Fixpoint fold_right {A B: Type} (f: B -> A -> A) (a0: A) (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right f a0 t)
    end.

  Use fold_right to define a function to add up all the numbers in a list.
*)

Definition sum (l: list nat) : nat := fold_right plus 0 l.

Lemma sum_decreasing: forall n,
  sum (decreasing (@cons _) nil n) = decreasing plus O n.
Proof.
  intros. induction n; simpl. reflexivity. omega.
Qed.
(** [] *)

(** **** Exercise: 2 stars (problem_3) *)
(* Fun with permutations.  For useful lemmas, do "SearchAbout Permutation".  *)

Lemma filter_permut: forall (A: Type) (f: A -> bool) (l: list A),
  Permutation (filter f l ++ filter (fun x => negb (f x)) l) l.
Proof.
  intros. induction l; simpl.
    reflexivity.
    destruct (f a) eqn:Heqe; simpl.
      constructor. assumption.
      symmetry. apply Permutation_cons_app. symmetry. assumption.
Qed.
(** [] *)

(* Best if viewed in Lucida Sans Unicode... *)
(**********************************************************************)
(*  An "ordinary" linked list looks like this (with $ representing nil):

             ------          ------          ------         ------
             | 1 | *-|---> | 4 | *-|---> | 1 | *-|---> | 5 | $ |
             ------          ------          ------         ------

or like this:

   ------          ------          ------          ------         ------
   | 3 | *-|---> | 1 | *-|---> | 4 | *-|---> | 1 | *-|---> | 5 | $ |
   ------          ------          ------          ------         ------

Un "unrolled list" looks like this:
   --------          ---------          ---------
   EVEN | *-|---> | 1 |  4 | *-|---> | 1 |  5 | $ |
   --------          ---------          ---------

or like this:
   ----------          ---------          ---------
   ODD | 3 | *-|---> | 1 |  4 | *-|---> | 1 |  5 | $ |
   ----------          ---------          ---------

The purpose of an unrolled list is that computations (loops
or recursive functions) go faster because the chain of data-dependencies
caused by dereferencing tail-pointers is only half as long,
and a typical CPU can fetch the two "head" elements in a cell
(such as 1,4   or 1,5)  in parallel.

The representation of an unrolled list starts with a special
"even" or "odd" cell, followed by a "tail" which is a chain of
two-head cons cells.

However, the programmer wants to pretend that there is just
an abstract data type (ADT) that behaves just like ordinary lists;
all the unrolling should be done "under the hood" by the compiler.

In this exam you'll reason about this ADT using Coq.
The goal is to have a set of types and functions as follows:

  list' :    Type -> Type.
  nil'  :    forall {X: Type}, list' X.
  cons':  forall {X: Type}, X -> list' X -> list' X.
  app':    forall {X: Type}, list' X -> list' X -> list' X.
and so on.

*)

(** **** Exercise: 2 stars (problem_4) *)
(* Write inductive data type [tail] to represent the tail chain,
  and the inductive data type [list']  to represent the even/odd header. *)

Inductive tail (X: Type)  : Type :=
  | end' : tail X
  | link' : X -> X -> tail X -> tail X.

Inductive list' (X: Type) : Type :=
  | evenll : tail X -> list' X
  | oddll : X -> tail X -> list' X.

(* Use the Arguments command to make the X parameter of your
   data constructors implicit, as in the definition of "list" in Poly.v *)
Arguments end' {X}.
Arguments link' {X} _ _ _.
Arguments evenll {X} _.
Arguments oddll {X} _ _.
(** [] *)

(** **** Exercise: 2 stars (problem_5) *)
(* Implement [nil'] that makes the empty [list'], and [cons'] that prepends one
  element.   To [cons'] a single element onto the front of an unrolled list, if the
  list was previously an even list it becomes an odd one, and vice versa. *)

Definition nil' {X}:  list' X := evenll end'.

Definition cons' {X} (n: X) (l: list' X) : list' X :=
  match l with
    | evenll xs => oddll n xs
    | oddll x xs => evenll (link' n x xs)
  end.
(** [] *)

(** **** Exercise: 2 stars (problem_6) *)
(*  Write a function that converts a [list'] into an ordinary [list].
  Hint: write a helper function to walk down the tail. *)

Fixpoint tail2list {X} (t: tail X) : list X :=
  match t with
    | end' => nil
    | link' x y xs => x :: y :: tail2list xs
  end.

Definition list'2list {X} (l: list' X) : list X :=
  match l with
    | evenll xs => tail2list xs
    | oddll x xs => x :: tail2list xs
  end.

(*   The following unit test should work; if not, adjust your definitions. *)

Example list'2list_12345: list'2list  (cons' 1 (cons' 2 (cons' 3 (cons' 4 (cons' 5 nil')))))  = [1;2;3;4;5].
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star (list2list') *)
(* Problem 7.  Use fold_right to define a function that converts an ordinary
  list into an unrolled list. *)

Definition list2list' {X} (l: list X) : list' X :=
  fold_right cons' nil' l.
(** [] *)

(** **** Exercise: 1 star *)
(*  Prove that if you start with a list', convert it to a list, then convert back
    to a list', you get your original unrolled-list back.    *)

Lemma cons_swap: forall X (l l': list' X) (x y : X),
      cons' x (cons' y l) = cons' x (cons' y l')
  -> cons' y (cons' x l) = cons' y (cons' x l').
Proof.
  intros. induction l; simpl; induction l'; inversion H; subst; reflexivity.
Qed.

Lemma cons_swap_odd: forall X (t t': tail X) (x y : X),
     cons' x (oddll y t) = cons' x (oddll y t')
  -> cons' y (oddll x t) = cons' y (oddll x t').
Proof.
  intros. induction t; simpl; induction t'; inversion H; subst; reflexivity.
Qed.

Lemma cons_oddll_eq : forall X (t : tail X) (x : X),
  cons' x (list2list' (tail2list t)) = oddll x t.
Proof.
  intros. induction t; simpl.
    reflexivity.
    destruct (list2list' (tail2list t)) eqn:Heqe; simpl.
      simpl in IHt. inversion IHt. reflexivity.
      inversion IHt.
Qed.

Lemma list'2list2list': forall X (l: list' X), list2list' (list'2list l) = l.
Proof.
  intros. destruct l; simpl.
  - induction t; simpl. reflexivity.
    rewrite IHt. reflexivity.
  - apply cons_oddll_eq.
Qed.
(** [] *)

(** **** Exercise: 2 stars *)
(* Prove that if you start with an ordinary list, convert it into an unrolled list,
   then convert back to an ordinary list, you get the original list.   *)

Lemma list2list'2list:
  forall X (l: list X), list'2list (list2list' l) = l.
Proof.
  intros. induction l; simpl.
    reflexivity.
    unfold list'2list. unfold cons'.
    destruct (list2list' l); rewrite <- IHl; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars (fold_right') *)
(* One way to define a fold function on unrolled lists is to first convert to
  an ordinary list, then call fold_right:  *)

Definition fold_right'_slow {A B: Type} (f: A-> B -> B) (base: B) (l: list' A) : B :=
      fold_right f base (list'2list l).

(* This definition is correct, as it has the expected behavior: *)

Lemma fold_right'_slow_example:
  fold_right'_slow plus 0 (cons' 3 (cons' 5 nil')) = 8.
Proof. reflexivity. Qed.

(* The reason it's slow is that cons' keeps building and unbuilding the odd
  and even list headers.  Define a more efficient fold_right' function that
   just directly applies f (twice) for each (two-element) cell of the tail chain.
  As usual, you'll need an auxiliary function.  *)

Fixpoint fold_right'tail {A B: Type} (f: A-> B -> B) (base: B) (l: tail A) : B :=
  match l with
    | end' => base
    | link' x y xs => f x (f y (fold_right'tail f base xs))
  end.

Definition fold_right' {A B: Type} (f: A-> B -> B) (base: B) (l: list' A) : B :=
  match l with
    | evenll xs => fold_right'tail f base xs
    | oddll x xs => f x (fold_right'tail f base xs)
  end.

Lemma fold_right'tail_correct : forall A B (f: A -> B -> B) base t,
  fold_right'tail f base t = fold_right f base (tail2list t).
Proof.
  intros. induction t; simpl.
    reflexivity.
    repeat f_equal. assumption.
Qed.

(* Now prove that you have the right function: *)
Lemma fold_right'_correct:
  forall A B (f: A -> B -> B) base l, fold_right' f base l = fold_right'_slow f base l.
Proof.
  intros. induction l; simpl;
  unfold fold_right', fold_right'_slow; simpl;
  repeat f_equal; apply fold_right'tail_correct.
Qed.
(** [] *)
