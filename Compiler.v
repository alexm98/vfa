Require Import Imp.

(** Proving the correctness of a compiler.
   Andrew W. Appel, Princeton University, December 2009.
   Minor edits, March 2011 and May 2014.
*)

(** Let's start by defining a machine language.  The compiler will only use the
   first 5 instructions, but the extra instructions don't hurt. *)

Inductive instr : Type :=
| i_move: id -> id -> instr
| i_num: nat -> id -> instr
| i_plus: id -> id -> id -> instr
| i_minus: id -> id -> id -> instr
| i_mult: id -> id -> id -> instr
| i_eq: id -> id -> id -> instr
| i_le: id -> id -> id -> instr
| i_not: id -> id -> instr
| i_and: id -> id -> id -> instr
| i_or: id -> id -> id -> instr.

(** Operational semantics for instructions. *)
Inductive exec: state -> instr -> state -> Prop :=
| exec_move: forall st i j, exec st (i_move i j) (update st j (st i))
| exec_num: forall st n i, exec st (i_num n i) (update st i n)
| exec_plus: forall st i j k, exec st (i_plus i j k) (update st k (st i + st j))
| exec_minus: forall st i j k, exec st (i_minus i j k) (update st k (st i - st j))
| exec_mult: forall st i j k, exec st (i_mult i j k) (update st k (st i * st j))
| exec_eq_true : forall st i j k, st i = st j -> exec st (i_eq i j k) (update st k 1)
| exec_eq_false : forall st i j k, st i <> st j -> exec st (i_eq i j k) (update st k 0).

Hint Constructors exec.

(** Operational semantics for lists of instructions. *)
Inductive exec_list: state -> list instr -> state -> Prop :=
| exec_nil: forall st, exec_list st nil st
| exec_cons: forall h t st st' st'', exec st h st' -> exec_list st' t st'' -> exec_list st (h::t) st''.

Hint Constructors exec_list.

(** Here's the compiler for arithmetic expressions.   
      It uses variables >= N as scratch temporaries for subexpressions *)
Fixpoint compile_aexp (N: nat) (a: aexp) : list instr :=
  match a with
  | ANum n =>  i_num n (Id N) :: nil
  | AId i => i_move i (Id N) :: nil
  | APlus a1 a2 => compile_aexp N a1 ++ compile_aexp (S N) a2 ++ 
                               i_plus (Id N) (Id (S N)) (Id N) :: nil
  | AMinus a1 a2 => compile_aexp N a1 ++ compile_aexp (S N) a2 ++ 
                               i_minus (Id N) (Id (S N)) (Id N) :: nil
  | AMult a1 a2 => compile_aexp N a1 ++ compile_aexp (S N) a2 ++ 
                               i_mult (Id N) (Id (S N)) (Id N) :: nil
 end.

Fixpoint compile_com (N: nat) (c: com) : list instr := 
 match c with
  | CSkip => nil
  | CAss i a => compile_aexp N a ++ i_move (Id N) i :: nil
  | CSeq c1 c2 => compile_com N c1 ++ compile_com N c2
  | _ => nil
 end.

Fixpoint check_exp N (a: aexp) : Prop :=
  match a with
  | ANum n => True
  | AId (Id i) => i < N
  | APlus a1 a2 => check_exp N a1 /\ check_exp N a2
  | AMinus a1 a2 => check_exp N a1 /\ check_exp N a2
  | AMult a1 a2 => check_exp N a1 /\ check_exp N a2
 end.

Fixpoint check_com N (c: com) : Prop :=
  match c with
  | CSkip => True
  | CAss (Id i) a => i < N /\ check_exp N a
  | CSeq c1 c2 => check_com N c1 /\ check_com N c2
  | _ => False
 end.


Definition my_prog := (X ::= APlus (AId Y) (ANum 1) ;; Y ::= AMult (AId X)  (APlus (AId X) (AId Y))).

Example check_my_prog:
  check_com 10 my_prog.
Proof. simpl. intuition. Qed.

Example compile_my_prog:
   compile_com 10 my_prog = 
    i_move Y (Id 10)
    :: i_num 1 (Id 11)
    :: i_plus (Id 10) (Id 11) (Id 10)
    :: i_move (Id 10) X
    :: i_move X (Id 10)
    :: i_move X (Id 11)
    :: i_move Y (Id 12)
    :: i_plus (Id 11) (Id 12) (Id 11)
    :: i_mult (Id 10) (Id 11) (Id 10)
    :: i_move (Id 10) Y 
    :: nil.
Proof. reflexivity. Qed.

Example ceval_my_prog:
     my_prog / empty_state || (update (update empty_state X 1) Y 1).
Proof.
repeat (econstructor; simpl; try reflexivity).
Qed.

Example exec_my_prog:
    exists st, exec_list empty_state (compile_com 10 my_prog) st.
Proof.
econstructor.
simpl.
repeat (eapply exec_cons; [eauto|]).
apply exec_nil.
Qed.

(*EX 3 (wrong_compiler_correctness) *)
Definition wrong_compiler_correctness_specification :=
     forall c N, check_com N c ->
           forall st stx, exec_list st (compile_com N c) stx ->
                      ceval c st stx. 

Theorem wrong_specification_wrong:
  ~ wrong_compiler_correctness_specification.
(* FILL IN HERE *) Admitted.
(** [] *)

Definition same_below (N: nat) (st st': state) : Prop :=
            forall i, i < N -> st (Id i) = st' (Id i).

Definition compiler_correctness_specification :=
     forall c N, check_com N c ->
           forall st stx, exec_list st (compile_com N c) stx ->
                 forall sty, ceval c st sty ->
                   same_below N stx sty.

Ltac inv H := inversion H; clear H; subst.

(** **** Exercise: 3 stars (exec_list_lemmas) *)
Lemma exec_list_app:
    forall il1 il2 st1 st2 st3, 
      exec_list st1 il1 st2 -> exec_list st2 il2 st3 ->
      exec_list st1 (il1++il2) st3.
(* FILL IN HERE *) Admitted.
Hint Resolve exec_list_app.

Lemma exec_list_app_inv:
  forall il1 il2 st1 st3, exec_list st1 (il1++il2) st3 ->
  exists st2, exec_list st1 il1 st2 /\ exec_list st2 il2 st3.
(* FILL IN HERE *) Admitted.
(** [] *)

Ltac overr := rewrite update_neq; 
                         [| intro Hx; inv  Hx; subst; omega].

(* The tactic [crunch] is an example of the "Adam Chlipala style"; just
  a baby example of course.  For a complete introduction to this style
  of proof automation, see,
   Certified Programming with Dependent Types
   by Adam Chlipala, MIT Press, 2013.
   http://adam.chlipala.net/cpdt/
*)

Ltac crunch := 
          intros; 
          repeat
             first [rewrite update_eq
                    | overr 
                    | match goal with 
                        | H: False |- _ => contradiction
                        | H: _ /\ _ |- _  => destruct H
                        | H: exec_list _ (_ ++ _) _ |- _ =>
                            apply exec_list_app_inv in H; destruct H as [?st [? ?]]
                        | H: exec_list _ (_ :: _) _ |- _ => inv H
                        | H: exec_list _ nil _ |- _ => inv H
                        | H: exec _ (i_move _ _) _ |- _ => inv H
                        | H: exec _ (i_num _ _) _ |- _ => inv H
                        | H: exec _ (i_plus _ _ _) _ |- _ => inv H
                        | H: exec _ (i_minus _ _ _) _ |- _ => inv H
                        | H: exec _ (i_mult _ _ _) _ |- _ => inv H
                        | H: match ?ii with Id _ => _ end |- _ => destruct ii
                        | H: ceval _ CSkip _ |- _ => inv H
                        | H: ceval _ (CAss _ _) _  |- _=> inv H
                        end]; auto.

Lemma check_S:  forall N a, check_exp N a -> check_exp (S N) a.
Proof.
(aexp_cases (induction a) Case); simpl; crunch.
Qed.

Lemma same_below_refl: forall N st, same_below N st st.
Proof. unfold same_below; auto.
Qed.

Hint Resolve same_below_refl.

Lemma same_below_sym: forall N st st', 
        same_below N st st' -> same_below N st' st.
Proof.
unfold same_below; intros. symmetry; auto.
Qed.

Lemma same_below_trans:  forall N st1 st2 st3,
        same_below N st1 st2 -> same_below N st2 st3 -> same_below N st1 st3.
Proof.
unfold same_below; intros.
rewrite H; auto.
Qed.

(** **** Exercise: 2 stars (same_below_update) *)
Lemma same_below_update:
  forall i N v v' st st', 
         v = v' ->
        same_below N st st' -> 
        same_below N (update st i v) (update st' i v').
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

Hint Resolve same_below_update.

(** **** Exercise: 3 stars (compile_aexp_same_below) *)
Lemma compile_aexp_same_below:
  forall a N st st', exec_list st (compile_aexp N a) st' ->
          same_below N st st'.
Proof.
unfold same_below.
(aexp_cases (induction a) Case); simpl; crunch.
(** Instructions:  First, remove "crunch" from the line above, and use
     "Focus" to examine each of the 5 subgoals.  Now, put "crunch" back,
     notice that it has already disposed of 2 subgoals and made some progress
     in the other 3, and finish the proof.
*)     
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (aeval_same_below) *)
Lemma aeval_same_below:
  forall st st' a N,
   check_exp N a ->  
   same_below N st st' ->
   aeval st a = aeval st' a.
Proof.
unfold same_below.
(aexp_cases (induction a) Case); simpl; crunch.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (compile_aexp_correct) *)
Theorem compile_aexp_correct: 
     forall a N, check_exp N a ->
           forall st st', exec_list st (compile_aexp N a) st' ->
                    st' (Id N) = aeval st a.
Proof.
(aexp_cases (induction a) Case); simpl; crunch.
(* FILL IN HERE *) Admitted.
(** [] *)


(**  Consider an arithmetic expression [a] with no variables named N or above,
      and compile it with [compile N a]. 
      Now we believe that executing the compiled expression [compile N a] 
      should not affect any variables below N.  That is, if [st1] and [st1'] are
      the same below N, and we can execute from [st1] to get [st2], then
      we should be able to execute from st1' to get st2'.   Not only must
     st2' exist, but it should be the same as st2, below N.

    This can be explained by a  "commutative diagram".    The solid lines
    ( st1---st1',  st1---st2) indicate sides that are given in the hypothesis.
    The dotted lines  (st1' - - - st2',  st2 - - - st2') indicate sides that
    we claim must exist.

   (Caveat: This diagram works in Lucida Sans Unicode 10, looks terrible otherwise)

      st1 ----------------------  st1'
         |              same_below                 i
         |                                                  i
         | compile                                    i compile
         |                                                  i
         |              same_below                 i
       st2 - - - - - - - - - - - - - - -  st2'

   The formal statement of this is [comple_exp_fiddle], below.
*)

(** **** Exercise: 4 stars (compile_exp_fiddle) *)
Lemma compile_exp_fiddle:
  forall a N, check_exp N a ->
          forall J st1 st1', J <= N -> same_below J st1 st1' ->
          forall st2, exec_list st1 (compile_aexp N a) st2 ->
            exists st2', exec_list st1' (compile_aexp N a) st2' /\ same_below J st2 st2'.
Proof.
(aexp_cases (induction a) Case); simpl; crunch.
(* FILL IN HERE *) Admitted.
(** [] *)

(** We have the same kind of commutative diagram for compile_com. *)

(** **** Exercise: 4 stars (compile_com_fiddle) *)
Lemma compile_com_fiddle:
  forall c N,
          check_com N c ->
          forall st1 st1', same_below N st1 st1' ->
          forall st2, exec_list st1 (compile_com N c) st2 ->
                exists st2', exec_list st1' (compile_com N c) st2' /\ same_below N st2 st2'.
Proof.
(com_cases (induction c) Case); simpl; crunch.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars (compile_com_correct) *)
Theorem compile_com_correct: compiler_correctness_specification.
Proof.
unfold compiler_correctness_specification.
(com_cases (induction c) Case); simpl; crunch.
(* FILL IN HERE *) Admitted.

(** [] *)


