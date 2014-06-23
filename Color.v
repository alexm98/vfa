(* Implementation of the Kempe/Chaitin algorithm for graph coloring,
   by Andrew W. Appel, 2011.

  Required reading:
  Formal Verification of Coalescing Graph-Coloring Register Allocation,
  by Sandrine Blazy, Benoit Robillard, and Andrew W. Appel.
  ESOP 2010: 19th European Symposium on Programming, pp. 145-164, March 2010.
  http://www.cs.princeton.edu/~appel/papers/regalloc.pdf

  We implement a program to K-color an undirected graph, perhaps leaving
  some nodes uncolored.  In a register-allocation problem, the graph nodes
  correspond to variables in a program, the colors correspond to registers,
  and the graph edges are interference constraints:  two nodes connected
  by an edge cannot be assigned the same color.  Nodes left uncolored are
  "spilled," that is, a register allocator would implement such nodes in
  memory locations instead of in registers.  We desire to have as few
  uncolored nodes as possible, but this desire is not formally specified.

  In this exercise we show a simple and unsophisticated algorithm; the program
  described by Blazy et al. (cited above) is more sophisticated in several ways,
  such as the use of "register coalescing" to get better results and the use of
  worklists to make it run faster.

  Our algorithm does, at least, make use of efficient data structures for
  representing undirected graphs, adjacency sets, and so on.

*)

(*  PRELIMINARIES:  EFFICIENT DATA STRUCTURES FOR REPRESENTING
    SETS OF NODES, and FUNCTIONS THAT MAP NODES TO WHATEVER *)

Require Import List.
Require Import FSets.    (* Efficient functional sets *)
Require Import FMaps.  (* Efficient functional maps *)
Require Import Compare_dec.  (* to get lt_dec on natural numbers *)

(* The nodes in our graph will be taken from some ordered type, so that
  we can use efficient data structures for sets and maps.  FSets are a purely
  functional representation of sets over some element type,
  with logarithmic-time membership test and add-one-element,
  and linear-time or NlogN set union.  The type of keys (members of sets, indexes
  of maps) will be E.t;  and type type of sets will be S.t, and maps from E.t to A
  will be M.t(A) for any type A.

   We choose the "positive" type, because the Coq library has particularly efficient
   implementations of sets and maps on positives.  But our proofs will
  be easier if we hide the particular representation type.  We would like to say,
   Module E <: OrderedType := PositiveOrderedTypeBits.
   Module S <: (FSetInterface.S with Module E := E) := PositiveSet.
   Module M <: (FMapInterface.S with Module E := E) := PositiveMap.
  but for a stupid Coq technical reason (transparency of definitions interfering
  with rewrite tactics) we use the following clumsy definition instead:
*)
Module E : OrderedType with Definition t := BinPos.positive
                                      with Definition eq := (@eq BinPos.positive)
                                      with Definition lt := PositiveOrderedTypeBits.bits_lt
                                      with Definition eq_dec := PositiveOrderedTypeBits.eq_dec
                                      with Definition eq_refl := PositiveOrderedTypeBits.eq_refl
                                      with Definition eq_sym := PositiveOrderedTypeBits.eq_sym
                                      with Definition eq_trans := PositiveOrderedTypeBits.eq_trans
                                      with Definition lt_trans := PositiveOrderedTypeBits.lt_trans
                                      with Definition lt_not_eq := PositiveOrderedTypeBits.lt_not_eq
                                      with Definition compare := PositiveOrderedTypeBits.compare
     := PositiveOrderedTypeBits.
Module S : FSetInterface.S with Module E := E
                                         with Definition elt := PositiveSet.elt
                                         with Definition t := PositiveSet.t
                                         with Definition empty := PositiveSet.empty
                                     with Definition is_empty :=  PositiveSet.is_empty
                                     with Definition mem :=  PositiveSet.mem
                                     with Definition add := PositiveSet.add
                                     with Definition singleton :=  PositiveSet.singleton
                                     with Definition remove :=  PositiveSet.remove
                                     with Definition union :=  PositiveSet.union
                                     with Definition inter :=  PositiveSet.inter
                                     with Definition diff :=  PositiveSet.diff
                                     with Definition equal :=  PositiveSet.equal
                                     with Definition subset :=  PositiveSet.subset
                                     with Definition fold :=  PositiveSet.fold
                                     with Definition for_all :=  PositiveSet.for_all
                                     with Definition exists_ :=  PositiveSet.exists_
                                     with Definition filter :=  PositiveSet.filter
                                     with Definition partition :=  PositiveSet.partition
                                     with Definition cardinal :=  PositiveSet.cardinal
                                     with Definition elements :=  PositiveSet.elements
                                     with Definition choose :=  PositiveSet.choose
     := PositiveSet.

Module M : FMapInterface.S with Module E := E
                       with Definition t := PositiveMap.t
                       with Definition empty := PositiveMap.empty
                       with Definition is_empty := PositiveMap.is_empty
                       with Definition add := PositiveMap.add
                       with Definition find := PositiveMap.find
                       with Definition remove := PositiveMap.remove
                       with Definition mem := PositiveMap.mem
                       with Definition map := PositiveMap.map
                       with Definition mapi := PositiveMap.mapi
                       with Definition map2 := PositiveMap.map2
                       with Definition elements := PositiveMap.elements
                       with Definition cardinal := PositiveMap.cardinal
                       with Definition fold := PositiveMap.fold
                       with Definition equal := PositiveMap.equal
                       with Definition MapsTo := PositiveMap.MapsTo

 := PositiveMap.
Module Import WF := WFacts_fun E M.  (* Library of useful lemmas about maps *)
Module Import WP := WProperties_fun E M.  (* More useful stuff about maps *)

(* USEFUL LEMMAS ABOUT SETS AND MAPS *)

(* The domain of a map is the set of elements that map to Some(_) *)
Definition Mdomain {A} (m: M.t A) : S.t :=
   M.fold (fun n _ s => S.add n s) m S.empty.

Lemma StrictOrder_lt: StrictOrder E.lt.
(* This lemma useful when using the lemma SortA_equivlistA_eqlistA *)
Proof.
constructor.
unfold Irreflexive, Reflexive, complement.
intros; eapply E.lt_not_eq; eauto.
unfold Transitive.
intros; eapply E.lt_trans; eauto.
Qed.

Lemma lt_eq_trans: forall {x y z}, E.lt x y -> E.eq y z -> E.lt x z.
Proof.
intros. destruct (E.compare x z); auto.
apply E.lt_not_eq in H. contradiction H. transitivity z; auto.
contradiction (E.lt_not_eq (E.lt_trans l H)). auto.
Qed.

Lemma eq_lt_trans: forall {x y z}, E.eq x y -> E.lt y z -> E.lt x z.
Proof.
intros. destruct (E.compare x z); auto.
apply E.lt_not_eq in H0. contradiction H0. transitivity x; auto.
contradiction (E.lt_not_eq (E.lt_trans H0 l)). auto.
Qed.

Lemma Proper_lt: Proper (E.eq ==> E.eq ==> iff) E.lt.
Proof.
constructor; intros.
destruct (E.compare y y0); auto.
apply E.lt_not_eq in H1.  contradiction H1; congruence.
generalize (E.lt_trans (lt_eq_trans l (E.eq_sym H)) H1); intro.
apply E.lt_not_eq in H2. contradiction H2; auto.
generalize (lt_eq_trans H1 (E.eq_sym H0)); intro.
apply @eq_lt_trans with y; auto.
Qed.

(* Pay attention here to the use of SortA_equivlistA_eqlistA.
  Here we specialize it to the case there the comparison operator is E.lt,
  but in the proof of Mremove_elements we will use it specialized to a
  different (though related) total ordering on a different type of list elements. *)
Lemma SortE_equivlistE_eqlistE:
 forall l l', Sorted E.lt l -> Sorted E.lt l' -> equivlistA E.eq l l' -> eqlistA E.eq l l'.
Proof.
  apply SortA_equivlistA_eqlistA; auto.
  apply StrictOrder_lt.
  apply Proper_lt.
Qed.

Lemma filter_sortE: forall f l, Sorted E.lt l -> Sorted E.lt (List.filter f l).
(* This lemma is useful in the proof of Sremove_elements *)
Proof.
apply filter_sort with E.eq; auto.
apply StrictOrder_lt.
apply Proper_lt.
Qed.

(** **** Exercise: 3 stars (Sremove_elements) *)
Lemma Sremove_elements:  forall (i: E.t) (s: S.t),
  S.In i s ->
     eqlistA E.eq (S.elements (S.remove i s))
              (List.filter (fun x => if E.eq_dec x i then false else true) (S.elements s)).
Proof.
intros.
assert (PROPER: Proper (E.eq ==> eq)
  (fun x : E.t => if F.eq_dec x i then false else true)).
(* FILL IN HERE *) admit.
apply SortE_equivlistE_eqlistE; auto.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (InA_map_fst_key) *)
Lemma InA_map_fst_key:
 forall A j l, InA E.eq j (map (@fst _ A) l) <-> exists e, InA (@M.eq_key_elt _) (j,e) l.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (cardinal_map) *)
Lemma cardinal_map:  forall A B (f: A -> B) g, M.cardinal (M.map f g) = M.cardinal g.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (Sremove_cardinal_less) *)
Lemma Sremove_cardinal_less: forall i s, S.In i s ->
        S.cardinal (S.remove i s) < S.cardinal s.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (eqv_eq_key_elt) *)
Lemma eqv_eq_key_elt: forall elt, Equivalence (@M.eq_key_elt elt).
(* This lemma is useful in the proof of Mremove_elements *)
(* ADMITTED*)
Proof.
 intros. unfold M.eq_key_elt; split; repeat intro; intuition.
   eapply M.E.eq_trans; eauto. rewrite H2; auto.
Qed.
(* /ADMITTED *)
(** [] *)

(** **** Exercise: 3 stars (Mremove_elements) *)
Lemma Mremove_elements:  forall A i s,
  M.In i s ->
     eqlistA (@M.eq_key_elt A) (M.elements (M.remove i s))
              (List.filter (fun x => if E.eq_dec (fst x) i then false else true) (M.elements s)).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (Mremove_cardinal_less) *)
Lemma Mremove_cardinal_less: forall A i (s: M.t A), M.In i s ->
        M.cardinal (M.remove i s) < M.cardinal s.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (two_little_lemmas) *)

Lemma fold_right_rev_left:
  forall (A B: Type) (f: A -> B -> A) (l: list B) (i: A),
  fold_left f l i = fold_right (fun x y => f y x) i (rev l).
(* FILL IN HERE *) Admitted.

Lemma Snot_in_empty: forall n, ~ S.In n S.empty.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (Sin_domain) *)
Lemma Sin_domain: forall A n (g: M.t A), S.In n (Mdomain g) <-> M.In n g.
(* FILL IN HERE *) Admitted.
(** [] *)

(* Now begins the graph coloring program *)

Definition node := E.t.
Definition nodeset := S.t.
Definition nodemap: Type -> Type := M.t.
Definition graph := nodemap nodeset.

Definition adj (g: graph) (i: node) : nodeset :=
  match M.find i g with Some a => a | None => S.empty end.

Definition undirected (g: graph) :=
   forall i j, S.In j (adj g i) -> S.In i (adj g j).

Definition no_selfloop (g: graph) := forall i, ~ S.In i (adj g i).

Definition nodes (g: graph) := Mdomain g.

Definition subset_nodes
                    {P: node -> nodeset -> Prop}
                    (P_dec: forall n adj, {P n adj}+{~P n adj})
                    (g: graph) :=
   M.fold (fun n adj s => if P_dec n adj then S.add n s else s) g S.empty.

(* We need to prove some lemmas related to the termination of the algorithm
  before we can actually define the Function *)

(** **** Exercise: 3 stars (subset_notes_sub) *)
Lemma subset_nodes_sub:  forall P f g, S.Subset (@subset_nodes P f g) (nodes g).
(* FILL IN HERE *) Admitted.
(** [] *)

Definition low_deg (K: nat) (n: node) (adj: nodeset) := S.cardinal adj < K.

Lemma low_deg_dec: forall K n adj, {low_deg K n adj}+{~low_deg K n adj}.
Proof.
intros. unfold low_deg. destruct (lt_dec (S.cardinal adj0) K); auto.
Defined.  (* Must use Defined here instead of Qed so it Computes *)

Definition remove_node (n: node) (g: graph) : graph :=
  M.map (S.remove n) (M.remove n g).

(** **** Exercise: 3 stars (select_terminates) *)
Lemma select_terminates:
  forall (K: nat) (g : graph) (n : S.elt),
   S.choose (subset_nodes (low_deg_dec K) g) = Some n ->
   M.cardinal (remove_node n g) < M.cardinal g.
(* FILL IN HERE *) Admitted.
(** [] *)

Require Recdef.

Function select (K: nat) (g: graph) {measure M.cardinal g}: list node :=
  match S.choose (subset_nodes (low_deg_dec K) g) with
  | Some n => n :: select K (remove_node n g)
  | None => nil
  end.
Proof. apply select_terminates.
Defined.  (* Do not use Qed on a Function, otherwise it won't Compute! *)

Definition coloring := M.t node.

Definition colors_of (f: coloring) (s: S.t) : S.t :=
   S.fold (fun n s => match M.find n f with Some c => S.add c s | None => s end) s S.empty.

Definition color1 (palette: S.t) (g: graph) (n: node) (f: coloring) : coloring :=
   match S.choose (S.diff palette (colors_of f (adj g n))) with
   | Some c => M.add n c f
   | None => f
   end.

Definition color (palette: S.t) (g: graph) : coloring :=
  fold_right (color1 palette g)  (M.empty _) (select (S.cardinal palette) g).

(* Now, the proof of correctness of the algorithm.
  We want to show that any coloring produced by the [color] function
  actually respects the interference constraints.  This property is
  called [coloring_ok].
*)

Definition coloring_ok (palette: S.t) (g: graph) (f: coloring) :=
 forall i j, S.In j (adj g i) ->
     (forall ci, M.find i f = Some ci -> S.In ci palette) /\
     (forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci<>cj).

(** **** Exercise: 2 stars (adj_ext) *)
Lemma adj_ext: forall g i j, E.eq i j -> S.eq (adj g i) (adj g j).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (in_colors_of_1) *)
Lemma in_colors_of_1:
  forall i s f c, S.In i s -> M.find i f = Some c -> S.In c (colors_of f s).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (color_correct) *)
Theorem color_correct:
  forall palette g,
       no_selfloop g ->
       undirected g ->
       coloring_ok palette g (color palette g).
(* FILL IN HERE *) Admitted.
(** [] *)

(* TEST CASE *)

Delimit Scope positive_scope with positive.

(* Let's use only three colors *)
Definition palette: S.t := fold_right S.add S.empty (1::2::3::nil)%positive.

Definition add_edge (e: (E.t*E.t)) (g: graph) : graph :=
 M.add (fst e) (S.add (snd e) (adj g (fst e)))
  (M.add (snd e) (S.add (fst e) (adj g (snd e))) g).

Definition mk_graph (el: list (E.t*E.t)) :=
  fold_right add_edge (M.empty _) el.

Definition mygraph := mk_graph ( (5,6)::(6,2)::(5,2)::(1,5)::(1,2)::(2,4)::(1,4)::nil)%positive.

Compute (S.elements (Mdomain mygraph)).
(*   = 4%positive
       :: 2%positive :: 6%positive :: 1%positive :: 5%positive :: nil
     : list S.elt
*)

Compute (M.elements (color palette mygraph)).
(*   = (4%positive, 1%positive)
       :: (2%positive, 3%positive)
          :: (6%positive, 2%positive)
             :: (1%positive, 2%positive) :: (5%positive, 1%positive) :: nil
     : list (M.key * node)
*)