(******************************************************************************
 *  timedevent/Example.v
 *
 *  Copyright 2023 Bastiaan Laarakker
 *
 ******************************************************************************)

(*
 * This file is part of the Verified Calculus Library.
 *
 * The Verified Calculus Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The Verified Calculus Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
 * Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * the Verified Calculus Library. If not, see <https://www.gnu.org/licenses/>.
 *)


From Coq Require Import Arith.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Reals.
From Coq Require Import Bool.
From Coq Require Import Logic.
From Coq Require Import Logic.Eqdep.
From Coq Require Import FunctionalExtensionality.

From TimedEvent Require Import BoolSet.
From TimedEvent Require Import Definitions.
From TimedEvent Require Import IO.
From TimedEvent Require Import IOComposition.
From TimedEvent Require Import InputEnabling.


(*
  Here we show that for the simplest IO behaviours,
  which are input-enabling,
  their composition is also input-enabling
*)

Inductive U : Set :=
  ping
| send
| receive
| stutter.

Definition I1 : BoolSet U :=
  Single ping.

Definition O1 : BoolSet U :=
  Single send.

Definition O2 : BoolSet U :=
  Single receive.

Lemma t x : BoolSet.In x I1 = true -> x = ping.
Proof.
  intros. unfold I1, Single, BoolSet.In in H.
  destruct (U_eq_dec ping x).
  - symmetry. assumption.
  - discriminate H.
Qed.

Lemma disjointIO1 : Disjoint I1 O1.
Proof.
  unfold Disjoint, Intersection, I1, O1, Single, BoolSet.In.
  intro.
  destruct (U_eq_dec ping x).
  destruct (U_eq_dec send x).
  rewrite <- e in e0. inversion e0.
  all: easy.
Qed.

Lemma disjointIO2 : Disjoint I1 O2.
Proof.
  unfold Disjoint, Intersection, I1, O2, Single, BoolSet.In.
  intro.
  destruct (U_eq_dec ping x).
  destruct (U_eq_dec receive x).
  rewrite <- e in e0. inversion e0.
  all: easy.
Qed.

Lemma no_stut1 : In stutter (I1 :|: O1) = false.
Proof.
  unfold I1, O1, Union, Single, In.
  destruct (U_eq_dec ping stutter);
  destruct (U_eq_dec send stutter).
  all: easy.
Qed.

Lemma no_stut2 : In stutter (I1 :|: O2) = false.
Proof.
  unfold I1, O2, Union, Single, In.
  destruct (U_eq_dec ping stutter);
  destruct (U_eq_dec receive stutter).
  all: easy.
Qed.

Definition example_behaviour1 :
  IO_behaviour I1 O1 stutter :=
  mkIOBehaviour disjointIO1 no_stut1
  (fun I_tr => fun O_tr => True).


Definition example_behaviour2 :
  IO_behaviour I1 O2 stutter :=
  mkIOBehaviour disjointIO2 no_stut2
  (fun I_tr => fun O_tr => True).

Fixpoint construct_stutter_raw stut (I_l : raw_tr_list U)
  : raw_tr_list U :=
  match I_l with
  | [] => []
  | ((t, e) :: tl) => (t, stut) :: construct_stutter_raw stut tl
  end.


Lemma construct_stutter_list_good : forall I_l O stut,
  good_tr_list (BoolSet.Add stut O)
    (construct_stutter_raw stut I_l) = true.
Proof.
  intros. induction I_l.
  - reflexivity.
  - destruct a. simpl; apply andb_true_iff; split.
    apply In_Add. apply IHI_l.
Qed.

Definition construct_stutter_list {I} stut O (I_l : trace_list I)
  : trace_list (BoolSet.Add stut O) :=
  mkTrlist (BoolSet.Add stut O) (construct_stutter_raw stut I_l)
    (construct_stutter_list_good I_l O stut).

Lemma construct_increasing (I_l : raw_tr_list U) : forall stut,
  increasing_time I_l -> increasing_time (@construct_stutter_raw stut I_l).
Proof.
  intros.
  assert (fst_list I_l = fst_list (@construct_stutter_raw stut I_l)).
  { induction I_l. easy. simpl. destruct a. simpl. f_equal. inversion H. apply (IHI_l H3). }
  apply (incr_fst_list I_l). all: assumption.
Qed.

Definition construct_stutter_trace {I} O (I_tr : trace I)
  : trace (BoolSet.Add stutter O) :=
  exist _ (construct_stutter_list _ _ (proj1_sig I_tr))
    (construct_increasing (proj1_sig I_tr) _ (proj2_sig I_tr)).


Lemma stutter_trace_stutters {I O : BoolSet U} : forall (I_tr : trace I),
  trace_stutters stutter I_tr (construct_stutter_trace O I_tr).
Proof.
  intros. destruct I_tr as [I_l incr]. unfold trace_stutters. simpl.
  unfold trlist_stutters. destruct I_l as [I_l good]. induction I_l.
  - simpl. easy.
  - simpl. destruct a. unfold rawlist_stutters. simpl in *. rewrite Stut_stut. simpl.
    f_equal. inversion incr. apply andb_true_iff in good; destruct good.
    apply (IHI_l H4 H2).
Qed.


Lemma enable1 : input_enabling example_behaviour1.
Proof.
unfold input_enabling. intros.
exists (exist _ (construct_stutter_trace O1 I_tr) (stutter_trace_stutters I_tr)).
easy.
Qed.

Lemma enable2 : input_enabling example_behaviour2.
Proof.
unfold input_enabling. intros.
exists (exist _ (construct_stutter_trace O2 I_tr) (stutter_trace_stutters I_tr)).
easy.
Qed.

Lemma enable1' : forall tr, (from_IO_behaviour example_behaviour1) tr = True.
Proof.
  intros. unfold from_IO_behaviour. easy.
Qed.

Lemma enable2' : forall tr, (from_IO_behaviour example_behaviour2) tr = True.
Proof.
  intros. unfold from_IO_behaviour. easy.
Qed.

Definition composed_behaviour := compose_IO2 example_behaviour1 example_behaviour2.

Lemma enable_comp : input_enabling composed_behaviour.
Proof.
  unfold input_enabling, composed_behaviour, compose_IO2, Composition.compose; intros.
  exists (exist _ (construct_stutter_trace (O1 :|: O2) I_tr) (stutter_trace_stutters I_tr)).
  pose (x:=fun
        tr : trace
               (Setminus (I1 :|: I1) (O1 :|: O2)
             :|: (O1 :|: O2)) =>
      from_IO_behaviour
        example_behaviour1
        (Composition.proj_trace (I1 :|: O1) tr) /\
      from_IO_behaviour
        example_behaviour2
        (Composition.proj_trace (I1 :|: O2) tr)).
  pose (x':=(fun tr : trace (Setminus (I1 :|: I1) (O1 :|: O2)
             :|: (O1 :|: O2)) => True)).
  assert (x ≡ x').
  { unfold x, x', eq_behaviour. intros.
    rewrite enable1'. rewrite enable2'. easy. }
  unfold x, x' in H.
  generalize (@u_eqv_comp2 U I1 I1 O1 O2).
  rewrite u_eqv_comp2. intros.
  rewrite (UIP_refl _ _ e).
  unfold eq_behaviour in H.
  rewrite H. easy.
Qed.
