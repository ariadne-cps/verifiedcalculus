(******************************************************************************
 *  timedevent/Composition.v
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


From Coq Require Import Reals.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Eqdep.

From TimedEvent Require Import BoolSet.
From TimedEvent Require Import Definitions.

Section Universal.
Context {U : Set}.

Section Filter.
Fixpoint raw_tr_list_filter (E : BoolSet U) (w : raw_tr_list U) : raw_tr_list U :=
  match w with
  | [] => []
  | hd :: tl => if In (snd hd) E then
        hd :: raw_tr_list_filter E tl
      else
        raw_tr_list_filter E tl
  end.


(* Proof that, using this filter, all remaining elements are in E2 *)
Lemma goodFilterE  (E2 : BoolSet U) (w : raw_tr_list U) :
  is_true (good_tr_list E2 (raw_tr_list_filter E2 w)).
Proof.
  unfold is_true. induction w as [|a r IHraw].
  - easy.
  - simpl. destruct (In (snd a) E2) eqn:Hin.
    * unfold good_tr_list. rewrite Hin. now simpl.
    * apply IHraw.
Defined.


Lemma filter_ge_help : forall E A (a : R*A) (w : raw_tr_list U),
  increasing_time w -> ge_head_zero a w ->
  ge_head_zero a (raw_tr_list_filter E w).
Proof.
  intros. induction w.
  - simpl. apply H0.
  - unfold raw_tr_list_filter. destruct (In (snd a0) E);
    fold raw_tr_list_filter.
    * apply H0.
    * inversion H. apply (IHw H4).
      apply ge_app_ge_l with (a:=a) in H. apply H. apply H0.
Qed.


Lemma filter_preserves_increasing :
  forall E (w : raw_tr_list U),
  increasing_time w -> increasing_time (raw_tr_list_filter E w).
Proof.
  intros. induction w.
  - simpl. apply incr_nil.
  - unfold raw_tr_list_filter. destruct (In (snd a)).
    * fold raw_tr_list_filter. inversion H. apply incr_app.
      ** apply (filter_ge_help _ _ _ _ H3 H2).
      ** apply (IHw H3).
    * fold raw_tr_list_filter; apply IHw; inversion H; apply H3.
Qed.

Definition proj_list {E1 : BoolSet U} (E2 : BoolSet U) (w : trace_list E1)
    : trace_list E2 :=
  mkTrlist _ _ (goodFilterE E2 w).

Lemma proj_list_preserves_increasing {E1 : BoolSet U} (E2 : BoolSet U) :
  forall (w : trace_list E1),
  increasing_time w -> increasing_time (proj_list E2 w).
Proof.
  intros. unfold proj_list.
  apply (filter_preserves_increasing E2 w) in H.
  apply H.
Qed.

(* finally define filter on trace *)
Definition proj_trace {E1 : BoolSet U} (E2 : BoolSet U) (tr : trace E1) : trace E2 :=
  match tr with
  | exist _ tr_list inc_time =>
      exist _ (proj_list E2 tr_list)
        (proj_list_preserves_increasing E2 tr_list inc_time)
  end.

End Filter.


Section Composition.

Variable E1 E2 : BoolSet U.

Definition compose : behaviour E1 -> behaviour E2 -> behaviour (E1 :|: E2) :=
  fun B1 B2 tr => B1 (proj_trace E1 tr) /\ B2 (proj_trace E2 tr).

Definition is_composition (b_comp : behaviour (E1 :|: E2))
  (b1 : behaviour E1) (b2 : behaviour E2) :=
    forall tr, b_comp tr <-> (compose b1 b2) tr.

Lemma compose_is_composition (b1 : behaviour E1) (b2 : behaviour E2) :
  is_composition (compose b1 b2) b1 b2.
Proof.
  unfold compose, is_composition; intros; split; intros; assumption.
Qed.


End Composition.
Arguments compose {E1 E2}.
Notation "B1 || B2" := (compose B1 B2).

Section Properties.

Lemma b_union_comm {E1 E2 : BoolSet U} :
  behaviour (E1 :|: E2) = behaviour (E2 :|: E1).
Proof. rewrite union_comm. easy. Defined.

(* note that m_eq_type just matches the types *)
Definition compose_comm {E1 E2 : BoolSet U} :
  forall (B1 : behaviour E1) (B2 : behaviour E2),
   (B1 || B2) ≡ m_eq_type b_union_comm (B2 || B1).
Proof.
  intros. unfold compose, m_eq_type. generalize (@b_union_comm E2 E1).
  rewrite union_comm. intros. rewrite (UIP_refl _ _ e).
  now unfold eq_behaviour.
Qed.

Lemma raw_tr_list_filter_subset_eq {E1 E2 : BoolSet U} w :
  Subset E1 E2 ->
  raw_tr_list_filter E1 (raw_tr_list_filter E2 w) =
  raw_tr_list_filter E1 w.
Proof.
  intro; induction w.
  - easy.
  - simpl. destruct (In (snd a) E2) eqn:Hinu.
    * destruct (In (snd a) E1) eqn:Hin.
      + simpl. rewrite Hin. now f_equal.
      + simpl. now rewrite Hin.
    * destruct (In (snd a) E1) eqn:Hin.
      + unfold Subset in H. apply H in Hin. now rewrite Hinu in Hin.
      + apply IHw.
Qed.

Lemma proj_subset_eq {E1 E3 : BoolSet U} (tr : trace E3) E2 :
  Subset E1 E2 ->
  proj_trace E1 (proj_trace E2 tr) = proj_trace E1 tr.
Proof.
  intro; apply trace_eq, trace_list_eq.
  unfold proj_trace; destruct tr; simpl.
  now apply raw_tr_list_filter_subset_eq.
Qed.


Lemma b_union_assoc {E1 E2 E3 : BoolSet U} :
  behaviour (E1 :|: (E2 :|: E3)) = behaviour (E1 :|: E2 :|: E3).
Proof. rewrite union_assoc. easy. Defined.

Lemma compose_assoc {E1 E2 E3 : BoolSet U} :
  forall (B1 : behaviour E1) (B2 : behaviour E2) (B3 : behaviour E3),
    ((B1 || B2) || B3) ≡ m_eq_type b_union_assoc (B1 || (B2 || B3)).
Proof.
  intros B1 B2 B3. unfold compose, m_eq_type.
  generalize (@b_union_assoc E1 E2 E3).
  generalize dependent ((B1 || B2) || B3). generalize (B1 || (B2 || B3)).
  rewrite union_assoc. intros. rewrite (UIP_refl _ _ e).
  unfold eq_behaviour; intros.
  rewrite !proj_subset_eq in *. easy.
  all: try apply union_subset_r; try apply union_subset_l.
Qed.

End Properties.

End Universal.
Arguments compose {U E1 E2}.
Arguments is_composition {U E1 E2}.
Notation "B1 || B2" := (compose B1 B2).
