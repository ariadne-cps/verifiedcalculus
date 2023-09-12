(******************************************************************************
 *  timedevent/Prefix.v
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


From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.
From Coq Require Import Reals.

From TimedEvent Require Import BoolSet.
From TimedEvent Require Import Definitions.
From TimedEvent Require Import Composition.

Section Universal.
Context {U : Set}.

Section Prefix.

(* Note that because we work with reverse lists,
   prefixes of traces are actually suffixes of lists. *)
Inductive suffix {A : Type} : list A -> list A -> Prop :=
  | suffix_refl : forall l : list A, suffix l l
  | suffix_cons : forall (x : A) (l1 l2 : list A), suffix l1 l2 -> suffix l1 (x :: l2).

Lemma empty_all_suffix {A} : forall (l: list A), suffix [] l.
Proof. induction l; now constructor. Qed.

Lemma suffix_app {A : Type} : forall (xs ys : list A),
  suffix xs ys <->
  exists ws, ys = ws ++ xs.
Proof.
  split.
  * intros; induction H.
    - exists []; easy.
    - destruct IHsuffix as [ws IH]. subst l2.
      now exists (x :: ws).
  * intros. induction ys.
    - destruct H as [ws H]. simpl in H. destruct xs.
      + constructor.
      + now apply app_cons_not_nil in H.
    - destruct H as [ws H]. destruct ws.
      + symmetry in H. simpl in H. subst xs. constructor.
      + simpl in H. constructor. apply IHys.
        exists ws. now inversion H.
Qed.

Lemma suffix_empty {A} : forall (l : list A), suffix l [] -> l = [].
Proof. intros. induction l; firstorder; easy. Qed.

(* an equivalent definition of suffix *)
Definition suffix' {A : Type} (l1 l2 : list A) :=
  (exists n, skipn n l2 = l1).

Lemma suffix'_app {A : Type} : forall (xs ys : list A),
  suffix' xs ys <->
  exists ws, ys = ws ++ xs.
Proof.
  intros; split; intros.
  - destruct H as [n H]. destruct n.
    * simpl in H. exists []. symmetry. simpl. now symmetry.
    * destruct ys.
      + simpl in H. subst. now exists [].
      + simpl in H. exists (a :: (firstn n ys)).
        simpl. f_equal. subst xs. now rewrite firstn_skipn.
  - destruct H as [ws H]. unfold suffix'.
    generalize dependent ws. induction ys; intros.
    * destruct xs. now exists 0%nat. now apply app_cons_not_nil in H.
    * destruct ws.
      + symmetry in H. simpl in H. subst. now exists 0%nat.
      + simpl in H. inversion H. rewrite <- H2.
        apply (IHys ws) in H2.
        destruct H2 as [n H2].
        exists (S n). now simpl.
Qed.

Lemma suffix'_suffix {A} : forall (l1 l2 : list A),
  suffix' l1 l2 <-> suffix l1 l2.
Proof.
  intros. now rewrite suffix_app, suffix'_app.
Qed.

(* pre_tr is a prefix of tr, non-strict definition! *)
Definition prefix {E : BoolSet U} (pre_tr tr : trace E) :=
  suffix (raw_of_tracelist (proj1_sig pre_tr))
    (raw_of_tracelist (proj1_sig tr)).

Definition prefix_free {E : BoolSet U} (b : behaviour E) :=
  forall tr, b tr -> (forall tr', prefix tr' tr -> b tr' -> tr = tr').

Definition prefix_closed {E : BoolSet U} (b : behaviour E) :=
  forall tr, b tr -> (forall tr', prefix tr' tr -> b tr').

End Prefix.


Lemma prefix_proj {E F : BoolSet U} (tr tr' : trace E) :
  prefix tr' tr -> prefix (proj_trace F tr') (proj_trace F tr).
Proof.
  intro H. destruct tr as [[w g] incr], tr' as [[w' g'] incr'].
  unfold prefix in *; simpl in *.
  induction H as [|x w w' Hp IHp].
  - constructor.
  - unfold raw_tr_list_filter. destruct (In (snd x) F);
    try constructor; and_destr g;
    inversion incr; now apply IHp.
Qed.

Lemma prefix_closed_compose {E1 E2 : BoolSet U} :
  forall (B1 : behaviour E1) (B2 : behaviour E2),
  prefix_closed B1 -> prefix_closed B2 -> prefix_closed (B1 || B2).
Proof.
  unfold compose, prefix_closed. intros B1 B2 H1 H2 tr Hc tr' Hp.
  specialize (H1 (proj_trace E1 tr)).
  specialize (H2 (proj_trace E2 tr)).
  destruct Hc as [Hc1 Hc2].
  assert (Hp1': prefix (proj_trace E1 tr') (proj_trace E1 tr))
    by (apply prefix_proj; assumption).
  assert (Hp2': prefix (proj_trace E2 tr') (proj_trace E2 tr))
    by (apply prefix_proj; assumption).
  split.
  - apply (H1 Hc1 (proj_trace E1 tr') Hp1').
  - apply (H2 Hc2 (proj_trace E2 tr') Hp2').
Qed.

(* Here we characterise the length of a trace list using this function *)
Fixpoint count_double (E1 E2 : BoolSet U) (l : raw_tr_list U) : nat :=
  match l with
  | [] => 0
  | (x :: xs) => if (In (snd x) E1) && (In (snd x) E2)
                 then 1 + count_double E1 E2 xs
                 else count_double E1 E2 xs
  end.

Lemma double_in_filter {E1 E2} : forall (l : raw_tr_list U),
  good_tr_list (E1 :|: E2) l = true ->
  (count_double E1 E2 l) = (count_double E1 E2 (raw_tr_list_filter E1 l)).
Proof.
  intros. induction l; simpl.
  - easy.
  - and_destr H; destruct (In (snd a) E1) eqn:H1.
    * destruct (In (snd a) E2) eqn:H2.
      + simpl. rewrite H1, H2. simpl. f_equal. apply (IHl H0).
      + simpl. rewrite H1, H2. simpl. apply (IHl H0).
    * destruct (In (snd a) E2) eqn:H2.
      + simpl. apply (IHl H0).
      + simpl. apply (IHl H0).
Qed.

Close Scope R_scope.

Lemma succ_min : forall (a b c d : nat),
  a = b + c - d -> c >= d -> S a = (S b) + c - d.
Proof. lia. Qed.

Lemma succ_min' : forall (a b c d : nat),
  a = b + c - S d -> c >= S d -> S a = b + c - d.
Proof. lia. Qed.

Lemma succ_ge_pred_ge : forall (a b : nat), a >= b -> S a >= b.
Proof. lia. Qed.

Lemma filter_length_gt_double1 {E1 E2} : forall (l : raw_tr_list U),
  good_tr_list (E1 :|: E2) l = true ->
  length (raw_tr_list_filter E1 l) >= count_double E1 E2 l.
Proof.
  intros. induction l.
  - simpl. left.
  - simpl. destruct (In (snd a) E1).
    * destruct (In (snd a) E2); simpl;
      and_destr H; specialize (IHl H0).
      + lia.
      + now apply succ_ge_pred_ge.
    * destruct (In (snd a) E2); simpl;
      and_destr H; specialize (IHl H0);
      apply IHl.
Qed.

Lemma filter_length_gt_double2 {E1 E2} : forall (l : raw_tr_list U),
  good_tr_list (E1 :|: E2) l = true ->
  length (raw_tr_list_filter E2 l) >= count_double E1 E2 l.
Proof.
  intros. induction l.
  - simpl. left.
  - simpl. destruct (In (snd a) E2).
    * destruct (In (snd a) E1); simpl;
      and_destr H; specialize (IHl H0).
      + lia.
      + now apply succ_ge_pred_ge.
    * destruct (In (snd a) E1); simpl;
      and_destr H; specialize (IHl H0);
      apply IHl.
Qed.

(* This is the length characterised *)
Lemma length_filters {E1 E2} : forall (l : raw_tr_list U),
  good_tr_list (E1 :|: E2) l = true ->
  length l =
    (length (raw_tr_list_filter E1 l)) +
    (length (raw_tr_list_filter E2 l)) -
    (count_double E1 E2 l).
Proof.
  intros. induction l; simpl in *; intros.
  - easy.
  - destruct (In (snd a) E1) eqn:Hin1.
    * destruct (In (snd a) E2) eqn:Hin2;
      simpl; and_destr H; specialize (IHl H0).
      + rewrite add_comm. apply succ_min.
        now rewrite add_comm. now apply filter_length_gt_double1.
      + destruct (count_double E1 E2 l) eqn:Hc.
        ++ f_equal. lia.
        ++ apply succ_min'. apply IHl.
           rewrite <- Hc. now apply filter_length_gt_double2.
    * destruct (In (snd a) E2) eqn:Hin2.
      + simpl. and_destr H. specialize (IHl H0).
        rewrite add_comm. apply succ_min.
        now rewrite add_comm. now apply filter_length_gt_double1.
      + and_destr H. apply in_union_or in H. destruct H.
        now rewrite H in Hin1. now rewrite H in Hin2.
Qed.

(* they must have equal length if projections are equal *)
Lemma filters_eq_length {E1 E2 : BoolSet U} :
  forall (l1 l2 : trace_list (E1 :|: E2)),
  raw_tr_list_filter E1 l1 = raw_tr_list_filter E1 l2 ->
  raw_tr_list_filter E2 l1 = raw_tr_list_filter E2 l2 ->
  length (raw_of_tracelist l1) = length (raw_of_tracelist l2).
Proof.
  intros. destruct l1 as [l1 g1], l2 as [l2 g2]; simpl in *.
  rewrite (length_filters l1 g1).
  rewrite (length_filters l2 g2).
  rewrite (double_in_filter l1 g1).
  rewrite (double_in_filter l2 g2).
  rewrite H. rewrite H0. reflexivity.
Qed.

(* equal length and one suffix of the other implies equal lists *)
Lemma suffix_eq_length_eq {A : Type} : forall (l1 l2 : list A),
  length l1 = length l2 -> suffix l1 l2 -> l1 = l2.
Proof.
  intros l1 l2 Hlen Hsuffix.
  apply suffix_app in Hsuffix.
  destruct Hsuffix as [ws Hs].
  destruct ws.
  - now apply symmetry in Hs.
  - assert (forall (xs ys : list A), xs = ys -> length xs = length ys).
    { induction xs.
      - intros. now subst ys.
      - destruct ys.
        * now intro.
        * intro. now inversion H. }
    apply H in Hs. rewrite Hs in Hlen. rewrite app_length in Hlen.
    simpl in Hlen. lia.
Qed.

Lemma eq_proj_union {E1 E2 : BoolSet U} :
  forall (tr tr' : trace (E1 :|: E2)),
  proj_trace E1 tr = proj_trace E1 tr' ->
  proj_trace E2 tr = proj_trace E2 tr' ->
  prefix tr' tr ->
  tr = tr'.
Proof.
  intros.
  apply trace_eq; apply trace_list_eq.
  apply trace_eq in H, H0; apply trace_list_eq in H, H0.
  unfold proj_trace, proj_list, prefix in *.
  destruct tr as [w incr], tr' as [w' incr'].
  simpl in *. symmetry.
  apply suffix_eq_length_eq. apply symmetry in H, H0.
  apply (filters_eq_length _ _ H H0).
  exact H1.
Qed.

Lemma prefix_free_compose {E1 E2 : BoolSet U} :
  forall (B1 : behaviour E1) (B2 : behaviour E2),
  prefix_free B1 -> prefix_free B2 -> prefix_free (B1 || B2).
Proof.
  unfold compose, prefix_free. intros.
  specialize (H (proj_trace E1 tr)).
  specialize (H0 (proj_trace E2 tr)).
  destruct H1.
  assert (prefix (proj_trace E1 tr') (proj_trace E1 tr))
  by (apply prefix_proj; assumption).
  assert (prefix (proj_trace E2 tr') (proj_trace E2 tr))
  by (apply prefix_proj; assumption).
  destruct H3.
  specialize (H H1 (proj_trace E1 tr') H5 H3).
  specialize (H0 H4 (proj_trace E2 tr') H6 H7).
  now apply eq_proj_union.
Qed.

End Universal.
