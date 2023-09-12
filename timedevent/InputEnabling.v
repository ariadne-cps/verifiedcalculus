(******************************************************************************
 *  timedevent/InputEnabling.v
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


From Coq Require Import Eqdep.
From Coq Require Import Logic.
From Coq Require Import Program.
From Coq Require Import Reals.
From Coq Require Import Bool.
From Coq Require Import Nat.
From Coq Require Import Lists.List. Import ListNotations.

From TimedEvent Require Import BoolSet.
From TimedEvent Require Import Definitions.
From TimedEvent Require Import Composition.
From TimedEvent Require Import IO.
From TimedEvent Require Import IOComposition.

Section Universal.
Context {U : Set}.

Section InputEnabling.

Definition input_enabling {I O : BoolSet U} {stut : U}
  (bio : IO_behaviour I O stut) :=
  forall I_tr, exists O_tr, (mapping bio) I_tr O_tr.

End InputEnabling.

Section HelpingLemmas.

Context {I O : BoolSet U}.
Context {stut : U}.

Hypothesis Disjoint_IO : Disjoint I O.
Hypothesis IO_no_stut' : In stut (I :|: O) = false.

Lemma from_bio_accept (bio : IO_behaviour I O stut) tr:
  (from_IO_behaviour bio) tr -> (mapping bio) (fst (to_IO_trace stut tr))
    (exist _ (snd (to_IO_trace stut tr)) (to_IO_trace_stutters (IO_no_stut bio) tr)).
Proof.
  intros. unfold from_IO_behaviour in H. exact H.
Qed.


Lemma to_bio_accept (b : behaviour (I :|: O)) I_tr O_tr :
  (mapping (to_IO_behaviour stut b Disjoint_IO IO_no_stut')) I_tr O_tr ->
  b (from_IO_trace Disjoint_IO IO_no_stut' I_tr (` O_tr) (proj2_sig O_tr)).
Proof.
  intros. unfold to_IO_behaviour in *. destruct O_tr. apply H.
Qed.

Lemma from_bio_accept' (bio : IO_behaviour I O stut) I_tr O_tr :
  (mapping bio) I_tr O_tr -> (from_IO_behaviour bio) (from_IO_trace Disjoint_IO IO_no_stut' I_tr (`O_tr) (proj2_sig O_tr)).
Proof.
  intros. unfold from_IO_behaviour.
  apply bio_accept_if_eqv with (I_tr:=I_tr) (O_tr:=O_tr).
  now rewrite to_inv_from_trace.
  apply trace_eq, trace_list_eq. simpl. rewrite to_inv_from_raw with (O:=O);
  try easy. apply (proj2_sig O_tr). apply (goodprop _ (`I_tr)).
  apply (goodprop _ (``O_tr)). apply H.
Qed.

Lemma exists_Otr_from I_tr (b : behaviour (I :|: O)) :
  (exists tr, b tr /\ fst (to_IO_trace stut tr) = I_tr) <->
  exists (O_tr : {O_tr : trace (O' O stut)
         | trace_stutters stut I_tr O_tr}),
         (mapping (to_IO_behaviour stut b Disjoint_IO IO_no_stut')) I_tr O_tr.
Proof.
  split.
  - intros. destruct H as [tr H]. destruct H. subst I_tr.
    pose (x:= (exist (trace_stutters stut (fst (to_IO_trace stut tr)))
      (snd (to_IO_trace stut tr)) (to_IO_trace_stutters IO_no_stut' tr))).
    exists x. unfold x. apply from_bio_accept.
    apply from_inv_to_behaviour. assumption.
  - intros. destruct H as [O_tr H]. exists (from_IO_trace Disjoint_IO IO_no_stut' I_tr (`O_tr) (proj2_sig O_tr)).
    split. apply to_bio_accept. apply H. rewrite to_inv_from_trace. easy.
Qed.

End HelpingLemmas.

Section Merge.

Fixpoint merge (l1 l2 : raw_tr_list U) (v : nat) : raw_tr_list U :=
  match v with
  | 0 => []
  | S n =>
    match l1, l2 with
    | [], l => l
    | l, [] => l
    | x :: xs, y :: ys =>
      if Rlt_dec (fst x) (fst y)
        then x :: (merge xs (y :: ys) n)
        else y :: (merge (x :: xs) ys n)
    end
  end.

Lemma empty_merge_l (l1 : raw_tr_list U) :
  merge l1 [] (length l1) = l1.
Proof. destruct l1; easy. Qed.

Lemma empty_merge_r (l2 : raw_tr_list U) :
  merge [] l2 (length l2) = l2.
Proof. destruct l2; easy. Qed.

Definition merge' l1 l2 := merge l1 l2 (length (l1 ++ l2)).

Lemma merge_ge_head_zero1 {E} : forall l1 l2 (a:R*E),
  increasing_time l1 -> increasing_time l2 ->
    ge_head_zero a l1 -> ge_head_zero a l2 ->
      ge_head_zero a (merge' l1 l2).
Proof.
  intros. destruct a as [t e]; generalize dependent l1. induction l2; intros.
  - unfold merge'; destruct l1; simpl; apply H1.
  - unfold merge'. simpl. destruct l1.
    * simpl. apply H2.
    * simpl. destruct (Rlt_dec (fst p) (fst a)).
      + simpl. simpl in H2. destruct H2.
        ++ left. apply Rlt_gt in r. apply Rgt_trans with (r2:=(fst a)).
           all: assumption.
        ++ rewrite H2. left. apply Rlt_gt. apply r.
      + simpl. apply H2.
Qed.

Lemma merge_increasing : forall l1 l2,
  increasing_time l1 -> increasing_time l2 ->
    increasing_time (merge' l1 l2 ).
Proof.
  intros. generalize dependent l2. induction l1; intros; simpl; unfold merge'.
  - destruct l2.
    * simpl. apply incr_nil.
    * simpl in *. exact H0.
  - destruct l2.
    * exact H.
    * simpl. destruct (Rlt_dec (fst a) (fst p)).
      + apply incr_app. all: admit.
      + apply incr_app. admit.
Admitted.

Lemma merge_all_in l1 l2 : forall x,
  List.In x (merge' l1 l2) -> List.In x l1 \/ List.In x l2.
Proof.
  intros. generalize dependent l2. induction l1; intros; unfold merge' in *; simpl.
  - right. destruct l2. simpl in *. apply H. simpl in H; apply H.
  - destruct l2.
    * simpl in H. left; exact H.
    * simpl in H. destruct (Rlt_dec (fst a) (fst p)).
      + simpl in H. destruct H. auto. apply IHl1 in H.
        destruct H. all: auto.
      + simpl in H. destruct H. right; left. easy.
Admitted.

Lemma merge_good {E1 E2} : forall (l1 : trace_list E1) (l2 : trace_list E2),
  good_tr_list (E1 :|: E2) (merge l1 l2 (length (raw_of_tracelist l1 ++ raw_of_tracelist l2))) = true.
Proof.
  intros; destruct l1 as [l1 g1], l2 as [l2 g2]; simpl in *.
  induction l1.
  - simpl. destruct l2.
    * easy.
    * simpl. and_destr g2.
      apply andb_true_iff. split. admit.
      apply (subset_good l2 _ _ H0 (union_subset_r _ _)).
  - simpl. destruct l2.
    * apply (subset_good _ _ _ g1 (union_subset_l _ _)).
    * destruct (Rlt_dec (fst a) (fst p)).
      + simpl. apply andb_true_iff. admit.
      +
Admitted.

Definition merge_trlist {E1 E2} (l1 : trace_list E1) (l2 : trace_list E2) : trace_list (E1 :|: E2) :=
  mkTrlist (E1 :|: E2)
    (merge l1 l2 (length (raw_of_tracelist l1 ++ raw_of_tracelist l2)))
    (merge_good l1 l2).

Definition merge_traces {E1 E2} (tr1 : trace E1) (tr2 : trace E2) : trace (E1 :|: E2) :=
  exist _ (merge_trlist (`tr1) (`tr2))
    (merge_increasing (`tr1) (`tr2) (proj2_sig tr1) (proj2_sig tr2)).

Definition merge_traces' {E1 E2 F} (tr1 : trace E1) (tr2 : trace E2)
  (p : good_tr_list F (merge (`tr1) (`tr2) (length (raw_of_tracelist (`tr1) ++ raw_of_tracelist (`tr2)))) = true)
  : trace F :=
  exist _ (mkTrlist F
    (merge (`tr1) (`tr2) (length (raw_of_tracelist (`tr1) ++ raw_of_tracelist (`tr2)))) p)
    (merge_increasing (`tr1) (`tr2) (proj2_sig tr1) (proj2_sig tr2)).

Lemma fst_to_is_proj {I O : BoolSet U} {stut : U} (tr : trace (I :|: O)) :
  fst (to_IO_trace stut tr) = (proj_trace I tr).
Proof.
  intros. apply trace_eq. apply trace_list_eq.
  destruct tr as [[w g] incr]. simpl in *. induction w.
  - easy.
  - simpl. destruct a as [t e]. simpl. destruct (In e I) eqn:Hin.
    * simpl. f_equal. apply IHw. and_destr g. assumption.
    inversion incr. assumption.
    * simpl. apply IHw. and_destr g. assumption.
    inversion incr. assumption.
Qed.

Lemma disjoint_empty_proj {E1 E2} (tl : raw_tr_list U) :
  Disjoint E1 E2 -> good_tr_list E1 tl = true -> raw_tr_list_filter E2 tl = [].
Proof.
  intros. induction tl.
  - easy.
  - simpl in *. and_destr H0. apply (disjoint_not_in _ _ _ H0) in H.
    rewrite H. apply (IHtl H1).
Qed.

Lemma from_IO_disjoint {I O : BoolSet U} {stut : U} I_tr O_tr :
  forall (p : Disjoint I O) (p1 : In stut (I :|: O) = false)
    (p2 : trace_stutters stut I_tr O_tr),
    Disjoint I O ->
    proj_trace I (from_IO_trace p p1 I_tr O_tr p2) = proj_trace I I_tr.
Proof.
  intros; apply trace_eq, trace_list_eq. simpl.
  destruct I_tr as [[w1 g1] incr1], O_tr as [[w2 g2] incr2].
  unfold trace_stutters, trlist_stutters in p2.
  simpl in *. assert (Disjoint I (Add stut O)).
  apply (disjoint_I_O' _ _ _ p p1).
  generalize dependent w1; induction w2; intros.
  - simpl. induction w1.
    * easy.
    * unfold rawlist_stutters in p2; simpl in p2. inversion p2.
  - destruct w1.
    * simpl in *. destruct a.
      destruct (U_eq_dec u stut). easy.
      simpl. and_destr g2. apply disjoint_not_in with (B:=I) in H1.
      rewrite H1. apply IHw2; try easy. now inversion incr2.
      unfold rawlist_stutters in p2. simpl in p2.
      now rewrite x_non_Stut in p2.
      now rewrite disjoint_comm.
    * simpl in *. destruct p0. destruct a. and_destr g1.
      simpl. rewrite H1. destruct (U_eq_dec u0 stut).
      + simpl. rewrite H1. f_equal. inversion incr1.
        inversion incr2. and_destr g2.
        apply IHw2; try easy. unfold rawlist_stutters in p2.
        simpl in p2. rewrite e in p2. rewrite Stut_stut in p2.
        inversion p2. easy.
      + assert ((raw_tr_list_filter I w1 -::- (r, u)) = raw_tr_list_filter I (w1 -::- (r, u))).
        simpl. now rewrite H1.
        simpl. and_destr g2.
        apply disjoint_not_in with (B:=I) in H4. rewrite H4.
        rewrite H3. apply IHw2; try easy. now inversion incr2.
        simpl. apply andb_true_iff. auto.
        unfold rawlist_stutters in p2. simpl in p2.
        apply x_non_Stut in n. now rewrite n in p2.
        now rewrite disjoint_comm.
Qed.

End Merge.

Section InputEnablingComp.

Context {I1 O1 I2 O2 : BoolSet U}.
Context {stut : U}.

Hypothesis disjoint_O12 : Disjoint O1 O2.

Variable bio1 : IO_behaviour I1 O1 stut.
Variable bio2 : IO_behaviour I2 O2 stut.

(* What about if (Disjoint I1 O2) and (Disjoint I2 O1)? *)
Lemma IO_compose_enabling : input_enabling bio1 -> input_enabling bio2
      -> input_enabling (compose_IO2 bio1 bio2).
Proof.
  unfold input_enabling. intros H1 H2 I_tr.
  unfold compose_IO2, compose.
  generalize (@u_eqv_comp2 _ I1 I2 O1 O2).
  assert ((I1 :|: O1 :|: (I2 :|: O2)) =
      (Setminus (I1 :|: I2) (O1 :|: O2) :|: (O1 :|: O2))).
  { rewrite u_eqv. easy. }
  rewrite H. intros. rewrite (UIP_refl _ _ e).
  clear e; clear H.
  specialize (H1 (proj_trace I1 I_tr)).
  specialize (H2 (proj_trace I2 (proj_trace (Setminus I2 I1) I_tr))).
  destruct H1 as [O_tr1 H1], H2 as [O_tr2 H2].
  pose (O_tr:= merge_traces (`O_tr1) (`O_tr2)).
  assert (p : good_tr_list (Add stut (O1 :|: O2)) (merge (``O_tr1) (``O_tr2) (length (raw_of_tracelist (``O_tr1) ++ raw_of_tracelist (``O_tr2)))) = true).
  { admit. (* provable *) }
  pose (O_tr' := merge_traces' (`O_tr1) (`O_tr2) p).
  assert (trace_stutters stut I_tr O_tr') by admit. (* difficult *)
  pose (O_tr'' := (exist _ O_tr' H)). exists O_tr''.
Abort.

End InputEnablingComp.
End Universal.
