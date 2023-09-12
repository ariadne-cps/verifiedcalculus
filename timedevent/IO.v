(******************************************************************************
 *  timedevent/IO.v
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
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.
From Coq Require Import Logic.Eqdep_dec.

From Coq Require Import Reals.
From Coq Require Import Program.

From TimedEvent Require Import BoolSet.
From TimedEvent Require Import Definitions.
From TimedEvent Require Import Composition.

Section IO.

Context {U : Set}.

Section Stutter.

Context {I O : BoolSet U}.
Variable stut : U.

(* compatibility property *)

Definition proj_list_stut (O_l : trace_list (Add stut O)) : trace_list (Single stut)
  := proj_list (Single stut) O_l.

Definition rawlist_stutters (I_l O_l : raw_tr_list U)
  := (fst_list I_l) = (fst_list (raw_tr_list_filter (Single stut) O_l)).

Definition trlist_stutters (I_l : trace_list I) (O_l : trace_list (Add stut O))
  := rawlist_stutters (raw_of_tracelist I_l) (raw_of_tracelist O_l).

Definition trace_stutters (I_tr : trace I) (O_tr : trace (Add stut O))
  := trlist_stutters (proj1_sig I_tr) (proj1_sig O_tr).

End Stutter.

Record IO_behaviour ( Input Output : BoolSet U) (stut_event : U) := mkIOBehaviour {
  disjoint_IO : Disjoint Input Output;
  IO_no_stut : In stut_event (Input :|: Output) = false;
  mapping : forall (I_tr : trace Input),
    { O_tr : trace (Add stut_event Output) | trace_stutters stut_event I_tr O_tr } -> Prop
}.
Arguments disjoint_IO {Input Output stut_event}.
Arguments IO_no_stut {Input Output stut_event}.
Arguments mapping {Input Output stut_event}.

Section Properties.

Variable I O : BoolSet U.
Variable stut : U.
Definition Stut := Single stut.
Definition O' := Add stut O.

(* Input and output sets should be disjoint *)
Hypothesis disjoint_IO : Disjoint I O.

(* The stutter action is not in I or O *)
Hypothesis IO_no_stut : In stut (I :|: O) = false.

(* equivalence relation *)
Definition eq_IO_behaviour : IO_behaviour I O stut -> IO_behaviour I O stut -> Prop :=
  fun bio1 bio2 =>
    forall (I_tr : trace I) O_tr,
      (mapping bio1) I_tr O_tr <-> (mapping bio2) I_tr O_tr.

Notation "bio1 |≡ bio2" := (eq_IO_behaviour bio1 bio2) (at level 89, no associativity).

Lemma eq_IO_behaviour_refl : reflexive _ eq_IO_behaviour.
Proof.
  intros; unfold reflexive, eq_IO_behaviour; intros. easy.
Qed.

Lemma eq_IO_behaviour_sym : symmetric _ eq_IO_behaviour.
Proof.
  intros; unfold symmetric, eq_IO_behaviour; intros.
  specialize (H I_tr O_tr); symmetry. assumption.
Qed.

Lemma eq_IO_behaviour_trans : transitive _ eq_IO_behaviour.
Proof.
  intros; unfold transitive, eq_IO_behaviour; intros.
  specialize (H I_tr O_tr). specialize (H0 I_tr O_tr).
  rewrite H. apply H0.
Qed.

Add Parametric Relation : (IO_behaviour I O stut) eq_IO_behaviour
  reflexivity proved by (eq_IO_behaviour_refl)
  symmetry proved by (eq_IO_behaviour_sym)
  transitivity proved by (eq_IO_behaviour_trans)
  as eq_IO_behaviour_rel.

(* Helping lemmas about sets *)

Lemma I_sub_IO : Subset I (I :|: O).
Proof.
  unfold Subset. intros. unfold Union, In in *. rewrite H. auto.
Qed.

Lemma O_sub_IO : Subset O (I :|: O).
Proof.
  unfold Subset. intros. unfold Union, In in *. rewrite H. apply orb_comm.
Qed.

Lemma I_no_stut : In stut I = false.
Proof.
  assert (H: In stut (I :|: O) = false) by apply IO_no_stut.
  unfold In, Union in *. destruct (In stut I) eqn:Hin.
  * simpl in *; easy.
  * apply Hin.
Qed.

Lemma I_no_stut' : I stut = false.
Proof.
  assert (H: In stut (I :|: O) = false) by apply IO_no_stut.
  unfold Union, In in *. destruct (I stut) eqn:Hin.
  all: auto.
Qed.

Lemma O_no_stut : In stut O = false.
Proof.
  assert (H: In stut (I :|: O) = false) by apply IO_no_stut.
  unfold Union, In in *. destruct (O stut) eqn:Hin; try easy.
  * rewrite orb_comm in H. simpl in *; easy.
Qed.

Lemma O'_stut : In stut (Add stut O) = true.
Proof.
  unfold O', Add, In in *; destruct (U_eq_dec stut stut); easy.
Qed.

Lemma Stut_stut : In stut (Single stut) = true.
Proof.
  unfold Stut, Single, In in *; destruct (U_eq_dec stut stut); easy.
Qed.

Lemma disjoint_I_O' : Disjoint I (Add stut O).
Proof.
  unfold Disjoint, Intersection, O', Add, In in *.
  intros x. destruct (U_eq_dec stut x).
  - rewrite <- e. rewrite andb_comm. simpl. apply I_no_stut'.
  - apply (disjoint_IO x).
Qed.

Lemma x_non_Stut x : x <> stut -> In x (Single stut) = false.
Proof.
   intros. unfold Stut, Single, In.
  destruct (U_eq_dec stut x); auto. rewrite e in H. easy.
Qed.

Lemma x_non_Stut' x : In x (Single stut) = false -> x <> stut.
Proof.
  intros. unfold Stut, Single, In in *.
   destruct (U_eq_dec stut x). easy. unfold not.
   unfold not in n. intro. apply symmetry in H0.
   easy.
Qed.


Lemma x_non_Stut_in_O x : x <> stut -> In x (Add stut O) = true -> In x O = true.
Proof.
  intros. unfold O', Add, Stut, Single, In in *.
  destruct (U_eq_dec stut x); auto.
Qed.

(* Make the sigma type slightly easier to work with *)
Lemma O_tr_eqv (I_tr : trace I)
  (O_tr O_tr' : { O_tr : trace O' | trace_stutters stut I_tr O_tr }) :
    proj1_sig O_tr = proj1_sig O_tr' -> O_tr = O_tr'.
Proof.
  intros. destruct O_tr as [O_tr p], O_tr' as [O_tr' p']. simpl in *.
  subst O_tr. assert (H1 : p = p').
  { apply proof_irrelevance. } subst p. easy.
Qed.

Lemma O_tr_eqv' (I_tr I_tr' : trace I) (p : I_tr = I_tr') :
  { O_tr : trace O' | trace_stutters stut I_tr' O_tr } =
  { O_tr : trace O' | trace_stutters stut I_tr O_tr }.
Proof.
  rewrite p. easy.
Qed.

Lemma O_tr_I_eqv' I_tr I_tr'
  (O_tr : { O_tr : trace O' | trace_stutters stut I_tr O_tr })
  (O_tr' : { O_tr : trace O' | trace_stutters stut I_tr' O_tr }) :
    forall (p : I_tr = I_tr'),
    proj1_sig O_tr = proj1_sig O_tr' ->
    O_tr = match (O_tr_eqv' _ _ p) in (_ = l) return l with
           | eq_refl => O_tr'
           end.
Proof.
  intros. subst I_tr'. rewrite O_tr_eqv with (O_tr':=O_tr').
  - apply (O_tr_eqv _ _ _ H).
  - rewrite (UIP_refl _ _ (O_tr_eqv' I_tr I_tr eq_refl)). reflexivity.
Qed.

Lemma bio_accept_if_eqv : forall (bio : IO_behaviour I O stut) (I_tr I_tr' : trace I)
  (O_tr : { O_tr : trace O' | trace_stutters stut I_tr O_tr })
  (O_tr' : { O_tr' : trace O' | trace_stutters stut I_tr' O_tr' }),
  I_tr = I_tr' -> (`O_tr) = (`O_tr') -> (mapping bio) I_tr O_tr ->
  (mapping bio) I_tr' O_tr'.
Proof.
  intros. subst I_tr'.
  assert (O_tr = O_tr') by (now apply O_tr_eqv).
  now subst O_tr'.
Qed.

Fixpoint raw_from_IO_list (I_l : raw_tr_list U) (O_l : raw_tr_list U)
  : raw_tr_list U :=
  match O_l with
  | [] => []
  | ((t_o, oe) :: tlO) => match (U_eq_dec oe stut) with
    | right f => (t_o, oe) :: raw_from_IO_list I_l tlO
    | left t => match I_l with
      | [] => [] (* Can not happen with stuttering property! *)
      | ((t_i, ie) :: tlI) => (t_i, ie) :: raw_from_IO_list tlI tlO
      end
    end
  end.

(* We show that the case O_l = ((t_o, oe) :: tlO), I_l = []
   where oe = stut cannot happen with the stuttering property *)
Lemma no_empty_inputs_on_outputs :
  forall (I_l O_l : raw_tr_list U) t tlO,
  I_l = [] -> O_l = (t, stut) :: tlO ->
    rawlist_stutters stut I_l O_l -> False.
Proof.
  intros. rewrite H, H0 in H1.
  unfold rawlist_stutters in H1.
  simpl in H1.
  rewrite Stut_stut in H1.
  inversion H1.
Qed.

(* Helping lemmas to show good property is retained *)
Lemma goodFromIOHelp1 (I_l : raw_tr_list U) (O_l : raw_tr_list U) x :
  List.In x (raw_from_IO_list I_l O_l) ->
  List.In x I_l \/ List.In x O_l.
Proof.
  revert I_l.
  induction O_l as [| [t_o oe] tlO IH]; intros I_l H_in; simpl in *.
  - contradiction.
  - simpl in H_in; destruct (U_eq_dec oe stut) as [Heq | Hneq];
    destruct I_l as [| [t_i ie] tlI]; try contradiction;
    simpl in H_in; destruct H_in as [Hx | Hx].
    * left; left; assumption.
    * pose Hx as Hx'. apply IH in Hx'.
       destruct Hx'.
       ++ left; right; apply H.
       ++ right; right; apply H.
    * right; left; assumption.
    * apply IH in Hx. destruct Hx. easy. right; right; apply H.
    * right; left; assumption.
    * apply IH in Hx. destruct Hx. left; apply H. right; right; apply H.
Qed.

Lemma goodFromIOHelp2 (I_l : raw_tr_list U) (O_l : raw_tr_list U) x :
  good_tr_list I I_l = true -> good_tr_list O' O_l = true ->
  List.In x (raw_from_IO_list I_l O_l) -> ~ (In (snd x) Stut = true).
Proof.
  revert I_l. unfold Stut in *.
  induction O_l as [| [t_o oe] tlO IH];
  intros I_l goodI goodO H_in; simpl in *.
  - contradiction.
  - simpl in H_in. destruct (U_eq_dec oe stut) as [Heq | Hneq];
    destruct I_l as [| [t_i ie] I_l]; try contradiction.
    * simpl in H_in. unfold good_tr_list, is_true in *.
      pose goodI as goodI'.
      and_destr goodI'. and_destr goodO.
      destruct H_in as [Hx | Hx].
      -- simpl in H. apply (disjoint_neq I O' ie oe) in H1.
         rewrite <- Hx; simpl. unfold not; intros. rewrite Heq in H1.
         apply (x_non_Stut ie) in H1. rewrite H1 in H3. easy.
         apply H. apply disjoint_I_O'.
      -- apply (IH I_l H0 H2) in Hx; assumption.
    * simpl in H_in; destruct H_in as [Hx | Hx].
      -- rewrite <- Hx; simpl. rewrite (x_non_Stut oe Hneq).
         easy.
      -- and_destr goodO. apply (IH [] goodI H0 Hx).
    * simpl in H_in; destruct H_in as [Hx | Hx].
      -- rewrite <- Hx; simpl. rewrite (x_non_Stut oe Hneq).
         easy.
      -- and_destr goodO.
         apply (IH (I_l -::- (t_i, ie)) goodI H0 Hx).
Qed.

Lemma goodFromIO (I_l : trace_list I) (O_l : trace_list O') :
  good_tr_list (I :|: O) (raw_from_IO_list I_l O_l) = true.
Proof.
  apply all_in_good. intros. pose H as H'.
  apply goodFromIOHelp1 in H'; apply goodFromIOHelp2 in H.
  destruct I_l as [rawI goodI], O_l as [rawO goodO]; simpl in *.
  destruct H'.
  - rewrite <- (all_in_good rawI I) in goodI.
    apply goodI in H0. apply (in_subset I (I :|: O) (snd x) H0 I_sub_IO).
  - rewrite <- (all_in_good rawO O') in goodO.
    apply goodO in H0. unfold In, Stut, Single in H.
    destruct (U_eq_dec stut (snd x)).
    * easy.
    * apply x_non_Stut_in_O in H0.
      apply (in_subset _ (I :|: O) (snd x) H0 O_sub_IO).
      auto.
  - apply (goodprop _ I_l).
  - apply (goodprop _ O_l).
Qed.

Definition from_IO_list (I_l : trace_list I) (O_l : trace_list O')
  (p : trlist_stutters stut I_l O_l) : trace_list (I :|: O)
  := mkTrlist _ _ (goodFromIO I_l O_l).


Lemma ge_head_preserved_from_IO_O : forall E1 E2 I_l O_l t
  (e1 : E1) (e2 : E2) (stut_prop : rawlist_stutters stut I_l O_l),
  increasing_time I_l -> increasing_time O_l ->
  ge_head_zero (t, e1) O_l -> ge_head_zero (t, e2) (raw_from_IO_list I_l O_l).
Proof.
  intros. induction O_l.
  - easy.
  - destruct a as [t_o oe] in *; simpl.
    * simpl in H1. destruct (U_eq_dec oe stut).
      + destruct I_l.
        ++ simpl. apply incr_ge_zero in H0. apply (Rge_gt_trans t0 t_o 0 H1 H0).
        ++ destruct p. simpl. unfold rawlist_stutters in stut_prop.
           simpl in stut_prop. rewrite e in stut_prop.
           rewrite Stut_stut in stut_prop. simpl in stut_prop.
           inversion stut_prop. apply H1.
      + apply H1.
Qed.

Lemma raw_from_IO_list_preserves_increasing : forall I_l O_l,
  increasing_time I_l -> increasing_time O_l -> rawlist_stutters stut I_l O_l ->
  increasing_time (raw_from_IO_list I_l O_l).
Proof.
  intros. unfold Stut in *. generalize dependent I_l. induction O_l.
  - constructor.
  - destruct a as [t oe].
    * intros. unfold raw_from_IO_list. destruct (U_eq_dec oe stut).
      + destruct I_l.
        ++ easy.
        ++ fold raw_from_IO_list. destruct p. apply incr_app. pose H1 as H1'.
           unfold rawlist_stutters in H1'. simpl in H1'. rewrite e in H1'.
           rewrite Stut_stut in H1'. inversion H1'. inversion H0.
           inversion H.
           apply (ge_head_preserved_from_IO_O _ _ _ _ _ _ _ H4 H11 H7 H6).
           inversion H0. inversion H.
           unfold rawlist_stutters in H1. simpl in H1. rewrite e in H1.
           rewrite Stut_stut in H1. inversion H1.
           apply (IHO_l H5 I_l H9 H12).
      + fold raw_from_IO_list. apply incr_app.
        ++ pose H1 as H1'. unfold rawlist_stutters in H1'.
           simpl in H1'. rewrite (x_non_Stut oe n) in H1'.
           inversion H0.
           apply (ge_head_preserved_from_IO_O U U _ _ t oe oe H1' H H5 H4).
        ++ pose H1 as H1'. unfold rawlist_stutters in H1'.
           simpl in H1'. rewrite (x_non_Stut oe n) in H1'.
           inversion H0. apply (IHO_l H5 I_l H H1').
Qed.

Definition from_IO_trace (I_tr : trace I) (O_tr : trace O')
  (p : trace_stutters stut I_tr O_tr) : trace (I :|: O) :=
      exist _ (from_IO_list (proj1_sig I_tr) (proj1_sig O_tr) p)
        (raw_from_IO_list_preserves_increasing (proj1_sig I_tr) (proj1_sig O_tr)
          (proj2_sig I_tr) (proj2_sig O_tr) p).


Fixpoint raw_to_IO_list (IO_l : raw_tr_list U)
    : (raw_tr_list U) * (raw_tr_list U) :=
  match IO_l with
  | [] => ([], [])
  | ((t, e) :: tl) => if In e I then
                        ((t, e) :: fst (raw_to_IO_list tl),
                        (t, stut) :: snd (raw_to_IO_list tl))
                      else (* must be in O, as I and O are disjoint *)
                        (fst (raw_to_IO_list tl), (t, e) :: snd (raw_to_IO_list tl))
  end.


Lemma goodToIO1 (IO_l : trace_list (I :|: O))
  : is_true (good_tr_list I (fst (raw_to_IO_list IO_l))).
Proof.
  unfold is_true. destruct IO_l as [raw goodprop]. induction raw.
  - auto.
  - destruct a as [t e]. simpl. destruct (In e I) eqn:Hin.
    all: (simpl; simpl in IHraw; inversion goodprop; and_destr H0;
    rewrite H0; apply IHraw in H0; rewrite H; rewrite H0;
      try rewrite Hin; easy).
Qed.

Lemma goodToIO2 (IO_l : trace_list (I :|: O))
  : is_true (good_tr_list O' (snd (raw_to_IO_list IO_l))).
Proof.
  unfold is_true. destruct IO_l as [raw goodprop]. induction raw.
  - auto.
  - destruct a as [t e]. simpl. destruct (In e I) eqn:Hin;
    simpl in *; inversion goodprop; and_destr H0;
    rewrite H0; apply IHraw in H0; rewrite H; rewrite H0;
    unfold O'; unfold Add; unfold In; destruct U_eq_dec; try auto.
    * unfold In,Union in H; rewrite Hin in H; simpl in *; unfold In in H;
      rewrite H; easy.
Qed.

Definition to_IO_list (IO_l : trace_list (I :|: O))
  : trace_list I * trace_list O' :=
    pair (mkTrlist _ _ (goodToIO1 IO_l)) (mkTrlist _ _ (goodToIO2 IO_l)).

(* raw_to_IO_lists gives stuttering output lists *)
Lemma raw_to_IO_list_stutters : forall (IO_l : trace_list (I :|: O)),
  rawlist_stutters stut (fst (raw_to_IO_list IO_l)) (snd (raw_to_IO_list IO_l)).
Proof.
  intros. destruct IO_l as [raw good]. induction raw.
  - simpl. easy.
  - inversion good. and_destr H0; destruct a as [t e].
    * simpl. destruct (In e I) eqn:Hin.
      + simpl. unfold rawlist_stutters. simpl. destruct (In stut Stut) eqn:Hst.
        ++ simpl in *. and_destr good;
           apply IHraw in H2. unfold rawlist_stutters in H2. rewrite H2.
           rewrite Stut_stut. reflexivity.
        ++ unfold Stut, In, Single in Hst; destruct U_eq_dec in Hst. easy.
           easy.
      + simpl. unfold rawlist_stutters. simpl. destruct (In e Stut) eqn:Hst.
        ++ simpl. unfold Stut, In, Single in Hst. destruct U_eq_dec in Hst.
            +++ rewrite <- e0 in H. simpl in H. rewrite IO_no_stut in H. easy.
            +++ easy.
        ++ simpl in IHraw. apply IHraw in H0. rewrite x_non_Stut. apply H0.
           now apply x_non_Stut' in Hst.
Qed.

Lemma ge_head_zero_preserved_fst : forall A1 A2 IO_l t (e1 : A1) (e2 : A2),
  increasing_time IO_l -> ge_head_zero (t, e1) IO_l ->
  ge_head_zero (t, e2) (fst (raw_to_IO_list IO_l)).
Proof.
  intros. induction IO_l.
  - easy.
  - destruct a as [ti e] in *; simpl.
    * simpl in *. destruct (In e I); simpl.
      + apply H0.
      + inversion H. apply (ge_ge_head_zero _ _ t0 ti e e1 IO_l) in H3.
        apply (IHIO_l H4 H3). all: assumption.
Qed.

Lemma ge_head_zero_preserved_snd : forall A1 A2 IO_l t (e1 : A1) (e2 : A2),
  increasing_time IO_l -> ge_head_zero (t, e1) IO_l ->
  ge_head_zero (t, e2) (snd (raw_to_IO_list IO_l)).
Proof.
  intros. induction IO_l.
  - easy.
  - destruct a as [ti e] in *; simpl.
    * simpl in *. destruct (In e I); simpl.
      + apply H0.
      + simpl. inversion H. apply (ge_ge_head_zero _ _ t0 ti e e1 IO_l) in H3.
        apply IHIO_l in H3. all: assumption.
Qed.

Lemma raw_to_IO_list_preserves_increasing : forall IO_l,
  increasing_time IO_l ->
  increasing_time (fst (raw_to_IO_list IO_l)) /\
  increasing_time (snd (raw_to_IO_list IO_l)).
Proof.
  intros. split; induction IO_l; try easy.
    + destruct a as [t e]; simpl.
      destruct (In e I).
      - simpl. inversion H. apply incr_app.
        apply (ge_head_zero_preserved_fst U U _ t e e H3 H2).
        apply (IHIO_l H3).
      - simpl. inversion H. apply (IHIO_l H3).
    + destruct a as [t e]; simpl.
      destruct (In e I); simpl; inversion H; apply incr_app;
        try apply (IHIO_l H3);
        apply (ge_head_zero_preserved_snd U U _ t e e H3 H2).
Qed.

Definition to_IO_trace (IO_tr : trace (I :|: O)) : trace I * trace O' :=
  match IO_tr with
  | exist _ IO_l IO_incr =>
    let tr_lists := to_IO_list IO_l in
    let p := raw_to_IO_list_preserves_increasing IO_l IO_incr in
      pair (exist _ (fst tr_lists) (proj1 p)) (exist _ (snd tr_lists) (proj2 p))
  end.

Lemma to_IO_trace_stutters : forall IO_tr,
  trace_stutters stut (fst (to_IO_trace IO_tr)) (snd (to_IO_trace IO_tr)).
Proof.
  intros; destruct IO_tr. apply raw_to_IO_list_stutters.
Qed.

(* Show that to and from functions are mutually inverse
   at all levels *)
Lemma to_inv_from_raw (I_l : raw_tr_list U) (O_l : raw_tr_list U)
  (p : rawlist_stutters stut I_l O_l) :
  good_tr_list I I_l = true -> good_tr_list (Add stut O) O_l = true ->
  raw_to_IO_list (raw_from_IO_list I_l O_l) = (I_l, O_l).
Proof.
  revert I_l p. induction O_l as [|[t_o oe] O_l IHO_l].
  - simpl. destruct I_l as [|[t_i ie] I_l]; simpl in *.
    * easy.
    * intros p goodI goodO. unfold rawlist_stutters in p. simpl in p. discriminate p.
  - intros I_l p goodI goodO. simpl. destruct (U_eq_dec oe stut) eqn:Heq.
    * destruct I_l as [|[t_i ie] I_l].
      + unfold rawlist_stutters in p. simpl in p.
        rewrite e in p. rewrite Stut_stut in p. discriminate p.
      + simpl in *; and_destr goodI; and_destr goodO; rewrite H.
        rewrite e in p. unfold rawlist_stutters in p. simpl in p.
        rewrite Stut_stut in p. inversion p. apply (IHO_l I_l H5 H0) in H2.
        rewrite H2. simpl. rewrite <- e. reflexivity.
    * simpl in *. and_destr goodO;
      apply (disjoint_not_in O' I _) in H. rewrite H.
      unfold rawlist_stutters in p. simpl in p. rewrite (x_non_Stut _ n) in p.
      apply (IHO_l I_l p goodI) in H0. rewrite H0. easy. rewrite disjoint_comm.
      apply disjoint_I_O'.
Qed.


Lemma from_inv_to_raw (IO_l : raw_tr_list U)
  (p : rawlist_stutters stut (fst (raw_to_IO_list IO_l)) (snd (raw_to_IO_list IO_l)))
  (good : good_tr_list (I :|: O) IO_l = true) :
  raw_from_IO_list (fst (raw_to_IO_list IO_l)) (snd (raw_to_IO_list IO_l)) = IO_l.
Proof.
  revert p. induction IO_l.
  - intros. simpl. reflexivity.
  - intros. destruct a as [t e]. simpl. destruct (In e I) eqn:Hin.
    * simpl in *. destruct (U_eq_dec stut stut); try contradiction.
      f_equal. apply IHIO_l. and_destr good; assumption.
      rewrite Hin in p; simpl in p. unfold rawlist_stutters in p. simpl in p.
      rewrite Stut_stut in p. inversion p. apply H0.
    * simpl in *. and_destr good.
      apply In_UnionL in H. destruct (U_eq_dec e stut).
      + rewrite e0 in H. rewrite O_no_stut in H. discriminate H.
      + f_equal. rewrite Hin in p. unfold rawlist_stutters in p.
        simpl in p. rewrite (x_non_Stut _ n) in p. apply (IHIO_l H0 p).
      + apply Hin.
Qed.


(*
  We have the stuttering property in the lemma definition
  as we would like to generalize on it.
  In reality, the stuttering property is given by to_IO_list_stutters
*)

Lemma to_inv_from_list (I_l : trace_list I) (O_l : trace_list O')
  (p: trlist_stutters stut I_l O_l) :
    to_IO_list (from_IO_list I_l O_l p) = (I_l, O_l).
Proof.
  unfold from_IO_list, to_IO_list. simpl.
  assert (H : raw_to_IO_list (raw_from_IO_list I_l O_l)
            = (raw_of_tracelist I_l, raw_of_tracelist O_l)).
  { apply (to_inv_from_raw I_l O_l).
  apply p. apply (goodprop _ I_l). apply (goodprop _ O_l). }
  apply injective_projections; simpl; apply trace_list_eq; simpl; rewrite H; easy.
Qed.

Lemma from_inv_to_list (IO_l : trace_list (I :|: O)) :
  from_IO_list (fst (to_IO_list IO_l)) (snd (to_IO_list IO_l))
    (raw_to_IO_list_stutters _) = IO_l.
Proof.
  unfold from_IO_list, to_IO_list. simpl. apply trace_list_eq.
  simpl. apply from_inv_to_raw. apply (raw_to_IO_list_stutters IO_l).
  apply (goodprop _ IO_l).
Qed.

Lemma to_inv_from_trace (I_tr : trace I) (O_tr : trace O')
  (p: trace_stutters stut I_tr O_tr) :
    to_IO_trace (from_IO_trace I_tr O_tr p) = (I_tr, O_tr).
Proof.
  unfold from_IO_trace, to_IO_trace. simpl. apply injective_projections; simpl;
  apply trace_eq; apply trace_list_eq; simpl;
  rewrite to_inv_from_raw; try easy;
  try apply (goodprop _ (proj1_sig I_tr));
  try apply (goodprop _ (proj1_sig O_tr)).
Qed.

Lemma from_inv_to_trace (IO_tr : trace (I :|: O)) :
  from_IO_trace (fst (to_IO_trace IO_tr)) (snd (to_IO_trace IO_tr))
    (to_IO_trace_stutters _) = IO_tr.
Proof.
  destruct IO_tr as [IO_l incr]; apply trace_eq.
  unfold from_IO_trace, to_IO_trace;
  apply trace_list_eq; simpl; apply from_inv_to_raw.
  apply (raw_to_IO_list_stutters IO_l). apply (goodprop _ IO_l).
Qed.

End Properties.
Arguments to_IO_trace {I O}.
Arguments from_IO_trace {I O stut}.
Arguments to_IO_trace_stutters {I O stut}.
Arguments eq_IO_behaviour {I O stut}.
Notation "bio1 |≡ bio2" := (eq_IO_behaviour bio1 bio2) (at level 89, no associativity).

Section Conversions.

Context {I O : BoolSet U}.
Context {stut : U}.

Definition from_IO_behaviour (bio : IO_behaviour I O stut) : behaviour (I :|: O) :=
  fun IO_tr =>
    let traces := to_IO_trace stut IO_tr in
    let I_tr := fst traces in
    let O_tr := snd traces in
      (mapping bio) I_tr (exist _ O_tr (to_IO_trace_stutters (IO_no_stut bio) IO_tr)).

Definition to_IO_behaviour (b : behaviour (I :|: O)) :
  Disjoint I O -> In stut (I :|: O) = false -> IO_behaviour I O stut :=
  fun p1 p2 =>
    mkIOBehaviour I O stut p1 p2
    (fun I_tr => fun O_tr =>
      b (from_IO_trace p1 p2 I_tr (`O_tr) (proj2_sig O_tr))).

(* to and from are mutually inverse for behaviours *)
Lemma to_inv_from_behaviour (bio : IO_behaviour I O stut) :
  forall (p : Disjoint I O) (p1 : In stut (I :|: O) = false),
  bio |≡ to_IO_behaviour (from_IO_behaviour bio) p p1.
Proof.
  unfold eq_IO_behaviour. intros. split; simpl in *.
  - intros. unfold from_IO_behaviour, to_IO_behaviour.
    apply bio_accept_if_eqv with (I_tr:=I_tr) (O_tr:=O_tr).
    now rewrite to_inv_from_trace.
    apply trace_eq, trace_list_eq.
    destruct O_tr as [[[w g] incr] stut_prop].
    simpl in *. rewrite to_inv_from_raw with (O:=O).
    easy. apply (disjoint_IO bio). apply (IO_no_stut bio).
    apply stut_prop. apply (goodprop _ (`I_tr)).
    apply g. apply H.
  - intros. unfold from_IO_behaviour, to_IO_behaviour in H.
    apply bio_accept_if_eqv with
    (I_tr:=(fst (to_IO_trace stut (from_IO_trace p p1 I_tr (` O_tr) (proj2_sig O_tr)))))
    (O_tr:=(exist (trace_stutters stut (fst (to_IO_trace stut (from_IO_trace p p1 I_tr (` O_tr) (proj2_sig O_tr)))))
         (snd (to_IO_trace stut (from_IO_trace p p1 I_tr (` O_tr) (proj2_sig O_tr))))
         (to_IO_trace_stutters (IO_no_stut bio) (from_IO_trace p p1 I_tr (` O_tr) (proj2_sig O_tr))))).
    now rewrite to_inv_from_trace.
    apply trace_eq, trace_list_eq.
    destruct O_tr as [[[w g] incr] stut_prop].
    simpl in *. rewrite to_inv_from_raw with (O:=O).
    easy. apply (disjoint_IO bio). apply (IO_no_stut bio).
    apply stut_prop. apply (goodprop _ (`I_tr)).
    apply g. apply H.
Qed.


Lemma from_inv_to_behaviour (b : behaviour (I :|: O))
  (p1 : Disjoint I O) (p2 : In stut (I :|: O) = false) :
  b ≡ from_IO_behaviour (to_IO_behaviour b p1 p2).
Proof.
  unfold eq_behaviour; simpl in *; split; intros;
  unfold to_IO_behaviour, from_IO_behaviour in *;
  rewrite from_inv_to_trace in *; assumption.
Qed.


Lemma to_IO_eqv (b1 b2 : behaviour (I :|: O))
  (p1 : Disjoint I O) (p2 : In stut (I :|: O) = false):
  b1 ≡ b2 <-> (to_IO_behaviour b1 p1 p2) |≡ (to_IO_behaviour b2 p1 p2).
Proof.
  split.
  - intros; unfold eq_behaviour, eq_IO_behaviour in *; intros; split; destruct O_tr;
    intros; unfold to_IO_behaviour in *; apply H in H0; apply H0.
  - intros; unfold eq_behaviour, eq_IO_behaviour in *; intros; split; simpl in *;
    intros; unfold to_IO_behaviour in *; pose (O_tr:=(snd (to_IO_trace stut tr)));
    pose (y:=to_IO_trace_stutters p2 tr);
    specialize (H (fst (to_IO_trace stut tr)) ((exist _ O_tr) y));
    assert (from_IO_trace p1 p2 (fst (to_IO_trace stut tr)) O_tr y = tr) by apply from_inv_to_trace;
    rewrite <- H1; rewrite <- H1 in H0; apply H; apply H0.
Qed.


Lemma from_IO_eqv bio1 bio2 :
  bio1 |≡ bio2 <-> from_IO_behaviour bio1 ≡ from_IO_behaviour bio2.
Proof.
  split.
  - assert (IO_no_stut bio1 = IO_no_stut bio2).
    { apply eq_proofs_unicity_on. intros. decide equality. }
    intros; unfold eq_behaviour, eq_IO_behaviour in *; intros; split;
    intros; unfold from_IO_behaviour in *.
    specialize (H0 (fst (to_IO_trace stut tr))).
    apply H0 in H1. rewrite H in H1. apply H1.
    specialize (H0 (fst (to_IO_trace stut tr))).
    apply H0 in H1. rewrite <- H in H1. apply H1.
  - intros. apply (to_IO_eqv _ _ (disjoint_IO bio1) (IO_no_stut bio1)) in H.
    assert (bio1 |≡ to_IO_behaviour (from_IO_behaviour bio1)
      (disjoint_IO bio1) (IO_no_stut bio1)). apply to_inv_from_behaviour.
    assert (bio2 |≡ to_IO_behaviour (from_IO_behaviour bio2)
      (disjoint_IO bio1) (IO_no_stut bio1)). apply to_inv_from_behaviour.
    unfold eq_IO_behaviour in *. intros.
    rewrite H0. rewrite H1. rewrite H. easy.
Qed.


End Conversions.

End IO.
Arguments mkIOBehaviour {U Input Output stut_event}.
Arguments disjoint_IO {U Input Output stut_event}.
Arguments IO_no_stut {U Input Output stut_event}.
Arguments mapping {U Input Output stut_event}.

Arguments to_IO_trace_stutters {U I O stut}.
Arguments from_IO_behaviour {U I O stut}.
Arguments from_IO_trace {U I O stut}.
Arguments to_IO_trace {U I O}.
Arguments to_IO_behaviour {U I O}.
Arguments eq_IO_behaviour {U I O stut}.
Notation "bio1 |≡ bio2" := (eq_IO_behaviour bio1 bio2) (at level 89, no associativity).
