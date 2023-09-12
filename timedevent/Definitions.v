(******************************************************************************
 *  timedevent/Definitions.v
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


From Coq Require Import Bool.
From Coq Require Import Reals.
From Coq Require Import Program.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import ProofIrrelevance.
From Coq Require Export Relation_Definitions.
From Coq Require Export RelationClasses.
From Coq Require Import Morphisms.
From Coq Require Import Lra.
From Coq Require Import Lists.List. Import ListNotations.

From TimedEvent Require Import BoolSet.

Open Scope R_scope.

Notation "tl -::- hd" := (hd :: tl) (at level 89, left associativity).

(* mapping the same term to equal types *)
Definition m_eq_type {A B} (p : A = B) : A -> B :=
  fun a =>
  match p in (_ = e) return e with
  | eq_refl => a
  end.

Section Definitions.

Context {U : Set}.

(* Restricted to finite traces *)
Definition raw_tr_list : Type := list (R * U).

Fixpoint good_tr_list (E : BoolSet U) (w : raw_tr_list) : bool :=
  match w with
  | [] => true
  | tl -::- hd => In (snd hd) E && good_tr_list E tl
  end.

Lemma all_in_good w E : (forall x, List.In x w -> In (snd x) E = true) <->
  good_tr_list E w = true.
Proof.
  split; intros H; induction w as [| hd tl IH].
  - easy.
  - simpl.
    apply andb_true_iff.
    split.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros x H_in.
      apply H. simpl. right. assumption.
  - easy.
  - intros x H0; simpl in *. apply andb_true_iff in H; destruct H. destruct H0.
    + rewrite <- H0; apply H.
    + apply IH. all: assumption.
Qed.

Lemma subset_good w E1 E2 :
  good_tr_list E1 w = true -> Subset E1 E2 -> good_tr_list E2 w = true.
Proof.
  intros H1 Hs. induction w.
  - easy.
  - simpl in *. apply andb_true_iff in H1; destruct H1 as [H1 H2].
    apply in_subset with (B:=E2) in H1.
    rewrite H1. apply IHw in H2. rewrite H2. all: trivial.
Qed.

(* A list with the property that all elements are in E
   Note that this is a subtype of raw_tr_list *)
Record trace_list (E : BoolSet U) : Type := mkTrlist {
  raw_of_tracelist :> raw_tr_list;
  goodprop : good_tr_list E raw_of_tracelist = true;
}.

Lemma trace_list_eq {E} :
  forall (t1 t2 : trace_list E),
    raw_of_tracelist _ t1 = raw_of_tracelist _ t2 <-> t1 = t2.
Proof.
  split.
  - intros Hraw.
    destruct t1 as [raw1 good1], t2 as [raw2 good2].
    simpl in Hraw. subst raw2.
    assert (H : good1 = good2).
    (* UIP is true for boolean propositions *)
    { apply eq_proofs_unicity_on. intros. decide equality. }
    subst good2.
    easy.
  - intros; rewrite H; easy.
Qed.

Definition fst_list {A B} (l : list (A*B)) : list A :=
  map fst l.

Definition ge_head_zero {E1 : Type} (x : R * E1) (l : raw_tr_list) : Prop :=
  match l with
  | [] => (fst x) > 0
  | tl -::- hd => fst x >= fst hd
  end.

(* forall i, t_i <= t_(i+1) *)
Inductive increasing_time : raw_tr_list -> Prop :=
  incr_nil                           : increasing_time nil
| incr_app x (l : raw_tr_list)       : ge_head_zero x l ->
                                       increasing_time l ->
                                       increasing_time (l -::- x).

Definition trace (E : BoolSet U) :=
  { tr_list : trace_list E | increasing_time tr_list}.

Lemma trace_eq : forall (E : BoolSet U) (tr1 tr2 : trace E),
  proj1_sig tr1 = proj1_sig tr2 <-> tr1 = tr2.
Proof.
  split.
  - intros Hpeq. destruct tr1, tr2. unfold proj1_sig in Hpeq.
    subst x0.
    assert (H : i = i0) by (apply proof_irrelevance).
    now subst i.
  - intros; rewrite H; easy.
Qed.


Definition behaviour (E : BoolSet U) := trace E -> Prop.

Definition eq_behaviour {E : BoolSet U} (b1 b2 : trace E -> Prop) : Prop :=
  forall tr, b1 tr <-> b2 tr.
Notation "b1 ≡ b2" := (eq_behaviour b1 b2) (at level 89, no associativity).

(* Defining equivalence relation *)
#[export]Instance eq_sub {E} :
  subrelation eq_behaviour (pointwise_relation (trace E) iff).
Proof.
  unfold subrelation, pointwise_relation, eq_behaviour; repeat intro;
  apply H.
Qed.

Lemma eq_behaviour_proper_flip_impl : forall E,
  Proper (eq_behaviour ==> (@eq_behaviour E) ==> flip impl) eq_behaviour.
Proof.
  intros. unfold Proper, eq_behaviour, flip, impl, "==>".
  intros. split.
  - intros. apply H in H2. apply H1 in H2. apply H0 in H2. apply H2.
  - intros. apply H0 in H2. apply H1 in H2. apply H in H2. apply H2.
Qed.

Instance eq_behaviour_proper_inst : forall (E : BoolSet U),
  Proper (eq_behaviour ==> (@eq_behaviour E) ==> flip impl) eq_behaviour :=
    eq_behaviour_proper_flip_impl.


Lemma eq_behaviour_refl : forall (E : BoolSet U), reflexive _ (@eq_behaviour E).
Proof.
  intros; unfold reflexive, eq_behaviour; intros; reflexivity.
Qed.

Lemma eq_behaviour_sym : forall (E : BoolSet U), symmetric _ (@eq_behaviour E).
Proof.
  intros; unfold symmetric, eq_behaviour; intros;
  specialize (H tr); symmetry; assumption.
Qed.

Lemma eq_behaviour_trans : forall (E : BoolSet U), transitive _ (@eq_behaviour E).
Proof.
  intros; unfold transitive, eq_behaviour; intros. transitivity (y tr).
  apply H. apply H0.
Qed.

Add Parametric Relation E : (behaviour E) (@eq_behaviour E)
  reflexivity proved by (eq_behaviour_refl E)
  symmetry proved by (eq_behaviour_sym E)
  transitivity proved by (eq_behaviour_trans E)
  as eq_behaviour_rel.

(* To rewrite *)
#[export]Instance eq_behaviour_Proper (E : BoolSet U)
  : Proper (@eq_behaviour E ==> @eq_behaviour E ==> iff) eq_behaviour.
Proof.
  intros b1 b2 H1 b3 b4 H2.
  split.
  - intros. symmetry in H1.
    assert (Heq : b2 ≡ b3).
    { apply transitivity with (y:=b1). all: assumption. }
    apply transitivity with (y:=b3). all: assumption.
  - intros. symmetry in H2.
    assert (Heq : b1 ≡ b4).
    { apply transitivity with (y:=b2). all: assumption. }
    apply transitivity with (y:=b4). all: assumption.
Qed.

(* Helping lemmas *)
Lemma gt_event_trans : forall E1 E2 E3 (x : R * E1) (y : R * E2) (z : R * E3),
  fst x > fst y -> fst y > fst z -> fst x > fst z.
Proof. intros. lra. Qed.

Lemma ge_app_ge_l : forall Usub (a : R*Usub) (h : R*_)
  (l : raw_tr_list), increasing_time (l -::- h) ->
    ge_head_zero a (l -::- h) -> ge_head_zero a l.
Proof.
  intros Usub a h l Hinc Hlt. induction l;
  inversion Hinc; unfold ge_head_zero in *;
  lra.
Qed.

Lemma ge_ge_head_zero : forall E1 E2 t ti (ei:E2) (e:E1) l,
  ge_head_zero (ti, ei) l -> t >= ti -> ge_head_zero (t, e) l.
Proof.
  intros. unfold ge_head_zero in *. destruct l; simpl in *; lra.
Qed.

Lemma ge_head_zero_ge_zero : forall E1 t (e:E1) l,
  increasing_time l -> ge_head_zero (t, e) l -> t > 0.
Proof.
  intros E1 t e l Hinc Hge. induction l.
  - exact Hge.
  - inversion Hinc. apply ge_app_ge_l in Hge. apply (IHl H2 Hge). trivial.
Qed.

Lemma incr_cons2 : forall x y l,
  increasing_time l -> ge_head_zero y l -> ge_head_zero x (y :: l)
  -> increasing_time (x :: y :: l).
Proof.
  intros x y l Hinc Hge Hge2. apply incr_app.
  - assumption.
  - apply incr_app. all: assumption.
Qed.

Lemma inc_three : forall x y (l : raw_tr_list),
  increasing_time (x :: y :: l) -> increasing_time (x :: l).
Proof.
  intros x y l H.
  inversion H. apply incr_app.
  - apply (ge_app_ge_l _ _ y l H3 H2).
  - now inversion H3.
Qed.

Lemma incr_ge_zero l t e : increasing_time (l -::- (t, e)) -> t > 0.
Proof.
  intros Hinc. induction l.
  - inversion Hinc. assumption.
  - apply inc_three in Hinc. apply (IHl Hinc).
Qed.

Lemma incr_fst_list (tl : raw_tr_list) (tl' : raw_tr_list) :
  increasing_time tl -> fst_list tl = fst_list tl' ->
  increasing_time tl'.
Proof.
  intros. generalize dependent tl'. induction tl; intros; destruct tl';
  try apply incr_nil.
  - discriminate H0.
  - inversion H0. apply incr_app.
    + inversion H. unfold ge_head_zero in *.
      rewrite H2 in H5. destruct tl.
      ++ inversion H0. destruct tl'.
        ** rewrite H2. assumption.
        ** discriminate H9.
      ++ inversion H0. destruct tl'.
        ** discriminate H9.
        ** simpl in H9. inversion H9. rewrite H2.
           assumption.
    + inversion H. apply (IHtl H6 _ H3).
Qed.

End Definitions.
Notation "b1 ≡ b2" := (eq_behaviour b1 b2) (at level 89, no associativity).
Tactic Notation "and_destr" constr(H) :=
  simpl in H;
  apply andb_true_iff in H;
  match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Arguments raw_tr_list : clear implicits.
Arguments raw_of_tracelist {U E}.
