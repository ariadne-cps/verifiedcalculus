(******************************************************************************
 *  timedevent/BoolSet.v
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


From Coq Require Import FunctionalExtensionality.
From Coq Require Import Bool.
From Coq Require Import Logic.
From Coq Require Import Logic.Eqdep_dec.

Section BoolSet.

Context {U : Set}.

(* We assume U has decidable equality *)
Axiom U_eq_dec : forall (x y : U), {x = y} + {x <> y}.

Lemma U_eq_l : forall x, U_eq_dec x x = left (eq_refl x).
Proof.
  intros. destruct (U_eq_dec x x).
  - f_equal. apply UIP_dec. apply U_eq_dec.
  - easy.
Qed.

Definition BoolSet := U -> bool.

Definition In (x : U) (A : BoolSet) : bool := A x.

Definition EmptySet : BoolSet := fun _ => false.

Definition FullSet : BoolSet := fun _ => true.

Definition Single (x : U) : BoolSet :=
  fun y => if U_eq_dec x y then true else false.

Definition Union A B : BoolSet := fun x => orb (In x A) (In x B).

Lemma union_comm : forall A B, Union A B = Union B A.
Proof.
  intros A B; unfold Union. apply functional_extensionality.
  intros. apply orb_comm.
Defined.

Lemma union_assoc : forall A B C,
  Union (Union A B) C = Union A (Union B C).
Proof.
  intros A B C; unfold Union, In. apply functional_extensionality.
  intros x. rewrite orb_assoc. easy.
Defined.

Lemma in_union_or : forall A B x, In x (Union A B) = true ->
  In x A = true \/ In x B = true.
Proof.
  intros A B x H. unfold Union, In in *. apply (orb_true_iff) in H. exact H.
Qed.

Lemma in_union_false : forall A B x, In x (Union A B) = false ->
  In x A = false /\ In x B = false.
Proof.
  intros A B x H. unfold Union, In in *. now apply (orb_false_iff) in H.
Qed.

Lemma In_UnionL : forall A B x,
  In x (Union A B) = true -> In x A = false -> In x B = true.
Proof.
  unfold Union, In. intros. rewrite H0 in H. simpl in H. apply H.
Qed.

Lemma In_UnionR : forall A B x,
  In x (Union A B) = true -> In x B = false -> In x A = true.
Proof.
  unfold Union, In. intros. rewrite H0 in H.
  rewrite orb_comm in H. simpl in H. apply H.
Qed.

Definition Intersection A B : BoolSet := fun x => andb (In x A) (In x B).

Lemma intsect_comm : forall A B, Intersection A B = Intersection B A.
Proof.
  intros A B; unfold Intersection. apply functional_extensionality.
  intro. apply andb_comm.
Defined.

Definition Setminus (B C: BoolSet) : BoolSet :=
    fun x:U => In x B && (negb (In x C)).

Lemma setminus_not_in : forall A B x,
  In x B = true -> In x (Setminus A B) = false.
Proof.
  intros A B x H. unfold Setminus, In in *. rewrite H.
  simpl. rewrite andb_comm. easy.
Qed.

Definition Add (x : U) (A : BoolSet) : BoolSet :=
  fun y => if U_eq_dec x y then true else A y.

Lemma In_Add : forall A x, In x (Add x A) = true.
Proof.
  intros A x; unfold Add, In. destruct (U_eq_dec x x). all: easy.
Qed.

Definition Disjoint (A B : BoolSet) :=
  forall (x : U), In x (Intersection A B) = false.

Lemma disjoint_not_in : forall A B x,
  In x A = true -> Disjoint A B -> In x B = false.
Proof.
   intros A B x H1 H2. unfold Disjoint, Intersection, In in *.
   specialize (H2 x). rewrite H1 in H2. easy.
Qed.

Lemma disjoint_comm : forall A B, Disjoint A B = Disjoint B A.
Proof.
  intros A B; unfold Disjoint. rewrite intsect_comm. easy.
Qed.

Lemma disjoint_union : forall A B C,
  Disjoint A B -> Disjoint A C -> Disjoint A (Union B C).
Proof.
  unfold Disjoint, Intersection, Union, In. intros A B C H1 H2 x.
  specialize (H1 x). specialize (H2 x).
  apply andb_false_iff in H1, H2. destruct H1 as [H1|H1], H2 as [H2|H2].
  all: rewrite H1; try rewrite H2; auto; rewrite andb_comm; auto.
Qed.

Definition Subset (A B : BoolSet) :=
  forall (x : U), In x A = true -> In x B = true.

Lemma refl_subset : forall A, Subset A A.
Proof.
  unfold Subset; intros; apply H.
Qed.

Lemma union_subset_l : forall A B, Subset A (Union A B).
Proof.
  unfold Subset, Union, In. intros. rewrite H. easy.
Qed.

Lemma union_subset_r : forall A B, Subset A (Union B A).
Proof.
  unfold Subset, Union, In. intros. rewrite H. rewrite orb_comm. easy.
Qed.

Lemma add_subset : forall A x, Subset A (Add x A).
Proof.
  intros. unfold Subset. intros.
  unfold Add. unfold In. destruct U_eq_dec.
  - easy.
  - apply H.
Qed.

Lemma in_subset : forall A B x, In x A = true -> Subset A B -> In x B = true.
Proof.
  intros. unfold Subset, In in *. apply H0 in H. apply H.
Qed.

Lemma minus_subset : forall A B, Subset (Setminus A B) (Union (Setminus A B) B).
Proof.
  unfold Subset, Setminus, Union, In. intros. rewrite H.
  easy.
Qed.

Lemma minus_disjoint : forall A B, Disjoint (Setminus A B) B.
Proof.
  unfold Setminus, Disjoint, In, Intersection, In.
  intros. unfold negb. destruct (B x).
  - rewrite andb_comm with (b1:= A x). auto.
  - rewrite andb_comm. auto.
Qed.

Lemma not_in_not_eq : forall A x y,
  In x A = true -> In y A = false -> x <> y.
Proof.
  intros. unfold In in *. unfold not. intros.
  rewrite H1 in H. rewrite H in H0. easy.
Qed.

Lemma disjoint_neq : forall A B x y,
  In x A = true -> In y B = true -> Disjoint A B -> x <> y.
Proof.
  intros. unfold Disjoint, Intersection, In in *.
  specialize (H1 x). unfold not. intros.
  rewrite <- H2 in H0.
  rewrite H,H0 in H1.
  easy.
Qed.

Lemma u_eqv {A1 A2 B1 B2 : BoolSet} :
  Union (Setminus (Union A1 A2) (Union B1 B2)) (Union B1 B2) =
    Union (Union A1 B1) (Union A2 B2).
Proof.
  unfold Union, Setminus, Union, In;
  apply functional_extensionality; intros;
  destruct (A1 x), (A2 x), (B1 x), (B2 x); simpl;  auto.
Qed.

End BoolSet.
Arguments BoolSet : clear implicits.

Notation "E1 :|: E2" := (Union E1 E2) (at level 89, left associativity).
