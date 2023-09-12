(******************************************************************************
 *  timedevent/IOComposition.v
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
From Coq Require Import Bool.

From TimedEvent Require Import BoolSet.
From TimedEvent Require Import Definitions.
From TimedEvent Require Import Composition.
From TimedEvent Require Import IO.

Section Universal.
Context {U : Set}.

Section IO_composition.

Context {stut : U}.
Context {I1 I2 I3 O1 O2 O3 : BoolSet U}.

Variable bio1 : IO_behaviour I1 O1 stut.
Variable bio2 : IO_behaviour I2 O2 stut.
Variable bio3 : IO_behaviour I3 O3 stut.

(* The output sets must be disjoint *)
Hypothesis disjoint_O12 : Disjoint O1 O2.
Hypothesis disjoint_O23 : Disjoint O2 O3.
Hypothesis disjoint_O13 : Disjoint O1 O3.

(*
  The input set of a composition will be (I1 :|: I2) \ (O1 :|: O2)
  The output set of a composition will be (O1 :|: O2)
  These are disjoint
*)
Lemma in_out_disjoint2 :
  Disjoint (Setminus (I1 :|: I2) (O1 :|: O2)) (O1 :|: O2).
Proof. apply minus_disjoint. Qed.

Lemma in_out_no_stut2 :
  In stut (Union (Setminus (I1 :|: I2) (O1 :|: O2)) (O1 :|: O2)) = false.
Proof.
  assert (H1 : In stut (I1 :|: O1) = false) by exact (IO_no_stut bio1).
  assert (H2 : In stut (I2 :|: O2) = false) by exact (IO_no_stut bio2).
  unfold Setminus, Union, In in *.
  apply orb_false_iff in H1, H2.
  destruct H1, H2. now rewrite H, H0, H1, H2.
Qed.

Lemma u_eqv_comp2 :
  ((I1 :|: O1) :|: (I2 :|: O2))
  = Union (Setminus (I1 :|: I2) (O1 :|: O2)) (O1 :|: O2).
Proof. rewrite u_eqv. reflexivity. Defined.

(* match on u_eqv_comp2 to get the right type *)
Definition compose_IO2 :=
  to_IO_behaviour stut (
    match (u_eqv_comp2) in (_ = t) return behaviour t with
    | eq_refl =>
      (from_IO_behaviour bio1) ||
      (from_IO_behaviour bio2)
    end
  ) in_out_disjoint2 in_out_no_stut2.


Lemma u_eqv_comp3 :
  ((I1 :|: O1) :|: (I2 :|: O2) :|: (I3 :|: O3))
  = Union (Setminus (I1 :|: I2 :|: I3) (O1 :|: O2 :|: O3)) (O1 :|: O2 :|: O3).
Proof.
  rewrite u_eqv. rewrite (union_assoc I1). rewrite <- (union_assoc (I1 :|: I2)).
  rewrite <- (union_assoc O1). rewrite <- (union_comm I2 O1).
  rewrite <- (union_assoc I1). rewrite <- (union_assoc I1). reflexivity.
Qed.

Lemma in_out_disjoint3 :
  Disjoint (Setminus (I1 :|: I2 :|: I3) (O1 :|: O2 :|: O3)) (O1 :|: O2 :|: O3).
Proof. apply minus_disjoint. Qed.

Lemma in_out_no_stut3 :
  In stut (Union (Setminus (I1 :|: I2 :|: I3) (O1 :|: O2 :|: O3)) (O1 :|: O2 :|: O3)) = false.
Proof.
  assert (H1 : In stut (I1 :|: O1) = false) by exact (IO_no_stut bio1).
  assert (H2 : In stut (I2 :|: O2) = false) by exact (IO_no_stut bio2).
  assert (H3 : In stut (I3 :|: O3) = false) by exact (IO_no_stut bio3).
  unfold Setminus, Union, In in *.
  apply orb_false_iff in H1, H2, H3.
  destruct H1, H2, H3. now rewrite H, H0, H1, H2, H3, H4.
Qed.

(*
  By associativity of the regular compose operator,
  this is well defined in either order of operator association
*)
Definition compose_IO3 :=
  to_IO_behaviour stut (
    match (u_eqv_comp3) in (_ = t) return behaviour t with
    | eq_refl =>
      (from_IO_behaviour bio1) || (from_IO_behaviour bio2) || (from_IO_behaviour bio3)
    end
  ) in_out_disjoint3 in_out_no_stut3.

End IO_composition.


Section IO_comp_properties.

(* This is to show the resulting types are equal in commutativity
  *)
Lemma u_eqv_comp2' {I1 I2 O1 O2 : BoolSet U} :
  ((I1 :|: O1) :|: (I2 :|: O2))
  = Union (Setminus (I2 :|: I1) (O2 :|: O1)) (O2 :|: O1).
Proof.
  rewrite u_eqv. rewrite union_comm. easy.
Defined.

(* Matching types shows us that commutativity holds
   when moving to the IO level
 *)
Lemma IO_compose_comm {I1 O1 I2 O2 stut} :
  forall (bio1 : IO_behaviour I1 O1 stut) (bio2 : IO_behaviour I2 O2 stut),
  to_IO_behaviour stut (
    match (@u_eqv_comp2 I1 I2 O1 O2) in (_ = t) return behaviour t with
    | eq_refl => (from_IO_behaviour bio1) || (from_IO_behaviour bio2)
    end
  ) in_out_disjoint2 (in_out_no_stut2 bio1 bio2)
  |≡
  to_IO_behaviour stut (
    match (@u_eqv_comp2' I2 I1 O2 O1) in (_ = t) return behaviour t with
    | eq_refl => (from_IO_behaviour bio2) || (from_IO_behaviour bio1)
    end
  ) in_out_disjoint2 (in_out_no_stut2 bio1 bio2).
Proof.
  generalize (@u_eqv_comp2 I1 I2 O1 O2).
  generalize (@u_eqv_comp2' I2 I1 O2 O1).
  generalize (@in_out_disjoint2 I1 I2 O1 O2).
  generalize (@in_out_no_stut2 stut I1 I2 O1 O2).
  unfold compose. rewrite u_eqv_comp2. rewrite u_eqv_comp2'.
  rewrite (union_comm I1 I2). rewrite (union_comm O1 O2).
  intros. rewrite (UIP_refl _ _ e1). rewrite (UIP_refl _ _ e0).
  apply to_IO_eqv.
  unfold eq_behaviour. intros; split;
  intros; rewrite and_comm in H; apply H;
  intros; rewrite and_comm in H; apply H.
Qed.


(* This is to show the resulting types are equal in associativity
  *)
Lemma u_eqv_comp3' {I1 I2 I3 O1 O2 O3 : BoolSet U} :
  ((I1 :|: O1) :|: ((I2 :|: O2) :|: (I3 :|: O3)))
  = Union (Setminus (I1 :|: I2 :|: I3) (O1 :|: O2 :|: O3)) (O1 :|: O2 :|: O3).
Proof.
  rewrite <- union_assoc. apply u_eqv_comp3.
Qed.

(* Matching types shows us that associativity holds
   when moving to the IO level
 *)
Lemma IO_compose_assoc {I1 O1 I2 O2 I3 O3 stut} :
  forall (bio1 : IO_behaviour I1 O1 stut) (bio2 : IO_behaviour I2 O2 stut)
    (bio3 : IO_behaviour I3 O3 stut),
  (* associate left *)
  to_IO_behaviour stut (
    (* match type *)
    match (u_eqv_comp3) in (_ = t) return behaviour t with
    | eq_refl =>
      ((from_IO_behaviour bio1) || (from_IO_behaviour bio2)) || (from_IO_behaviour bio3)
    end
  ) in_out_disjoint3 (in_out_no_stut3 bio1 bio2 bio3)
  |≡
  (* associate right *)
  to_IO_behaviour stut (
    (* match type *)
    match (u_eqv_comp3') in (_ = t) return behaviour t with
    | eq_refl =>
      (from_IO_behaviour bio1) || ((from_IO_behaviour bio2) || (from_IO_behaviour bio3))
    end
  ) in_out_disjoint3 (in_out_no_stut3 bio1 bio2 bio3).
Proof.
  generalize (@u_eqv_comp3 I1 I2 I3 O1 O2 O3).
  generalize (@u_eqv_comp3' I1 I2 I3 O1 O2 O3).
  generalize (@in_out_disjoint3 I1 I2 I3 O1 O2 O3).
  generalize (@in_out_no_stut3 stut I1 I2 I3 O1 O2 O3).
  unfold compose. rewrite u_eqv_comp3, u_eqv_comp3'.
  intros. rewrite (UIP_refl _ _ e1). rewrite (UIP_refl _ _ e0).
  apply to_IO_eqv.
  unfold eq_behaviour. intro.
  rewrite !proj_subset_eq in *. easy.
  all: try apply union_subset_r; try apply union_subset_l.
Qed.

End IO_comp_properties.

End Universal.
