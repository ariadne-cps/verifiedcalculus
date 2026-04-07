(******************************************************************************
 *  Sets/OvertSets.v
 *
 *  Copyright 2026 Pieter Collins
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


Require Sierpinskian.
Require VerifiedCalculus.Logic.Sierpinskian.
Require Import OpenSets.

Module OvertSets.

Import OpenSets.

Definition overt_respectful {X} (v : OpenSet X -> S) : Prop := 
  forall U1 U2, (forall x, U1 x == U2 x) -> v U1 == v U2.

Definition overt_proper {X} (v : OpenSet X -> S) : Prop := 
  forall U1 U2, (v (union U1 U2)) == (Sor (v U1) (v U2)).

Definition OvertSet (X : Set) :=
  { c : OpenSet X -> S | overt_respectful c /\ overt_proper c }.

Definition mkOvertSet {X : Set} (v : OpenSet X -> S)
    (r : overt_respectful v) (p : overt_proper v) : OvertSet X :=
  @exist (OpenSet X -> S) _ v (conj r p).

Definition intersects {X} (V : OvertSet X) (U : OpenSet X) := (proj1_sig V) U.


Notation Ounion := OpenSets.union.
Notation Ointersection := OpenSets.intersection.

Definition union_op {X} (v1 v2 : OpenSet X -> S) : OpenSet X -> S :=
  fun U => Sor (v1 U) (v2 U).

Lemma union_respectful {X} (v1 v2 : OpenSet X -> S) : 
  overt_respectful v1 -> overt_respectful v2 -> overt_respectful (union_op v1 v2).
Proof.
  unfold overt_respectful, union_op.
  intros HR1 HR2 U1 U2 HU.
  apply Sierpinskian.or_respectful.
  - apply HR1. exact HU.
  - apply HR2. exact HU.
Qed.


Lemma Sinner_or_comm : forall p11 p12 p21 p22 : S, 
  Sor (Sor p11 p12) (Sor p21 p22) == Sor (Sor p11 p21) (Sor p12 p22).
Proof.
  intros p11 p12 p21 p22;
  apply (Sierpinskian.eqv_trans _ (Sor (Sor (Sor p11 p12) p21) p22) _).
    apply Sierpinskian.eqv_sym. apply Sierpinskian.or_assoc.
  apply (Sierpinskian.eqv_trans _ (Sor (Sor p11 (Sor p12 p21)) p22) _).
    apply Sierpinskian.or_respectful. apply Sierpinskian.or_assoc. apply Sierpinskian.eqv_refl. 
  apply (Sierpinskian.eqv_trans _ (Sor (Sor p11 (Sor p21 p12)) p22) _).
    apply Sierpinskian.or_respectful. apply Sierpinskian.or_respectful. apply Sierpinskian.eqv_refl. apply Sierpinskian.or_comm. apply Sierpinskian.eqv_refl. 
  apply (Sierpinskian.eqv_trans _ (Sor (Sor (Sor p11 p21) p12) p22) _).
    apply Sierpinskian.or_respectful. apply Sierpinskian.eqv_sym. apply Sierpinskian.or_assoc. apply Sierpinskian.eqv_refl.
  now apply Sierpinskian.or_assoc. 
Qed.

Lemma union_proper {X} (v1 v2 : OpenSet X -> S) : 
  overt_proper v1 -> overt_proper v2 -> overt_proper (union_op v1 v2).
Proof.
  intros HP1 HP2 U1 U2.
  unfold overt_proper in *.
  specialize HP1 with U1 U2.
  specialize HP2 with U1 U2.
  unfold union_op.
  apply (Sierpinskian.eqv_trans _ (Sor (Sor (v1 U1) (v1 U2)) (Sor (v2 U1) (v2 U2))) _).
  - apply Sierpinskian.or_respectful. exact HP1. exact HP2.
  - now apply Sinner_or_comm.
Qed.

Definition union {X} (V1 V2 : OvertSet X) : OvertSet X :=
  let v1 := proj1_sig V1 in let v2 := proj1_sig V2 in
  let r1 := proj1 (proj2_sig V1) in let r2 := proj1 (proj2_sig V2) in
  let p1 := proj2 (proj2_sig V1) in let p2 := proj2 (proj2_sig V2) in
     mkOvertSet (union_op v1 v2) (union_respectful v1 v2 r1 r2) (union_proper v1 v2 p1 p2).


Definition intersection_op {X} (v : OpenSet X -> S) (W : OpenSet X) : OpenSet X -> S :=
  fun U => v (intersection W U).

Lemma intersection_respectful {X} (v : OpenSet X -> S) (W : OpenSet X) : 
  overt_respectful v -> overt_respectful (intersection_op v W).
Proof.
  unfold overt_respectful.
  intros HR U1 U2 HU.
  unfold intersection_op.
  apply HR.
  apply OpenSets.intersection_respectful.
  - now apply OpenSets.equivalent_refl.
  - exact HU.
Qed.

Lemma intersection_proper {X} (v : OpenSet X -> S) (W : OpenSet X) : 
  overt_respectful v -> overt_proper v -> overt_proper (intersection_op v W).
Proof.
  unfold overt_proper.
  intros HR HP U1 U2.
  unfold intersection_op.
  apply (Sierpinskian.eqv_trans _ (v (Ounion (Ointersection W U1) (Ointersection W U2))) _).
  2: now apply (HP (Ointersection W U1) (Ointersection W U2)).
  apply HR.
  intro x.
  unfold Ointersection, Ounion.
  now apply Sierpinskian.and_or_distrib_r.
Qed.

Definition intersection {X} (V : OvertSet X) (W : OpenSet X) : OvertSet X :=
  let v := proj1_sig V in let r := proj1 (proj2_sig V) in let p := proj2 (proj2_sig V) in
    mkOvertSet (intersection_op v W) (intersection_respectful v W r) (intersection_proper v W r p).


Definition interior {X} (H : effective_discrete X) (V: OvertSet X) : OpenSet X :=
  fun x => (proj1_sig V) (fun x' => (proj1_sig H) x x').

Definition discrete_intersection {X} (H : effective_discrete X) (V1 V2 : OvertSet X) : OvertSet X :=
  intersection V1 (interior H V2).

End OvertSets.
