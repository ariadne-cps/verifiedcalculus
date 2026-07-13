(******************************************************************************
 *  Sets/CompactSets.v
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
Require Import OpenSets.

Module CompactSets.

Import OpenSets.

Definition compact_respectful {X} (c : OpenSet X -> S) : Prop := 
  forall U1 U2, (forall x, U1 x == U2 x) -> c U1 == c U2.

Definition compact_proper {X} (c : OpenSet X -> S) : Prop := 
  forall U1 U2, Sierpinskian.eqv (c (intersection U1 U2)) (Sand (c U1) (c U2)).

Definition CompactSet (X : Set) :=
  { c : OpenSet X -> S | compact_respectful c /\ compact_proper c }.

Definition mkCompactSet {X : Set} (c : OpenSet X -> S) 
    (r : compact_respectful c) (p : compact_proper c) : CompactSet X :=
  @exist _ _ c (conj r p).

Definition subset {X} (C : CompactSet X) (U : OpenSet X) := (proj1_sig C) U.


Notation Ounion := OpenSets.union.
Notation Ointersection := OpenSets.intersection.


Definition union_op {X} (c1 c2 : OpenSet X -> S) : OpenSet X -> S :=
  fun U => Sierpinskian.and (c1 U) (c2 U).

Lemma union_respectful {X} (c1 c2 : OpenSet X -> S) : 
  compact_respectful c1 -> compact_respectful c2 -> compact_respectful (union_op c1 c2).
Proof.
  unfold compact_respectful, union_op.
  intros HR1 HR2 U1 U2 HU.
  apply Sierpinskian.and_respectful.
  - apply HR1. exact HU.
  - apply HR2. exact HU.
Qed.

Lemma Sinner_and_comm : forall p11 p12 p21 p22 : S, 
  Sand (Sand p11 p12) (Sand p21 p22) == Sand (Sand p11 p21) (Sand p12 p22).
Proof.
  intros p11 p12 p21 p22;
  apply (Sierpinskian.eqv_trans _ (Sand (Sand (Sand p11 p12) p21) p22) _).
    apply Sierpinskian.eqv_sym. apply Sierpinskian.and_assoc.
  apply (Sierpinskian.eqv_trans _ (Sand (Sand p11 (Sand p12 p21)) p22) _).
    apply Sierpinskian.and_respectful. apply Sierpinskian.and_assoc. apply Sierpinskian.eqv_refl. 
  apply (Sierpinskian.eqv_trans _ (Sand (Sand p11 (Sand p21 p12)) p22) _).
    apply Sierpinskian.and_respectful. apply Sierpinskian.and_respectful. apply Sierpinskian.eqv_refl. apply Sierpinskian.and_comm. apply Sierpinskian.eqv_refl. 
  apply (Sierpinskian.eqv_trans _ (Sand (Sand (Sand p11 p21) p12) p22) _).
    apply Sierpinskian.and_respectful. apply Sierpinskian.eqv_sym. apply Sierpinskian.and_assoc. apply Sierpinskian.eqv_refl.
  now apply Sierpinskian.and_assoc. 
Qed.

Lemma union_proper {X} (c1 c2 : OpenSet X -> S) : 
  compact_proper c1 -> compact_proper c2 -> compact_proper (union_op c1 c2).
Proof.
  intros HP1 HP2 U1 U2.
  unfold compact_proper in *.
  specialize HP1 with U1 U2.
  specialize HP2 with U1 U2.
  unfold union_op.
  apply (Sierpinskian.eqv_trans _ (Sand (Sand (c1 U1) (c1 U2)) (Sand (c2 U1) (c2 U2))) _).
  - apply Sierpinskian.and_respectful. exact HP1. exact HP2.
  - now apply Sinner_and_comm.
Qed.


Definition union {X} (C1 C2 : CompactSet X) : CompactSet X :=
  let c1 := proj1_sig C1 in let c2 := proj1_sig C2 in
  let r1 := proj1 (proj2_sig C1) in let r2 := proj1 (proj2_sig C2) in
  let p1 := proj2 (proj2_sig C1) in let p2 := proj2 (proj2_sig C2) in
    mkCompactSet (union_op c1 c2) (union_respectful c1 c2 r1 r2) (union_proper c1 c2 p1 p2).


Definition difference_op {X} (c : OpenSet X -> S) (W : OpenSet X) : OpenSet X -> S :=
  fun U => c (OpenSets.union W U).

Lemma difference_respectful {X} (c : OpenSet X -> S) (W : OpenSet X) : 
  compact_respectful c -> compact_respectful (difference_op c W).
Proof.
  unfold compact_respectful.
  intros HR U1 U2 HU.
  unfold difference_op.
  apply HR.
  apply OpenSets.union_respectful.
  - now apply OpenSets.equivalent_refl.
  - exact HU.
Qed.

Lemma difference_proper {X} (c : OpenSet X -> S) (W : OpenSet X) : 
  compact_respectful c -> compact_proper c -> compact_proper (difference_op c W).
Proof.
  unfold compact_proper.
  intros HR HP U1 U2.
  unfold difference_op.
  apply (Sierpinskian.eqv_trans _ (c (Ointersection (Ounion W U1) (Ounion W U2))) _).
  2: now apply (HP (Ounion W U1) (Ounion W U2)).
  apply HR.
  intro x.
  unfold Ointersection, Ounion.
  now apply Sierpinskian.or_and_distrib_r.
Qed.

Definition difference {X} (C : CompactSet X) (W : OpenSet X) : CompactSet X :=
  let c := proj1_sig C in let r := proj1 (proj2_sig C) in let p := proj2 (proj2_sig C) in
    mkCompactSet (difference_op c W) (difference_respectful c W r) (difference_proper c W r p).

Definition complement {X} (H : effective_hausdorff X) (C : CompactSet X) : OpenSet X :=
  fun x => (proj1_sig C) (fun x' => (proj1_sig H) x x').

Definition hausdorff_intersection {X} (H : effective_hausdorff X) (C1 C2 : CompactSet X) : CompactSet X :=
  difference C1 (complement H C2).

End CompactSets.
