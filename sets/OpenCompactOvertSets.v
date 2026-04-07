(******************************************************************************
 *  sets/OpenCompactOvertSets.v
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

Module Sets.

Notation N := nat.
Notation Strue := Sierpinskian.true.
Notation Sand := Sierpinskian.and.
Notation Sor := Sierpinskian.or.
Notation Sdisj := Sierpinskian.disj.
Notation Sierpinskian := Sierpinskian.Sierpinskian.
Notation S := Sierpinskian.
Infix "==" := Sierpinskian.eqv (at level 70, no associativity).


Module OpenSets.

Definition OpenSet (X : Set) : Set := X -> S.

Definition equivalent {X : Set} (U1 U2 : OpenSet X) : Prop :=
  forall x : X, Sierpinskian.eqv (U1 x) (U2 x).

Infix "===" := equivalent (at level 70, no associativity).

Lemma equivalent_refl {X : Set} : forall U : OpenSet X, U === U.
Proof.
  intros U x. 
  now apply Sierpinskian.eqv_refl.
Qed.
 
Definition intersection {X : Set} (U1 U2 : OpenSet X) : OpenSet X :=
  fun x => Sand (U1 x) (U2 x).

Lemma intersection_respectful {X : Set} : 
  forall (U1 U2 U1' U2' : OpenSet X), U1 === U1' -> U2 === U2' -> 
     intersection U1 U2 === intersection U1' U2'.
Proof.
  unfold equivalent, intersection.
  intros U1 U2 U1' U2' H1 H2 x.
  apply Sierpinskian.and_respectful.
  exact (H1 x). exact (H2 x).
Qed.

Definition union {X : Set} (U1 U2 : OpenSet X) : OpenSet X :=
  fun x => Sor (U1 x) (U2 x).

Lemma union_respectful {X : Set} : 
  forall (U1 U2 U1' U2' : OpenSet X), U1 === U1' -> U2 === U2' -> 
     union U1 U2 === union U1' U2'.
Proof.
  unfold equivalent, union.
  intros U1 U2 U1' U2' H1 H2 x.
  apply Sierpinskian.or_respectful.
  exact (H1 x). exact (H2 x).
Qed.

Definition denumerable_union {X : Set} (U : N -> OpenSet X) : OpenSet X :=
  fun x => Sdisj (fun n => (U n x)).

Lemma denumerable_union_respectful {X : Set} : 
  Sierpinskian.LPO -> forall (U U' : N -> OpenSet X), (forall n, U n === U' n) -> 
     denumerable_union U === denumerable_union U'.
Proof.
  unfold equivalent, denumerable_union.
  intros plpo U U' H x.
  apply (Sierpinskian.disj_respectful plpo).
  intro n; exact (H n x).
Qed.



Theorem quantifier_monotone {X : Set} :
  forall Q : (X -> S) -> S, forall U V : X -> S, 
    (forall x, (U x == Strue) -> (V x == Strue)) -> Q U == Strue -> Q V == Strue.
Proof. Admitted.
 
Theorem quantifier_continuous {X : Set} :
  forall Q : (X -> S) -> S, forall U : N -> X -> S, 
    (forall n, (forall x, (U n x == Strue) -> (U (Nat.succ n) x == Strue))) -> 
      Q (denumerable_union U) == Strue <-> exists n, Q (U n) == Strue.
Proof. Admitted.
 
End OpenSets.


Definition effective_discrete (X : Set) : Set :=
  { equal : X -> X -> Sierpinskian.Sierpinskian | forall x1 x2, (equal x1 x2 == Sierpinskian.true) <-> (x1 = x2) }.

Definition effective_hausdorff (X : Set) : Set :=
  { apart : X -> X -> Sierpinskian.Sierpinskian | forall x1 x2, (apart x1 x2 == Sierpinskian.true) <-> (x1 <> x2) }.


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


End Sets.
