(******************************************************************************
 *  Sets/OpenSets.v
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
From VerifiedCalculus Require Logic.Sierpinskian.
From VerifiedCalculus.Logic Require Sierpinskian.


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





(* Continuity *)

Require Import Reals.

Definition less_eq_open (a : R) : R -> Sierpinskian :=
  fun b => if R.le b a then true else indeterminate.
 
