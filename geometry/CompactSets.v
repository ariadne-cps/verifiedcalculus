(******************************************************************************
 *  geometry/CompactSets.v
 *
 *  Copyright 2023 Pieter Collins
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


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Require Import DependentChoice.
Require Import Bool.

Require Export Monads.
Require Export SubMonads.
Require Export LimitMonads.

Require ContinuationMonads.


Section CompactSets.

Notation Continuation := ContinuationMonads.Continuation.
Notation Continuation_Monad := ContinuationMonads.Continuation_Monad.
Notation Cbind := ContinuationMonads.bind.
Notation Cpure := ContinuationMonads.pure.

(*
Inductive Sierpinskian :=
  | sier : (nat -> bool) -> Sierpinskian.
*)

Definition Sierpinskian : Type := nat -> bool.

Fixpoint any_before (seq : nat -> bool) (n : nat) : bool :=
  match n with | O => seq O | S m => orb (any_before seq m) (seq (S m)) end.
Definition Sor (s1 s2 : Sierpinskian) := fun n => orb (any_before s1 n) (any_before s2 n).
Definition Sand (s1 s2 : Sierpinskian) := fun n => andb (any_before s1 n) (any_before s2 n).

Definition OpenSet {A : Type} : Type := A -> Sierpinskian.

Definition is_filter {A} (q : @OpenSet A -> Sierpinskian) : Prop :=
  forall U1 U2 : @OpenSet A,
    q (fun a => Sor (U1 a) (U2 a)) = Sor (q U1) (q U2).
Definition is_cofilter {A} (q : @OpenSet A -> Sierpinskian) : Prop :=
  forall U1 U2 : @OpenSet A,
    q (fun a => Sand (U1 a) (U2 a)) = Sand (q U1) (q U2).


Record CompactSet {A:Type} : Type :=
{
  intersects : @OpenSet A -> Sierpinskian;
  intersects_is_filter : is_filter intersects;
}.

Lemma Cpure_is_filter : forall {A} (a : A),
  is_filter (Cpure a).
Proof.
  unfold is_filter, Cpure.
  reflexivity.
Qed.

Lemma Cbind_is_filter : forall {A B} (F : A -> Continuation Sierpinskian B) (C : Continuation Sierpinskian A),
  (forall a, is_filter (F a)) -> is_filter C -> is_filter (Cbind F C).
Proof.
  unfold is_filter, Cbind.
  intros A B F C HF HC.
  intros V1 V2.
  rewrite <- HC.
  f_equal.
  apply functional_extensionality.
  intro a.
  apply HF.
Qed.


Definition singleton {A : Type} (a : A) : @CompactSet A
  := {| intersects := Cpure a;
        intersects_is_filter := Cpure_is_filter a |}.

Definition image {A B : Type}
   (C : @CompactSet A) (F : A -> @CompactSet B) : @CompactSet B
 := {| intersects := Cbind (fun a => (F a).(intersects)) C.(intersects);
       intersects_is_filter :=
         Cbind_is_filter
           (fun a => (F a).(intersects)) C.(intersects)
           (fun a => (F a).(intersects_is_filter)) C.(intersects_is_filter);
         |}.

Definition CompactSetSubtype {A:Type} : Type
  := @Subtype (Continuation Sierpinskian A) (is_filter).

Instance CompactSetSubtypeMonad : Monad (@CompactSetSubtype) :=
  @Subtype_Monad
    (@Continuation Sierpinskian)
    (@is_filter)
    (@Continuation_Monad Sierpinskian)
    (@Cpure_is_filter)
    (@Cbind_is_filter)
.



Lemma Cpure_is_cofilter : forall {A} (a : A),
  is_cofilter (Cpure a).
Proof.
  unfold is_cofilter, Cpure.
  reflexivity.
Qed.

Lemma Cbind_is_cofilter : forall {A B} (F : A -> (B -> Sierpinskian) -> Sierpinskian) C,
  (forall a, is_cofilter (F a)) -> is_cofilter C -> is_cofilter (Cbind F C).
Proof.
  unfold is_cofilter, Cbind.
  intros A B F C HF HC.
  intros V1 V2.
  rewrite <- HC.
  f_equal.
  apply functional_extensionality.
  intro a.
  apply HF.
Qed.

Definition OvertSetSubtype {A:Type} : Type
  := @Subtype (Continuation Sierpinskian A) (is_cofilter).

Instance OvertSetSubtypeMonad : Monad (@OvertSetSubtype) :=
  @Subtype_Monad
    (@Continuation Sierpinskian)
    (@is_cofilter)
    (@Continuation_Monad Sierpinskian)
    (@Cpure_is_cofilter)
    (@Cbind_is_cofilter)
.


End CompactSets.
