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

From Stdlib Require Logic.FunctionalExtensionality.

Require Sierpinskian.
Require Import OpenSets.

Require Import DependentChoice.

(*
Require Export Monads.
Require Export SubMonads.
Require Export LimitMonads.
*)
Require Export Monads.
Require Export ContinuationMonads.

Notation N := nat.
Notation Strue := Sierpinskian.true.
Notation Sand := Sierpinskian.and.
Notation Sor := Sierpinskian.or.
Notation Sdisj := Sierpinskian.disj.
Notation Sierpinskian := Sierpinskian.Sierpinskian.
Notation S := Sierpinskian.
Infix "==" := Sierpinskian.eqv (at level 70, no associativity).


Module CompactSets.

Notation Continuation := ContinuationMonads.Continuation.
Notation Continuation_Monad := ContinuationMonads.Continuation_Monad.
Notation Cbind := ContinuationMonads.bind.
Notation Cpure := ContinuationMonads.pure.


Import OpenSets.

Definition compact_respectful {X} (c : OpenSet X -> S) : Prop := 
  forall U1 U2, (forall x, U1 x == U2 x) -> c U1 == c U2.

Definition compact_proper {X} (c : OpenSet X -> S) : Prop := 
  forall U1 U2, Sierpinskian.eqv (c (intersection U1 U2)) (Sand (c U1) (c U2)).

Definition CompactSet (X : Set) : Set :=
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


Print Cpure.

Definition is_filter {A} (q : (A -> Sierpinskian) -> Sierpinskian) : Prop :=
  forall U1 U2 : A -> Sierpinskian,
    q (fun a => Sor (U1 a) (U2 a)) == Sor (q U1) (q U2).

Definition is_cofilter {A} (q : @OpenSet A -> Sierpinskian) : Prop :=
  forall U1 U2 : @OpenSet A,
    q (fun a => Sand (U1 a) (U2 a)) == Sand (q U1) (q U2).


Definition singleton_op {A : Set} (a : A) : OpenSet A -> Sierpinskian := 
  fun U => U a.

Lemma singleton_is_respectful : forall {A : Set} (a : A),
  compact_respectful (singleton_op a).
Proof.
  unfold compact_respectful, singleton_op.
  intros A a U1 U2 H. exact (H a).
Qed.

Lemma singleton_is_proper : forall {A : Set} (a : A),
  compact_proper (singleton_op a).
Proof.
  unfold compact_proper, singleton_op, Ointersection.
  intros A a U1 U2. reflexivity.
Qed.

Definition singleton {A : Set} (a : A) : @CompactSet A
  := mkCompactSet (singleton_op a) (singleton_is_respectful  a) (singleton_is_proper a).


Definition image_op {A B : Set}
   (C : OpenSet A -> Sierpinskian) (F : A -> OpenSet B -> Sierpinskian) : OpenSet B -> Sierpinskian
 := fun V => C (fun a => F a V).

Lemma image_is_respectful {A B : Set} : forall {C : OpenSet A -> Sierpinskian} {F : A -> OpenSet B -> Sierpinskian},
  compact_respectful C -> (forall a, compact_respectful (F a)) -> compact_respectful (image_op C F).
Proof.
  unfold Cbind, compact_respectful.
  intros C F HC HF U1 U2 HU.
  apply HC.
  intros x.
  apply HF.
  intro y.
  exact (HU y).
Qed.

Lemma image_is_proper {A B : Set} : forall {C : OpenSet A -> Sierpinskian} {F : A -> OpenSet B -> Sierpinskian},
   compact_respectful C -> compact_proper C -> (forall a, compact_proper (F a))-> compact_proper (image_op C F).
Proof.
  unfold compact_proper, image_op.
  intros C F HR HC HF.
  intros V1 V2.
  rewrite <- HC.
  apply HR.
  intro a.
  now apply HF.
Qed.

Definition image {A B : Set} (C : CompactSet A) (F : A -> CompactSet B) : CompactSet B
  := mkCompactSet (image_op (proj1_sig C) (fun a => proj1_sig (F a)))
       (image_is_respectful (proj1 (proj2_sig C)) (fun a => proj1 (proj2_sig (F a))))
       (image_is_proper (proj1 (proj2_sig C)) (proj2 (proj2_sig C)) (fun a => proj2 (proj2_sig (F a)))).



Lemma cpure_is_respectful {A : Set} (a : A) : compact_respectful (Cpure a).
Proof.
  unfold compact_respectful, Cpure.
  intros U1 U2 H. exact (H a).
Qed.

Lemma cpure_is_filter {A : Set} (a : A) : is_filter (Cpure A).
Proof.
  unfold is_filter, Cpure.
  intros U1 U2.
  reflexivity.
Qed.
  
Lemma cbind_is_respectful : forall {A B : Set} (F : A -> Continuation Sierpinskian B) (C : Continuation Sierpinskian A),
  (forall a, compact_respectful (F a)) -> compact_respectful C -> compact_respectful (Cbind F C).
Proof.
  unfold Cbind, compact_respectful.
  intros A B F C HF HC U1 U2 HU.
  apply HC.
  intros x.
  apply HF.
  intro y.
  now apply HU.
Qed.

Lemma cbind_is_filter : forall {A B : Set} (F : A -> Continuation Sierpinskian B) (C : Continuation Sierpinskian A),
  (compact_respectful C) -> (forall a, is_filter (F a)) -> is_filter C -> is_filter (Cbind F C).
Proof.
  unfold compact_respectful, is_filter, Cbind.
  intros A B F C HR HF HC.
  intros V1 V2.
  rewrite <- HC.
  apply HR. 
  intro a.
  now apply HF.
Qed.


Class SetMonad (M : Set -> Set) :=
{
    (* monad has pure and bind *)
    SMpure : forall {A : Set}, A -> M A;
    SMbind : forall {A B : Set}, (A -> M B) -> M A -> M B;

    (* coherence conditions *)
    SMleft_identity : forall {A B : Set} (f:A->M B) (a:A), SMbind f (SMpure a) = f a;
    SMright_identity : forall {A} (x : M A), SMbind (@SMpure A) x = x;
    SMassociativity : forall {A B C} (x : M A) (f : A -> M B) (g : B -> M C),
        SMbind g (SMbind f x) = SMbind (fun a => SMbind g (f a)) x;

    (* Mfunctor_map : forall {A B : Set}, (A -> B) -> M A -> M B; *)
    SMfunctor_map {A B : Set} : (A -> B) -> M A -> M B
      := fun (f : A -> B) (x : M A) => SMbind (fun x' => SMpure (f x')) x;
    SMlift {A B : Set} (f : A -> B) (a : M A) : M B
      := SMbind (fun a' => SMpure (f a')) a;

   SMleft_product {X Y} : M X -> M Y -> (M (prod X Y)) :=
      fun (mu : M X) (nu : M Y) => SMbind ( fun y => ( SMbind (fun x => SMpure (pair x y)) mu ) ) nu;
   SMright_product {A B} : M A -> M B -> M (prod A B)
      := fun mu nu => SMbind ( fun x => ( SMbind (fun y => SMpure (pair x y)) nu ) ) mu;
}.

Print SetMonad.

Definition bind {A B : Set} (F : A -> CompactSet B) (C : CompactSet A) : CompactSet B :=
  @image A B C F.

Print Build_SetMonad.


Lemma compact_set_equal {A} : forall C1 C2 : CompactSet A, proj1_sig C1 = proj1_sig C2 -> C1 = C2.
Proof.
  unfold CompactSet.
  intros C1 C2 H. destruct C1; destruct C2.
  simpl in H.
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  exact H.
Qed.

  

#[global]
Instance CompactSetMonad : SetMonad (CompactSet).
Proof.
  apply (Build_SetMonad CompactSet (@singleton) (@bind)).
  - intros A B F a; unfold bind, singleton, image, mkCompactSet; simpl.
    apply compact_set_equal; simpl.
    unfold image_op, singleton_op; simpl.
    apply FunctionalExtensionality.functional_extensionality.
    intro V.
    reflexivity.
  - intros A C; unfold bind, singleton, mkCompactSet; simpl.
    apply compact_set_equal; simpl.
    unfold image_op, singleton_op; simpl.
    apply FunctionalExtensionality.functional_extensionality.
    intro U.
    f_equal.    
  - admit.
Admitted.


(*
Definition image {A B : Type}
   (C : @CompactSet A) (F : A -> @CompactSet B) : @CompactSet B
 := mkCompactSet (Cbind (fun a => (F a).(intersects)) C.(intersects);
 := {| intersects := Cbind (fun a => (F a).(intersects)) C.(intersects);
       intersects_is_filter :=
         Cbind_is_filter
           (fun a => (F a).(intersects)) C.(intersects)
           (fun a => (F a).(intersects_is_filter)) C.(intersects_is_filter);
         |}.
*)

Instance CompactSetMonad {A:Set} : Monad (@CompactSet).
  := @Subtype (Continuation Sierpinskian A) (is_filter).

Instance CompactSetSubtypeMonad : Monad (@CompactSetSubtype) :=
  @Subtype_Monad
    (@Continuation Sierpinskian)
    (@is_filter)
    (@Continuation_Monad Sierpinskian)
    (@cpure_is_filter)
    (@cbind_is_filter)
.




Definition CompactSetSubtype {A:Type} : Type
  := @Subtype (Continuation Sierpinskian A) (is_filter).

Instance CompactSetSubtypeMonad : Monad (@CompactSetSubtype) :=
  @Subtype_Monad
    (@Continuation Sierpinskian)
    (@is_filter)
    (@Continuation_Monad Sierpinskian)
    (@cpure_is_filter)
    (@cbind_is_filter)
.



End CompactSets.
