(******************************************************************************
 *  systems/joint_distribution.v
 *
 *  Copyright 2024 Pieter Collins
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


Require Import Setoid.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Monads.
Require Import LimitMonads.

Lemma Mbind_associative {M} {_ : Monad M} {X Y Z : Type} :
  forall (G : Y -> M Z) (F : X -> M Y) (A : M X), Mbind G (Mbind F A) = Mbind (fun x => Mbind G (F x)) A.
Proof. intros. now apply Massociativity. Qed.
Lemma Mlift_associative {M} {_ : Monad M} {X Y Z : Type} :
  forall (g : Y -> Z) (f : X -> Y) (A : M X), Mlift g (Mlift f A) = Mlift (fun x => g (f x)) A.
Proof. intros. unfold Mlift. rewrite -> Massociativity. apply Mbind_extensional; intro x. now rewrite -> Mleft_identity. Qed.
Lemma Mlift_bind_associative {M} {_ : Monad M} {X Y Z : Type} : 
  forall (A : M X) (F : X -> M Y) (g : Y -> Z), Mlift g (Mbind F A) = Mbind (fun x => Mlift g (F x)) A.
Proof. intros. unfold Mlift. now apply Massociativity. Qed.
Lemma Mbind_lift_associative {M} {_ : Monad M} {X Y Z : Type} : 
  forall (A : M X) (f : X -> Y) (G : Y -> M Z), Mbind G (Mlift f A) = Mbind (fun x => G (f x)) A.
Proof. intros. unfold Mlift. rewrite -> Massociativity. apply Mbind_extensional; intro x. now rewrite -> Mleft_identity. Qed.




Context `{M : Type -> Type } `{Monad_M : Monad M}
  `{preserves_constants_M : @preserves_constants M Monad_M}.

Definition Mproduct {X1 X2} : M X1 -> M X2 -> M (X1*X2) := @Mright_product M Monad_M X1 X2.


Variable (X Y Z : Type).
Variable (e : M X) (f : X -> M Y) (g : (X*Y) -> M Z) (h : Y -> M (X * Z)).

Definition ef : M (X*Y) := Mbind (fun x => Mlift (fun y=>(x,y)) (f x)) e.
Definition efg : M (X*Y*Z) := Mbind (fun xy => Mlift (fun z=>(xy,z)) (g xy)) ef.

Definition fh : M (X*Y*Z) := Mbind (fun xy => Mlift (fun xz => (xy, snd xz)) (h (snd xy))) ef.
Axiom ghy : forall y : Y, Mbind (fun x => Mlift (fun z => (x,z)) (g (x,y))) e = h y.

Proposition compute_joint_distribution : efg = fh.
Proof.
  unfold efg, fh, ef.
  rewrite -> Mbind_associative.
  rewrite -> Mbind_associative.
  assert ( forall x, Mbind (fun xy : X * Y => Mlift (fun z : Z => (xy, z)) (g xy)) (Mlift (fun y : Y => (x, y)) (f x))
            = Mbind (fun xy : X * Y => Mlift (fun xz : X * Z => (xy, snd xz)) (h (snd xy))) (Mlift (fun y : Y => (x, y)) (f x)) ).
  - intro x.
    rewrite -> Mbind_lift_associative.
 
	   rewrite -> Mbind_lift_associative.
    apply Mbind_extensional; intro y.
    simpl. rewrite <- ghy.
    symmetry; rewrite <- Mlift_associative; symmetry.
    rewrite -> Mlift_bind_associative.
    rewrite -> Mbind_extensional with (F' := fun x' : X => g (x',y)).
  2: { intro x'. rewrite -> Mlift_associative. 
       rewrite <- Mlift_extensional with (f := fun z : Z => z) by trivial.
       now rewrite -> Mlift_identity. }
    f_equal.
    apply Mbind_extensional; intro x.
  (* NOT TRUE; ABORT *)
Admitted.


