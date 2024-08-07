(******************************************************************************
 *  utilities/LimitMonads.v
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


Require Import Coq.Logic.PropExtensionality.

Require Import Monads.
Require Import DependentChoice.


Section LimitMonads.

Definition lcons {X : Type} : prod (list X) X -> list X :=
  fun xl_x => cons (snd xl_x) (fst xl_x).

Definition is_list_infinite_skew_product {M : Type -> Type} {_ : Monad M} {X : Type}
  (F : (list X) -> M X) (Finf : M (nat -> X)) :=
    (Mlift (proj 0) Finf = Mpure nil) /\
      forall (n:nat),
        Mlift lcons (Mright_skew (Mlift (proj n) Finf) F) =
        Mlift (proj (S n)) Finf.

Definition exists_list_infinite_skew_product (M : Type -> Type) (_ : Monad M) :=
  forall (X : Type) (F : (list X) -> M X),
    exists (Finf : M (nat -> X)),
      is_list_infinite_skew_product F Finf.

Definition has_list_infinite_skew_product (M : Type -> Type) (_ : Monad M) :=
  forall (X : Type) (F : (list X) -> M X),
    sig (fun Finf : M (nat -> X) => is_list_infinite_skew_product F Finf).

Definition list_infinite_skew_product (M : Type -> Type) (Monad_M : Monad M) (H : has_list_infinite_skew_product  M Monad_M)
  {X : Type} (F : (list X) -> M X) : M (nat -> X).
Proof.
  unfold has_list_infinite_skew_product in H.
  specialize (H X F).
  destruct H as [Finf _].
  exact Finf.
Qed.


End LimitMonads.
