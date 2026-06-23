(******************************************************************************
 *  Numbers/FixedDyadicFloat.v
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


From Stdlib Require Import Reals.
From Stdlib Require Import Reals.Rbase.
From Stdlib Require Import Reals.Rfunctions.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rdefinitions.

Require Export RealAddenda.

Require Export FixedDyadic.
Require Export Floats.


#[export]
#[refine]
Instance FixedDyadic_Float (n:nat) : Float (FixedDyadic n) :=
{
  of_nat := W.of_nat n;
  injR := W.injR;
  neg := W.neg;
  abs := W.abs;

  add := W.add;
  sub := W.sub;
  mul := W.mul;
  div := W.div;

  rec := W.rec;

  shft := W.shft;

  min := W.min;
  max := W.max;

  leb := W.leb;
}.
Proof.
  - apply W.injR_correct.
  - apply W.leb_correct.
  - apply W.neg_exact.
  - apply W.abs_exact.
  - apply W.min_exact.
  - apply W.max_exact.
  - intros rnd; destruct rnd.
    -- intros x y; apply Req_le; apply W.add_exact.
    -- intros x y z.
       assert (Hadd := W.add_exact); specialize (Hadd n near x y).
       unfold W.injR in *; simpl in *.
       rewrite -> Hadd; apply Rdist_eq_le.
    -- intros x y; apply Req_ge; apply W.add_exact.
  - intros rnd; destruct rnd.
    -- intros x y; apply Req_le; apply W.sub_exact.
    -- intros x y z.
       assert (Hsub := W.sub_exact); specialize (Hsub n near x y).
       unfold W.injR in *; simpl in *.
       rewrite -> Hsub; apply Rdist_eq_le.
    -- intros x y; apply Req_ge; apply W.sub_exact.
  - intros rnd; destruct rnd.
    -- apply W.mul_down.
    -- apply W.mul_near.
    -- apply W.mul_up.
  - intros rnd; destruct rnd.
    -- apply (W.div_correct n down).
    -- apply (W.div_correct n near).
    -- apply (W.div_correct n up).
  - intros rnd; destruct rnd.
    -- apply (W.rec_correct n down).
    -- apply (W.rec_correct n near).
    -- apply (W.rec_correct n up).
  - intros rnd; destruct rnd.
    -- apply (W.shft_correct n down).
    -- apply (W.shft_correct n near).
    -- apply (W.shft_correct n up).
Qed.

Close Scope Z_scope.
