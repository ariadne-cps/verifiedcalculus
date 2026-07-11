(******************************************************************************
 *  Numbers/FloatTranscendentals.v
 *
 *  Copyright 2026 Pieter Collins
 *
 ******************************************************************************)

(*
 * This file is part of the Verified Calculus Library.
 *
 * The Verified Calculus Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU General Public License as
(*  * published by the Free Software Foundation, either version 3 of the License, *)
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

From Stdlib Require Import List.

Require Import Numbers.Floats.
Require Import Numbers.Analysis.

Module FT.

Section FloatTranscendentals_section.

Context `{F : Type} `{FltF : Float F}.


Open Scope R_scope.

Notation fact := Factorial.fact.

Notation Rexp := exp.
Notation Rtaylor_exp := taylor_exp.
Notation Rtaylor_exp_succ := taylor_exp_succ.

Fixpoint taylor_exp rnd n x :=
  match n with
  | 0 => F.unit
  | S m => F.add rnd (taylor_exp rnd m x) (F.div rnd (F.pow rnd x (S m)) (F.of_nat (fact (S m))))
  end.

Lemma taylor_exp_succ : forall rnd n x, taylor_exp rnd (S n) x =
 F.add rnd (taylor_exp rnd n x) (F.div rnd (F.pow rnd x (S n)) (F.of_nat (fact (S n)))).
Proof. reflexivity. Qed.

Lemma taylor_exp_rnd_down_spec : forall n x,
  F.injR (taylor_exp down n x) <= Rtaylor_exp n (F.injR x).
Proof.
  intros n x. induction n.
  - simpl. rewrite -> F.unit_spec. now apply Rle_refl.
  - rewrite -> taylor_exp_succ, Rtaylor_exp_succ.
    apply F.add_down_step.
    exact IHn.
    transitivity (F.injR (F.pow down x (S n)) / Rfact (S n)).
    -- replace (Rfact (S n)) with (F.injR (F.of_nat (fact (S n)))).
       apply F.div_down_spec.
       rewrite -> F.ninjr_spec. now apply INR_fact_neq_0.
       rewrite -> F.ninjr_spec. reflexivity.
    -- apply Rdiv_le_compat_r.
       now apply Rfact_pos.
       now apply F.pow_down_spec.
Qed.

Lemma taylor_exp_rnd_up_spec : forall n x,
  F.injR (taylor_exp up n x) >= Rtaylor_exp n (F.injR x).
Proof.
  intros n x. induction n.
  - simpl. rewrite -> F.unit_spec. now apply Rle_refl.
  - rewrite -> taylor_exp_succ, Rtaylor_exp_succ.
    apply Rle_ge; apply F.add_up_step.
    apply Rge_le; exact IHn.
    transitivity (F.injR (F.pow up x (S n)) / Rfact (S n)).
    -- apply Rdiv_le_compat_r.
       now apply Rfact_pos.
       now apply F.pow_up_le_spec.
    -- replace (Rfact (S n)) with (F.injR (F.of_nat (fact (S n)))).
       apply F.div_up_le_spec.
       rewrite -> F.ninjr_spec. now apply INR_fact_neq_0.
       rewrite -> F.ninjr_spec. reflexivity.
Qed.

Definition exp_unit rnd n x :=
  match rnd with
  | down => taylor_exp down n x
  | near => taylor_exp near n x
  | up => F.add up (taylor_exp up n x)
            (F.mul up (F.div up (F.of_nat 3) (F.of_nat (fact (S n)))) (F.pow up x (S n)))
  end.


Lemma sig_log2_up : forall (x : F), { n : nat | (2 : R) ^ n > F.injR (F.abs x) }.
Proof.
  intro x.
  set (y := F.injR (F.abs x)).
  pose proof (INR_unbounded y) as Hy.
  apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat_direct in Hy.
  - destruct Hy as [n Hyn].
    set (m := Nat.log2_up n).
    assert (0 <= m)%nat as H0lem by now apply Nat.le_0_l.
    exists m.
    apply (Rge_gt_trans _ n _).
    -- apply Rle_ge.
       replace (Rpow 2 m) with (INR (Nat.pow 2 m)) by now apply pow_INR.
       apply le_INR.
       destruct (Nat.eq_0_gt_0_cases n).
       --- rewrite -> H; now apply Nat.le_0_l.
       --- unfold m. apply Nat.log2_up_le_pow2. exact H. now apply Nat.le_refl.
    -- assumption.
  - intro n.
    remember (F.leb (F.of_nat n) (F.abs x)) as b.
    destruct b.
    -- right.
       apply Rle_not_gt.
       apply eq_sym in Heqb.
       apply F.leb_spec in Heqb.
       unfold y.
       rewrite <- F.ninjr_spec.
       exact Heqb.
    -- left.
       apply Rlt_gt.
       apply eq_sym, F.leb_false_spec in Heqb.
       unfold y.
       rewrite <- F.ninjr_spec.
       exact Heqb.
Qed.

Close Scope R_scope.

End FloatTranscendentals_section.

End FT.
