(******************************************************************************
 * Copyright 2023 Pieter Collins
 *
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
 ******************************************************************************)


Require Import Floats.


Require Export QArith.
Require Export QArith.Qabs.
Require Export QArith.Qminmax.
Require Export QArith.Qreals.

Open Scope Q_scope.



Lemma Qleb : forall q1 q2 : Q, Qle_bool q1 q2 = true <-> Rle (Q2R q1) (Q2R q2).
Proof.
  intros q1 q2.
  apply iff_trans with (B:=(Qle q1 q2)).
  - apply Qle_bool_iff.
  - split. apply Qle_Rle. apply Rle_Qle.
Qed.


Definition INQ := fun n => Qmake (Z.of_nat n) 1.

Lemma plus_INQ : forall n1 n2 : nat, (INQ n1) + (INQ n2) == INQ (n1 + n2).
Proof.
  intros n1 n2.
  unfold INQ.
  assert (Zplus (Z.of_nat n1) (Z.of_nat n2) = Z.of_nat (n1 + n2)) as Hn. {
    apply eq_sym. apply Nat2Z.inj_add.
  }
  rewrite <- Hn.
  apply Qinv_plus_distr.
Qed.

Lemma mult_INQ : forall n1 n2 : nat, (INQ n1) * (INQ n2) == INQ (n1 * n2).
Proof.
  intros n1 n2.
  unfold INQ.
  assert (Zmult (Z.of_nat n1) (Z.of_nat n2) = Z.of_nat (n1 * n2)) as Hn. {
    apply eq_sym. apply Nat2Z.inj_mul.
  }
  rewrite <- Hn.
  unfold Qmult. unfold Qeq.
  unfold Qnum. unfold Qden.
  f_equal.
Qed.

(*
plus_INR: forall n m : nat, INR (n + m) = (INR n + INR m)%R
Q2R_plus : forall x y : Q, Q2R (x + y) = (Q2R x + Q2R y)%R
*)

Lemma INQ_0 : INQ 0%nat == 0%Q.
Proof.
  rewrite <- (Qplus_0_r (INQ 0)).
  rewrite <- (Qplus_opp_r (INQ 0)).
  rewrite -> Qplus_assoc.
  rewrite -> Qplus_opp_r.
  rewrite -> plus_INQ.
  rewrite -> Nat.add_0_r.
  rewrite -> Qplus_opp_r.
  reflexivity.
Qed.

Lemma INQ_1 : INQ 1%nat == 1%Q.
Proof.
  assert (~ 1%Q == 0%Q) as H1ne0. { discriminate. }
  rewrite <- (Qmult_1_r (INQ 1)).
  rewrite <- (Qmult_inv_r (INQ 1)) by (apply H1ne0).
  rewrite -> Qmult_assoc.
  rewrite -> mult_INQ.
  rewrite -> Nat.mul_1_r.
  reflexivity.
Qed.

Definition Q2R_0 := RMicromega.Q2R_0.
Definition Q2R_1 := RMicromega.Q2R_1.

Lemma Q2R_neq_0 : forall q, Q2R q <> 0%R -> ~(q == 0%Q).
Proof.
  intros s Hneq Heqv.
  apply Qeq_eqR in Heqv.
  rewrite -> Q2R_0 in Heqv.
  contradiction.
Qed.


Lemma Qnijnr : forall n : nat, Q2R (INQ n) = INR n.
Proof.
  intro n.
  induction n.
  - rewrite -> INQ_0. apply Q2R_0.
  - replace (S n) with (n + 1)%nat by (apply Nat.add_1_r).
    rewrite <- plus_INQ.
    rewrite -> Q2R_plus.
    rewrite -> IHn.
    rewrite -> INQ_1.
    rewrite -> Q2R_1.
    rewrite -> plus_INR.
    rewrite -> INR_1.
    reflexivity.
Qed.


Lemma Qle_total : forall q1 q2 : Q, q1 <= q2 \/ q2 <= q1.
Proof.
  intros q1 q2.
  apply or_impl_compat with (p1:=q1<q2) (p2:=q1==q2\/q2<q1).
  - apply Qlt_le_weak.
  - (* For some reason, can't apply Qeq_sym directly *)
    intros H. apply Qle_lteq. destruct H.
    -- right. apply Qeq_sym. exact H.
    -- left. exact H.
  -  apply Q.OT.lt_total.
Qed.

Lemma Qabs_Rabs : forall q : Q, Q2R (Qabs q) = Rabs (Q2R q).
Proof.
  intro q.
  apply or_ind with (A:=0<=q) (B:=q<=0).
  - intro Hq.
    assert (Rle 0 (Q2R q)) as Hr. { rewrite <- Q2R_0. apply (Qle_Rle). exact Hq. }
    rewrite Qabs_pos by (exact Hq). rewrite Rabs_pos_eq by (exact Hr). reflexivity.
  - intro Hq.
    assert (Rle (Q2R q) 0) as Hr. { rewrite <- Q2R_0. apply (Qle_Rle). exact Hq. }
    rewrite Qabs_neg by (exact Hq). { rewrite Rabs_neg_eq by (exact Hr). apply Q2R_opp. }
  - apply Qle_total.
Qed.


Lemma Qmax_Rmax : forall q1 q2 : Q, Q2R (Qmax q1 q2) = Rmax (Q2R q1) (Q2R q2).
Proof.
  intros q1 q2.
  apply or_ind with (A:=q1<=q2) (B:=q2<=q1).
  - intro Hq.
    assert (Rle (Q2R q1) (Q2R q2)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.max_r by (exact Hq). rewrite Rmax_right by (exact Hr). reflexivity.
  - intro Hq.
    assert (Rle (Q2R q2) (Q2R q1)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.max_l by (exact Hq). { rewrite Rmax_left by (exact Hr). reflexivity. }
  - apply Qle_total.
Qed.

Lemma Qmin_Rmin : forall q1 q2 : Q, Q2R (Qmin q1 q2) = Rmin (Q2R q1) (Q2R q2).
Proof.
  intros q1 q2.
  apply or_ind with (A:=q1<=q2) (B:=q2<=q1).
  - intro Hq.
    assert (Rle (Q2R q1) (Q2R q2)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.min_l by (exact Hq). rewrite Rmin_left by (exact Hr). reflexivity.
  - intro Hq.
    assert (Rle (Q2R q2) (Q2R q1)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.min_r by (exact Hq). { rewrite Rmin_right by (exact Hr). reflexivity. }
  - apply Qle_total.
Qed.



#[refine]
Instance Rational_Float : Float Q :=
{
  NinjF := (fun n => Qmake (Z.of_nat n) 1);
  FinjR := (fun q => Q2R q);
  Fneg := Qopp;
  Fabs := Qabs;

  Fadd := (fun (r:Rounding) q1 q2 => Qplus q1 q2);
  Fsub := (fun (r:Rounding) q1 q2 => Qminus q1 q2);
  Fmul := (fun (r:Rounding) q1 q2 => Qmult q1 q2);
  Fdiv := (fun (r:Rounding) q1 q2 => Qdiv q1 q2);

  Frec := (fun (r:Rounding) q => Qinv q);

  Fmin := Qmin;
  Fmax := Qmax;

  Fleb := Qle_bool;

  flt_ninjr := Qnijnr;

  flt_leb := Qleb;

  flt_neg_exact := Q2R_opp;
  flt_abs_exact := Qabs_Rabs;
  flt_min_exact := Qmin_Rmin;
  flt_max_exact := Qmax_Rmax;
}.
Proof.
 - (* add rounded *)
    intros rnd x1 x2.
    destruct rnd; rewrite <- Q2R_plus.
    -- apply Req_ge; reflexivity.
    -- intro z; unfold Rdist; rewrite -> Rminus_eq_0; rewrite -> Rabs_R0; apply Rabs_pos.
    -- apply Req_ge; reflexivity.
 - (* sub rounded *)
    intros rnd x1 x2.
    destruct rnd; rewrite <- Q2R_minus.
    -- apply Req_ge; reflexivity.
    -- intro z; unfold Rdist; rewrite -> Rminus_eq_0; rewrite -> Rabs_R0; apply Rabs_pos.
    -- apply Req_ge; reflexivity.
 - (* mul rounded *)
    intros rnd x1 x2.
    destruct rnd; rewrite <- Q2R_mult.
    -- apply Req_ge; reflexivity.
    -- intro z; unfold Rdist; rewrite -> Rminus_eq_0; rewrite -> Rabs_R0; apply Rabs_pos.
    -- apply Req_ge; reflexivity.
 - (* div rounded *)
    intros rnd x1 x2 Hx2.
    destruct rnd; rewrite <- Q2R_div by (exact (Q2R_neq_0 x2 Hx2)).
    -- apply Req_ge; reflexivity.
    -- intro z; unfold Rdist; rewrite -> Rminus_eq_0; rewrite -> Rabs_R0; apply Rabs_pos.
    -- apply Req_ge; reflexivity.
 - (* rec rounded *)
    intros rnd x Hx.
    destruct rnd; rewrite <- Q2R_inv by (exact (Q2R_neq_0 x Hx)).
    -- apply Req_ge; reflexivity.
    -- intro z; unfold Rdist; rewrite -> Rminus_eq_0; rewrite -> Rabs_R0; apply Rabs_pos.
    -- apply Req_ge; reflexivity.
Qed.
