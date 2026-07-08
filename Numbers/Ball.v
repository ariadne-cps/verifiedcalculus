(******************************************************************************
 *  Numbers/Ball.v
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
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

Require Import RealAddenda.
Require Import Floats.
Require Import Calculus.
Require Import Analysis.
Require Import Bounds.

Module Bll.

Inductive Ball {F:Type} {FltF : Float F} :=
  ball (value:F) (error:F).

Arguments Ball (F) {FltF}.

Check ball.


Section Ball_section.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.

Definition value (x : @Ball F FltF) : F := match x with ball v _ => v end.
Definition error (x : @Ball F FltF) : F := match x with ball _ e => e end.

Definition models : Ball F -> R -> Prop :=
  fun x y => match x with ball v e => Rdist (F.injR v) y <= (F.injR e) end.


Ltac step mid := (apply Rle_trans with mid).

Open Scope R_scope.

Lemma Fadd_up_le_compat : forall w1 x1 w2 x2,
  w1 <= F.injR x1 -> w2 <= F.injR x2 -> (w1 + w2) <= F.injR (F.add up x1 x2).
Proof.
  intros w1 x1 w2 x2 H1 H2.
  step (F.injR x1 + F.injR x2).
  apply Rplus_le_compat; [exact H1|exact H2].
  apply Rge_le; apply F.add_up_spec.
Qed.

Lemma Fadd_up_le_compat_l : forall x1 w2 x2,
  w2 <= F.injR x2 -> (F.injR x1 + w2) <= F.injR (F.add up x1 x2).
Proof.
  intros x1 w2 x2 H2. apply (Fadd_up_le_compat (F.injR x1) x1 w2 x2). apply Rle_refl. exact H2.
Qed.

Lemma Fadd_up_le_compat_r : forall w1 x1 x2,
  w1 <= F.injR x1 -> (w1 + F.injR x2) <= F.injR (F.add up x1 x2).
Proof.
  intros w1 x1 x2 H1. apply (Fadd_up_le_compat w1 x1 (F.injR x2) x2). apply H1. apply Rle_refl.
Qed.

Local Lemma Fmul_up_le_compat : forall w1 x1 w2 x2,
  0 <= w1 -> 0 <= w2 -> w1 <= F.injR x1 -> w2 <= F.injR x2
    -> (w1 * w2) <= F.injR (F.mul up x1 x2).
Proof.
  intros w1 x1 w2 x2 Hw1 Hw2 H1 H2.
  step (F.injR x1 * F.injR x2).
  apply Rmult_le_compat; [exact Hw1 | exact Hw2 | exact H1 | exact H2].
  apply F.mul_up_le_spec.
Qed.

Local Lemma Fmul_up_le_compat_l : forall x1 w2 x2,
  0 <= F.injR x1 -> 0 <= w2 -> w2 <= F.injR x2
    -> (F.injR x1 * w2) <= F.injR (F.mul up x1 x2).
Proof.
  intros x1 w2 x2 Hx1 Hw2 H2.
  apply (Fmul_up_le_compat (F.injR x1) x1 w2 x2).
  exact Hx1. exact Hw2. apply Rle_refl. exact H2.
Qed.

Local Lemma Fmul_up_le_compat_r : forall w1 x1 x2,
  0 <= w1 -> 0 <= F.injR x2 -> w1 <= F.injR x1
    -> (w1 * F.injR x2) <= F.injR (F.mul up x1 x2).
Proof.
  intros w1 x1 x2 Hw1 Hx2 H1.
  apply (Fmul_up_le_compat w1 x1 (F.injR x2) x2).
  exact Hw1. exact Hx2. exact H1. apply Rle_refl.
Qed.


Local Lemma Fdiv_up_le_compat : forall w1 x1 w2 x2,
  0 <= w1 -> 0 < F.injR x2 -> w1 <= F.injR x1 -> F.injR x2 <= w2 ->
    (w1 / w2) <= F.injR (F.div up x1 x2).
Proof.
  intros w1 x1 w2 x2 Hw1 Hx2 H1 H2.
  assert (F.injR x2<>0) as Hx2n; [exact (not_eq_sym (Rlt_not_eq _ _ Hx2))|].
  assert (0<w2) as Hw2; [exact (Rlt_le_trans _ _ _ Hx2 H2)|].
  assert (0<=/w2) as Hrw2; [exact (Rlt_le _ _ (Rinv_0_lt_compat _ Hw2))|].
  assert (/w2<=/F.injR x2) as Hr2; [exact (Rinv_le_contravar _ _ Hx2 H2)|].
  step (F.injR x1 / F.injR x2).
  unfold Rdiv. apply Rmult_le_compat; [exact Hw1|exact Hrw2|exact H1|exact Hr2].
  apply Rge_le. apply F.div_up_spec. exact Hx2n.
Qed.


Definition of_nat (n : nat) : Ball F := ball (F.of_nat n) F.null.

Lemma of_nat_correct : forall n, models (of_nat n) (INR n).
Proof.
  intros n. unfold models, of_nat.
  rewrite -> F.null_spec, F.ninjr_spec, Rdist_eq.
  exact (Rle_refl 0).
Qed.


Definition neg : Ball F -> Ball F :=
  fun x => match x with ball v e => ball (F.neg v) e end.

Lemma neg_correct :
  forall (x : Ball F) (y : R),
    models x y -> models (neg x) (-y).
Proof.
  intros x y H.
  destruct x as (v & e).
  unfold models in H;
  unfold models; unfold neg.
  rewrite -> F.neg_exact_spec.
  unfold Rdist in *.
  rewrite -> Rminus_def, <- Ropp_plus_distr, -> Rabs_Ropp.
  exact H.
Qed.


Definition add : Ball F -> Ball F -> Ball F :=
  fun x1 x2 =>
    match x1 with ball v1 e1
      => match x2 with ball v2 e2
        => ball (F.add near v1 v2) (F.add up (F.div2 up (F.sub up (F.add up v1 v2) (F.add down v1 v2))) (F.add up e1 e2)) end end.

Lemma add_correct :
  forall (x1 x2 : Ball F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (add x1 x2) (y1+y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (v1 & e1), x2 as (v2 & e2).
  unfold models in H1,H2;
  unfold models; unfold add.
  set (v12 := F.add near v1 v2).
  set (w12 := F.injR v1 + F.injR v2).
  set (y12 := y1 + y2).
  set (re12 := F.div2 up (F.sub up (F.add up v1 v2) (F.add down v1 v2))).
  assert (Rdist (F.injR v12) w12 <= F.injR re12) as Hre. {
    unfold v12,w12,re12.
    replace F.add with (F.apply Add) by (trivial).
    apply F.op_near_up_down_sub_hlf_up_spec.
  }
  assert (Rdist w12 y12 <= F.injR e1 + F.injR e2) as Hy. {
    unfold w12,y12.
    apply Rle_trans with (Rdist (F.injR v1) y1 + Rdist (F.injR v2) y2).
    - apply Rdist_plus_compat.
    - apply Rplus_le_compat. exact H1. exact H2.
  }
  step (Rdist (F.injR v12) w12 + Rdist w12 y12).
    apply Rdist_triang.
  step (F.injR re12 + F.injR (F.add up e1 e2)).
  - apply Rplus_le_compat.
    -- apply Hre.
    -- step (F.injR e1 + F.injR e2). exact Hy. apply F.add_up_le_spec.
  - apply F.add_up_le_spec.
Qed.


Definition sub (x1 x2 : Ball F) : Ball F :=
  match x1 with ball v1 e1 => match x2 with ball v2 e2
    => ball (F.sub near v1 v2) (F.add up (F.div2 up (F.sub up (F.sub up v1 v2) (F.sub down v1 v2))) (F.add up e1 e2)) end end.

Lemma sub_correct :
  forall (x1 x2 : Ball F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (sub x1 x2) (y1-y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (v1 & e1), x2 as (v2 & e2).
  unfold models in H1,H2;
  unfold models; unfold add.
  set (v12 := F.sub near v1 v2).
  set (w12 := F.injR v1 - F.injR v2).
  set (y12 := y1 - y2).
  set (re12 := F.div2 up (F.sub up (F.sub up v1 v2) (F.sub down v1 v2))).
  assert (Rdist (F.injR v12) w12 <= F.injR re12) as Hre. {
    unfold v12,w12,re12.
    replace F.sub with (F.apply Sub) by (trivial).
    apply F.op_near_up_down_sub_hlf_up_spec.
  }
  assert (Rdist w12 y12 <= F.injR e1 + F.injR e2) as Hy. {
    unfold w12,y12.
    apply Rle_trans with (Rdist (F.injR v1) y1 + Rdist (F.injR v2) y2).
    - apply Rdist_minus_compat.
    - apply Rplus_le_compat. exact H1. exact H2.
  }
  step (Rdist (F.injR v12) w12 + Rdist w12 y12).
    apply Rdist_triang.
  step (F.injR re12 + F.injR (F.add up e1 e2)).
  - apply Rplus_le_compat.
    -- apply Hre.
    -- step (F.injR e1 + F.injR e2). exact Hy. apply F.add_up_le_spec.
  - apply F.add_up_le_spec.
Qed.


Definition Fmul_err_up v1 v2 e1 e2 re :=
  F.add up (F.add up re (F.mul up e1 e2))
          (F.add up (F.mul up (F.abs v1) e2) (F.mul up e1 (F.abs v2))).

Lemma Fmul_err_up_correct : forall v1 v2 e1 e2 re,
  mul_err (F.injR v1) (F.injR v2) (F.injR e1) (F.injR e2) + (F.injR re)
    <= F.injR (Fmul_err_up v1 v2 e1 e2 re).
Proof.
  intros v1 v2 e1 e2 re.
    unfold mul_err,Fmul_err_up.
  stepl ( (F.injR re + (F.injR e1) * (F.injR e2)) + (Rabs (F.injR v1)*F.injR e2 + F.injR e1 * Rabs (F.injR v2)) ) by ring.
  apply Fadd_up_le_compat.
  - apply Fadd_up_le_compat_l.
    apply F.mul_up_le_spec.
  - repeat (rewrite <- F.abs_exact_spec).
    apply Fadd_up_le_compat.
    -- apply F.mul_up_le_spec.
    -- apply F.mul_up_le_spec.
Qed.

Definition mul (x1 x2 : Ball F) : Ball F :=
  match x1 with ball v1 e1 =>
    match x2 with ball v2 e2 =>
     let v12 := (F.mul near v1 v2) in
       let re12 := (F.div2 up (F.sub up (F.mul up v1 v2) (F.mul down v1 v2))) in
         ball v12 (Fmul_err_up v1 v2 e1 e2 re12)
    end
  end
.

Lemma mul_correct :
  forall (x1 x2 : Ball F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (mul x1 x2) (y1*y2).
Proof.
  intros x1 x2 y1 y2.
  destruct x1 as (v1 & e1), x2 as (v2 & e2).
  unfold mul, models in *.
  set (v12 := F.mul near v1 v2).
  set (w1:=F.injR v1); set (w2:=F.injR v2).
  set (w12 := w1 * w2).
  set (y12 := y1 * y2).
  set (re12 := F.div2 up (F.sub up (F.mul up v1 v2) (F.mul down v1 v2))).
  intros H1 H2.
  assert (Rdist (F.injR v12) w12 <= F.injR re12) as Hre. {
    unfold v12,w12,re12.
    replace F.mul with (F.apply Mul) by trivial.
    apply F.op_near_up_down_sub_hlf_up_spec.
  }
  assert (Rdist w12 y12 <= mul_err w1 w2 (F.injR e1) (F.injR e2)) as Hae. {
    apply mul_err_correct. exact H1. exact H2.
  }
  assert (mul_err w1 w2 (F.injR e1) (F.injR e2) + F.injR re12 <= F.injR (Fmul_err_up v1 v2 e1 e2 re12)) as Hme. {
    apply Fmul_err_up_correct.
  }
  1: step (Rdist (F.injR v12) w12 + Rdist w12 y12).
  2: step (mul_err w1 w2 (F.injR e1) (F.injR e2) + F.injR re12).
  - apply Rdist_triang.
  - rewrite -> Rplus_comm. apply Rplus_le_compat. exact Hae. exact Hre.
  - exact Hme.
Qed.


Definition div_err_up v1 v2 e1 e2 re :=
  F.add up re (F.div up (F.add up e1 (F.mul up e2 (F.div up (F.abs v1) (F.abs v2)))) (F.sub down (F.abs v2) e2)).

Definition div_defined (v1 v2 e1 e2 : F) :=
  0 < F.injR (F.sub down (F.abs v2) e2).

Lemma div_nonzero : forall v1 v2 e1 e2,
  div_defined v1 v2 e1 e2 -> 0 <= F.injR e2 -> F.injR e2 < F.injR (F.abs v2).
Proof.
  unfold div_defined.
  intros _ v _ e H He.
  apply Rlt_zero_Rminus.
  apply Rlt_le_trans with (F.injR (F.sub down (F.abs v) e)).
  exact H.
  apply F.sub_down_spec.
Qed.

Lemma Rminus_ge_0 : forall a b, 0<=b -> a-b <= a.
Proof.
  intros a b Hb.
  assert (a-b <= a-0).
  apply Rplus_le_compat_l; apply Ropp_le_contravar; exact Hb.
  rewrite -> Rminus_0_r in H; assumption.
Qed.

Lemma div_err_up_correct : forall v1 v2 e1 e2 re,
  0<=F.injR e1 ->
    0<=F.injR e2 ->
      0 < F.injR (F.sub down (F.abs v2) e2) ->
        div_err (F.injR v1) (F.injR v2) (F.injR e1) (F.injR e2) + (F.injR re)
          <= F.injR (div_err_up v1 v2 e1 e2 re).
Proof.
  intros v1 v2 e1 e2 re He1 He2 Hr.
  assert (0<F.injR (F.abs v2)) as Hav2. {
    apply Rlt_le_trans with (F.injR (F.sub down (F.abs v2) e2)); [exact Hr|].
    apply Rle_trans with (F.injR (F.abs v2) - F.injR e2); [apply F.sub_down_spec|].
    apply Rminus_ge_0; [exact He2].
  }
  assert (0<Rabs (F.injR v2) - F.injR e2) as Hrw. {
    apply (Rlt_le_trans _ _ _ Hr). rewrite <- F.abs_exact_spec. apply F.sub_down_spec. }
  assert (F.injR (F.abs v2)<>0) as Hav2ne0. {
     apply not_eq_sym. apply Rlt_not_eq. exact Hav2. }
  assert (F.injR v2<>0) as Hv2ne0. {
    apply Rabs_0_neq. rewrite <- F.abs_exact_spec. exact Hav2ne0. }
  assert (Rabs (F.injR v2)<>0) as Haw2ne0. {
     rewrite <- F.abs_exact_spec. exact Hav2ne0. }
  assert (0</Rabs (F.injR v2)) as Hraw2. {
    apply Rinv_pos. rewrite <- F.abs_exact_spec. exact Hav2. }
  unfold div_err,div_err_up, div_defined.
  rewrite -> Rplus_comm.
  apply Fadd_up_le_compat_l.
  rewrite <- Rdiv_Rdiv_Rmult_numerator;
    [|exact Haw2ne0|apply not_eq_sym; apply Rlt_not_eq; apply Hrw].
  apply Fdiv_up_le_compat.
  - unfold Rdiv. apply Rle_mult_nonneg_nonneg; [|exact (Rlt_le _ _ Hraw2)].
    apply Rplus_le_le_0_compat; apply Rle_mult_nonneg_nonneg;
      [exact He1|apply Rabs_pos|apply Rabs_pos|exact He2].
  - exact Hr.
  - rewrite -> Rdiv_plus_distr; unfold Rdiv.
    rewrite -> (Rinv_r_simpl_l (Rabs (F.injR v2))); [|exact Haw2ne0].
    apply Fadd_up_le_compat_l.
    rewrite -> (Rmult_comm _ (F.injR e2)).
    rewrite -> (Rmult_assoc).
    rewrite <- Rdiv_mult_inv.
    apply Fmul_up_le_compat; [exact He2| |apply Rle_refl|].
    -- unfold Rdiv. apply Rle_mult_nonneg_nonneg.
       apply Rabs_pos. apply Rlt_le. apply Hraw2.
    -- repeat (rewrite <- F.abs_exact_spec).
       apply Rge_le. apply F.div_up_spec. rewrite -> F.abs_exact_spec. exact Haw2ne0.
  - rewrite <- F.abs_exact_spec.
    apply F.sub_down_spec.
Qed.

Definition div (x1 x2 : Ball F) : Ball F :=
  match x1 with ball v1 e1 =>
    match x2 with ball v2 e2 =>
      let re := (F.div2 up (F.sub up (F.div up v1 v2) (F.div down v1 v2))) in
        ball (F.div near v1 v2) (div_err_up v1 v2 e1 e2 re)
    end
  end
.

Lemma div_correct :
  forall (x1 x2 : Ball F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 ->
      div_defined (value x1) (value x2) (error x1) (error x2) ->
        models (div x1 x2) (y1/y2).
Proof.
  intros x1 x2 y1 y2.
  destruct x1 as (v1 & e1); destruct x2 as (v2 & e2).
  unfold div,div_defined, models in *.
  set (rv := F.div near v1 v2).
  set (w1:=F.injR v1); set (w2:=F.injR v2).
  set (d1:=F.injR e1); set (d2:=F.injR e2).
  set (rw := w1 / w2).
  set (ry := y1 / y2).
  set (re := F.div2 up (F.sub up (F.div up v1 v2) (F.div down v1 v2))).
  intros H1 H2 Hp; simpl in Hp.
  assert (0<=d1) as Hd1. {
    step (Rdist w1 y1). apply Rge_le. apply Rdist_pos. apply H1. }
  assert (0<=d2) as Hd2. {
    step (Rdist w2 y2). apply Rge_le. apply Rdist_pos. apply H2. }
  assert (0<F.injR (F.abs v2)) as Hav2. {
    apply Rlt_le_trans with (F.injR (F.sub down (F.abs v2) e2)); [exact Hp|].
    apply Rle_trans with (F.injR (F.abs v2) - F.injR e2); [apply F.sub_down_spec|].
    apply Rminus_ge_0; [exact Hd2].
  }
  assert (0<Rabs w2 - d2) as Hrw. {
    unfold w2. apply (Rlt_le_trans _ _ _ Hp). rewrite <- F.abs_exact_spec. apply F.sub_down_spec. }
  assert (F.injR (F.abs v2)<>0) as Hav2ne0. {
     apply not_eq_sym. apply Rlt_not_eq. exact Hav2. }
  assert (w2 <> 0) as Hw2ne0. {
    unfold w2. apply Rabs_0_neq. rewrite <- F.abs_exact_spec. exact Hav2ne0. }
  assert (Rabs w2 <> 0) as Haw2ne0. {
    unfold w2. rewrite <- F.abs_exact_spec. exact Hav2ne0. }
  assert (0</Rabs w2) as Hraw2. {
    unfold w2. rewrite <- F.abs_exact_spec. apply Rinv_pos. exact Hav2. }
  assert (Rdist (F.injR rv) rw <= F.injR re) as Hre. {
    unfold rv,rw,re.
    apply (F.div_near_up_down_sub_hlf_up_spec); exact Hw2ne0.
  }
  assert (Rdist rw ry <= div_err w1 w2 d1 d2) as Hae. {
    apply div_err_correct.
    unfold w1, w2.
    rewrite <- F.abs_exact_spec.
    apply (div_nonzero v1 v2 e1 e2). exact Hp.
    exact Hd2.
    exact H1.
    exact H2.
  }
  assert (div_err w1 w2 d1 d2 + F.injR re <= F.injR (div_err_up v1 v2 e1 e2 re)) as Hme. {
    apply div_err_up_correct. exact Hd1. exact Hd2. exact Hp.
  }
  1: step (Rdist (F.injR rv) rw + Rdist rw ry).
  2: step ((div_err w1 w2 d1 d2) + F.injR re).
  - apply Rdist_triang.
  - rewrite -> Rplus_comm. apply Rplus_le_compat. exact Hae. exact Hre.
  - exact Hme.
Qed.


Definition rec_err_up v e re :=
  F.add up re (F.div up e (F.mul down (F.abs v) (F.sub down (F.abs v) e))).

Definition rec_defined v e :=
  0 < F.injR (F.mul down (F.abs v) (F.sub down (F.abs v) e)).

Lemma rec_nonzero : forall v e,
  rec_defined v e -> 0 <= F.injR e -> F.injR e < F.injR (F.abs v).
Proof.
  intros v e H He.
  unfold rec_defined in H.
  assert (0 < F.injR (F.abs v)). {
    assert (0 <= F.injR (F.abs v)) as Hp. { rewrite -> F.abs_exact_spec. apply Rabs_pos. }
    unfold Rle in Hp; destruct Hp as [Hgt|H0]; [assumption|].
    assert (F.injR (F.mul down (F.abs v) (F.sub down (F.abs v) e)) <= 0) as Hle0. {
      replace 0 with (F.injR (F.abs v) * F.injR (F.sub down (F.abs v) e)).
      apply F.mul_down_spec.
      rewrite <- H0.
      apply Rmult_0_l.
    }
    apply Rle_not_lt in Hle0.
    contradiction.
  }
  apply Rlt_zero_Rminus.
  apply Rlt_pos_pos_Rmult with (F.injR (F.abs v)).
    exact H0.
  rewrite -> Rmult_comm.
  apply Rlt_le_trans with (F.injR (F.abs v) * (F.injR (F.sub down (F.abs v) e))).
  apply Rlt_le_trans with (F.injR (F.mul down (F.abs v) (F.sub down (F.abs v) e))).
  - exact H.
  - apply F.mul_down_spec.
  - apply Rmult_le_compat_l.
    apply Rlt_le; exact H0.
    apply F.sub_down_spec.
Qed.

Lemma rec_err_up_correct : forall v e re,
  0<=F.injR e ->
    rec_defined v e ->
      rec_err (F.injR v) (F.injR e) + (F.injR re)
        <= F.injR (rec_err_up v e re).
Proof.
  intros v e re He Hr.
  unfold rec_err,rec_err_up, rec_defined.
  rewrite -> Rplus_comm.
  step (F.injR re + F.injR (F.div up e (F.mul down (F.abs v) (F.sub down (F.abs v) e)))).
  2: apply F.add_up_le_spec.
  apply Rplus_le_compat_l.
  step (F.injR e / F.injR (F.mul down (F.abs v) (F.sub down (F.abs v) e))).
  2: { apply Rge_le. apply F.div_up_spec. apply Rgt_not_eq. apply Rlt_gt. exact Hr. }
  apply Rmult_le_compat_l. { exact He. }
  apply Rinv_le_contravar. { exact Hr. }
  rewrite <- F.abs_exact_spec.
  step (F.injR (F.abs v) * F.injR (F.sub down (F.abs v) e)).
  - apply F.mul_down_spec.
  - apply Rmult_le_compat_l. { rewrite -> F.abs_exact_spec. apply Rabs_pos. }
    apply F.sub_down_spec.
Qed.

Definition rec (x : Ball F) : Ball F :=
  match x with ball v e =>
    let re := (F.div2 up (F.sub up (F.rec up v) (F.rec down v))) in
      ball (F.rec near v) (rec_err_up v e re)
  end
.

Lemma rec_correct :
  forall (x : Ball F) (y : R),
    models x y ->
      rec_defined (value x) (error x) ->
        models (rec x) (/y).
Proof.
  intros x y.
  destruct x as (v & e).
  unfold rec,rec_defined, models in *.
  set (rv := F.rec near v).
  set (w:=F.injR v).
  set (rw := / w).
  set (ry := / y).
  set (re := F.div2 up (F.sub up (F.rec up v) (F.rec down v))).
  intros H Hp; simpl in Hp.
  assert (0<=F.injR e) as He. {
    step (Rdist w y). apply Rge_le. apply Rdist_pos. apply H.
  }
  assert (F.injR v <> 0) as Hv. {
    apply rec_nonzero in Hp; [|exact He].
    apply Rabs_0_neq; apply Rgt_not_eq; apply Rlt_gt.
    rewrite <- F.abs_exact_spec.
    apply (Rle_lt_trans _ _ _ He Hp).
  }
  assert (Rdist (F.injR rv) rw <= F.injR re) as Hre. {
    unfold rv,rw,re.
    apply (F.rec_near_up_down_sub_hlf_up_spec); exact Hv.
  }
  assert (Rdist rw ry <= rec_err w (F.injR e)) as Hae. {
    apply rec_err_correct.
    unfold w.
    rewrite <- F.abs_exact_spec.
    apply rec_nonzero. exact Hp.
    exact He.
    exact H.
  }
  assert (rec_err w (F.injR e) + F.injR re <= F.injR (rec_err_up v e re)) as Hme. {
    apply rec_err_up_correct. exact He. exact Hp.
  }
  1: step (Rdist (F.injR rv) rw + Rdist rw ry).
  2: step (rec_err w (F.injR e) + F.injR re).
  - apply Rdist_triang.
  - rewrite -> Rplus_comm. apply Rplus_le_compat. exact Hae. exact Hre.
  - exact Hme.
Qed.


Definition div' (x1 x2 : Ball F) : Ball F :=
  mul x1 (rec x2).

Lemma div_correct' :
  forall (x1 x2 : Ball F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 ->
      rec_defined (value x2) (error x2) ->
        models (div' x1 x2) (y1/y2).
Proof.
  intros x1 x2 y1 y2 H1 H2 Hor.
  unfold Rdiv.
  apply mul_correct.
  - exact H1.
  - apply rec_correct.
    exact H2.
    exact Hor.
Qed.


Fixpoint pow (x : Ball F) (n : nat) : Ball F :=
  match n with | O => ball F.unit F.null | S m => mul (pow x m) x end.

Lemma pow_succ : forall x n, pow x (S n) = mul (pow x n) x.
Proof. reflexivity. Qed.

Lemma pow_correct : forall x r n, models x r -> models (pow x n) (Rpow r n).
Proof.
  intros x r n Hxr.
  induction n.
  - unfold pow, Rpow, models.
    rewrite -> F.null_spec, F.unit_spec, Rdist_eq.
    exact (Rle_refl 0).
  - rewrite -> pow_succ. replace (Rpow r (S n)) with (Rpow r n * r).
    apply mul_correct. exact IHn. exact Hxr.
    simpl. now apply Rmult_comm.
Qed.


Definition mag (x : Ball F) : F :=
  F.max (F.sub up (error x) (value x)) (F.add up (value x) (error x)).

Lemma mag_correct : forall x r, models x r -> Rabs r <= F.injR (mag x).
Proof.
  unfold models, mag.
  intros x r Hxr.
  destruct x as [v e]; simpl.
  rewrite -> F.max_exact_spec.
  set (F.injR v) as yv; set (F.injR e) as ye.
  transitivity (Rmax (ye-yv) (yv+ye)).
  - rewrite -> Rdist_sym in Hxr. now apply Rdist_abs_ivl.
  - apply Rle_max_compat.
    now apply F.sub_up_le_spec.
    now apply F.add_up_le_spec.
Qed.


Definition ball_to_bounds (x : Ball F) : Bounds F :=
  let (v,e) := (value x, error x) in
    bounds (F.sub down v e) (F.add up v e).

Proposition ball_to_bounds_correct :
  forall (x : Ball F) (y : R),
    models x y -> Bnds.models (ball_to_bounds x) y.
Proof.
  intros x y H.
  destruct x as (v & e).
  unfold ball_to_bounds; unfold models in H; unfold Bnds.models; simpl.
  unfold Rdist in H; apply Rabs_ivl in H; destruct H as (Hl&Hu).
  split.
  - apply Rle_trans with (r2:=F.injR v - F.injR e).
    apply F.sub_down_spec.
    lra.
  - apply Rle_trans with (r2:=F.injR v + F.injR e).
    lra.
    apply Rge_le; apply F.add_up_spec.
Qed.


Definition bounds_to_ball (x : Bounds F) : (Ball F) :=
  let (l,u) := (Bnds.lower x, Bnds.upper x) in
    let v := F.div near (F.add near l u) (F.of_nat 2) in
      let e := F.max (F.sub up v l) (F.sub up u v) in
        ball v e.

Proposition bounds_to_ball_correct :
  forall (x : Bounds F) (y : R),
    Bnds.models x y -> models (bounds_to_ball x) y.
Proof.
  intros x y H.
  destruct x as (l & u).
  unfold bounds_to_ball; unfold Bnds.models in H; unfold models; simpl.
  destruct H as (Hl&Hu).
  set (v:=F.div near (F.add near l u) (F.of_nat 2)).
  unfold Rdist.
  assert (F.injR v <= y \/ y <= F.injR v) as Hvy; [apply Rle_or_le|].
  destruct Hvy as [Hvley|Hylev].
  - assert (F.injR v - y <= 0) as Hvsy. { apply Rle_minus. exact Hvley. }
    rewrite -> Rabs_neg_eq by (exact Hvsy).
    rewrite -> Ropp_minus_distr.
    apply Rle_trans with (r2:=Rmax (F.injR v - F.injR l) (F.injR u - F.injR v)).
    apply Rle_trans with (r2:=F.injR u - F.injR v).
    -- apply Rplus_le_compat_r.
       exact Hu.
    -- apply Rmax_r.
    -- rewrite -> F.max_exact_spec.
       apply Rle_max_compat.
       apply Rge_le; apply F.sub_up_spec.
       apply Rge_le; apply F.sub_up_spec.
  - assert (0<=F.injR v - y) as Hvsy. { apply Rle_Rminus_zero. exact Hylev. }
    rewrite -> Rabs_pos_eq by (exact Hvsy).
    apply Rle_trans with (r2:=Rmax (F.injR v - F.injR l) (F.injR u - F.injR v)).
    apply Rle_trans with (r2:=F.injR v - F.injR l).
    -- apply Rplus_le_compat_l.
       apply Ropp_le_contravar.
       exact Hl.
    -- apply Rmax_l.
    -- rewrite -> F.max_exact_spec.
       apply Rle_max_compat.
       apply Rge_le; apply F.sub_up_spec.
       apply Rge_le; apply F.sub_up_spec.
Qed.


Definition Rexp : R -> R := exp.

Definition exp (x : Ball F) : Ball F :=
  bounds_to_ball (Bnds.exp (ball_to_bounds x)).

Theorem exp_correct :
  forall (x : Ball F) (y : R),
    (F.injR (F.sub down F.unit (F.add up (value x) (error x))) > 0) ->
      (models x y) -> (models (exp x) (Rexp y)).
Proof.
  intros x y Hu H.
  unfold exp.
  apply bounds_to_ball_correct.
  apply Bnds.exp_correct.
  apply ball_to_bounds_correct.
  exact H.
Qed.

Definition Rexp_approx (x : R) : R :=
  (x / 2 + 1) * x + 1.

Definition exp_approx' (rnd : Rounding) (x : F) : F :=
  F.add rnd (F.mul rnd (F.add rnd (F.div rnd x (F.of_nat 2)) F.unit) x) F.unit.

Definition exp_approx (x : F) : F := exp_approx' near x.

Definition exp_approx_rng (x : F) : F :=
  F.sub up (exp_approx' up x) (exp_approx' down x).

Lemma exp_approx_down :
  forall (x : F), (0 <= F.injR x) -> F.injR (exp_approx' down x) <= Rexp_approx (F.injR x).
Proof.
  intros x  Hx.
  unfold exp_approx', Rexp_approx.
  apply Rle_trans with (r2:=F.injR (F.mul down (F.add down (F.div down x (F.of_nat 2)) F.unit) x) + 1).
  rewrite <- F.unit_spec.
  apply F.add_down_spec.
  apply Rplus_le_compat_r.
  apply Rle_trans with (r2:=F.injR (F.add down (F.div down x (F.of_nat 2)) F.unit) * F.injR x).
  apply F.mul_down_spec.
  apply Rmult_le_compat_r. apply Hx.
  apply Rle_trans with (r2:=F.injR (F.div down x (F.of_nat 2)) + 1).
  rewrite <- F.unit_spec.
  apply F.add_down_spec.
  apply Rplus_le_compat_r.
  replace 2 with (F.injR (F.of_nat 2%nat)).
  apply F.div_down_spec.
  rewrite -> F.ninjr_spec. apply not_0_INR. auto.
  rewrite -> F.ninjr_spec. auto.
Qed.

Lemma exp_approx_up :
  forall (x : F), (0 <= F.injR x) -> F.injR (exp_approx' up x) >= Rexp_approx (F.injR x).
Proof.
  intros x  Hx.
  unfold exp_approx', Rexp_approx.
  apply Rge_trans with (r2:=F.injR (F.mul up (F.add up (F.div up x (F.of_nat 2)) F.unit) x) + 1).
  rewrite <- F.unit_spec.
  apply F.add_up_spec.
  apply Rplus_ge_compat_r.
  apply Rge_trans with (r2:=F.injR (F.add up (F.div up x (F.of_nat 2)) F.unit) * F.injR x).
  apply F.mul_up_spec.
  apply Rmult_ge_compat_r. apply Rle_ge; apply Hx.
  apply Rge_trans with (r2:=F.injR (F.div up x (F.of_nat 2)) + 1).
  rewrite <- F.unit_spec.
  apply F.add_up_spec.
  apply Rplus_ge_compat_r.
  replace 2 with (F.injR (F.of_nat 2%nat)).
  apply F.div_up_spec.
  rewrite -> F.ninjr_spec. apply not_0_INR. auto.
  rewrite -> F.ninjr_spec. auto.
Qed.


Lemma Rdist_ge : forall (r1 r2 : R), r1>=r2 -> Rdist r1 r2 = r1-r2.
Proof.
  intros r1 r2 H; unfold Rdist.
  apply Rabs_pos_eq; apply Rle_Rminus_zero; apply Rge_le; exact H.
Qed.

Lemma Rdist_le : forall (r1 r2 : R), r1<=r2 -> Rdist r1 r2 = r2-r1.
Proof.
  intros r1 r2 H; unfold Rdist.
  rewrite <- (Ropp_minus_distr r1 r2); apply Rabs_neg_eq; apply Rle_minus; exact H.
Qed.


Lemma flt_add_near_up : forall (x y : F), F.injR (F.add near x y) <= F.injR (F.add up x y).
Proof.
  intros x y.
  assert (Rdist (F.injR (F.add near x y)) (F.injR x + F.injR y) <= Rdist (F.injR (F.add up x y)) (F.injR x + F.injR y)) as Hn;
    [apply F.add_near_spec|].
  assert ((F.injR x + F.injR y) <= F.injR (F.add up x y)) as Hu; [apply Rge_le; apply F.add_up_spec|].
  set (zn := F.injR (F.add near x y)) in *;
  set (zu := F.injR (F.add up x y)) in *;
  set (ze := F.injR x + F.injR y) in *.
  rewrite -> (Rdist_ge zu ze) in Hn; [|apply Rle_ge; exact Hu].
  unfold Rdist in Hn.
  apply Rabs_ivl in Hn.
  apply Rplus_le_reg_r with (r:=-ze).
  apply Hn.
Qed.

Lemma flt_add_near_down : forall (x y : F), F.injR (F.add down x y) <= F.injR (F.add near x y).
Proof.
  intros x y.
  assert (Rdist (F.injR (F.add near x y)) (F.injR x + F.injR y) <= Rdist (F.injR (F.add down x y)) (F.injR x + F.injR y)) as Hn;
    [apply F.add_near_spec|].
  assert (F.injR (F.add down x y) <= (F.injR x + F.injR y)) as Hl; [apply F.add_down_spec|].
  set (zn := F.injR (F.add near x y)) in *;
  set (zl := F.injR (F.add down x y)) in *;
  set (ze := F.injR x + F.injR y) in *.
  rewrite -> (Rdist_le zl ze) in Hn; [|exact Hl].
  unfold Rdist in Hn.
  apply Rabs_ivl in Hn.
  rewrite -> Ropp_minus_distr in Hn.
  apply Rplus_le_reg_r with (r:=-ze).
  apply Hn.
Qed.

Lemma flt_add_near_monotone : forall (x1 x2 y1 y2 : F),
  F.injR x1 <= F.injR x2 -> F.injR y1 <= F.injR y2 ->
    F.injR (F.add near x1 y1) <= F.injR (F.add near x2 y2).
Proof.
(* z1<z2; |w1-z1|<=|w2-z1|; |w2-z2|<=|w1-z2| *)
  assert (forall (x1 x2 : F), (F.injR x1 = F.injR x2) -> x1=x2) as HFinjR. { admit. }

  intros x1 x2 y1 y2 Hx Hy.
  set (z1 := F.injR x1 + F.injR y1).
  set (z2 := F.injR x2 + F.injR y2).
  assert ((x1=x2 /\ y1=y2) \/ z1<z2) as Hz. {
    destruct Hx as [Hx|Hx].
    - right. apply Rplus_lt_le_compat; [exact Hx|exact Hy].
    - destruct Hy as [Hy|Hy].
      right. apply Rplus_le_lt_compat; [apply Req_le;exact Hx|exact Hy].
      left. split. apply HFinjR. exact Hx. apply HFinjR. exact Hy.
  }
  destruct Hz as [Hzeq | Hzlt].
  - apply Req_le. f_equal. f_equal. apply Hzeq. apply Hzeq.
  - apply Rlt_le in Hzlt as Hzle.
    assert (Rdist (F.injR (F.add near x1 y1)) z1 <= (Rdist (F.injR (F.add near x2 y2)) z1)) as Hz1. {
      apply F.add_near_spec. }
    assert (Rdist (F.injR (F.add near x2 y2)) z2 <= (Rdist (F.injR (F.add near x1 y1)) z2)) as Hz2. {
      apply F.add_near_spec. }
    set (w1 := F.injR (F.add near x1 y1)) in *.
    set (w2 := F.injR (F.add near x2 y2)) in *.
    assert (w1<=z2 \/ z1<=w2 \/ (z2<=w1 /\ w2<=z1)) as Hd. {
      assert (w1<=z2 \/ z2<=w1) as Hw1; [apply Rle_or_le|].
      assert (z1<=w2 \/ w2<=z1) as Hw2; [apply Rle_or_le|].
      destruct Hw1 as [Hw1lez2|Hz2lew1].
      - left. exact Hw1lez2.
      - right. destruct Hw2 as [Hz1lew2|Hw2lez1].
        -- left. exact Hz1lew2.
        -- right. split. exact Hz2lew1. exact Hw2lez1.
    }
    destruct Hd as [Hw1lez2 | [Hz1lew2 | Hw2lez1ltz2lew1]].
    -- rewrite -> (Rdist_le w1 z2) in Hz2.
       unfold Rdist in Hz2; apply Rabs_ivl in Hz2.
       rewrite -> Ropp_minus_distr in Hz2.
       apply Rplus_le_reg_r with (r:=-z2).
       apply Hz2.
       exact Hw1lez2.
    -- rewrite -> (Rdist_ge w2 z1) in Hz1.
       unfold Rdist in Hz1; apply Rabs_ivl in Hz1.
       apply Rplus_le_reg_r with (r:=-z1).
       apply Hz1.
       apply Rle_ge; exact Hz1lew2.
    -- destruct Hw2lez1ltz2lew1 as (Hz2lew1 & Hw2lez1).
       rewrite -> (Rdist_le w2 z1) in Hz1; [|exact Hw2lez1].
       rewrite -> (Rdist_ge w1 z2) in Hz2; [|apply Rle_ge; exact Hz2lew1].
       unfold Rdist in Hz1; apply Rabs_ivl in Hz1.
       unfold Rdist in Hz2; apply Rabs_ivl in Hz2.
       rewrite -> Ropp_minus_distr in Hz2.
       assert ((w1-z1)+(z2-w1)<=(z1-w2)+(w2-z2)) as Hc. {
         apply Rplus_le_compat. apply Hz1. apply Hz2. }
       lra.
Admitted.

Lemma flt_mul_near_monotone : forall (x1 x2 y1 y2 : F),
  0 <= F.injR x1 -> 0<=F.injR y1 -> F.injR x1 <= F.injR x2 -> F.injR y1 <= F.injR y2 ->
    F.injR (F.mul near x1 y1) <= F.injR (F.mul near x2 y2).
Proof. Admitted.

Lemma flt_mul_near_monotone_r : forall (x1 x2 y : F),
  0<=F.injR y -> F.injR x1 <= F.injR x2 ->
    F.injR (F.mul near x1 y) <= F.injR (F.mul near x2 y).
Proof. Admitted.

Lemma flt_div_near_monotone : forall (x1 x2 y : F),
  0 <= F.injR x1 -> 0<=F.injR y -> F.injR x1 <= F.injR x2 ->
    F.injR (F.div near x1 y) <= F.injR (F.div near x1 y).
Proof. Admitted.

Lemma flt_mul_near_up : forall (x y : F), F.injR (F.mul near x y) <= F.injR (F.mul up x y).
Proof. Admitted.

Lemma flt_div_near_up : forall (x y : F), F.injR (F.div near x y) <= F.injR (F.div up x y).
Proof. Admitted.

Lemma flt_add_monotone : forall rnd (x1 x2 y1 y2 : F),
  F.injR x1 <= F.injR x2 -> F.injR y1 <= F.injR y2 ->
    F.injR (F.add rnd x1 y1) <= F.injR (F.add rnd x2 y2).
Proof. Admitted.

Definition Fle (x1 x2 : F) : Prop := F.leb x1 x2 = true.

Lemma exp_approx_le : forall (x : F), (0<=F.injR x) -> Fle (exp_approx' near x) (exp_approx' up x).
Proof.
  intros x H0lex.
  unfold exp_approx'.
  assert (F.injR (F.div near x (F.of_nat 2)) <= F.injR (F.div up x (F.of_nat 2))) as H0. {
    apply flt_div_near_up. }
  assert ( F.injR (F.add near (F.div near x (F.of_nat 2)) F.unit)
             <= F.injR (F.add up (F.div up x (F.of_nat 2)) F.unit) ) as H1. {
    apply Rle_trans with (r2:=F.injR (F.add near (F.div up x (F.of_nat 2)) F.unit)).
    apply flt_add_near_monotone.
    exact H0.
    apply Req_le; reflexivity.
    apply flt_add_near_up.
  }
  assert ( F.injR (F.mul near (F.add near (F.div near x (F.of_nat 2)) F.unit) x)
             <= F.injR (F.mul up (F.add up (F.div up x (F.of_nat 2)) F.unit) x) ) as H2. {
    apply Rle_trans with (r2:=F.injR (F.mul near (F.add up (F.div up x (F.of_nat 2)) F.unit) x)).
    apply flt_mul_near_monotone_r.
    exact H0lex.
    exact H1.
    apply flt_mul_near_up.
  }
  assert (F.injR (F.add near (F.mul near (F.add near (F.div near x (F.of_nat 2)) F.unit) x) F.unit)
            <= F.injR (F.add up (F.mul up (F.add up (F.div up x (F.of_nat 2)) F.unit) x) F.unit)) as H3. {
    apply Rle_trans with (r2:=F.injR (F.add near (F.mul up (F.add up (F.div up x (F.of_nat 2)) F.unit) x) F.unit)).
    apply flt_add_near_monotone.
    exact H2.
    apply Req_le; reflexivity.
    apply flt_add_near_up.
  }
  set (wn:=(F.add near (F.mul near (F.add near (F.div near x (F.of_nat 2)) F.unit) x) F.unit)) in *.
  set (wu:=(F.add up (F.mul up (F.add up (F.div up x (F.of_nat 2)) F.unit) x) F.unit)) in *.
  unfold Fle.
  apply F.leb_spec.
  exact H3.
Qed.

Lemma bounds_error : forall (l u x1 x2 : R), l<=x1<=u -> l<=x2<=u -> Rdist x1 x2 <= u-l.
Proof. intros; unfold Rdist; apply Rabs_le; lra. Qed.

Lemma exp_approx_ge : forall (x : F), (0<=F.injR x) -> Fle (exp_approx' down x) (exp_approx' near x).
Proof. Admitted.

Lemma exp_approx_correct :
  forall (x : F), (0<=F.injR x) -> Rdist (Rexp_approx (F.injR x)) (F.injR (exp_approx x)) <= F.injR (exp_approx_rng x).
Proof.
  intros x Hx.
  unfold exp_approx, exp_approx_rng.
  set (wl := exp_approx' down x).
  set (wu := exp_approx' up x).
  assert (F.injR wu - F.injR wl <= F.injR (F.sub up wu wl) ) as He. {
    apply Rge_le; apply F.sub_up_spec. }
  set (zn := F.injR (exp_approx' near x)).
  set (ze := Rexp_approx (F.injR x)).
  apply Rle_trans with (r2:=F.injR wu - F.injR wl).
  set (zl := F.injR wl) in *.
  set (zu := F.injR wu) in *.
(*
  assert (zl <= zn) as Hln. { apply exp_approx_ge. exact Hx. }
  assert (zn <= zu) as Hnu. { apply exp_approx_le. apply Hx. }
  assert (zl <= ze) as Hle. { apply exp_approx_down. exact Hx. }
  assert (ze <= zu) as Heu. { apply Rge_le; apply exp_approx_up. exact Hx. }
  unfold Rdist; apply Rabs_le.
  lra.
  exact He.
*)
Admitted.

Local Definition fd_exp := fun (_ : nat) => Rexp.

Local Definition Pdf_exp : forall y, smooth_pt_lim fd_exp y :=
  fun y n => derivable_pt_lim_exp y.

Definition taylor_series_exp := fun n => taylor_series fd_exp Pdf_exp n 0.

Fixpoint taylor_series_exp_ball (n : nat) (x : Ball F) : Ball F :=
  match n with
  | O => ball F.unit F.null
  | S m => add (taylor_series_exp_ball m x)
             (div (pow x (S m)) (of_nat (Factorial.fact (S m))))
  end.

Local Definition taylor_series_exp_error_float (n : nat) (w : F) : F :=
  F.mul up (F.of_nat 3) (F.div up (F.pow_up w (S n)) (F.of_nat (Factorial.fact (S n)))).

Local Lemma taylor_exp_succ :
  forall n x, taylor_series_exp_ball (S n) x = add (taylor_series_exp_ball n x)
    (div (pow x (S n)) (of_nat (Factorial.fact (S n)))).
Proof. reflexivity. Qed.


Axiom Fsub_zero_exact : forall rnd (x : F), F.sub rnd x (F.null) = x.

Local Lemma taylor_series_correct :
  forall n x r, models x r -> models (taylor_series_exp_ball n x) (taylor_series_exp n r).
Proof.
  intros n x r Hxr. induction n.
  - unfold taylor_series_exp, taylor_series, fd_exp, Rexp. simpl.
    rewrite -> F.null_spec, F.unit_spec, exp_0, Rdist_eq. now apply Rle_refl.
  - unfold taylor_series_exp. rewrite -> taylor_series_succ, taylor_exp_succ.
    apply add_correct. 1: exact IHn.
    unfold fd_exp, Rexp. rewrite -> exp_0, Rmult_1_l, Rminus_0_r.
    apply div_correct.
    -- now apply pow_correct.
    -- unfold Rfact. now apply of_nat_correct.
    -- unfold div_defined, value, F.of_nat.
       remember (Factorial.fact (S n)) as Snfact.
       simpl.
       rewrite -> Fsub_zero_exact, F.abs_exact_spec, F.ninjr_spec.
       apply Rabs_pos_lt. replace (INR Snfact) with (Rfact (S n)).
       apply Rfact_nonzero. now rewrite -> HeqSnfact.
Qed.



Local Lemma mul_up_step : forall x1 x2 r1 r2,
  0 <= r1 -> 0 <= r2 -> r1 <= F.injR x1 -> r2 <= F.injR x2
    -> r1 * r2 <= F.injR (F.mul up x1 x2).
Proof. intros x1 x2 r1 r2 Hr1 Hr2 Hx1 Hx2.
  transitivity ((F.injR x1) * (F.injR x2)).
  now apply Rmult_le_compat.
  now apply F.mul_up_le_spec.
Qed.

Local Lemma div_up_step : forall x1 x2 r1 r2,
  0 <= r1 -> 0 < F.injR x2 -> r1 <= F.injR x1 -> F.injR x2 <= r2
    -> r1 / r2 <= F.injR (F.div up x1 x2).
Proof. intros x1 x2 r1 r2 Hr1 Hr2 Hx1 Hx2.
  transitivity ((F.injR x1) / (F.injR x2)).
  - rewrite -> Rdiv_def. apply Rmult_le_compat.
    -- exact Hr1.
    -- apply Rlt_le; apply Rinv_pos. apply (Rlt_le_trans _ (F.injR x2)).
       exact Hr2. exact Hx2.
    -- exact Hx1.
    -- apply Rinv_le_contravar.
       exact Hr2. exact Hx2.
  - apply F.div_up_le_spec.
    apply Rgt_not_eq. apply Rlt_gt. exact Hr2.
Qed.

Local Lemma pow_up_step : forall x r n,
  0 <= r -> r <= F.injR x ->
    Rpow r n <= F.injR (F.pow_up x n).
Proof. intros x r n Hr Hx.
  transitivity (Rpow (F.injR x) n).
  - now apply pow_incr.
  - apply F.pow_up_le_spec.
    now apply (Rle_trans _ r).
Qed.


Definition exp_unit (n : nat) (x : Ball F) : Ball F :=
  add (taylor_series_exp_ball n x) (ball F.null (taylor_series_exp_error_float n (mag x))).

Theorem exp_unit_correct : forall n x r, 0 < r -> (F.injR (mag x) <= 1) ->
  models x r -> models (exp_unit n x) (Rexp r).
Proof.
  intros n x r H0ltr Hmag Hxr.
  assert (r <= 1) as Hrle1. {
    transitivity (F.injR (mag x)).
    transitivity (Rabs r).
    exact (Rle_abs r).
    exact (mag_correct x r Hxr).
    exact Hmag.
  }
  pose proof (taylor_series_remainder fd_exp Pdf_exp n 0 r) H0ltr as [c [Pc Hc]].
  unfold exp_unit.
  replace (Rexp r) with (fd_exp 0 r) by reflexivity.
  rewrite -> Hc; clear Hc.
  apply add_correct.
  - now apply taylor_series_correct.
  - unfold models, taylor_series_exp_error_float.
    unfold Rdist. rewrite -> F.null_spec, Rabs_minus_sym, Rminus_0_r, Rminus_0_r.
    replace (fd_exp (S n)) with Rexp by reflexivity.
    rewrite <- Rmult_div_assoc.
    rewrite -> Rabs_mult.
    apply mul_up_step.
    -- now apply Rabs_pos.
    -- now apply Rabs_pos.
    -- rewrite -> Rabs_pos_eq, F.ninjr_spec.
       transitivity (Rexp 1).
       --- apply exp_incr. transitivity r. apply Rlt_le; exact (proj2 Pc). exact Hrle1.
       --- replace (INR 3) with (3%R). exact exp_le_3.
           rewrite -> INR_IZR_INZ; f_equal.
       --- apply Rlt_le; apply exp_pos.
    -- rewrite -> Rdiv_def, Rabs_mult, Rabs_inv, <- Rdiv_def.
       apply div_up_step.
       --- now apply Rabs_pos.
       --- rewrite -> F.ninjr_spec.
           stepr (Rfact (S n)).
           now apply Rfact_pos.
           reflexivity.
       --- rewrite <- RPow_abs.
           apply (pow_up_step (mag x) (Rabs r) (S n)).
           now apply Rabs_pos.
           now apply mag_correct.
       --- rewrite -> Rabs_pos_eq.
           apply Req_le.
           rewrite -> F.ninjr_spec.
           reflexivity.
           apply Rlt_le; now apply Rfact_pos.
Qed.

End Ball_section.

End Bll.

Export Bll(Ball,ball).

Declare Scope Ball_scope.
Notation "- x" := (Bll.neg x) : Ball_scope.
Infix "+" := Bll.add : Ball_scope.
Infix "-" := Bll.sub : Ball_scope.
Infix "*" := Bll.mul : Ball_scope.
Infix "/" := Bll.div : Ball_scope.
