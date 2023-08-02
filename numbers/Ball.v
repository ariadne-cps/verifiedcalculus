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


Require Import Reals.
Require Import Lia.
Require Import Lra.

Require Import R_addenda.
Require Import Floats.
Require Import Analysis.
Require Import Bounds.

Section FloatBall.

Ltac step mid := (apply Rle_trans with mid).

Open Scope R_scope.

Context `{F : Type} `{FltF : Float F}.


Inductive Ball {F:Type} {FltF : Float F} :=
  ball (value:F) (error:F).

Definition value (x : @Ball F FltF) : F := match x with ball v _ => v end.
Definition error (x : @Ball F FltF) : F := match x with ball _ e => e end.

Check ball.

Definition models : Ball -> R -> Prop :=
  fun x y => match x with ball v e => Rdist (FinjR v) y <= (FinjR e) end.




Lemma flt_add_up_le_compat : forall w1 x1 w2 x2,
  w1 <= FinjR x1 -> w2 <= FinjR x2 -> (w1 + w2) <= FinjR (Fadd up x1 x2).
Proof.
  intros w1 x1 w2 x2 H1 H2.
  step (FinjR x1 + FinjR x2).
  apply Rplus_le_compat; [exact H1|exact H2].
  apply Rge_le; apply flt_add_up.
Qed.

Lemma flt_add_up_le_compat_l : forall x1 w2 x2,
  w2 <= FinjR x2 -> (FinjR x1 + w2) <= FinjR (Fadd up x1 x2).
Proof.
  intros x1 w2 x2 H2. apply (flt_add_up_le_compat (FinjR x1) x1 w2 x2). apply Rle_refl. exact H2.
Qed.

Lemma flt_add_up_le_compat_r : forall w1 x1 x2,
  w1 <= FinjR x1 -> (w1 + FinjR x2) <= FinjR (Fadd up x1 x2).
Proof.
  intros w1 x1 x2 H1. apply (flt_add_up_le_compat w1 x1 (FinjR x2) x2). apply H1. apply Rle_refl.
Qed.

Lemma flt_mul_up_le_compat : forall w1 x1 w2 x2,
  0 <= w1 -> 0 <= w2 -> w1 <= FinjR x1 -> w2 <= FinjR x2
    -> (w1 * w2) <= FinjR (Fmul up x1 x2).
Proof.
  intros w1 x1 w2 x2 Hw1 Hw2 H1 H2.
  step (FinjR x1 * FinjR x2).
  apply Rmult_le_compat; [exact Hw1 | exact Hw2 | exact H1 | exact H2].
  apply flt_mul_up_le.
Qed.

Lemma flt_mul_up_le_compat_l : forall x1 w2 x2,
  0 <= FinjR x1 -> 0 <= w2 -> w2 <= FinjR x2
    -> (FinjR x1 * w2) <= FinjR (Fmul up x1 x2).
Proof.
  intros x1 w2 x2 Hx1 Hw2 H2.
  apply (flt_mul_up_le_compat (FinjR x1) x1 w2 x2).
  exact Hx1. exact Hw2. apply Rle_refl. exact H2.
Qed.

Lemma flt_mul_up_le_compat_r : forall w1 x1 x2,
  0 <= w1 -> 0 <= FinjR x2 -> w1 <= FinjR x1
    -> (w1 * FinjR x2) <= FinjR (Fmul up x1 x2).
Proof.
  intros w1 x1 x2 Hw1 Hx2 H1.
  apply (flt_mul_up_le_compat w1 x1 (FinjR x2) x2).
  exact Hw1. exact Hx2. exact H1. apply Rle_refl.
Qed.


Lemma flt_div_up_le_compat : forall w1 x1 w2 x2,
  0 <= w1 -> 0 < FinjR x2 -> w1 <= FinjR x1 -> FinjR x2 <= w2 ->
    (w1 / w2) <= FinjR (Fdiv up x1 x2).
Proof.
  intros w1 x1 w2 x2 Hw1 Hx2 H1 H2.
  assert (FinjR x2<>0) as Hx2n; [exact (not_eq_sym (Rlt_not_eq _ _ Hx2))|].
  assert (0<w2) as Hw2; [exact (Rlt_le_trans _ _ _ Hx2 H2)|].
  assert (0<=/w2) as Hrw2; [exact (Rlt_le _ _ (Rinv_0_lt_compat _ Hw2))|].
  assert (/w2<=/FinjR x2) as Hr2; [exact (Rinv_le_contravar _ _ Hx2 H2)|].
  step (FinjR x1 / FinjR x2).
  unfold Rdiv. apply Rmult_le_compat; [exact Hw1|exact Hrw2|exact H1|exact Hr2].
  apply Rge_le. apply flt_div_up. exact Hx2n.
Qed.




Definition add_ball : Ball -> Ball -> Ball :=
  fun x1 x2 =>
    match x1 with ball v1 e1
      => match x2 with ball v2 e2
        => ball (Fadd near v1 v2) (Fadd up (Fdiv2 up (Fsub up (Fadd up v1 v2) (Fadd down v1 v2))) (Fadd up e1 e2)) end end.

Lemma add_ball_correct :
  forall (x1 x2 : Ball) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (add_ball x1 x2) (y1+y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (v1 & e1), x2 as (v2 & e2).
  unfold models in H1,H2;
  unfold models; unfold add_ball.
  set (v12 := Fadd near v1 v2).
  set (w12 := FinjR v1 + FinjR v2).
  set (y12 := y1 + y2).
  set (re12 := Fdiv2 up (Fsub up (Fadd up v1 v2) (Fadd down v1 v2))).
  assert (Rdist (FinjR v12) w12 <= FinjR re12) as Hre. {
    unfold v12,w12,re12.
    replace Fadd with (Fapply Add) by (trivial).
    apply flt_op_near_up_down_sub_hlf_up.
  }
  assert (Rdist w12 y12 <= FinjR e1 + FinjR e2) as Hy. {
    unfold w12,y12.
    apply Rle_trans with (Rdist (FinjR v1) y1 + Rdist (FinjR v2) y2).
    - apply Rdist_plus_compat.
    - apply Rplus_le_compat. exact H1. exact H2.
  }
  step (Rdist (FinjR v12) w12 + Rdist w12 y12).
    apply Rdist_triang.
  step (FinjR re12 + FinjR (Fadd up e1 e2)).
  - apply Rplus_le_compat.
    -- apply Hre.
    -- step (FinjR e1 + FinjR e2). exact Hy. apply flt_add_up_le.
  - apply flt_add_up_le.
Qed.


Definition sub_ball (x1 x2 : Ball) : Ball :=
  match x1 with ball v1 e1 => match x2 with ball v2 e2
    => ball (Fsub near v1 v2) (Fadd up (Fdiv2 up (Fsub up (Fsub up v1 v2) (Fsub down v1 v2))) (Fadd up e1 e2)) end end.

Lemma sub_ball_correct :
  forall (x1 x2 : Ball) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (sub_ball x1 x2) (y1-y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (v1 & e1), x2 as (v2 & e2).
  unfold models in H1,H2;
  unfold models; unfold add_ball.
  set (v12 := Fsub near v1 v2).
  set (w12 := FinjR v1 - FinjR v2).
  set (y12 := y1 - y2).
  set (re12 := Fdiv2 up (Fsub up (Fsub up v1 v2) (Fsub down v1 v2))).
  assert (Rdist (FinjR v12) w12 <= FinjR re12) as Hre. {
    unfold v12,w12,re12.
    replace Fsub with (Fapply Sub) by (trivial).
    apply flt_op_near_up_down_sub_hlf_up.
  }
  assert (Rdist w12 y12 <= FinjR e1 + FinjR e2) as Hy. {
    unfold w12,y12.
    apply Rle_trans with (Rdist (FinjR v1) y1 + Rdist (FinjR v2) y2).
    - apply Rdist_minus_compat.
    - apply Rplus_le_compat. exact H1. exact H2.
  }
  step (Rdist (FinjR v12) w12 + Rdist w12 y12).
    apply Rdist_triang.
  step (FinjR re12 + FinjR (Fadd up e1 e2)).
  - apply Rplus_le_compat.
    -- apply Hre.
    -- step (FinjR e1 + FinjR e2). exact Hy. apply flt_add_up_le.
  - apply flt_add_up_le.
Qed.

Definition Fle x1 x2 := FinjR x1 <= FinjR x2.


Definition mul_err_up v1 v2 e1 e2 re :=
  Fadd up (Fadd up re (Fmul up e1 e2))
          (Fadd up (Fmul up (Fabs v1) e2) (Fmul up e1 (Fabs v2))).

Lemma mul_err_up_correct : forall v1 v2 e1 e2 re,
  mul_err (FinjR v1) (FinjR v2) (FinjR e1) (FinjR e2) + (FinjR re)
    <= FinjR (mul_err_up v1 v2 e1 e2 re).
Proof.
  intros v1 v2 e1 e2 re.
    unfold mul_err,mul_err_up.
  stepl ( (FinjR re + (FinjR e1) * (FinjR e2)) + (Rabs (FinjR v1)*FinjR e2 + FinjR e1 * Rabs (FinjR v2)) ) by ring.
  apply flt_add_up_le_compat.
  - apply flt_add_up_le_compat_l.
    apply flt_mul_up_le.
  - repeat (rewrite <- flt_abs_exact).
    apply flt_add_up_le_compat.
    -- apply flt_mul_up_le.
    -- apply flt_mul_up_le.
Qed.



Definition mul_ball (x1 x2 : Ball) : Ball :=
  match x1 with ball v1 e1 =>
    match x2 with ball v2 e2 =>
     let v12 := (Fmul near v1 v2) in
       let re12 := (Fdiv2 up (Fsub up (Fmul up v1 v2) (Fmul down v1 v2))) in
         ball v12 (mul_err_up v1 v2 e1 e2 re12)
    end
  end
.


Lemma mul_ball_correct :
  forall (x1 x2 : Ball) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (mul_ball x1 x2) (y1*y2).
Proof.
  intros x1 x2 y1 y2.
  destruct x1 as (v1 & e1), x2 as (v2 & e2).
  unfold mul_ball, models in *.
  set (v12 := Fmul near v1 v2).
  set (w1:=FinjR v1); set (w2:=FinjR v2).
  set (w12 := w1 * w2).
  set (y12 := y1 * y2).
  set (re12 := Fdiv2 up (Fsub up (Fmul up v1 v2) (Fmul down v1 v2))).
  intros H1 H2.
  assert (Rdist (FinjR v12) w12 <= FinjR re12) as Hre. {
    unfold v12,w12,re12.
    replace Fmul with (Fapply Mul) by trivial.
    apply flt_op_near_up_down_sub_hlf_up.
  }
  assert (Rdist w12 y12 <= mul_err w1 w2 (FinjR e1) (FinjR e2)) as Hae. {
    apply mul_err_correct. exact H1. exact H2.
  }
  assert (mul_err w1 w2 (FinjR e1) (FinjR e2) + FinjR re12 <= FinjR (mul_err_up v1 v2 e1 e2 re12)) as Hme. {
    apply mul_err_up_correct.
  }
  1: step (Rdist (FinjR v12) w12 + Rdist w12 y12).
  2: step (mul_err w1 w2 (FinjR e1) (FinjR e2) + FinjR re12).
  - apply Rdist_triang.
  - rewrite -> Rplus_comm. apply Rplus_le_compat. exact Hae. exact Hre.
  - exact Hme.
Qed.



Definition div_err_up v1 v2 e1 e2 re :=
  Fadd up re (Fdiv up (Fadd up e1 (Fmul up e2 (Fdiv up (Fabs v1) (Fabs v2)))) (Fsub down (Fabs v2) e2)).

Definition div_ball_defined (v1 v2 e1 e2 : F) :=
  0 < FinjR (Fsub down (Fabs v2) e2).

Lemma div_ball_nonzero : forall v1 v2 e1 e2,
  div_ball_defined v1 v2 e1 e2 -> 0 <= FinjR e2 -> FinjR e2 < FinjR (Fabs v2).
Proof.
  unfold div_ball_defined.
  intros _ v _ e H He.
  apply Rlt_zero_Rminus.
  apply Rlt_le_trans with (FinjR (Fsub down (Fabs v) e)).
  exact H.
  apply flt_sub_down.
Qed.


Lemma Rminus_ge_0 : forall a b, 0<=b -> a-b <= a.
Proof.
  intros a b Hb.
  assert (a-b <= a-0).
  apply Rplus_le_compat_l; apply Ropp_le_contravar; exact Hb.
  rewrite -> Rminus_0_r in H; assumption.
Qed.

Lemma div_err_up_correct : forall v1 v2 e1 e2 re,
  0<=FinjR e1 ->
    0<=FinjR e2 ->
      0 < FinjR (Fsub down (Fabs v2) e2) ->
        div_err (FinjR v1) (FinjR v2) (FinjR e1) (FinjR e2) + (FinjR re)
          <= FinjR (div_err_up v1 v2 e1 e2 re).
Proof.
  intros v1 v2 e1 e2 re He1 He2 Hr.
  assert (0<FinjR (Fabs v2)) as Hav2. {
    apply Rlt_le_trans with (FinjR (Fsub down (Fabs v2) e2)); [exact Hr|].
    apply Rle_trans with (FinjR (Fabs v2) - FinjR e2); [apply flt_sub_down|].
    apply Rminus_ge_0; [exact He2].
  }
  assert (0<Rabs (FinjR v2) - FinjR e2) as Hrw. {
    apply (Rlt_le_trans _ _ _ Hr). rewrite <- flt_abs_exact. apply flt_sub_down. }
  assert (FinjR (Fabs v2)<>0) as Hav2ne0. {
     apply not_eq_sym. apply Rlt_not_eq. exact Hav2. }
  assert (FinjR v2<>0) as Hv2ne0. {
    apply Rabs_0_neq. rewrite <- flt_abs_exact. exact Hav2ne0. }
  assert (Rabs (FinjR v2)<>0) as Haw2ne0. {
     rewrite <- flt_abs_exact. exact Hav2ne0. }
  assert (0</Rabs (FinjR v2)) as Hraw2. {
    apply Rinv_pos. rewrite <- flt_abs_exact. exact Hav2. }
  unfold div_err,div_err_up, div_ball_defined.
  rewrite -> Rplus_comm.
  apply flt_add_up_le_compat_l.
  rewrite <- Rdiv_Rdiv_Rmult_numerator;
    [|exact Haw2ne0|apply not_eq_sym; apply Rlt_not_eq; apply Hrw].
  apply flt_div_up_le_compat.
  - unfold Rdiv. apply Rle_mult_nonneg_nonneg; [|exact (Rlt_le _ _ Hraw2)].
    apply Rplus_le_le_0_compat; apply Rle_mult_nonneg_nonneg;
      [exact He1|apply Rabs_pos|apply Rabs_pos|exact He2].
  - exact Hr.
  - rewrite -> Rdiv_plus_distr; unfold Rdiv.
    rewrite -> (Rinv_r_simpl_l (Rabs (FinjR v2))); [|exact Haw2ne0].
    apply flt_add_up_le_compat_l.
    rewrite -> (Rmult_comm _ (FinjR e2)).
    rewrite -> (Rmult_assoc).
    rewrite <- Rdiv_mult_inv.
    apply flt_mul_up_le_compat; [exact He2| |apply Rle_refl|].
    -- unfold Rdiv. apply Rle_mult_nonneg_nonneg.
       apply Rabs_pos. apply Rlt_le. apply Hraw2.
    -- repeat (rewrite <- flt_abs_exact).
       apply Rge_le. apply flt_div_up. rewrite -> flt_abs_exact. exact Haw2ne0.
  - rewrite <- flt_abs_exact.
    apply flt_sub_down.
Qed.

Definition div_ball (x1 x2 : Ball) : Ball :=
  match x1 with ball v1 e1 =>
    match x2 with ball v2 e2 =>
      let re := (Fdiv2 up (Fsub up (Fdiv up v1 v2) (Fdiv down v1 v2))) in
        ball (Fdiv near v1 v2) (div_err_up v1 v2 e1 e2 re)
    end
  end
.

Lemma div_ball_correct :
  forall (x1 x2 : Ball) (y1 y2 : R),
    models x1 y1 -> models x2 y2 ->
      div_ball_defined (value x1) (value x2) (error x1) (error x2) ->
        models (div_ball x1 x2) (y1/y2).
Proof.
  intros x1 x2 y1 y2.
  destruct x1 as (v1 & e1); destruct x2 as (v2 & e2).
  unfold div_ball,div_ball_defined, models in *.
  set (rv := Fdiv near v1 v2).
  set (w1:=FinjR v1); set (w2:=FinjR v2).
  set (d1:=FinjR e1); set (d2:=FinjR e2).
  set (rw := w1 / w2).
  set (ry := y1 / y2).
  set (re := Fdiv2 up (Fsub up (Fdiv up v1 v2) (Fdiv down v1 v2))).
  intros H1 H2 Hp; simpl in Hp.
  assert (0<=d1) as Hd1. {
    step (Rdist w1 y1). apply Rge_le. apply Rdist_pos. apply H1. }
  assert (0<=d2) as Hd2. {
    step (Rdist w2 y2). apply Rge_le. apply Rdist_pos. apply H2. }
  assert (0<FinjR (Fabs v2)) as Hav2. {
    apply Rlt_le_trans with (FinjR (Fsub down (Fabs v2) e2)); [exact Hp|].
    apply Rle_trans with (FinjR (Fabs v2) - FinjR e2); [apply flt_sub_down|].
    apply Rminus_ge_0; [exact Hd2].
  }
  assert (0<Rabs w2 - d2) as Hrw. {
    unfold w2. apply (Rlt_le_trans _ _ _ Hp). rewrite <- flt_abs_exact. apply flt_sub_down. }
  assert (FinjR (Fabs v2)<>0) as Hav2ne0. {
     apply not_eq_sym. apply Rlt_not_eq. exact Hav2. }
  assert (w2 <> 0) as Hw2ne0. {
    unfold w2. apply Rabs_0_neq. rewrite <- flt_abs_exact. exact Hav2ne0. }
  assert (Rabs w2 <> 0) as Haw2ne0. {
    unfold w2. rewrite <- flt_abs_exact. exact Hav2ne0. }
  assert (0</Rabs w2) as Hraw2. {
    unfold w2. rewrite <- flt_abs_exact. apply Rinv_pos. exact Hav2. }
  assert (Rdist (FinjR rv) rw <= FinjR re) as Hre. {
    unfold rv,rw,re.
    apply (flt_div_near_up_down_sub_hlf_up); exact Hw2ne0.
  }
  assert (Rdist rw ry <= div_err w1 w2 d1 d2) as Hae. {
    apply div_err_correct.
    unfold w1, w2.
    rewrite <- flt_abs_exact.
    apply (div_ball_nonzero v1 v2 e1 e2). exact Hp.
    exact Hd2.
    exact H1.
    exact H2.
  }
  assert (div_err w1 w2 d1 d2 + FinjR re <= FinjR (div_err_up v1 v2 e1 e2 re)) as Hme. {
    apply div_err_up_correct. exact Hd1. exact Hd2. exact Hp.
  }
  1: step (Rdist (FinjR rv) rw + Rdist rw ry).
  2: step ((div_err w1 w2 d1 d2) + FinjR re).
  - apply Rdist_triang.
  - rewrite -> Rplus_comm. apply Rplus_le_compat. exact Hae. exact Hre.
  - exact Hme.
Qed.






Definition rec_err_up v e re :=
  Fadd up re (Fdiv up e (Fmul down (Fabs v) (Fsub down (Fabs v) e))).

Definition rec_ball_defined v e :=
  0 < FinjR (Fmul down (Fabs v) (Fsub down (Fabs v) e)).

Lemma rec_ball_nonzero : forall v e,
  rec_ball_defined v e -> 0 <= FinjR e -> FinjR e < FinjR (Fabs v).
Proof.
  intros v e H He.
  unfold rec_ball_defined in H.
  assert (0 < FinjR (Fabs v)). {
    assert (0 <= FinjR (Fabs v)) as Hp. { rewrite -> flt_abs_exact. apply Rabs_pos. }
    unfold Rle in Hp; destruct Hp as [Hgt|H0]; [assumption|].
    assert (FinjR (Fmul down (Fabs v) (Fsub down (Fabs v) e)) <= 0) as Hle0. {
      replace 0 with (FinjR (Fabs v) * FinjR (Fsub down (Fabs v) e)).
      apply flt_mul_down.
      rewrite <- H0.
      apply Rmult_0_l.
    }
    apply Rle_not_lt in Hle0.
    contradiction.
  }
  apply Rlt_zero_Rminus.
  apply Rlt_pos_pos_Rmult with (FinjR (Fabs v)).
    exact H0.
  rewrite -> Rmult_comm.
  apply Rlt_le_trans with (FinjR (Fabs v) * (FinjR (Fsub down (Fabs v) e))).
  apply Rlt_le_trans with (FinjR (Fmul down (Fabs v) (Fsub down (Fabs v) e))).
  - exact H.
  - apply flt_mul_down.
  - apply Rmult_le_compat_l.
    apply Rlt_le; exact H0.
    apply flt_sub_down.
Qed.


Lemma rec_err_up_correct : forall v e re,
  0<=FinjR e ->
    rec_ball_defined v e ->
      rec_err (FinjR v) (FinjR e) + (FinjR re)
        <= FinjR (rec_err_up v e re).
Proof.
  intros v e re He Hr.
  unfold rec_err,rec_err_up, rec_ball_defined.
  rewrite -> Rplus_comm.
  step (FinjR re + FinjR (Fdiv up e (Fmul down (Fabs v) (Fsub down (Fabs v) e)))).
  2: apply flt_add_up_le.
  apply Rplus_le_compat_l.
  step (FinjR e / FinjR (Fmul down (Fabs v) (Fsub down (Fabs v) e))).
  2: { apply Rge_le. apply flt_div_up. apply Rgt_not_eq. apply Rlt_gt. exact Hr. }
  apply Rmult_le_compat_l. { exact He. }
  apply Rinv_le_contravar. { exact Hr. }
  rewrite <- flt_abs_exact.
  step (FinjR (Fabs v) * FinjR (Fsub down (Fabs v) e)).
  - apply flt_mul_down.
  - apply Rmult_le_compat_l. { rewrite -> flt_abs_exact. apply Rabs_pos. }
    apply flt_sub_down.
Qed.

Definition rec_ball (x : Ball) : Ball :=
  match x with ball v e =>
    let re := (Fdiv2 up (Fsub up (Frec up v) (Frec down v))) in
      ball (Frec near v) (rec_err_up v e re)
  end
.

Lemma rec_ball_correct :
  forall (x : Ball) (y : R),
    models x y ->
      rec_ball_defined (value x) (error x) ->
        models (rec_ball x) (/y).
Proof.
  intros x y.
  destruct x as (v & e).
  unfold rec_ball,rec_ball_defined, models in *.
  set (rv := Frec near v).
  set (w:=FinjR v).
  set (rw := / w).
  set (ry := / y).
  set (re := Fdiv2 up (Fsub up (Frec up v) (Frec down v))).
  intros H Hp; simpl in Hp.
  assert (0<=FinjR e) as He. {
    step (Rdist w y). apply Rge_le. apply Rdist_pos. apply H.
  }
  assert (FinjR v <> 0) as Hv. {
    apply rec_ball_nonzero in Hp; [|exact He].
    apply Rabs_0_neq; apply Rgt_not_eq; apply Rlt_gt.
    rewrite <- flt_abs_exact.
    apply (Rle_lt_trans _ _ _ He Hp).
  }
  assert (Rdist (FinjR rv) rw <= FinjR re) as Hre. {
    unfold rv,rw,re.
    apply (flt_rec_near_up_down_sub_hlf_up); exact Hv.
  }
  assert (Rdist rw ry <= rec_err w (FinjR e)) as Hae. {
    apply rec_err_correct.
    unfold w.
    rewrite <- flt_abs_exact.
    apply rec_ball_nonzero. exact Hp.
    exact He.
    exact H.
  }
  assert (rec_err w (FinjR e) + FinjR re <= FinjR (rec_err_up v e re)) as Hme. {
    apply rec_err_up_correct. exact He. exact Hp.
  }
  1: step (Rdist (FinjR rv) rw + Rdist rw ry).
  2: step (rec_err w (FinjR e) + FinjR re).
  - apply Rdist_triang.
  - rewrite -> Rplus_comm. apply Rplus_le_compat. exact Hae. exact Hre.
  - exact Hme.
Qed.



Definition div_ball' (x1 x2 : Ball) : Ball :=
  mul_ball x1 (rec_ball x2).


Lemma div_ball_correct' :
  forall (x1 x2 : Ball) (y1 y2 : R),
    models x1 y1 -> models x2 y2 ->
      rec_ball_defined (value x2) (error x2) ->
        models (div_ball' x1 x2) (y1/y2).
Proof.
  intros x1 x2 y1 y2 H1 H2 Hor.
  unfold Rdiv.
  apply mul_ball_correct.
  - exact H1.
  - apply rec_ball_correct.
    exact H2.
    exact Hor.
Qed.


Definition ball_to_bounds (x : Ball) : (Bounds) :=
  let (v,e) := (value x, error x) in
    bounds (Fsub down v e) (Fadd up v e).

Proposition ball_to_bounds_correct : 
  forall (x : Ball) (y : R),
    models x y -> Bounds.models (ball_to_bounds x) y.
Proof.
  intros x y H.
  destruct x as (v & e).
  unfold ball_to_bounds; unfold models in H; unfold Bounds.models; simpl.
  unfold Rdist in H; apply Rabs_ivl in H; destruct H as (Hl&Hu).
  split.
  - apply Rle_trans with (r2:=FinjR v - FinjR e).
    apply flt_sub_down.
    lra.
  - apply Rle_trans with (r2:=FinjR v + FinjR e).
    lra.
    apply Rge_le; apply flt_add_up.
Qed.
  
  
Definition bounds_to_ball (x : Bounds) : (Ball) :=
  let (l,u) := (lower x, upper x) in
    let v := Fdiv near (Fadd near l u) (NinjF 2) in 
      let e := Fmax (Fsub up v l) (Fsub up u v) in
        ball v e.
        
Proposition bounds_to_ball_correct : 
  forall (x : Bounds) (y : R),
    Bounds.models x y -> models (bounds_to_ball x) y.
Proof.
  intros x y H.
  destruct x as (l & u).
  unfold bounds_to_ball; unfold Bounds.models in H; unfold models; simpl.
  destruct H as (Hl&Hu).
  set (v:=Fdiv near (Fadd near l u) (NinjF 2)).
  
  unfold Rdist.
  assert (FinjR v <= y \/ y <= FinjR v) as Hvy; [apply Rle_or_le|].
  destruct Hvy as [Hvley|Hylev].
  - assert (FinjR v - y <= 0) as Hvsy. { apply Rle_minus. exact Hvley. }
    rewrite -> Rabs_neg_eq by (exact Hvsy).
    rewrite -> Ropp_minus_distr.
    apply Rle_trans with (r2:=Rmax (FinjR v - FinjR l) (FinjR u - FinjR v)).
    apply Rle_trans with (r2:=FinjR u - FinjR v).
    -- apply Rplus_le_compat_r.
       exact Hu.
    -- apply Rmax_r.
    -- rewrite -> flt_max_exact.
       apply Rle_max_compat.
       apply Rge_le; apply flt_sub_up.
       apply Rge_le; apply flt_sub_up.
  - assert (0<=FinjR v - y) as Hvsy. { apply Rle_Rminus_zero. exact Hylev. }
    rewrite -> Rabs_pos_eq by (exact Hvsy).
    apply Rle_trans with (r2:=Rmax (FinjR v - FinjR l) (FinjR u - FinjR v)).
    apply Rle_trans with (r2:=FinjR v - FinjR l).
    -- apply Rplus_le_compat_l.
       apply Ropp_le_contravar.
       exact Hl.
    -- apply Rmax_l.
    -- rewrite -> flt_max_exact.
       apply Rle_max_compat.
       apply Rge_le; apply flt_sub_up.
       apply Rge_le; apply flt_sub_up.
Qed.
  

Definition exp_ball (x : Ball) : Ball :=
  bounds_to_ball (exp_bounds (ball_to_bounds x)).

Theorem exp_ball_correct : 
  forall (x : Ball) (y : R), 
    (FinjR (Fsub down Funit (Fadd up (value x) (error x))) > 0) ->
      (models x y) -> (models (exp_ball x) (exp y)).
Proof.
  intros x y Hu H.
  unfold exp_ball.
  apply bounds_to_ball_correct.
  apply exp_bounds_correct.
  apply ball_to_bounds_correct.
  exact H.
  unfold ball_to_bounds; simpl; exact Hu.
Qed.

Definition Rexp_approx (x : R) : R :=
  (x / 2 + 1) * x + 1.
  
Definition exp_approx' (rnd : Rounding) (x : F) : F :=
  Fadd rnd (Fmul rnd (Fadd rnd (Fdiv rnd x (NinjF 2)) Funit) x) Funit.

Definition exp_approx (x : F) : F := exp_approx' near x.

Definition exp_approx_rng (x : F) : F :=
  Fsub up (exp_approx' up x) (exp_approx' down x).

Lemma exp_approx_down : 
  forall (x : F), (0 <= FinjR x) -> FinjR (exp_approx' down x) <= Rexp_approx (FinjR x).
Proof.
  intros x  Hx.
  unfold exp_approx', Rexp_approx.
  apply Rle_trans with (r2:=FinjR (Fmul down (Fadd down (Fdiv down x (NinjF 2)) Funit) x) + 1).
  rewrite <- flt_unit.
  apply flt_add_down.
  apply Rplus_le_compat_r.
  apply Rle_trans with (r2:=FinjR (Fadd down (Fdiv down x (NinjF 2)) Funit) * FinjR x).
  apply flt_mul_down.
  apply Rmult_le_compat_r. apply Hx.
  apply Rle_trans with (r2:=FinjR (Fdiv down x (NinjF 2)) + 1).
  rewrite <- flt_unit.
  apply flt_add_down.
  apply Rplus_le_compat_r.
  replace 2 with (FinjR (NinjF 2%nat)).
  apply flt_div_down.
  rewrite -> flt_ninjr. apply not_0_INR. auto.
  rewrite -> flt_ninjr. auto. 
Qed.
 
Lemma exp_approx_up : 
  forall (x : F), (0 <= FinjR x) -> FinjR (exp_approx' up x) >= Rexp_approx (FinjR x).
Proof.
  intros x  Hx.
  unfold exp_approx', Rexp_approx.
  apply Rge_trans with (r2:=FinjR (Fmul up (Fadd up (Fdiv up x (NinjF 2)) Funit) x) + 1).
  rewrite <- flt_unit.
  apply flt_add_up.
  apply Rplus_ge_compat_r.
  apply Rge_trans with (r2:=FinjR (Fadd up (Fdiv up x (NinjF 2)) Funit) * FinjR x).
  apply flt_mul_up.
  apply Rmult_ge_compat_r. apply Rle_ge; apply Hx.
  apply Rge_trans with (r2:=FinjR (Fdiv up x (NinjF 2)) + 1).
  rewrite <- flt_unit.
  apply flt_add_up.
  apply Rplus_ge_compat_r.
  replace 2 with (FinjR (NinjF 2%nat)).
  apply flt_div_up.
  rewrite -> flt_ninjr. apply not_0_INR. auto.
  rewrite -> flt_ninjr. auto. 
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

Lemma flt_add_near_up : forall (x y : F), FinjR (Fadd near x y) <= FinjR (Fadd up x y).
Proof.
  intros x y.
  assert (Rdist (FinjR (Fadd near x y)) (FinjR x + FinjR y) <= Rdist (FinjR (Fadd up x y)) (FinjR x + FinjR y)) as Hn;
    [apply flt_add_near|].
  assert ((FinjR x + FinjR y) <= FinjR (Fadd up x y)) as Hu; [apply Rge_le; apply flt_add_up|].
  set (zn := FinjR (Fadd near x y)) in *; 
  set (zu := FinjR (Fadd up x y)) in *; 
  set (ze := FinjR x + FinjR y) in *.
  rewrite -> (Rdist_ge zu ze) in Hn; [|apply Rle_ge; exact Hu].
  unfold Rdist in Hn.
  apply Rabs_ivl in Hn.
  apply Rplus_le_reg_r with (r:=-ze).
  apply Hn.
Qed. 
  
Lemma flt_add_near_down : forall (x y : F), FinjR (Fadd down x y) <= FinjR (Fadd near x y).
Proof.
  intros x y.
  assert (Rdist (FinjR (Fadd near x y)) (FinjR x + FinjR y) <= Rdist (FinjR (Fadd down x y)) (FinjR x + FinjR y)) as Hn;
    [apply flt_add_near|].
  assert (FinjR (Fadd down x y) <= (FinjR x + FinjR y)) as Hl; [apply flt_add_down|].
  set (zn := FinjR (Fadd near x y)) in *; 
  set (zl := FinjR (Fadd down x y)) in *; 
  set (ze := FinjR x + FinjR y) in *.
  rewrite -> (Rdist_le zl ze) in Hn; [|exact Hl].
  unfold Rdist in Hn.
  apply Rabs_ivl in Hn.
  rewrite -> Ropp_minus_distr in Hn.
  apply Rplus_le_reg_r with (r:=-ze).
  apply Hn.
Qed. 
  
Lemma flt_add_near_monotone : forall (x1 x2 y1 y2 : F),
  FinjR x1 <= FinjR x2 -> FinjR y1 <= FinjR y2 -> 
    FinjR (Fadd near x1 y1) <= FinjR (Fadd near x2 y2).
Proof. 
(* z1<z2; |w1-z1|<=|w2-z1|; |w2-z2|<=|w1-z2| *)
  assert (forall (x1 x2 : F), (FinjR x1 = FinjR x2) -> x1=x2) as HFinjR. { admit. }
  
  intros x1 x2 y1 y2 Hx Hy.
  set (z1 := FinjR x1 + FinjR y1).
  set (z2 := FinjR x2 + FinjR y2).
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
    assert (Rdist (FinjR (Fadd near x1 y1)) z1 <= (Rdist (FinjR (Fadd near x2 y2)) z1)) as Hz1. {
      apply flt_add_near. }
    assert (Rdist (FinjR (Fadd near x2 y2)) z2 <= (Rdist (FinjR (Fadd near x1 y1)) z2)) as Hz2. {
      apply flt_add_near. }
    set (w1 := FinjR (Fadd near x1 y1)) in *.
    set (w2 := FinjR (Fadd near x2 y2)) in *.

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
  0 <= FinjR x1 -> 0<=FinjR y1 -> FinjR x1 <= FinjR x2 -> FinjR y1 <= FinjR y2 ->
    FinjR (Fmul near x1 y1) <= FinjR (Fmul near x2 y2).
Proof. Admitted.

Lemma flt_mul_near_monotone_r : forall (x1 x2 y : F),
  0<=FinjR y -> FinjR x1 <= FinjR x2 -> 
    FinjR (Fmul near x1 y) <= FinjR (Fmul near x2 y).
Proof. Admitted.

Lemma flt_div_near_monotone : forall (x1 x2 y : F),
  0 <= FinjR x1 -> 0<=FinjR y -> FinjR x1 <= FinjR x2 -> 
    FinjR (Fdiv near x1 y) <= FinjR (Fdiv near x1 y).
Proof. Admitted.

Lemma flt_mul_near_up : forall (x y : F), FinjR (Fmul near x y) <= FinjR (Fmul up x y).
Proof. Admitted.

Lemma flt_div_near_up : forall (x y : F), FinjR (Fdiv near x y) <= FinjR (Fdiv up x y).
Proof. Admitted.

Lemma flt_add_monotone : forall rnd (x1 x2 y1 y2 : F),
  FinjR x1 <= FinjR x2 -> FinjR y1 <= FinjR y2 -> 
    FinjR (Fadd rnd x1 y1) <= FinjR (Fadd rnd x2 y2).
Proof. Admitted.

Lemma exp_approx_le : forall (x : F), (0<=FinjR x) -> Fle (exp_approx' near x) (exp_approx' up x).
Proof.
  intros x H0lex.
  unfold exp_approx'.
  assert (FinjR (Fdiv near x (NinjF 2)) <= FinjR (Fdiv up x (NinjF 2))) as H0. {
    apply flt_div_near_up. }
  assert ( FinjR (Fadd near (Fdiv near x (NinjF 2)) Funit)
             <= FinjR (Fadd up (Fdiv up x (NinjF 2)) Funit) ) as H1. {
    apply Rle_trans with (r2:=FinjR (Fadd near (Fdiv up x (NinjF 2)) Funit)).
    apply flt_add_near_monotone.
    exact H0.
    apply Req_le; reflexivity.
    apply flt_add_near_up.
  }
  assert ( FinjR (Fmul near (Fadd near (Fdiv near x (NinjF 2)) Funit) x)
             <= FinjR (Fmul up (Fadd up (Fdiv up x (NinjF 2)) Funit) x) ) as H2. {
    apply Rle_trans with (r2:=FinjR (Fmul near (Fadd up (Fdiv up x (NinjF 2)) Funit) x)).
    apply flt_mul_near_monotone_r.
    exact H0lex.
    exact H1.
    apply flt_mul_near_up.
  }
  assert (FinjR (Fadd near (Fmul near (Fadd near (Fdiv near x (NinjF 2)) Funit) x) Funit)
            <= FinjR (Fadd up (Fmul up (Fadd up (Fdiv up x (NinjF 2)) Funit) x) Funit)) as H3. {
    apply Rle_trans with (r2:=FinjR (Fadd near (Fmul up (Fadd up (Fdiv up x (NinjF 2)) Funit) x) Funit)).
    apply flt_add_near_monotone.
    exact H2.
    apply Req_le; reflexivity.
    apply flt_add_near_up.
  }
  set (wn:=(Fadd near (Fmul near (Fadd near (Fdiv near x (NinjF 2)) Funit) x) Funit)) in *.
  set (wu:=(Fadd up (Fmul up (Fadd up (Fdiv up x (NinjF 2)) Funit) x) Funit)) in *.
  unfold Fle.
  exact H3.  
Qed.

Lemma bounds_error : forall (l u x1 x2 : R), l<=x1<=u -> l<=x2<=u -> Rdist x1 x2 <= u-l.
Proof. intros; unfold Rdist; apply Rabs_le; lra. Qed.
  
Lemma exp_approx_ge : forall (x : F), (0<=FinjR x) -> Fle (exp_approx' down x) (exp_approx' near x).
Proof. Admitted.

Check exp_approx_le.
Check exp_approx_ge.
 
Lemma exp_approx_correct : 
  forall (x : F), (0<=FinjR x) -> Rdist (Rexp_approx (FinjR x)) (FinjR (exp_approx x)) <= FinjR (exp_approx_rng x).
Proof.
  intros x Hx.
  unfold exp_approx, exp_approx_rng.
  set (wl := exp_approx' down x).
  set (wu := exp_approx' up x).
  assert (FinjR wu - FinjR wl <= FinjR (Fsub up wu wl) ) as He. {
    apply Rge_le; apply flt_sub_up. }
  set (zn := FinjR (exp_approx' near x)).
  set (ze := Rexp_approx (FinjR x)).
  apply Rle_trans with (r2:=FinjR wu - FinjR wl).
  set (zl := FinjR wl) in *.
  set (zu := FinjR wu) in *.
  assert (zl <= zn) as Hln. { apply exp_approx_ge. exact Hx. }
  assert (zn <= zu) as Hnu. { apply exp_approx_le. apply Hx. }
  assert (zl <= ze) as Hle. { apply exp_approx_down. exact Hx. }
  assert (ze <= zu) as Heu. { apply Rge_le; apply exp_approx_up. exact Hx. }
  unfold Rdist; apply Rabs_le.
  lra.
  exact He.
Qed.

(*
d(Fexp_approx x , exp x) <= d(Fexp_approx x , Rexp_approx x) + d(Rexp_approx x , exp x).
d(x,y)<=d -> d(e^x,e^y)<=e^x*d(e^(y-x),1)<=e^x * (e^d-1)
Suppose w≈e^x. Then 
  d(w,e^y)<=d(w,e^x)+d(e^x,e^y)
          <=d(w,e^x)+e^x*(e^d-1)
          <=d(w,e^x)+(w+d(w,e^x))*(e^d-1)
  
(1+x/n)^n=1+x+(n*(n-1))/2/n^2*x^2+...=1+x+(1-1/n)*x^2/2+...
*)

End FloatBall.
