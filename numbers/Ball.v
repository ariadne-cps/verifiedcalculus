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

Require Import R_addenda.
Require Import Floats.
Require Import Analysis.

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

End FloatBall.
