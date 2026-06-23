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

Require Import RealAddenda.
Require Import Floats.
Require Import Analysis.

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

End Ball_section.

End Bll.

Export Bll(Ball,ball).
