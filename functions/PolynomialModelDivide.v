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


Require Import Sum.

Require Export PolynomialModels.
Require Export PolynomialModelAdd.
Require Export PolynomialModelSubtract.
Require Export PolynomialModelScale.
Require Export PolynomialModelMonomialScale.
Require Export PolynomialModelMultiply.

Require Import Recdef.
Require Import Lia.
Require Import Lra.

Section Polynomial_Model_Divide.

Open Scope R_scope.

Context `{F : Type} `{FltF : Float F}.


Lemma PMmodels_approximation : forall t f f' d,
  PMmodels t f -> (forall x, -1<=x<=1 -> Rdist (f x) (f' x) <= FinjR d) ->
    PMmodels (PMadd t (PMerror_ball d)) f'.
Proof.
  unfold PMmodels.
  intros t f f' d.
  intros Hf He.
  destruct t as [p e].
  intros x Hx.
  specialize (Hf x Hx).
  specialize (He x Hx).
  simpl in *.
  unfold PMerror_ball, PMadd.
  simpl.
  unfold PMadd_error. simpl.
  rewrite -> (Padd_approx_eq_nil_r p).
  rewrite -> (Padd_error_eq_nil_r p).
  simpl.
  apply Rle_trans with (Rabs (Pax_eval p x - f x) + Rabs (f x - f' x)).
  - apply Rabs_dist_triang.
  - apply Rle_trans with (FinjR e + FinjR d).
    -- apply Rplus_le_compat. exact Hf. exact He.
    -- stepl ((FinjR e + FinjR d) + 0%R) by ring.
       rewrite <- flt_null.
       apply Rle_trans with (FinjR (Fadd up e d) + FinjR Fnull).
       --- apply Rplus_le_compat_r. apply flt_add_up_le.
       --- apply flt_add_up_le.
Qed.



Fixpoint PMgeometric n p :=
  match n with
  | O => PMconstant Funit
  | S m => PMadd (PMconstant Funit) (PMmul p (PMgeometric m p))
  end
.

Theorem PMgeometric_correct : forall n t f,
  PMmodels t f -> PMmodels (PMgeometric n t) (Fgeometric n f).
Proof.
  intros n t f H.
  induction n.
  - simpl.
    rewrite <- flt_unit. apply PMconstant_correct.
  - simpl.
    apply PMadd_correct.
    -- rewrite <- flt_unit.
       apply PMconstant_correct.
    -- apply PMmul_correct.
         exact H. exact IHn.
Qed.


Definition PMrec (n : nat) (t : PolynomialModel) : PolynomialModel :=
  let t' := PMsub (PMconstant Funit) t in
  let d' := PMnorm t' in
  PMadd (PMgeometric n t') (PMerror_ball (Fdiv up (Fpow_up d' (n+1)) (Fsub down Funit d'))).

(* A lower bound on min[-1<=x<=1](1-t(x)) *)
Definition PMunit_mig t :=
   FinjR (Fsub down Funit (PMnorm (PMsub (PMconstant Funit) t))).

Theorem PMrec_correct : forall (n : nat) (t : PolynomialModel) (f : R->R),
  (PMunit_mig t > 0) -> PMmodels t f ->
      PMmodels (PMrec n t) (fun x => / f(x)).
Proof.
  intros n t' f'.
  intros Hd H'.
  unfold PMunit_mig in *.
  remember (PMsub (PMconstant Funit) t') as t.
  remember (fun x => 1 - f' x) as f.
  set (b:=PMnorm t).
  assert (FinjR b < 1) as Hb1. {
    assert (FinjR (Funit) - FinjR (PMnorm t) > 0) as Hb'. {
      apply Rge_gt_trans with (FinjR (Fsub down Funit (PMnorm t))).
      apply Rle_ge. apply flt_sub_down. exact Hd.
    }
    rewrite -> flt_unit in Hb'.
    apply Rplus_lt_reg_r with (-FinjR b).
    rewrite -> Rplus_opp_r. apply Rgt_lt. apply Hb'.
  }
  assert (PMmodels t f) as H. {
    rewrite -> Heqt. rewrite -> Heqf.
    apply PMsub_correct.
    rewrite <- flt_unit.
    apply PMconstant_correct.
    exact H'.
  }
  assert (forall x, -1<=x<=1 -> Rabs (f x) <= FinjR b) as Hfb. {
    apply PMnorm_correct. exact H.
  }
  assert (forall x, -1<=x<=1 -> f' x > 0) as Hf0'. {
    intros x Hx.
    replace (f' x) with (1 - f x).
    assert (f x < 1) as Hf1. {
      apply Rabs_def2.
      apply Rle_lt_trans with (FinjR b).
      apply PMnorm_correct. exact H. exact Hx. exact Hb1.
    }
    apply Rplus_lt_reg_r with (f x).
    rewrite -> Rplus_0_l.
    unfold Rminus.
    rewrite -> Rplus_assoc.
    rewrite -> Rplus_opp_l.
    rewrite -> Rplus_0_r.
    exact Hf1.
    assert (f x = 1 - f' x) as Hfx. { rewrite -> Heqf. reflexivity. }
    rewrite -> Hfx.
    unfold Rminus. rewrite -> Ropp_plus_distr. rewrite <- Rplus_assoc.
    rewrite -> Rplus_opp_r. rewrite -> Rplus_0_l. rewrite -> Ropp_involutive.
    reflexivity.
  }
  apply PMmodels_extensional with (fun x => /(1 - f x)).
  2: { intros x Hx. rewrite -> Heqf. field. apply Rgt_not_eq. apply Hf0'. exact Hx. }
  unfold PMrec.
  rewrite <- Heqt.
  clear H'.

  assert (0<=FinjR b) as Hb0. {
    apply Rle_trans with (Rabs (f 0)).
    apply Rabs_pos.
    apply PMnorm_correct.
    exact H.
    lra.
  }
  set ( e := Fdiv up (Fpow_up b (n+1)) (Fsub down Funit b) ).
  set (fg := fun x => Fgeometric n f x).
  set (fe := fun x => /(1-f x) - Fgeometric n f x).
  apply PMmodels_extensional with (fun x => fg x + fe x).
  - apply PMadd_correct.
    -- apply PMgeometric_correct. exact H.
    -- unfold PMerror_ball, PMmodels.
       simpl.
       intros x Hx.
       replace (Rabs (0 - fe x)) with (Rabs (fe x)).
       2: { unfold Rminus. rewrite -> Rplus_0_l. rewrite -> Rabs_Ropp. reflexivity. }
       set (d:=FinjR b).
       assert (forall x, -1<=x<=1 -> Rabs (fe x) <= d^(n+1)/(1-d)) as Hde. {
         unfold fe. intros x0 Hx0. rewrite -> FRgeometric_equal. revert x0 Hx0.
         apply Fgeometric_approx.
         unfold d, b. exact Hb1.
         apply PMnorm_correct.
         exact H.
       }
       apply Rle_trans with (d^(n+1)/(1-d)).
       --- apply Hde. exact Hx.
       --- unfold d, e.
           apply Rle_trans with ( FinjR (Fpow_up b (n + 1)) / FinjR (Fsub down Funit b) ).
           ---- apply Rmult_le_compat.
                ----- apply pow_le. exact Hb0.
                ----- apply Rlt_le. apply Rinv_pos.
                      apply Rplus_lt_reg_r with (FinjR b). rewrite -> Rplus_0_l.
                      unfold Rminus. rewrite -> Rplus_assoc. rewrite -> Rplus_opp_l. rewrite -> Rplus_0_r. exact Hb1.
                ----- apply flt_pow_up_le. exact Hb0.
                ----- apply Rinv_le_contravar.
                      apply Rlt_gt. apply Hd.
                      rewrite <- flt_unit. apply flt_sub_down.
           ---- apply Rge_le. apply flt_div_up.
                apply Rgt_not_eq. apply Hd. (* The inequality FinjR (Fsub down Funit b) <> 0 is probably false. *)
  - unfold fg, fe. intros x Hx. field.
    assert (Rabs (f x) < 1) as Hfx1. {
      apply Rle_lt_trans with (FinjR b).
      apply PMnorm_correct. exact H. exact Hx. exact Hb1.
    }
    assert (f x < 1 /\ -1 < f x) as Hfx0. { apply Rabs_def2. exact Hfx1. }
    lra.
Qed.

Definition PMdiv n t1 t2 := PMmul t1 (PMrec n t2).

Theorem PMdiv_correct : forall n t1 t2 f1 f2,
  (PMunit_mig t2 > 0) ->
    PMmodels t1 f1 -> PMmodels t2 f2 ->
      PMmodels (PMdiv n t1 t2) (fun x => f1 x / f2 x).
Proof.
  intros n t1 t2 f1 f2 Hd H1 H2.
  unfold PMdiv, Rdiv.
  apply PMmul_correct. exact H1.
  set ( f2s := fun x => / f2 x ).
  apply PMrec_correct. exact Hd. exact H2.
Qed.


Close Scope R_scope.

End Polynomial_Model_Divide.
