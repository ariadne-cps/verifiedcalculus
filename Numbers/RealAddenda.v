(******************************************************************************
 *  Numbers/RealAddenda.v
 *
 *  Copyright 2006-10 Milad Niqui
 *            2023-6 Pieter Collins
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


(* This file contains various properties of R that are not in the standard library. *)

From Stdlib Require Import Reals.
From Stdlib Require Import Reals.Rbase.
From Stdlib Require Import Reals.Rfunctions.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rdefinitions.

From Stdlib Require Import Lra.

Open Scope R_scope.

Notation Rpow := Rpow_def.pow.

Lemma Rpow_zero : forall x, Rpow x (0%nat) = 1.
Proof. reflexivity. Qed.
Lemma Rpow_one : forall x, Rpow x (1%nat) = x.
Proof. intro x. simpl. exact (Rmult_1_r x). Qed.


Lemma Rlt_stepl:forall x y z, Rlt x y -> x=z -> Rlt z y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Lemma Rlt_stepr:forall x y z, Rlt x y -> y=z -> Rlt x z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Declare Left Step Rlt_stepl.
Declare Right Step Rlt_stepr.

Lemma Rlt_le_rng : forall {x1 x2 x3}, x1 < x2 < x3 -> x1 <= x2 <= x3.
Proof. intros; split. all: now apply Rlt_le. Qed.



Lemma Rle_eq_trans : forall x1 x2 x3, x1 <= x2 -> x2 = x3 -> x1 <= x3.
Proof. intros x1 x2 x3 H12 H23. rewrite <- H23. exact H12. Qed.

Lemma Req_le_trans : forall x1 x2 x3, x1 = x2 -> x2 <= x3 -> x1 <= x3.
Proof. intros x1 x2 x3 H12 H23. rewrite -> H12. exact H23. Qed.

Lemma Rle_stepl:forall x y z, Rle x y -> x=z -> Rle z y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Lemma Rle_stepr:forall x y z, Rle x y -> y=z -> Rle x z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Declare Left Step Rle_stepl.
Declare Right Step Rle_stepr.


Lemma Rneq_stepl:forall x y z:R, x<>y -> x=z -> z<>y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Lemma Rneq_stepr:forall x y z:R, x<>y -> y=z -> x<>z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Declare Left Step Rneq_stepl.
Declare Right Step Rneq_stepr.

Lemma Rle_not_eq_lt : forall r : R, r<=0 -> r<>0 -> r<0.
Proof.
  unfold Rle. intros r Hle0 Hne0.
  apply or_ind with (A:=r<0) (B:=r=0).
  - trivial.
  - intro Heq0. contradiction.
  - exact Hle0.
Qed.

Lemma Rge_not_eq_gt : forall r : R, 0<=r -> r<>0 -> 0<r.
Proof.
  unfold Rle. intros r Hge0 Hne0.
  apply or_ind with (A:=0<r) (B:=0=r).
  - trivial.
  - intro Heq0. assert (r=0). { apply eq_sym. exact Heq0. } contradiction.
  - exact Hge0.
Qed.


Lemma Ropp_0_le_le_contravar : forall r, 0 <= r -> -r <= 0.
Proof. intros r Hr. apply Rge_le. now apply Ropp_0_le_ge_contravar. Qed.

Lemma Ropp_0_le_contravar : forall (x:R), x <= 0 <-> 0 <= -x.
Proof.
  intro x.
  split.
  intro H. apply Ropp_0_ge_le_contravar. apply Rle_ge. exact H.
  intro H.
  assert (x + 0 <= x + -x) as He.
  apply Rplus_le_compat. apply Rle_refl. exact H.
  rewrite -> Rplus_0_r in He. rewrite -> Rplus_opp_r in He. exact He.
Qed.

Lemma Ropp_0_lt_contravar : forall r : R, r < 0 <-> 0 < - r.
Proof.
  intro r. split.
  - intro Hlt. apply Ropp_0_gt_lt_contravar. apply Rlt_gt. exact Hlt.
  - intro Hngt. rewrite <- (Ropp_involutive r). apply Ropp_lt_gt_0_contravar. apply Rlt_gt. exact Hngt.
Qed.

Lemma Rminus_eq_0 : forall x, (x-x=0)%R.
Proof.
  intro x.
  ring.
Qed.

Lemma Rminus_0_eq : forall r1 r2 : R, r1 - r2 = 0 -> r1 = r2.
Proof.
  intros. assert (r1=r2 \/ r1<>r2) as Heq_dec by (apply Req_dec).
  destruct Heq_dec as [Heq|Hneq]. exact Heq. apply Rminus_eq_contra in Hneq. contradiction.
Qed.

Lemma Rminus_ge_0 : forall a b, 0<=b -> a-b <= a.
Proof.
  intros a b Hb.
  assert (a-b <= a-0).
  apply Rplus_le_compat_l; apply Ropp_le_contravar; exact Hb.
  rewrite -> Rminus_0_r in H; assumption.
Qed.

Lemma Rlt_zero_Rminus : forall r1 r2:R , 0 < r1-r2  -> r2 < r1.
Proof.
 intros r1 r2 H; apply Rminus_lt; apply Ropp_lt_cancel; rewrite Ropp_minus_distr; rewrite Ropp_0; assumption.
Qed.

Lemma Rle_zero_Rminus : forall r1 r2:R , 0 <= r1-r2  -> r2 <= r1.
Proof.
 intros r1 r2 H; apply RIneq.Rminus_le; apply RIneq.Ropp_le_cancel;rewrite RIneq.Ropp_minus_distr; rewrite RIneq.Ropp_0; assumption.
Qed.

Lemma Rle_Rminus_zero : forall r1 r2:R , r2 <= r1 -> 0 <= r1-r2.
Proof.
 intros r1 r2 H; lra.
Qed.

Lemma Rminus_le_compat:
  forall r1 r2 r3 r4 : R, r1 <= r2 -> r4 <= r3 -> r1 - r3 <= r2 - r4.
Proof.
  intros r1 r2 r3 r4 H12 H34;
  lra.
Qed.

Lemma Rminus_le_compat_l:
  forall r1 r2 r3 : R, r1 <= r2 <-> r1 - r3 <= r2 - r3.
Proof.
  intros r1 r2 r3. split. all: intro H12; lra.
Qed.

Lemma Rminus_le_compat_r :
  forall r1 r2 r3 : R, r3 <= r2 <-> r1 - r2 <= r1 - r3.
Proof.
  intros r1 r2 r3. split. all: intro H12; lra.
Qed.

Lemma Rminus_plus_cancel : forall (x y : R), (x-y)+y = x.
Proof. intros x y; unfold Rminus; rewrite -> Rplus_assoc, -> Rplus_opp_l, -> Rplus_0_r; reflexivity. Qed.

Lemma Rplus_minus_cancel : forall (x y : R), (x+y)-y = x.
Proof. intros x y; unfold Rminus; rewrite -> Rplus_assoc, -> Rplus_opp_r, -> Rplus_0_r; reflexivity. Qed.

Lemma Rminus_plus_eqv : forall r r1 r2, r = r1 - r2 <-> r + r2 = r1.
Proof.
  intros r r1 r2.
  split.
  - intro Hr. rewrite -> Hr, <- Rplus_minus_swap. now rewrite -> Rplus_minus_cancel.
  - intro Hr1. rewrite <- Hr1. now rewrite -> Rplus_minus_cancel.
Qed.

Lemma Rlt_Rminus_zero : forall r1 r2:R , r2 < r1 -> 0 < r1-r2.
Proof.
 intros r1 r2 H; lra.
Qed.

Lemma Rlt_not_eq': forall r1 r2 : R, r1 < r2 -> r2 <> r1.
Proof.
 intros r1 r2 H; apply sym_not_eq; apply Rlt_not_eq; assumption.
Qed.


Lemma Rmult_reg_nonzero_r: forall r1 r2 : R, r1 * r2 <> 0 -> r2 <> 0.
Proof.
 intros r1 r2 H_r12 H_false; apply H_r12; subst r2; ring.
Qed.

Lemma Rmult_reg_nonzero_l: forall r1 r2 : R, r1 * r2 <> 0 -> r1 <> 0.
Proof.
 intros r1 r2 H_r12 H_false; apply H_r12; subst r1; ring.
Qed.

Lemma Rlt_Ropp_pos: forall r : R, r < 0 -> 0 < - r.
Proof.
 intros r Hr; lra.
Qed.

Lemma Rlt_mult_neg_neg: forall r1 r2 : R, r1<0 -> r2<0 -> 0 < r1 * r2.
Proof.
 intros r1 r2 Hr1 Hr2; stepr ((-r1)*(-r2)); [|ring]; apply Rmult_lt_0_compat; lra.
Qed.

Definition Rinv_pos:= Rinv_0_lt_compat.
Definition Rle_mult_nonneg_nonneg:=Rmult_le_pos.
Definition Rlt_mult_pos_pos:=Rmult_lt_0_compat.
Definition Rmult_resp_nonzero:=RIneq.prod_neq_R0.
Definition Rinv_resp_nonzero:=Rinv_neq_0_compat.
Definition Ropp_resp_nonzero:=RIneq.Ropp_neq_0_compat.

#[export]
Hint Resolve Rlt_Ropp_pos Rinv_pos R1_neq_R0 Rle_mult_nonneg_nonneg
             Rlt_mult_pos_pos Rlt_mult_neg_neg Rlt_not_eq' Rlt_not_eq
             Rmult_resp_nonzero Rinv_resp_nonzero Ropp_resp_nonzero.

Lemma Rmult_mult_nonneg: forall r, 0<=r*r.
Proof.
 intros r; stepr (Rsqr r); trivial; apply Rle_0_sqr.
Qed.

Lemma Rmult_mult_Ropp_nonpos: forall r, -(r*r)<=0.
Proof.
 intros r; generalize (r*r) (Rmult_mult_nonneg r); clear r; intros; lra.
Qed.

Lemma Rlt_mult_pos_neg: forall r1 r2 : R, r1 < 0 -> 0<r2 -> r1 * r2<0.
Proof.
 intros r1 r2 Hr1 Hr2; apply Ropp_lt_cancel; stepl R0; [|ring]; stepr ((-r1)*r2); [|ring]; apply Rlt_mult_pos_pos; auto.
Qed.

Lemma Rlt_mult_neg_pos: forall r1 r2 : R, 0<r1 -> r2<0 -> r1 * r2<0.
Proof.
 intros r1 r2 Hr1 Hr2; apply Ropp_lt_cancel; stepl R0; [|ring]; stepr (r1*(-r2)); [|ring]; apply Rlt_mult_pos_pos; auto.
Qed.

Lemma Ropp_mult_distr: forall r1 r2 : R, - (r1 * r2) = (- r1 * r2).
Proof.
 intros r1 r2; ring.
Qed.

Lemma Rmult_le_opp_compat_l : forall (r r1 r2 : R), r<=0 -> r1 <= r2 -> r*r2 <= r*r1.
Proof.
  intros r r1 r2 Hr0 Hr12.
  assert (0 <= -r) as H0r. { apply Ropp_0_ge_le_contravar. apply Rle_ge. exact Hr0. }
  apply Ropp_le_cancel;
  rewrite -> Ropp_mult_distr; rewrite -> Ropp_mult_distr.
  apply Rmult_le_compat_l; [exact H0r|]; exact Hr12.
Qed.

Lemma Rmult_le_opp_compat_r : forall (r r1 r2 : R), r<=0 -> r1 <= r2 -> r2*r <= r1*r.
Proof.
  intros r r1 r2 Hr0 Hr12.
  assert (r1 * r = r * r1) as H1c; [apply Rmult_comm|].
  assert (r2 * r = r * r2) as H2c; [apply Rmult_comm|].
  rewrite -> H1c; rewrite -> H2c.
  apply Rmult_le_opp_compat_l. assumption. assumption.
Qed.



Lemma Rdiv_lt_compat_l : forall r r1 r2 : R, 0 < r -> 0 < r2 < r1 -> r / r1 < r / r2.
Proof.
  intros r r1 r2 Hr0 [Hr1 Hr12].
  repeat rewrite -> Rdiv_def.
  apply Rmult_lt_compat_l.
  exact Hr0.
  now apply Rinv_0_lt_contravar.
Qed.

Lemma Rdiv_lt_compat_r : forall r r1 r2 : R, 0 < r -> r1 < r2 -> r1 / r < r2 / r.
Proof.
  intros r r1 r2 Hr0.
  repeat rewrite -> Rdiv_def.
  apply Rmult_lt_compat_r.
  now apply Rinv_pos.
Qed.

Lemma Rdiv_integral_contrapositive : 
  forall x y, x <> 0 -> y <> 0 -> x / y <> 0.
Proof.
  intros x y Hx Hy.
  rewrite -> Rdiv_def.
  apply (Rmult_integral_contrapositive x (/y)).
  split. exact Hx. apply Rinv_resp_nonzero; exact Hy.
Qed.

Lemma Rdiv_mult_eqv : forall r r1 r2, r2 <> 0 -> r = r1 / r2 <-> r * r2 = r1.
Proof.
  intros r r1 r2 Hr2.
  split.
  - intro Hr. rewrite -> Hr, <- Rmult_div_swap. exact (Rmult_div_l r1 r2 Hr2).
  - intro Hr1. rewrite <- Hr1. now rewrite -> (Rmult_div_l r r2 Hr2).
Qed.

Lemma Rdiv_Rmult_pos_neg_Rle: forall x y z t, R0 < z -> t < R0 -> x / z <= y / t -> y * z <= x * t.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_neg_pos; assumption.
Qed.

Lemma Rdiv_Rmult_pos_neg_Rle': forall x y z t, R0 < z -> t < R0 -> x / z <= y / t -> z*y <= t*x.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_neg_pos; assumption.
Qed.

Lemma Rdiv_Rmult_neg_pos_Rle: forall x y z t, z<0 -> 0<t -> x / z <= y / t -> y * z <= x * t.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_neg_pos_Rle': forall x y z t, z<0 -> 0<t -> x / z <= y / t -> z*y <= t*x.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_neg_neg_Rle: forall x y z t, z<0 -> t<0 -> x / z <= y / t -> x * t<=y * z.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_neg_neg_Rle': forall x y z t, z<0 -> t<0 -> x / z <= y / t -> t*x<=z*y.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_pos_pos_Rle: forall x y z t, 0<z -> 0<t -> x / z <= y / t -> x * t<=y * z.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_pos_pos_Rle': forall x y z t, 0<z -> 0<t -> x / z <= y / t -> t*x<=z*y.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.


Lemma Rdiv_Ropp_numerator: forall x y, y <> R0 -> (- x / y = - (x / y))%R.
Proof.
 intros x y Hy; field; trivial.
Qed.

Lemma Rdiv_Ropp_denomintor: forall x y, y <> R0 -> (x / - y = - (x / y))%R.
 intros x y Hy; field; trivial.
Qed.

Lemma Rdiv_Rmult_numerator: forall (x y z:R), y<>R0 -> (z*(x/y)=(z*x)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rdiv_Rmult_numerator_r: forall (x y z:R), y<>R0 -> ((x/y)*z=(x*z)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rdiv_Rplus_Rmult: forall (x y z:R), y<>R0 -> (x/y + z = (x+y*z)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rdiv_Rminus_Rmult: forall x y z, y<>R0 -> (x/y - z = (x-y*z)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.



Lemma Rminus_Rdiv_Rmult: forall x y z, ~(y=R0)->(z-x/y=(y*z-x)/y)%R.
Proof.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rplus_Rdiv_Rmult: forall x y z, ~(y=R0)->(z+x/y=(y*z+x)/y)%R.
Proof.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rminus_Rdiv:forall x y z t, z<>R0 -> t<>R0 -> (x/z - y/t = (x*t-y*z)/(z*t))%R.
Proof.
 intros x y z t Hz Ht; field; split; trivial.
Defined.

Lemma Rplus_Rdiv:forall x y z t, z<>R0 -> t<>R0 -> (x/z + y/t = (x*t+y*z)/(z*t))%R.
Proof.
 intros x y z t Hz Ht; field; split; trivial.
Defined.

Lemma Rle_pos_nonneg_Rmult: forall r1 r2 : R, 0 < r1 ->  0 <= r2 * r1 -> 0<= r2.
Proof.
 intros r1 r2 Hr2 Hr12; stepr ((r2*r1)*/r1); try field; auto; apply (Rle_mult_inv_pos _ _ Hr12 Hr2).
Qed.

Lemma Rle_pos_nonneg_Rdiv: forall r1 r2 : R, 0 < r1 ->  0 <= r2 / r1 -> 0<= r2.
Proof.
 intros r1 r2 Hr2 Hr12; unfold Rdiv in Hr12; apply Rle_pos_nonneg_Rmult with (/r1); auto.
Qed.

Lemma Rle_mult_nonpos_nonpos: forall r1 r2 : R, r1<=0 -> r2<=0 -> 0 <= r1 * r2.
Proof.
 intros r1 r2 Hr1 Hr2; stepr ((-r1)*(-r2)); [|ring]; apply Rle_mult_nonneg_nonneg; lra.
Qed.

Lemma Rlt_pos_pos_Rmult: forall r1 r2 : R, 0 < r1 ->  0 < r2 * r1 -> 0< r2.
Proof.
 intros r1 r2 Hr2 Hr12; stepr ((r2*r1)*/r1); try field; auto; apply (Rle_mult_inv_pos _ _ Hr12 Hr2).
Qed.

Lemma Rlt_pos_pos_Rdiv: forall r1 r2 : R, 0 < r1 ->  0 < r2 / r1 -> 0< r2.
Proof.
 intros r1 r2 Hr2 Hr12; unfold Rdiv in Hr12; apply Rlt_pos_pos_Rmult with (/r1); auto.
Qed.

Lemma Rdiv_Rdiv_simplify: forall x y z : R, z <> R0 -> y <> R0 -> x / z / (y / z) = x / y.
Proof.
 intros x y z Hz Hy; field; auto.
Qed.

Definition Rmult_reg_l := RIneq.Rmult_eq_reg_l.

Lemma Rmult_reg_r : forall r r1 r2 : R, r1 * r = r2 * r -> r <> 0 -> r1 = r2.
Proof.
  intros x y z; rewrite (Rmult_comm z x); rewrite (Rmult_comm y x); exact (Rmult_reg_l x y z).
Qed.

Lemma Rmult_Rdiv: forall x y z t : R, z <> R0 -> t <> R0 -> x * t = y * z -> x / z = y / t.
Proof.
 intros x y z t Hz Ht Hxtyz;
 apply Rmult_reg_l with (z*t); auto;
 transitivity (x*t);
 [|transitivity (y*z); trivial]; field; trivial.
Qed.

Lemma Rmult_Rdiv_pos_Rle: forall x y z t, (R0 < z)%R -> (R0 < t)%R -> (x * t <= y * z)%R -> (x / z <= y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rle_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Rle_mult_inv_pos; auto;
 apply Rle_Rminus_zero; assumption.
Qed.

Lemma Rmult_Rdiv_neg_Rle: forall x y z t, (z < R0)%R -> (t < R0)%R -> (x * t <= y * z)%R -> (x / z <= y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rle_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Rle_mult_inv_pos; auto;
 apply Rle_Rminus_zero; assumption.
Qed.


Lemma Rinv_neg : forall r : R, r < 0 -> / r < 0.
Proof.
  intro r. intro Hlt0.
  rewrite -> Ropp_0_lt_contravar. rewrite <- Rinv_opp. apply Rinv_pos. rewrite <- Ropp_0_lt_contravar. exact Hlt0.
Qed.

Lemma Rinv_le_compat : forall r1 r2 : R, (0 < r1 \/ r2 < 0) -> r1 <= r2 ->  / r2 <=  / r1.
Proof.
  intros r1 r2 Hne0 H.
  destruct Hne0.
  - apply Rinv_le_contravar. exact H0. exact H.
  - apply Ropp_le_cancel. rewrite <- Rinv_opp. rewrite <- Rinv_opp. apply Rinv_le_contravar.
    -- apply Ropp_0_lt_contravar. exact H0.
    -- apply Ropp_le_contravar. exact H.
Qed.


Lemma Rdiv_Rmult_simplify: forall x y z : R, z <> 0%R -> y <> 0%R -> (x * z / (y * z))%R = (x / y)%R.
Proof.
 intros; field; auto.
Qed.

Lemma Rdiv_Rmult_numerator_denominator: forall x y z t: R, t <> 0%R -> y <> 0%R -> ((x/y)*(z/t))%R=((x*z)/(y*t))%R.
Proof.
 intros; field; auto.
Qed.

Lemma Rdiv_Rdiv_Rmult_numerator: forall x y z : R, y <> 0 -> z <> 0 -> (x / y / z) = (x / (y * z)).
Proof.
 intros x y z Hy Hz; field; split; trivial.
Qed.

Lemma Rdiv_Rdiv_Rmult_denominator: forall x y z : R, y <> 0 -> z <> 0 -> (x / (y / z)) = (x*z / y ).
Proof.
 intros x y z Hy Hz; field; auto.
Qed.

Lemma Rmult_Rdiv_pos_Rlt: forall x y z t, (R0 < z)%R -> (R0 < t)%R -> (x * t < y * z)%R -> (x / z < y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rlt_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto;
 apply Rlt_Rminus_zero; assumption.
Qed.

Lemma Rmult_Rdiv_neg_Rlt: forall x y z t, (z < R0)%R -> (t < R0)%R -> (x * t < y * z)%R -> (x / z < y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rlt_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto;
 apply Rlt_Rminus_zero; assumption.
Qed.

Lemma Rdiv_le_compat_l : forall r r1 r2 : R, 0 <= r -> (0 < r1 \/ r2 < 0) -> r1 <= r2 -> r / r2 <= r / r1.
Proof.
  intros r r1 r2 Hge0 Hor H. unfold Rdiv.
  apply Rmult_le_compat_l; [apply Hge0|]. exact (Rinv_le_compat _ _ Hor H).
Qed.

Lemma Rdiv_le_compat_r : forall r r1 r2 : R, 0 < r -> r1 <= r2 -> r1 / r <= r2 / r.
Proof.
  intros r r1 r2 Hgt0 H. unfold Rdiv.
  apply Rmult_le_compat_r. { apply Rlt_le. apply Rinv_pos. exact Hgt0. } exact H.
Qed.

Lemma Rdiv_le_opp_compat_l : forall r r1 r2 : R, r <= 0 -> (0 < r1 \/ r2 < 0) -> r1 <= r2 -> r / r1 <= r / r2.
Proof.
  intros r r1 r2 Hle0 Hor H. unfold Rdiv.
  apply Rmult_le_opp_compat_l; [apply Hle0|]. exact (Rinv_le_compat _ _ Hor H).
Qed.

Lemma Rdiv_le_opp_compat_r : forall r r1 r2 : R, r < 0 -> r1 <= r2 -> r2 / r <= r1 / r.
Proof.
  intros r r1 r2 Hlt0 H. unfold Rdiv.
  apply Rmult_le_opp_compat_r. { apply Rlt_le. apply Rinv_neg. exact Hlt0. } exact H.
Qed.



Lemma Rlinear_non_zero_1:forall a b x y, (y<>0)%R -> (a*x+b*y<>0)%R -> (a*(x/y)+b<>0)%R.
Proof.
 intros a b x y Hy Habxy.
 stepl (/y*(a*x+b*y))%R; auto; field; auto.
Qed.

Lemma Rlinear_non_zero_2:forall a b x y, (y<>0)%R -> (a*(x/y)+b<>0)%R -> (a*x+b*y<>0)%R.
Proof.
 intros a b x y Hy Habxy.
 stepl (y*(a*(x/y)+b))%R; auto; field; auto.
Qed.

Lemma Rlinear_non_zero_3: forall a b x : R, a <> 0 -> x <> -b/a -> a * x + b <> 0.
Proof.
 intros a b x Ha Hx.
 generalize (Rminus_eq_contra _ _ Hx); clear Hx; intros Hx.
 stepl (a*(x+(b/a))); [apply Rmult_resp_nonzero|field]; trivial.
 stepl (x - - b / a); trivial; field; trivial.
Qed.

Lemma Rbilinear_non_zero_2:forall a b c d x y x' y', y<>0 -> y'<>0 ->
   (a*(x/y)*(x'/y')+b*(x/y)+c*(x'/y')+d<>0)%R -> (a*x*x'+b*x*y'+c*y*x'+d*y*y'<>0)%R.
Proof.
 intros a b c d x y x' y' Hy Hy' Habxy;
 stepl ((y*y')*(a*(x/y)*(x'/y')+b*(x/y)+c*(x'/y')+d))%R; auto; field; auto.
Qed.


Lemma Rle_or_ge : forall (x1 x2 : R), x1<=x2 \/ x1 >=x2.
Proof.
  intros x1 x2.
  apply or_ind with (A:=x1<x2) (B:=x1=x2\/x1>x2).
  - left. unfold Rle. left. assumption.
  - right. unfold Rge. destruct H. right. assumption. left. assumption.
  - apply Rtotal_order.
Qed.

Lemma Rle_or_le : forall (x1 x2 : R), x1<=x2 \/ x2 <=x1.
Proof.
  intros x1 x2.
  apply or_ind with (A:=x1<x2) (B:=x1=x2\/x1>x2).
  - left. unfold Rle. left. assumption.
  - intro H. destruct H. left. unfold Rle. right. assumption. right. unfold Rle. left. apply Rgt_lt. assumption.
  - apply Rtotal_order.
Qed.

Lemma Rle_dec_weak:forall (x y:R), {Rle x y}+{(Rle y x)}.
Proof.
 intros x y; case (Rlt_le_dec x y); intros; [ left | right ]; trivial; apply Rlt_le; trivial.
Defined.

Lemma Rtrichotomy_inf:forall r1 r2 : R, {(r1 < r2)%R} + {r1 = r2} + {(r2<r1)%R}.
Proof.
 intros r1 r2; elim (total_order_T r1 r2); intros ;auto.
Qed.

Lemma not_O_S_INR: forall n : nat, INR (S n) <> 0%R.
Proof.
 intros n; apply not_O_INR; auto with arith.
Qed.

Lemma pos_S_INR: forall n : nat, (0 < INR (S n))%R.
Proof.
 intros n; apply lt_INR_0; auto with arith.
Qed.

(*
#[export]
Hint Resolve not_O_S_INR pos_S_INR pos_INR.
*)

Lemma Req_Rdiv_Rone:forall x y, y<>0 -> x=y -> x/y =1.
Proof.
 intros x y Hy Hxy; subst x; unfold Rdiv; apply Rinv_r; trivial.
Qed.

Lemma Req_Ropp_Rdiv_minus_Rone:forall x y, y<>0 -> x=-y -> x/y =-1.
Proof.
 intros x y Hy Hxy; subst x; unfold Rdiv; field; assumption.
Qed.

Lemma conjL_range_l:forall r, -1 <= r -> -1<= (r-1)/(r+3).
Proof.
 intros r Hr;
 stepl (-1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle; try lra;
 rewrite Rmult_plus_distr_l; rewrite Rmult_1_r; lra.
Qed.

Lemma conjL_range_r:forall r, -1<=r -> r <= 1 -> (r-1)/(r+3) <= 0.
Proof.
 intros r Hr1 Hr2;
 apply Ropp_le_cancel; stepl 0; try ring;
 unfold Rdiv; rewrite Ropp_mult_distr;
 apply Rle_mult_inv_pos; lra.
Qed.

Lemma conjL_range_weak:forall r, -1 <= r <= 1-> -1<= (r-1)/(r+3)<=1.
Proof.
 intros r [Hr1 Hr2]; split.
 apply conjL_range_l; trivial.
 apply Rle_trans with 0; try lra; apply conjL_range_r; trivial.
Qed.


Lemma conjR_range_l:forall r, -1 <= r -> r <= 1 -> 0<= (r+1)/(-r+3).
Proof.
 intros r Hr1 Hr2;
 unfold Rdiv; apply Rle_mult_inv_pos; lra.
Qed.

Lemma conjR_range_r:forall r, r <= 1 -> (r+1)/(-r+3)<=1.
Proof.
 intros r Hr;
 stepr (1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle;  try lra;
 rewrite Rmult_1_r;  rewrite Rmult_1_l; lra.
Qed.

Lemma conjR_range_weak:forall r, -1 <= r <= 1-> -1<= (r+1)/(-r+3)<=1.
Proof.
 intros r [Hr1 Hr2]; split.
 apply Rle_trans with 0; try lra; apply conjR_range_l; trivial.
 apply conjR_range_r; trivial.
Qed.


Lemma conjM_range_l:forall r, -1 <= r -> -1/3<= r/3.
Proof.
 intros r Hr; lra.
Qed.

Lemma conjM_range_r:forall r, r <= 1 -> r/3<=1/3.
Proof.
 intros r Hr; lra.
Qed.


Lemma conjM_range_weak:forall r, -1 <= r <= 1-> -1<= r/3 <=1.
Proof.
 intros r [Hr1 Hr2]; split.
 apply Rle_trans with (-1/3); try lra; apply conjM_range_l; trivial.
 apply Rle_trans with (1/3); try lra; apply conjM_range_r; trivial.
Qed.


Lemma conjLinv_range_r:forall r, r <= 0 -> (3*r+1)/(-r+1)<=1.
Proof.
 intros r Hr;
 stepr (1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle;  try lra;
 rewrite Rmult_1_r;  rewrite Rmult_1_l; lra.
Qed.


Lemma conjLinv_range_l:forall r, -1<=r -> r <= 0 -> -1<=(3*r+1)/(-r+1).
Proof.
 intros r Hr1 Hr2;
 stepl (-1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle; try lra;
 rewrite Rmult_plus_distr_l; do 2 rewrite Rmult_1_r; rewrite Rmult_opp_opp; lra.
Qed.

Lemma conjRinv_range_r:forall r, 0<=r-> r <= 1 -> (3*r-1)/(r+1)<=1.
Proof.
 intros r Hr1 Hr2.
 stepr (1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle;  try lra;
 rewrite Rmult_1_r;  rewrite Rmult_1_l; lra.
Qed.

Lemma conjRinv_range_l:forall r, 0<=r -> -1<=(3*r-1)/(r+1).
Proof.
 intros r Hr;
 stepl (-1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle; lra.
 (* rewrite Rmult_plus_distr_l; do 2 rewrite Rmult_1_r; lra. *)
Qed.

Lemma conjMinv_range_r:forall r, r <= 1/3 -> 3*r<=1.
Proof.
 intros r Hr; lra.
Qed.

Lemma conjMinv_range_l:forall r, -1/3<=r -> -1<=3*r.
Proof.
 intros r Hr; lra.
Qed.


Lemma CV_const:  forall const, Un_cv (fun i : nat => const) const.
Proof.
 intros const eps H_eps; exists 0%nat; intros n _; rewrite Rfunctions.R_dist_eq; trivial.
Qed.

Lemma CV_shift_S' : forall Un l,  Un_cv (fun n => Un (S n)) l -> Un_cv Un l.
Proof.
 intros Un l; unfold Un_cv; intros H_lim eps H_eps.
 destruct (H_lim eps H_eps) as [N H_N].
 exists (S N).
 intros [|n] H_n.
  red in H_n; apply False_ind; apply (Nat.nle_succ_0 _ H_n).
  apply H_N; red; apply le_S_n; trivial.
Qed.

Lemma CV_shift_S : forall Un l,  Un_cv Un l -> Un_cv (fun n => Un (S n)) l.
Proof.
 intros Un l; unfold Un_cv; intros H_lim eps H_eps.
 destruct (H_lim eps H_eps) as [N H_N].
 exists (S N).
 intros [|n] H_n.
  red in H_n; apply False_ind; apply (Nat.nle_succ_0 _ H_n).
  apply H_N; red; apply Nat.le_trans with n.
   apply le_S_n; trivial.
   repeat constructor.
Qed.

Lemma CV_extensionality : forall Un Un', (forall n, Un n = Un' n) ->  forall l, Un_cv Un l -> Un_cv Un' l.
Proof.
 intros Un Un' H_ext l.
 unfold Un_cv; intros H_lim eps H_eps.
 destruct (H_lim eps H_eps) as [N H_N].
 exists N.
 intros n H_n'.
 rewrite <- (H_ext n); apply H_N; trivial.
Qed.

Ltac ring_exact_R hyp :=
 match type of hyp with
 | Rlt ?X1 ?X2 => (stepr X2; trivial; ring) || (stepl X1; trivial; ring)
 | Rle ?X1 ?X2 => (stepr X2; trivial; ring) || (stepl X1; trivial; ring)
 | ~(@eq R ?X1 ?X2) => (stepr X2; trivial; ring) || (stepl X1; trivial; ring)
 | ?X3 => fail 1
 end.

Lemma Rdiv_mult_inv : forall x y, Rdiv x y = Rmult x (Rinv y).
Proof. intros x y. unfold Rdiv. reflexivity. Qed.


Lemma Rabs_0_eq (a:R) : (Rabs a = 0) -> a=0.
Proof.
  intro H.
  (* Req_dec : forall r1 r2, r1 = r2 \/ r1 <> r2. *)
  assert (a=0 \/ a<>0) as Heq_dec by (apply Req_dec).
  destruct Heq_dec.
  - assumption.
  - assert (Rabs a <> 0) by (apply (Rabs_no_R0 a H0)).
    contradiction.
Qed.

Lemma Rabs_0_neq (a:R) : (Rabs a <> 0) -> a <> 0.
Proof.
  intros H Ha.
  rewrite -> Ha in H.
  rewrite -> Rabs_R0 in H.
  contradiction.
Qed.

Lemma Rabs_le_1 (a:R) : (-1 <= a) -> (a <= 1) -> (Rabs a) <= 1.
Proof.
  assert (-1 <= a <= 1 -> Rabs a <=1). { apply Rabs_le. }
  auto.
Qed.

Lemma Rabs_pow_le_1 : forall (x : R) (n : nat), Rabs x <=1 -> Rabs (pow x n) <= 1.
Proof.
  intros.
  rewrite <- RPow_abs.
  rewrite <- (pow1 n).
  apply pow_incr.
  assert (0 <= Rabs x). { apply Rabs_pos. }
  auto.
Qed.

Lemma Rabs_neg_eq : forall x : R, Rle x 0 -> Rabs x = Ropp x.
Proof.
  intro x. intro H.
  rewrite <- Rabs_pos_eq.
  apply eq_sym. apply Rabs_Ropp.
  apply Ropp_0_le_contravar; exact H.
Qed.

Lemma Rabs_dist_triang : forall x y z:R, Rabs (x-z) <= Rabs (x-y) + Rabs (y-z).
Proof.
  intros.
  replace (x-z) with ((x-y)+(y-z)) by ring.
  apply Rabs_triang.
Qed.

Lemma Rivl_abs_le_max : forall (a b x : R), (a <= x <= b) -> Rabs x <= Rmax (-a) b.
Proof.
  intros a b x Hx.
  destruct (Rle_or_le x 0) as [Hxle0|H0lex].
  - rewrite -> (Rabs_neg_eq _ Hxle0). transitivity (-a).
    apply Ropp_le_contravar. exact (proj1 Hx). exact (Rmax_l _ _).
  - rewrite -> (Rabs_pos_eq _ H0lex). transitivity b.
    exact (proj2 Hx). exact (Rmax_r _ _).
Qed.

Lemma Rabs_ivl : forall (a b : R), (Rabs a <= b) -> -b <= a <= b.
Proof.
  assert (forall (a b : R), -a <= b -> -b <= a) as Hle_neg. {
    intros.
    assert (a + (-a) <= a + b) as Hz. { apply Rplus_le_compat_l. exact H. }
    rewrite -> Rplus_opp_r with (r:=a) in Hz.
    rewrite <- Rplus_opp_r with (r:=(-b)) in Hz.
    rewrite -> Ropp_involutive in Hz.
    apply Rplus_le_reg_r with (r:=b).
    exact Hz.
  }
  intros.
  split.
  - apply Hle_neg. apply Rle_trans with (r2:=(Rabs a)). rewrite <- Rabs_Ropp. apply Rle_abs. exact H.
  - apply Rle_trans with (r2:=(Rabs a)). apply Rle_abs. exact H.
Qed.


Lemma Rpow_0_succ : forall n, Rpow (0%R) (S n) = 0.
Proof. intros n. apply pow_i. exact (Nat.lt_0_succ n). Qed.

Lemma Rpow_succ : forall x n, Rpow x (S n) = x * Rpow x n.
Proof. reflexivity. Qed.

Lemma Rpow_incr : forall (x y : R) (n : nat), 0<=x<=y -> x^n <= y^n.
Proof. apply pow_incr. Qed.

Lemma Rpow_succ_strict_incr : forall x1 x2 n, 0 <= x1 -> x1 < x2 -> Rpow x1 (S n) < Rpow x2 (S n).
Proof.
  intros x1 x2 n Hx1 Hx12.
  induction n.
  - repeat rewrite -> pow_1. exact Hx12.
  - replace (Rpow x1 (S (S n))) with (x1 * Rpow x1 (S n)) by reflexivity.
    replace (Rpow x2 (S (S n))) with (x2 * Rpow x2 (S n)) by reflexivity.
    apply Rmult_le_0_lt_compat.
    -- exact Hx1.
    -- apply pow_le. exact Hx1.
    -- exact Hx12.
    -- exact IHn.
Qed.


Lemma pow_Rle_1  : forall (x : R) (n : nat), -1 <= x <= 1 -> -1 <= pow x n <= 1.
Proof.
  intros.
  apply Rabs_ivl.
  apply Rabs_pow_le_1.
  apply Rabs_le.
  exact H.
Qed.

Lemma pow_Rle_r_1  : forall (x : R) (n : nat), -1 <= x <= 1 -> pow x n <= 1.
Proof.
  apply pow_Rle_1.
Qed.

Lemma pow_Rle_l_1  : forall (x : R) (n : nat), -1 <= x -> -1 <= pow x n.
Proof.
  intros.
  assert (x<=1 \/ 1<=x) as H1 by (apply Rle_or_le).
  destruct H1 as [H1|H1].
  - apply pow_Rle_1. split. apply H. apply H1.
  - apply Rle_trans with (1). lra. apply pow_R1_Rle. exact H1.
Qed.

Lemma Rabs_Rle_1 : forall (x : R), -1 <= x <= 1 -> Rabs x <= 1.
Proof.
  intros x H. apply Rabs_le. lra.
Qed.


Lemma Rsqr_pos_incr : forall x y, 0 <= x -> x <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y Hx0 Hxy. apply (Rsqr_incr_1 x y Hxy Hx0).
  apply (Rle_trans _ x). exact Hx0. exact Hxy.
Qed.

Lemma Rsqr_neg_decr : forall x y, y <= 0 -> x <= y -> Rsqr y <= Rsqr x.
Proof.
  intros x y Hy0 Hxy. rewrite -> (Rsqr_neg x), (Rsqr_neg y).
  apply (Rsqr_incr_1 (-y) (-x)).
  - apply Ropp_le_contravar. exact Hxy.
  - apply Ropp_0_le_contravar. exact Hy0.
  - apply Ropp_0_le_contravar. apply (Rle_trans _ y). exact Hxy. exact Hy0.
Qed.

Lemma Rle_min_compat : forall (r1 r2 r3 r4 : R), r1<=r3 -> r2<=r4 -> Rmin r1 r2 <= Rmin r3 r4.
Proof.
  intros r1 r2 r3 r4 H13 H24.
  apply Rle_trans with (r2 := Rmin r1 r4).
  apply Rle_min_compat_l; exact H24.
  apply Rle_min_compat_r; exact H13.
Qed.

Lemma Rle_max_compat : forall (r1 r2 r3 r4 : R), r1<=r3 -> r2<=r4 -> Rmax r1 r2 <= Rmax r3 r4.
Proof.
  intros r1 r2 r3 r4 H13 H24.
  apply Rle_trans with (r2 := Rmax r1 r4).
  apply Rle_max_compat_l; exact H24.
  apply Rle_max_compat_r; exact H13.
Qed.




Definition Rdist (x y:R) : R := Rabs (x - y).

Lemma Rdist_pos : forall x y : R, Rdist x y >= 0.
Proof. intros. unfold Rdist. apply Rle_ge. apply Rabs_pos. Qed.

Lemma Rdist_sym : forall x y : R, Rdist x y = Rdist y x.
Proof. intros. unfold Rdist. apply Rabs_minus_sym. Qed.

Lemma Rdist_refl : forall x y : R, Rdist x y = 0 <-> x = y.
Proof. intros. unfold Rdist. split.
  intro H. apply Rminus_0_eq. apply Rabs_0_eq. exact H.
  intro H. rewrite <- H. rewrite -> Rminus_eq_0. rewrite -> Rabs_R0. reflexivity.
Qed.

Lemma Rdist_eq : forall x : R, Rdist x x = 0.
Proof.
  intros. apply Rdist_refl. reflexivity.
Qed.

Lemma Rdist_triang : forall x y z : R, Rdist x y <= Rdist x z + Rdist z y.
Proof.
  intros. unfold Rdist.
  assert (x-y = (x-z)+(z-y)) as H by ring.
  rewrite -> H. apply Rabs_triang.
Qed.

Lemma Rdist_plus_compat : forall w x y z, Rdist (w+x) (y+z) <= Rdist w y + Rdist x z.
Proof.
  intros. unfold Rdist.
  replace ((w+x)-(y+z)) with ((w-y)+(x-z)) by ring.
  apply Rabs_triang.
Qed.

Lemma Rdist_minus_compat : forall w x y z, Rdist (w-x) (y-z) <= Rdist w y + Rdist x z.
Proof.
  intros. unfold Rdist.
  replace (Rabs (x-z)) with (Rabs (z-x)) by (apply Rabs_minus_sym).
  replace ((w-x)-(y-z)) with ((w-y)+(z-x)) by ring.
  apply Rabs_triang.
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

Lemma Rdist_abs_l : forall w x y, Rdist (w*x) (w*y) = Rabs w * Rdist x y.
Proof.
  intros. unfold Rdist.
  rewrite <- Rmult_minus_distr_l.
  apply Rabs_mult.
Qed.

(* |w*x - y*z| <= |w-y|*|x| + |y|*|x-z| <= |w-y|*|x| + |w|*|x-z| + |w-y|*|x-z| *)
Lemma Rdist_mult_compat : forall w x y z,
  Rdist (w*x) (y*z) <= Rdist w y * Rabs x + Rabs w * Rdist x z + Rdist w y * Rdist x z.
Proof.
  intros. unfold Rdist.
  replace (w*x-y*z) with ((w-y)*x+w*(x-z)-(w-y)*(x-z)) by ring.
  apply Rle_trans with (Rabs ((w-y)*x+w*(x-z)) + Rabs (-((w-y)*(x-z)))).
    apply Rabs_triang.
  rewrite -> Rabs_Ropp. rewrite -> Rabs_mult. apply Rplus_le_compat_r.
  repeat (rewrite <- Rabs_mult).
  apply Rabs_triang.
Qed.

Lemma Rdist_ivl : forall x y z, Rdist x y <= z -> y-z <= x <= y+z.
Proof.
  intros x y z.
  intros H.
  assert (-z <= x-y <= z) as Hb. { apply (Rabs_ivl _ _ H). }
  destruct Hb as [H0 H1].
  unfold Rminus in *.
  split.
  - apply Rplus_le_reg_l with (-y).
    rewrite <- Rplus_assoc. rewrite -> Rplus_opp_l. rewrite -> Rplus_0_l.
    rewrite -> Rplus_comm.
    exact H0.
  - apply Rplus_le_reg_l with (-y).
    rewrite <- Rplus_assoc. rewrite -> Rplus_opp_l. rewrite -> Rplus_0_l.
    rewrite -> Rplus_comm.
    exact H1.
Qed.

Lemma Rdist_abs_ivl : forall x y z, Rdist x y <= z -> Rabs x <= Rmax (z-y) (y+z).
Proof.
  intros x y z.
  - intro H. apply Rdist_ivl in H.
    destruct (Rle_or_le x 0) as [Hxle0|H0lex].
    -- rewrite -> Rabs_neg_eq. transitivity (z-y). lra. now apply Rmax_l. exact Hxle0.
    -- rewrite -> Rabs_pos_eq. transitivity (y+z). lra. now apply Rmax_r. exact H0lex.
Qed.



Lemma Rabs_dist_mult_l : forall x y z : R, Rabs x * Rdist y z = Rdist (x*y) (x*z).
Proof.
  intros. unfold Rdist.
  rewrite <- Rabs_mult.
  f_equal.
  apply Rmult_minus_distr_l.
Qed.

Lemma Rabs_dist_mult_r : forall x y z : R, Rdist x y * Rabs z = Rdist (x*z) (y*z).
Proof.
  intros. unfold Rdist.
  rewrite <- Rabs_mult.
  f_equal.
  apply Rmult_minus_distr_r.
Qed.

Lemma Rdist_mult_l : forall x y z : R, 0 <= x -> x * Rdist y z = Rdist (x*y) (x*z).
Proof.
  intros.
  rewrite <- Rabs_dist_mult_l.
  rewrite -> Rabs_pos_eq.
  reflexivity.
  assumption.
Qed.

Lemma Rdist_mult_r : forall x y z : R, 0 <= z -> (Rdist x y) * z = Rdist (x*z) (y*z).
Proof.
  intros.
  rewrite <- Rabs_dist_mult_r.
  rewrite -> Rabs_pos_eq.
  reflexivity.
  assumption.
Qed.

Lemma Rdist_eq_le : forall x y z, (Rdist x x <= Rdist y z)%R.
Proof.
  intros x y z. unfold Rdist. rewrite -> Rminus_eq_0.
  rewrite -> Rabs_R0. apply Rabs_pos.
Qed.

Definition Rshft (x : R) (n : Z) : R := Rmult x (powerRZ 2 n).

Lemma Rshft_zero : forall x, Rshft x 0 = x.
Proof. intros x. unfold Rshft. rewrite -> powerRZ_O. now rewrite -> Rmult_1_r. Qed.

Lemma Rshft_dbl : forall x, Rshft x 1 = x * 2.
Proof. intros x. replace (1%Z) with (Z.succ 0) by auto. unfold Rshft. now rewrite -> powerRZ_1. Qed.

Lemma Rshft_hlf : forall x, Rshft x (-1) = x / 2.
Proof.
  intros x. unfold Rshft. replace (-1)%Z with (-(1))%Z. rewrite -> powerRZ_neg'.
  replace (1%Z) with (Z.succ 0) by auto. now rewrite -> powerRZ_1.
  auto.
Qed.

Lemma Rshft_add : forall x m n, Rshft x (m + n) = Rshft (Rshft x m) n.
Proof. intros x m n. unfold Rshft. rewrite -> powerRZ_add. symmetry. now apply Rmult_assoc. lra. Qed.



Definition Rfact (n : nat) := INR (Factorial.fact n).

Lemma Rfact_succ : forall n, Rfact (S n) = INR (S n) * Rfact n.
Proof.
  intro n. unfold Rfact. rewrite -> fact_simpl. now apply mult_INR.
Qed.

Lemma Rfact_succ_cancel : forall n x, INR (S n) * x / Rfact (S n) = x / Rfact n.
Proof.
 intros n x. 
  rewrite -> Rmult_comm, -> Rfact_succ, <- Rmult_div_assoc, -> Rdiv_mult_distr.
  rewrite -> Rdiv_diag, -> Rmult_div_assoc, -> Rmult_1_r. reflexivity.
  exact (not_O_S_INR n).
Qed.

Lemma Rfact_pos : forall n, 0 < Rfact n. 
Proof.
  induction n.
  - replace (Rfact 0) with 1 by reflexivity. exact Rlt_0_1.
  - rewrite -> Rfact_succ. apply Rlt_mult_pos_pos.
    exact (pos_S_INR n). exact IHn.
Qed.

Lemma Rfact_nonzero : forall n, Rfact n <> 0. 
Proof. intro n. symmetry. apply Rlt_not_eq. now apply Rfact_pos. Qed.


Lemma Rfact_0 : Rfact 0 = 1. Proof. reflexivity. Qed.
Lemma Rfact_1 : Rfact 1 = 1. Proof. reflexivity. Qed.
Lemma Rfact_2 : Rfact 2 = 2. Proof. reflexivity. Qed.
Lemma Rfact_3 : Rfact 3 = 6.
Proof.
  rewrite -> Rfact_succ. rewrite -> Rfact_2. replace (INR 3) with 3. lra.
  rewrite -> INR_IZR_INZ. f_equal.
Qed.
Lemma Rfact_4 : Rfact 4 = 24.
Proof.
  rewrite -> Rfact_succ. rewrite -> Rfact_3. replace (INR 4) with 4. lra.
  rewrite -> INR_IZR_INZ. f_equal.
Qed.
Lemma Rfact_5 : Rfact 5 = 120.
Proof.
  rewrite -> Rfact_succ. rewrite -> Rfact_4. replace (INR 5) with 5. lra.
  rewrite -> INR_IZR_INZ. f_equal.
Qed.


Close Scope R_scope.




