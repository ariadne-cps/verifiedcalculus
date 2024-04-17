(******************************************************************************
 *  numbers/Floats.v
 *
 *  Copyright 2010 Milad Niqui
 *            2023 Pieter Collins
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


Require Import Reals.
Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Reals.Rbasic_fun.
Require Import Reals.Rbasic_fun.
Require Import Reals.Rdefinitions.

Require Import List.

Require Export R_addenda.

(*
Module Floats.
*)



Open Scope R_scope.


Lemma or_impl_compat : forall p1 p2 p3 p4 : Prop,
  (p1 -> p3) -> (p2 -> p4) -> (p1 \/ p2) -> (p3 \/ p4).
Proof.
  intros p1 p2 p3 p4 Hp13 Hp24 Hor.
  apply or_ind with (A:=p1) (B:=p2).
  - left. apply Hp13. exact H.
  - right. apply Hp24. exact H.
  - exact Hor.
Qed.


(*
INR_eq: forall n m : nat, INR n = INR m -> n = m
not_O_S_INR: forall n : nat, INR (S n) <> 0
plus_INR: forall n m : nat, INR (n + m) = INR n + INR m
not_0_INR: forall n : nat, n <> 0%nat -> INR n <> 0
INR_not_0: forall n : nat, INR n <> 0 -> n <> 0%nat
S_O_plus_INR: forall n : nat, INR (1 + n) = INR 1 + INR n
S_INR: forall n : nat, INR (S n) = INR n + 1
minus_INR: forall n m : nat, (m <= n)%nat -> INR (n - m) = INR n - INR m
*)

Lemma INR_0 : INR 0%nat = 0%R.
Proof.
  unfold INR. reflexivity.
Qed.

Lemma INR_1 : INR 1%nat = 1%R.
Proof.
  unfold INR. reflexivity.
Qed.

Lemma Rabs_neg_eq : forall x : R, Rle x 0 -> Rabs x = Ropp x.
Proof.
  intro x. intro H.
  rewrite <- Rabs_pos_eq.
  apply eq_sym. apply Rabs_Ropp.
  apply Ropp_0_le_contravar; exact H.
Qed.








Coercion INR : nat >-> R.


Inductive Rounding := down | near | up.


Inductive BinOp := Add | Sub | Mul.
(* Inductive BinOp := Add | Sub | Mul | Div. *)


Definition Rapply (fval:BinOp) : R -> R -> R :=
  match fval with
    | Add => Rplus | Sub => Rminus | Mul => Rmult (* | Div => Rdiv *)
  end
.



Class Float (F : Type) :=
{
  NinjF : nat -> F;
  FinjR : F -> R;

  Fnull := NinjF 0;
  Funit := NinjF 1;

  F0 := Fnull;
  F1 := Funit;

  Fneg : F -> F;
  Fabs : F -> F;

  Fadd : Rounding -> F -> F -> F;
  Fsub : Rounding -> F -> F -> F;
  Fmul : Rounding -> F -> F -> F;
  Fdiv : Rounding -> F -> F -> F;

  Frec : Rounding -> F -> F;

  Fdiv_flt_nat : Rounding -> F -> nat -> F := fun r x n => Fdiv r x (NinjF n);

  Fmin : F -> F -> F;
  Fmax : F -> F -> F;

  Fleb : F -> F -> bool;


  Fneg_exact := Fneg;
  Fabs_exact := Fabs;

  Fadd_up := Fadd up;
  Fadd_down := Fadd down;
  Fadd_near := Fadd near;

  Fsub_up := Fsub up;
  Fsub_down := Fsub down;
  Fsub_near := Fsub near;

  Fmul_up := Fmul up;
  Fmul_down := Fmul down;
  Fmul_near := Fmul near;

  Fdiv_up := Fdiv up;
  Fdiv_down := Fdiv down;
  Fdiv_near := Fdiv near;

  Frec_up := Frec up;
  Frec_down := Frec down;
  Frec_near := Frec near;

(*
  Fapply (fop : BinOp) : Rounding -> F -> F -> F :=
    match fop with | Add => Fadd | Sub => Fsub | Mul => Fmul | Div => Fdiv end;
*)
  Fapply (fop : BinOp) : Rounding -> F -> F -> F :=
    match fop with | Add => Fadd | Sub => Fsub | Mul => Fmul end;


  flt_val_exact (fval : F) (rval : R) :=
    FinjR fval = rval;
  flt_unop_exact (fop : F -> F) (rop : R -> R) :=
     forall x : F, FinjR (fop x) = rop (FinjR x);
  flt_op_exact (fop : F -> F -> F) (rop : R -> R -> R) :=
     forall x1 x2 : F, FinjR (fop x1 x2)  = rop (FinjR x1) (FinjR x2);

  flt_val_rounded (fval : Rounding -> F) (rval : R) (rnd : Rounding) :=
    match rnd with
    | down => FinjR (fval down) <= rval
    | near => forall w, Rdist (FinjR (fval near)) rval <= Rdist (FinjR w) rval
    | up   => FinjR (fval up) >= rval
    end;
  flt_unop_rounded (fop : Rounding -> F -> F) (rop : R -> R) (rnd : Rounding) :=
    forall (x : F), flt_val_rounded (fun r => fop rnd x) (rop (FinjR x)) rnd;
  flt_binop_rounded (fop : Rounding -> F -> F -> F) (rop : R -> R -> R) (rnd : Rounding) :=
    forall (x1 x2 : F), flt_val_rounded (fun r => fop rnd x1 x2) (rop (FinjR x1) (FinjR x2)) rnd;


  flt_ninjr : forall n : nat, FinjR (NinjF n) = INR n;

  flt_leb : forall (x1 x2 : F), (Fleb x1 x2 = true) <-> (FinjR x1) <= (FinjR x2);

  flt_neg_exact : forall x : F, FinjR (Fneg x) = Ropp (FinjR x);
  flt_abs_exact : forall x : F, FinjR (Fabs x) = Rabs (FinjR x);

  flt_min_exact : forall x1 x2 : F, FinjR (Fmin x1 x2) = Rmin (FinjR x1) (FinjR x2);
  flt_max_exact : forall x1 x2 : F, FinjR (Fmax x1 x2) = Rmax (FinjR x1) (FinjR x2);

  flt_add_rounded : forall rnd x1 x2,
    (flt_val_rounded (fun r => Fadd r x1 x2) (Rplus (FinjR x1) (FinjR x2)) rnd);
  flt_sub_rounded : forall rnd x1 x2,
    (flt_val_rounded (fun r => Fsub r x1 x2) (Rminus (FinjR x1) (FinjR x2)) rnd);
  flt_mul_rounded : forall rnd x1 x2,
    (flt_val_rounded (fun r => Fmul r x1 x2) (Rmult (FinjR x1) (FinjR x2)) rnd);
  flt_div_rounded : forall (rnd : Rounding) (x1 x2 : F),
    (FinjR x2 <> 0%R) -> (flt_val_rounded (fun r => Fdiv r x1 x2) (Rdiv (FinjR x1) (FinjR x2)) rnd);
  flt_rec_rounded : forall (rnd : Rounding) (x : F),
    (FinjR x <> 0%R) -> (flt_val_rounded (fun r => Frec r x) (Rinv (FinjR x)) rnd);

  flt_add_down := flt_add_rounded down;
  flt_add_near := flt_add_rounded near;
  flt_add_up   := flt_add_rounded up;

  flt_sub_down := flt_sub_rounded down;
  flt_sub_near := flt_sub_rounded near;
  flt_sub_up   := flt_sub_rounded up;

  flt_mul_down := flt_mul_rounded down;
  flt_mul_near := flt_mul_rounded near;
  flt_mul_up   := flt_mul_rounded up;

  flt_div_down := flt_div_rounded down;
  flt_div_near := flt_div_rounded near;
  flt_div_up   := flt_div_rounded up;

  flt_rec_down := flt_rec_rounded down;
  flt_rec_near := flt_rec_rounded near;
  flt_rec_up   := flt_rec_rounded up;
}.

(* Coercion (forall F : Float F), FinjR : F >-> R. *)






Section Float_defs.

Context `{F : Type} `{FltF : Float F}.


Definition Fdiv2 {F} {Flt : Float F} (r : Rounding) (x:F) := Fdiv r x (NinjF 2).

Definition Fdiv2_up {F} {Flt : Float F} := Fdiv2 up.

Fixpoint Fsum {F} {Flt : Float F} (r : Rounding) (xs : list F) :=
  match xs with | nil => Fnull | hd::tl => Fadd r hd (Fsum r tl) end.

Definition Fsum_snd_add {I} {F} {Flt : Float F} (r : Rounding) : list (I * F) -> F
  := fold_right (fun nf=> Fadd r (snd nf)) Fnull.

Fixpoint Fpow_up {F} {Flt : Float F} (x:F) (n:nat) :=
    match n with
    | O => Funit
    | S n' => Fmul up x (Fpow_up x n')
    end.

Lemma flt_null : FinjR (Fnull) = 0%R.
Proof.
  unfold Fnull. apply flt_ninjr.
Qed.

Lemma flt_unit : FinjR (Funit) = 1%R.
Proof.
  unfold Funit. apply flt_ninjr.
Qed.

Lemma flt_add_up_le : forall (x y:F),
  (FinjR x) + (FinjR y) <= FinjR (Fadd up x y).
Proof.
  intros x y.
  apply Rge_le; apply flt_add_up.
Qed.

Lemma flt_mul_up_le : forall (x y:F),
  (FinjR x) * (FinjR y) <= FinjR (Fmul up x y).
Proof.
  intros x y.
  apply Rge_le; apply flt_mul_up.
Qed.

Lemma flt_pow_up : forall (x:F) (n:nat),
  (FinjR x >= 0) -> FinjR (Fpow_up x n) >= (FinjR x)^n.
Proof.
  intros x n Hp.
  induction n.
  - simpl. apply Req_ge. apply flt_ninjr.
  - simpl.
    apply Rge_trans with (FinjR x * FinjR (Fpow_up x n)).
    -- apply flt_mul_up.
    -- apply Rmult_ge_compat_l.  exact Hp. exact IHn.
Qed.

Lemma flt_pow_up_le : forall (x:F) (n:nat),
  (0 <= FinjR x) -> (FinjR x)^n <= FinjR (Fpow_up x n).
Proof.
  intros x n Hp.
  apply Rge_le; apply flt_pow_up; apply Rle_ge; exact Hp.
Qed.


Lemma flt_val_near_up_abs : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= Rdist (FinjR (x up)) y.
Proof.
  intros x y H.
  specialize (H near).
  apply H.
Qed.

Lemma flt_val_near_down_abs : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= Rdist (FinjR (x down)) y.
Proof.
  intros x y H.
  apply (H near).
Qed.

Lemma flt_val_near_up : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= FinjR (x up) - y.
Proof.
  intros x y H.
  apply Rle_trans with (Rdist (FinjR (x up)) y).
  - apply flt_val_near_up_abs; exact H.
  - unfold Rdist. rewrite Rabs_pos_eq.
    -- apply Rle_refl.
    -- apply Rge_le. apply Rge_minus. apply (H up).
Qed.

Lemma flt_val_near_down : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= y - FinjR (x down).
Proof.
  intros x y H.
  apply Rle_trans with (Rabs (FinjR (x down) - y)).
  - apply flt_val_near_down_abs; exact H.
  - rewrite -> Rabs_minus_sym. rewrite Rabs_pos_eq.
    -- apply Rle_refl.
    -- apply Rge_le. apply Rge_minus. apply Rle_ge. apply (H down).
Qed.


Lemma flt_val_near_up_down : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= ( FinjR (x up) - FinjR (x down) ) / 2.
Proof.
  intros x y H. unfold Rdist.
  apply Rmult_le_reg_l with 2. exact Rlt_0_2.
  stepr ( (FinjR (x up) - y) + (y - FinjR (x down)) ) by field.
  - stepl ( Rabs (FinjR (x near) - y) + Rabs (FinjR (x near) - y) ) by ring.
    apply Rplus_le_compat.
    -- apply flt_val_near_up; exact H.
    -- apply flt_val_near_down; exact H.
Qed.

Lemma flt_op_near_up_down_sub_up : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= FinjR (Fsub up (x up) (x down)) / 2%R.
Proof.
  intros x y H.
  apply Rle_trans with (((FinjR (x up))-(FinjR (x down)))/2).
  apply flt_val_near_up_down; exact H.
  apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_pos; exact Rlt_0_2|].
  apply Rge_le. apply flt_sub_up.
Qed.

Lemma flt_val_near_up_down_sub_hlf_up : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= FinjR (Fdiv2 up (Fsub up (x up) (x down))).
Proof.
  intros x y H.
  apply Rle_trans with ((FinjR (Fsub up (x up) (x down)))/2).
  apply flt_op_near_up_down_sub_up; exact H.
  assert (FinjR (NinjF 2%nat) = 2) as H2. {
    rewrite -> flt_ninjr. reflexivity. }
  assert (FinjR (NinjF 2%nat) <> 0%R) as H2ne0. {
    rewrite -> flt_ninjr. apply not_O_S_INR. }
  replace (2) with (FinjR (NinjF 2)).
  apply Rge_le; unfold Fdiv2; apply flt_div_up; apply H2ne0.
Qed.

(*
Lemma flt_val_near_up_down_sub_hlf_up' : forall x y, (forall rnd, flt_val_rounded x y rnd) ->
  Rdist (FinjR (x near)) y <= FinjR (Fdiv2 up (Fsub up (x up) (x down))).
Proof.
  intros x y Hrnd.
  assert (FinjR (x down) <= y) as Hd. { exact (Hrnd down). }
  assert (forall w, Rdist (FinjR (x near)) y <= Rdist (FinjR w) y) as Hn. { exact (Hrnd near). }
  assert (FinjR (x up) >= y) as Hu. { exact (Hrnd up). }
  assert (2<>0) as Hneq_2_0. { apply not_eq_sym. apply Rlt_not_eq. exact Rlt_0_2. }
  apply Rle_trans with ((FinjR (x up) - FinjR (x down))/2).
  - apply Rmult_le_reg_r with (2) ; [exact Rlt_0_2|].
    unfold Rdiv. rewrite -> Rmult_assoc. rewrite -> Rinv_l; [|exact Hneq_2_0]. rewrite -> Rmult_1_r.
    replace (FinjR (x up) - FinjR (x down)) with (Rdist (FinjR (x up)) y + Rdist (FinjR (x down)) y).
    rewrite -> Rmult_comm. rewrite -> double.
    apply Rplus_le_compat; apply Hn.
    unfold Rdist.
    rewrite -> Rabs_pos_eq. rewrite -> Rabs_neg_eq. ring.
    apply Rle_minus; exact Hd.
    apply Rle_Rminus_zero. apply Rge_le. exact Hu.
  - apply Rge_le.
    apply Rge_trans with (FinjR (Fsub up (x up) (x down)) / FinjR (NinjF 2)).
    -- unfold Fdiv2; apply flt_div_up; [rewrite -> flt_ninjr; trivial].
    -- rewrite -> flt_ninjr.
       replace (INR 2%nat) with (2%R); [|trivial].
       apply Rmult_ge_compat_r; [apply Rle_ge; apply Rlt_le; apply pos_half_prf|].
       apply flt_sub_up.
Qed.
*)

Lemma flt_op_near_up_down_sub_hlf_up : forall fval x1 x2,
    Rdist (FinjR  (Fapply fval near x1 x2)) (Rapply fval (FinjR x1) (FinjR x2))
      <=  FinjR (Fdiv2 up (Fsub up (Fapply fval up x1 x2) (Fapply fval down x1 x2))).
Proof.
  intros fval x1 x2.
  apply (flt_val_near_up_down_sub_hlf_up (fun rnd => Fapply fval rnd x1 x2) (Rapply fval (FinjR x1) (FinjR x2))).
  unfold flt_val_rounded; destruct rnd; destruct fval; simpl.
  - apply (flt_add_down x1 x2).
  - apply (flt_sub_down x1 x2).
  - apply (flt_mul_down x1 x2).
  - apply (flt_add_near x1 x2).
  - apply (flt_sub_near x1 x2).
  - apply (flt_mul_near x1 x2).
  - apply (flt_add_up   x1 x2).
  - apply (flt_sub_up   x1 x2).
  - apply (flt_mul_up   x1 x2).
Qed.

Lemma flt_div_near_up_down_sub_hlf_up : forall x1 x2, (FinjR x2 <> 0) ->
  Rdist (FinjR  (Fdiv near x1 x2)) (Rdiv (FinjR x1) (FinjR x2))
    <=  FinjR (Fdiv2 up (Fsub up (Fdiv up x1 x2) (Fdiv down x1 x2))).
Proof.
  intros x1 x2 Hx2.
  apply (flt_val_near_up_down_sub_hlf_up (fun rnd => Fdiv rnd x1 x2) (Rdiv (FinjR x1) (FinjR x2))).
  intros rnd; apply flt_div_rounded; exact Hx2.
Qed.

Lemma flt_rec_near_up_down_sub_hlf_up : forall x, (FinjR x <> 0) ->
  Rdist (FinjR  (Frec near x)) (Rinv (FinjR x))
    <=  FinjR (Fdiv2 up (Fsub up (Frec up x) (Frec down x))).
Proof.
  intros x Hx.
  apply (flt_val_near_up_down_sub_hlf_up (fun rnd => Frec rnd x) (Rinv (FinjR x))).
  intros rnd; apply flt_rec_rounded; exact Hx.
Qed.


End Float_defs.

Close Scope R_scope.

(*
End Floats.
*)
