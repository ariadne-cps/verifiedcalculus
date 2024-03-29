(******************************************************************************
 *  functions/PolynomialModels.v
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


Require Export Reals.
Require Export Reals.Rbase.
Require Export Reals.Rfunctions.
Require Export Reals.Rbasic_fun.
Require Export Reals.Rbasic_fun.
Require Export Reals.Rdefinitions.

Require Export List.

Require Import Recdef.
Require Import Lia.

Require Export R_addenda.
Require Export Floats.

Require Export Bounds.


Section Polynomial_Models.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Inductive is_sorted_fst {C:Type} : list (nat*C) -> Prop :=
   | is_sorted_fst_nil : is_sorted_fst nil
   | is_sorted_fst_one : forall x, is_sorted_fst (cons x nil)
   | is_sorted_fst_cons : forall x0 xs x1, head xs = Some x1 -> (fst x0<fst x1)%nat -> is_sorted_fst xs -> is_sorted_fst (cons x0 xs).

Lemma is_sorted_fst_cons_inv : forall {C:Type} (x:nat*C) xs, is_sorted_fst (cons x xs) -> is_sorted_fst xs.
Proof.
 intros C x xs Hx; inversion Hx; trivial; apply is_sorted_fst_nil.
Qed.

Lemma is_sorted_fst_cons_lt: forall {C:Type} x0 x1 (xs2: list (nat*C)), is_sorted_fst (x0 :: x1 :: xs2) -> (fst x0 < fst x1)%nat.
Proof.
 intros C x0 x1 xs2 Hxs. inversion Hxs. injection H1; intros H_; subst x1; assumption.
Qed.

Definition Polynomial := list (nat*F).

Definition Ptail p : list (nat * F) :=
  match p with
  | nil => nil
  | a0 :: p1 => p1
  end
.

Record PolynomialModel {F} {FltF : Float F} : Type :=
{ polynomial : list (nat * F);
  error: F;
}.

Fixpoint Pax_eval (p:list (nat*F)) (x:R) : R :=
    match p with
    | nil => 0
    | fn :: p0 =>  (FinjR (snd fn) * (pow x (fst fn))) + Pax_eval p0 x
    end.

Lemma Pax_eval_eq : forall t p x,
  Pax_eval (t :: p) x = (FinjR (snd t)) * (pow x (fst t)) + Pax_eval p x.
Proof.
 intros; trivial.
Qed.

(* Polynomial norm: || p || = \sum_u |a_i| *)
Function Pnorm (p: Polynomial) : F :=
  match p with
  | nil  => Fnull
  | (n0,a0) :: l => Fadd_up (Fabs_exact a0) (Pnorm l)
  end.

Lemma Pnorm_nil :
  Pnorm nil = Fnull.
Proof.
  rewrite Pnorm_equation; trivial.
Qed.

Lemma Pnorm_cons : forall n0 a0 l,
  Pnorm ((n0,a0) :: l) = Fadd_up (Fabs_exact a0) (Pnorm l).
Proof.
  intros n0 a0 l; rewrite Pnorm_equation; trivial.
Qed.

Lemma Pnorm_property : forall p x,
  -1 <= x <= 1 -> Rabs (Pax_eval p x) <= FinjR (Pnorm p).
Proof.
  intros p.
  intros x Hx.
  induction p as [|(n0,a0) p].

    simpl in *.
    unfold Fnull; rewrite flt_ninjr; rewrite Rabs_R0; auto with real.

    rewrite Pnorm_cons.
    simpl in *.
    apply Rle_trans with ( (FinjR (Fabs_exact a0)) + FinjR (Pnorm p) ); [| apply Rge_le; apply flt_add_up].
    apply Rle_trans with ( (Rabs (FinjR a0 * (pow x n0))) + (Rabs (Pax_eval p x))); [apply Rabs_triang|].
    apply Rplus_le_compat; [|apply IHp].
    rewrite flt_abs_exact.
    rewrite Rabs_mult.
    stepr (Rabs (FinjR a0)*1) by ring.
    apply Rmult_le_compat_l; [apply Rabs_pos|].
    destruct Hx as [H1 H2].
    apply Rabs_pow_le_1.
    apply Rabs_le.
    auto.
Qed.

Function PMnorm (t: PolynomialModel) : F :=
  Fadd up (Pnorm t.(polynomial)) t.(error).

(* `multiplying' by polynomial norm *)
Definition Pscale_norm e sp := Fmul_up e (Pnorm sp).

Definition Pdifference (p:Polynomial) (f:R->R) (x:R) :=
  f(x)-(Pax_eval p x).

Definition PMmodels (t:PolynomialModel) (f:R->R) := forall x,
  -1 <= x <= 1 -> Rabs ((Pax_eval t.(polynomial) x) - f(x)) <= FinjR (t.(error)) .

Lemma PMmodels_extensional: forall t f1 f2, PMmodels t f1 -> (forall x, -1<=x<=1 -> f1 x = f2 x) -> PMmodels t f2.
Proof.
 intros t f1 f2 H H_ext x Hx.
 specialize (H _ Hx).
 stepl (Rabs (Pax_eval t.(polynomial) x - f1 x)); trivial.
 f_equal. rewrite H_ext. reflexivity. exact Hx.
Qed.

Lemma PMerror_nonneg : forall t f, PMmodels t f -> 0<=FinjR t.(error).
Proof.
 intros t f hyp;
 apply Rle_trans with (Rabs (Pax_eval t.(polynomial) 0 - f 0));[ apply Rabs_pos| apply hyp; auto with real].
Qed.

Definition PMzero : PolynomialModel :=
  {| polynomial :=nil;  error:=Fnull |}.

Definition PMconstant a : PolynomialModel :=
  {| polynomial := (0%nat, a) :: nil; error := Fnull |}.

Definition PMerror_ball e : PolynomialModel :=
  {| polynomial := nil; error := e |}.

Lemma PMconstant_correct : forall a,
  PMmodels (PMconstant a) (fun _ => FinjR a).
Proof.
  intros a.
  unfold PMmodels, PMconstant.
  simpl.
  intros x Hx.
  replace (FinjR Fnull) with (0%R) by (unfold Fnull; rewrite -> flt_ninjr; reflexivity).
  rewrite -> Rmult_1_r. rewrite -> Rplus_0_r.
  unfold Rminus. rewrite -> Rplus_opp_r. rewrite -> Rabs_R0. apply Req_le. exact eq_refl.
Qed.


Lemma PMnorm_correct : forall t f,
  PMmodels t f -> forall x, -1<=x<=1 -> Rabs (f x) <= FinjR (PMnorm t).
Proof.
  intros t f H x Hx.
  destruct t as [p e].
  unfold PMmodels in H.
  unfold PMnorm.
  simpl in *.
  apply Rle_trans with (FinjR (Pnorm p) + FinjR e).
  apply Rle_trans with (Rabs (Pax_eval p x) + FinjR e).
  - specialize (H x Hx).
    set (px := Pax_eval p x).
    replace (f x) with (px + (f x - px)).
    apply Rle_trans with (Rabs px + Rabs (f x - px)).
    apply Rabs_triang.
    apply Rplus_le_compat_l.
    rewrite -> Rabs_minus_sym.
    exact H.
    field.
  - apply Rplus_le_compat_r.
    apply Pnorm_property. exact Hx.
  - apply flt_add_up_le.
Qed.

Definition PMtail t : PolynomialModel :=
  match t with
  | {| polynomial := nil |} => PMzero
  | {| polynomial := a0 :: p1; error :=e |} =>
        {| polynomial := p1; error := e |}
  end.

Theorem PMtail_correct:forall t f, PMmodels t f -> forall n a l,
  t.(polynomial) = (n,a) :: l -> PMmodels (PMtail t) (fun x=>f(x)- (FinjR a)*(pow x n)).
Proof.
  intros [[|(n0,a0) l0] e] f H_t n a l hyp.
  discriminate hyp.

  unfold PMmodels in *; simpl in *.
  intros x Hx.
  specialize (H_t _ Hx); inversion hyp; subst n0; subst a0; subst l0;
  stepl (Rabs (FinjR a * x ^ n + Pax_eval l x - f x)); trivial; f_equal. ring.
Qed.




Fixpoint Peval {FF} {FltFF : Float FF}
  (p : list (nat * FF)) (x : @Bounds FF FltFF) : @Bounds FF FltFF :=
    match p with
    | nil => bounds Fnull Fnull
    | a0 :: p1 => let c := bounds (snd a0) (snd a0) in
                    let y := pow_bounds x (fst a0) in
                      add_bounds (mul_bounds c y) (Peval p1 x)
    end.

Lemma Peval_cons : forall a0 p1 x, Peval (a0::p1) x =
  add_bounds (mul_bounds (bounds (snd a0) (snd a0)) (pow_bounds x (fst a0))) (Peval p1 x).
Proof. intros. simpl. trivial. Qed.

Lemma Pax_eval_cons : forall a0 p1 y, Pax_eval (a0::p1) y =
  FinjR (snd a0) * (pow y (fst a0)) + (Pax_eval p1 y).
Proof. intros. simpl. trivial. Qed.


Lemma Peval_correct :
  forall p x y, models x y -> models (Peval p x) (Pax_eval p y).
Proof.
  intros p x y H.
  induction p as [|a0 p1 IHp].
  - simpl. unfold Fnull.
    rewrite -> flt_ninjr.
    split; apply Rle_refl.
  - rewrite -> Peval_cons, Pax_eval_cons.
    1: apply add_bounds_correct.
    1: apply mul_bounds_correct.
    2: apply pow_bounds_correct.
    -- unfold models. split; apply Rle_refl.
    -- exact H.
    -- exact IHp.
Qed.


Definition PMeval {FF} {FltFF : Float FF}
   (t : PolynomialModel) (x : Bounds) : Bounds :=
  add_bounds
    (Peval t.(polynomial) x)
    (bounds (Fneg t.(error)) (t.(error))).

Theorem PMeval_correct : forall t f x y, (-1 <= y <= 1) ->
  PMmodels t f -> models x y -> models (PMeval t x) (f y).
Proof.
  intros t f x y Hy.
  destruct t as [p e].
  unfold PMmodels.
  unfold PMeval.
  simpl.
  set (g:=Pax_eval p).
  intros Hmt Hmx.
  specialize (Hmt y Hy).
  replace (f y) with (g y + (f y - g y)) by ring.
  apply add_bounds_correct.
  - apply Peval_correct.
    exact Hmx.
  - unfold models.
    rewrite -> flt_neg_exact.
    apply Rabs_ivl.
    rewrite -> Rabs_minus_sym.
    exact Hmt.
Qed.

Close Scope R_scope.

End Polynomial_Models.
