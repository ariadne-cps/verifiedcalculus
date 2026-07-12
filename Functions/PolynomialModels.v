(******************************************************************************
 *  Functions/PolynomialModels.v
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


From Stdlib Require Export Reals.
From Stdlib Require Export Reals.Rbase.
From Stdlib Require Export Reals.Rfunctions.
From Stdlib Require Export Reals.Rbasic_fun.
From Stdlib Require Export Reals.Rbasic_fun.
From Stdlib Require Export Reals.Rdefinitions.

From Stdlib Require Export List.

From Stdlib Require Import Recdef.
From Stdlib Require Import Lia.

Require Export RealAddenda.
Require Export Floats.

Require Export Bounds.


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

Definition Polynomial (F : Type) := list (nat*F).

Definition Ptail {F} (p : list (nat * F)) : list (nat * F) :=
  match p with
  | nil => nil
  | a0 :: p1 => p1
  end
.

Record PolynomialModel {F : Type} {FltF : Float F} : Type :=
  { polynomial : list (nat * F); error: F; }.

Arguments PolynomialModel (F) {FltF}.


Section Polynomial_Models.

Context `{F : Type} `{FltF : Float F}.

Fixpoint Pax_eval (p:list (nat*F)) (x:R) : R :=
    match p with
    | nil => 0
    | fn :: p0 =>  (F.injR (snd fn) * (Rpow x (fst fn))) + Pax_eval p0 x
    end.

Lemma Pax_eval_eq : forall t p x,
  Pax_eval (t :: p) x = (F.injR (snd t)) * (Rpow x (fst t)) + Pax_eval p x.
Proof.
 intros; trivial.
Qed.

(* Polynomial norm: || p || = \sum_u |a_i| *)
Function Pnorm (p: Polynomial F) : F :=
  match p with
  | nil  => F.null
  | (n0,a0) :: l => F.add_up (F.abs_exact a0) (Pnorm l)
  end.

Lemma Pnorm_nil :
  Pnorm nil = F.null.
Proof.
  rewrite Pnorm_equation; trivial.
Qed.

Lemma Pnorm_cons : forall n0 a0 l,
  Pnorm ((n0,a0) :: l) = F.add_up (F.abs_exact a0) (Pnorm l).
Proof.
  intros n0 a0 l; rewrite Pnorm_equation; trivial.
Qed.

Lemma Pnorm_property : forall p x,
  -1 <= x <= 1 -> Rabs (Pax_eval p x) <= F.injR (Pnorm p).
Proof.
  intros p.
  intros x Hx.
  induction p as [|(n0,a0) p].

    simpl in *.
    unfold F.null; rewrite F.ninjr_spec; rewrite Rabs_R0; auto with real.

    rewrite Pnorm_cons.
    simpl in *.
    apply Rle_trans with ( (F.injR (F.abs_exact a0)) + F.injR (Pnorm p) ); [| apply Rge_le; apply F.add_up_spec].
    apply Rle_trans with ( (Rabs (F.injR a0 * (pow x n0))) + (Rabs (Pax_eval p x))); [apply Rabs_triang|].
    apply Rplus_le_compat; [|apply IHp].
    rewrite F.abs_exact_spec.
    rewrite Rabs_mult.
    stepr (Rabs (F.injR a0)*1) by ring.
    apply Rmult_le_compat_l; [apply Rabs_pos|].
    destruct Hx as [H1 H2].
    apply Rabs_pow_le_1.
    apply Rabs_le.
    auto.
Qed.

Function PMnorm (t: PolynomialModel F) : F :=
  F.add up (Pnorm t.(polynomial)) t.(error).

(* `multiplying' by polynomial norm *)
Definition Pscale_norm e sp := F.mul_up e (Pnorm sp).

Definition Pdifference (p:Polynomial F) (f:R->R) (x:R) :=
  f(x)-(Pax_eval p x).

Definition PMmodels (t:PolynomialModel F) (f:R->R) := forall x,
  -1 <= x <= 1 -> Rabs ((Pax_eval t.(polynomial) x) - f(x)) <= F.injR (t.(error)) .

Lemma PMmodels_extensional: forall t f1 f2, PMmodels t f1 -> (forall x, -1<=x<=1 -> f1 x = f2 x) -> PMmodels t f2.
Proof.
 intros t f1 f2 H H_ext x Hx.
 specialize (H _ Hx).
 stepl (Rabs (Pax_eval t.(polynomial) x - f1 x)); trivial.
 f_equal. rewrite H_ext. reflexivity. exact Hx.
Qed.

Lemma PMerror_nonneg : forall t f, PMmodels t f -> 0<=F.injR t.(error).
Proof.
 intros t f hyp;
 apply Rle_trans with (Rabs (Pax_eval t.(polynomial) 0 - f 0));[ apply Rabs_pos| apply hyp; auto with real].
Qed.

Definition PMzero : PolynomialModel F :=
  {| polynomial :=nil;  error:=F.null |}.

Definition PMconstant a : PolynomialModel F :=
  {| polynomial := (0%nat, a) :: nil; error := F.null |}.

Definition PMerror_ball e : PolynomialModel F :=
  {| polynomial := nil; error := e |}.

Lemma PMconstant_correct : forall a,
  PMmodels (PMconstant a) (fun _ => F.injR a).
Proof.
  intros a.
  unfold PMmodels, PMconstant.
  simpl.
  intros x Hx.
  replace (F.injR F.null) with (0%R) by (unfold F.null; rewrite -> F.ninjr_spec; reflexivity).
  rewrite -> Rmult_1_r. rewrite -> Rplus_0_r.
  unfold Rminus. rewrite -> Rplus_opp_r. rewrite -> Rabs_R0. apply Req_le. exact eq_refl.
Qed.


Lemma PMnorm_correct : forall t f,
  PMmodels t f -> forall x, -1<=x<=1 -> Rabs (f x) <= F.injR (PMnorm t).
Proof.
  intros t f H x Hx.
  destruct t as [p e].
  unfold PMmodels in H.
  unfold PMnorm.
  simpl in *.
  apply Rle_trans with (F.injR (Pnorm p) + F.injR e).
  apply Rle_trans with (Rabs (Pax_eval p x) + F.injR e).
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
  - apply F.add_up_le_spec.
Qed.

Definition PMtail t : PolynomialModel F :=
  match t with
  | {| polynomial := nil |} => PMzero
  | {| polynomial := a0 :: p1; error :=e |} =>
        {| polynomial := p1; error := e |}
  end.

Theorem PMtail_correct:forall t f, PMmodels t f -> forall n a l,
  t.(polynomial) = (n,a) :: l -> PMmodels (PMtail t) (fun x=>f(x)- (F.injR a)*(pow x n)).
Proof.
  intros [[|(n0,a0) l0] e] f H_t n a l hyp.
  discriminate hyp.

  unfold PMmodels in *; simpl in *.
  intros x Hx.
  specialize (H_t _ Hx); inversion hyp; subst n0; subst a0; subst l0;
  stepl (Rabs (F.injR a * x ^ n + Pax_eval l x - f x)); trivial; f_equal. ring.
Qed.




Fixpoint Peval {FF} {FltFF : Float FF}
  (p : list (nat * FF)) (x : @Bounds FF FltFF) : @Bounds FF FltFF :=
    match p with
    | nil => bounds F.null F.null
    | a0 :: p1 => let c := bounds (snd a0) (snd a0) in
                    let y := Bnds.pow x (fst a0) in
                      Bnds.add (Bnds.mul c y) (Peval p1 x)
    end.

Lemma Peval_cons : forall a0 p1 x, Peval (a0::p1) x =
  Bnds.add (Bnds.mul (bounds (snd a0) (snd a0)) (Bnds.pow x (fst a0))) (Peval p1 x).
Proof. intros. simpl. trivial. Qed.

Lemma Pax_eval_cons : forall a0 p1 y, Pax_eval (a0::p1) y =
  F.injR (snd a0) * (pow y (fst a0)) + (Pax_eval p1 y).
Proof. intros. simpl. trivial. Qed.

Lemma Pax_eval_cons_pair : forall a0 c0 p1 y, Pax_eval ((a0,c0)::p1) y =
  F.injR c0 * (pow y a0) + (Pax_eval p1 y).
Proof. intros. simpl. trivial. Qed.


Lemma Peval_correct :
  forall p x y, Bnds.models x y -> Bnds.models (Peval p x) (Pax_eval p y).
Proof.
  intros p x y H.
  induction p as [|a0 p1 IHp].
  - simpl. unfold F.null.
    rewrite -> F.ninjr_spec.
    split; apply Rle_refl.
  - rewrite -> Peval_cons, Pax_eval_cons.
    1: apply Bnds.add_correct.
    1: apply Bnds.mul_correct.
    2: apply Bnds.pow_correct.
    -- unfold Bnds.models. split; apply Rle_refl.
    -- exact H.
    -- exact IHp.
Qed.


Definition PMeval (t : PolynomialModel F) (x : Bounds F) : Bounds F :=
  Bnds.add
    (Peval t.(polynomial) x)
    (bounds (F.neg t.(error)) (t.(error))).

Theorem PMeval_correct : forall t f x y, (-1 <= y <= 1) ->
  PMmodels t f -> Bnds.models x y -> Bnds.models (PMeval t x) (f y).
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
  apply Bnds.add_correct.
  - apply Peval_correct.
    exact Hmx.
  - unfold Bnds.models.
    rewrite -> F.neg_exact_spec.
    apply Rabs_ivl.
    rewrite -> Rabs_minus_sym.
    exact Hmt.
Qed.

Close Scope R_scope.

End Polynomial_Models.
