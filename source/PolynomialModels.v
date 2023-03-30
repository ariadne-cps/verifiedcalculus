(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export R_addenda.
Require Export Floats.
Require Import Recdef.
Require Import Lia.


Section Polynomial_Models.

Open Scope R_scope.

Context `{F : Type} `{FltF : Float F}.

(*
Variable Flt : Float.
Definition F := crr Flt.
*)

Inductive is_sorted {A:Type} : list (nat*A) -> Prop :=
   | is_sorted_nil : is_sorted nil
   | is_sorted_one : forall m a, is_sorted (cons (m,a) nil)
   | is_sorted_cons : forall m (a:A) xs a0, head xs = Some a0 -> (m<fst a0)%nat -> is_sorted xs -> is_sorted (cons (m,a) xs).

Lemma is_sorted_cons_inv: forall  {A:Type} m (a:A) xs, is_sorted (cons (m,a) xs) -> is_sorted xs. 
Proof.
 intros A m a xs H_ma; inversion H_ma; trivial; apply is_sorted_nil.
Qed.

Lemma is_sorted_cons_lt: forall a0 a1 (p'': list (nat*F)), is_sorted (a0 :: a1 :: p'') -> (fst a0 < fst a1)%nat.
Proof.
 intros a0 a1 p H_aap; inversion H_aap; injection H1; intros H_; subst a1; assumption.
Qed.

Record Sparse_polynom : Type :=
{ polynom:> list (nat*F)
; polynom_sorted: is_sorted polynom
}.

Definition tail_Sparse_polynom sp :=
    match sp with
    | {| polynom := Datatypes.nil |} => {| polynom := Datatypes.nil; polynom_sorted := is_sorted_nil |}
    | {| polynom := (n,a0) :: l; polynom_sorted := H_p |} => 
          {| polynom := l; polynom_sorted := is_sorted_cons_inv _ _ _ H_p |}
    end.

Record Polynomial_model : Type := 
{ spolynom : Sparse_polynom
; error: F
}.

Fixpoint ax_eval_polynom  (p: list (nat*F)) x {struct p} : R :=
    match p with
    | nil => 0
    | fn :: p0 =>  (FinjR (snd fn) * (pow x (fst fn))) + ax_eval_polynom p0 x
    end.

Fixpoint ax_eval_polynom_F  (p: list (nat*F)) (z:F) {struct p} : F :=
    match p with
    | nil => Fnull
    | fn :: p0 =>  Fadd_up (Fmul_up (snd fn) (Fpow_up z (fst fn))) (ax_eval_polynom_F p0 z)
    end.


Definition ax_eval_Sparse_polynom sp x : R  :=
       match sp with
       | {| polynom := p |} => ax_eval_polynom p x
       end.

Definition ax_eval_Sparse_polynom_F (sp : Sparse_polynom) (z:F) : F  :=
       match sp with
       | {| polynom := p |} => ax_eval_polynom_F p z
       end.

Lemma ax_eval_Sparse_polynom_eq_1 :forall fn p H1 H2 x, ax_eval_Sparse_polynom (Build_Sparse_polynom (fn :: p) H1) x =
                                          (FinjR (snd fn)) * (pow x (fst fn)) + ax_eval_Sparse_polynom (Build_Sparse_polynom p H2) x.
Proof.
 intros; trivial.
Qed.

Lemma ax_eval_Sparse_polynom_F_eq_1 :forall fn p H1 H2 z, 
  ax_eval_Sparse_polynom_F (Build_Sparse_polynom (fn :: p) H1) z =
    Fadd_up (Fmul_up (snd fn) (Fpow_up z (fst fn))) (ax_eval_Sparse_polynom_F (Build_Sparse_polynom p H2) z).
Proof.
 intros; trivial.
Qed.

Definition ax_eval_Polynomial_model t x : R  :=
       match t with
       | {| spolynom := sp |} => ax_eval_Sparse_polynom sp x
       end.

Definition ax_eval_Polynomial_model_F (t: Polynomial_model) (z:F) : F  :=
       match t with
       | {| spolynom := sp |} => ax_eval_Sparse_polynom_F sp z
       end.


(* Polynomial norm: || p || = \sum_u |a_i| *)
Function pnorm (sp: Sparse_polynom)
   {measure (fun sp0=> length sp0.(polynom)) sp} : F :=
    match sp with
    | {| polynom := Datatypes.nil |} => Fnull
    | {| polynom := (n0,a0) :: l |} => 
          Fadd_up (Fabs_exact a0) (pnorm (tail_Sparse_polynom sp))
    end.
Proof.
 intros; simpl; 
 lia.
Qed.

Lemma pnorm_nil: forall H_p,
       pnorm {| polynom := Datatypes.nil; polynom_sorted := H_p |}  = Fnull.
Proof.
 intros H_p; rewrite pnorm_equation; trivial.
Qed.

Lemma pnorm_cons: forall n0 a0 l H_p, 
       pnorm {| polynom := (n0,a0) :: l; polynom_sorted := H_p |} = 
          Fadd_up (Fabs_exact a0) (pnorm {| polynom := l; polynom_sorted := is_sorted_cons_inv _ _ _ H_p |}).
Proof.
 intros n0 a0 l H_p; rewrite pnorm_equation; trivial.
Qed.

Lemma Rpow_incr : forall (x y : R) (n : nat), 0<=x<=y -> x^n <= y^n.
Proof. apply pow_incr. Qed.

Lemma pnorm_property: forall sp x,
 -1 <= x <= 1 -> Rabs (ax_eval_Sparse_polynom sp x) <= FinjR (pnorm sp). 
Proof.
 intros [p H_p].
 intros x Hx.
 induction p as [|(n0,a0) p].

  simpl in *.
  rewrite pnorm_nil.
  unfold Fnull; rewrite flt_ninjr; rewrite Rabs_R0; auto with real.

  rewrite pnorm_cons.
  simpl in *.
  apply Rle_trans with ( (FinjR (Fabs_exact a0)) + FinjR (pnorm
           {| polynom := p; polynom_sorted := is_sorted_cons_inv n0 a0 p H_p |})); [| apply Rge_le; apply flt_add_up].
  apply Rle_trans with ( (Rabs (FinjR a0 * (pow x n0))) + (Rabs (ax_eval_polynom p x))); [apply Rabs_triang|].
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

(* `multiplying' by polynomial norm *)
Definition scale_pnorm e sp := Fmul_up e (pnorm sp).

Definition pdifference t f x := f(x)-(ax_eval_Sparse_polynom t.(spolynom) x).

Definition Models t f := forall x,
  -1 <= x <= 1 -> Rabs ((ax_eval_Polynomial_model t x) - f(x)) <= FinjR (t.(error)) .

Lemma Models_extensional: forall t f1 f2, Models t f1 -> (forall x, f1 x = f2 x) -> Models t f2.
Proof.
 intros t f1 f2 H H_ext x hyp.
 specialize (H _ hyp).
 stepl (Rabs (ax_eval_Polynomial_model t x - f1 x)); trivial.
 f_equal; rewrite H_ext; reflexivity.
Qed.

Lemma Polynomial_model_error_nonneg : forall t f, Models t f -> 0<=FinjR t.(error).
Proof.
 intros t f hyp;
 apply Rle_trans with (Rabs (ax_eval_Polynomial_model t 0 - f 0));[ apply Rabs_pos| apply hyp; auto with real].
Qed.

Definition zero_PolynomialM : Polynomial_model := 
{| spolynom := {| polynom :=nil
                ;  polynom_sorted :=is_sorted_nil|}
 ; error:=Fnull |}.

Definition constant_PolynomialM n a : Polynomial_model := 
{| spolynom := {| polynom := (n, a) :: Datatypes.nil
                ; polynom_sorted := is_sorted_one n a |}
; error := a |}.


Definition tail_PolynomialM t : Polynomial_model :=
    match t with
    | {| spolynom:={| polynom := Datatypes.nil |} |} => zero_PolynomialM 
    | {| spolynom:={| polynom := (n,a0) :: l; polynom_sorted := H_p |}; error :=e |} => 
          {| spolynom:= {| polynom := l; polynom_sorted := is_sorted_cons_inv _ _ _ H_p |}; error := e |}
    end.

Theorem tail_PolynomialM_correct:forall t f, Models t f -> forall n a l, 
    polynom t.(spolynom) = (n,a) :: l -> Models (tail_PolynomialM t) (fun x=>f(x)- (FinjR a)*(pow x n)). 
Proof.
 intros [[[|(n0,a0) l0] H_p] e] f H_t n a l hyp; unfold Models in *; simpl in *.
  discriminate hyp.

  intros x Hx;
  specialize (H_t _ Hx); inversion hyp; subst n0; subst a0; subst l0;
  stepl (Rabs (FinjR a * x ^ n + ax_eval_polynom l x - f x)); trivial; f_equal; ring.
Qed.

Close Scope R_scope.

End Polynomial_Models.

Arguments is_sorted_cons_lt {F}.
Arguments error {F}.
Arguments spolynom {F}.
Arguments Build_Sparse_polynom {F}.
Arguments Build_Polynomial_model {F}.
Arguments ax_eval_polynom {F} {FltF}.
Arguments ax_eval_Sparse_polynom {F} {FltF}.
Arguments ax_eval_Polynomial_model {F} {FltF}.
Arguments Models {F} {FltF}.
Arguments ax_eval_polynom_F {F} {FltF}.
Arguments ax_eval_Sparse_polynom_F {F} {FltF}.
Arguments ax_eval_Polynomial_model_F {F} {FltF}.
Arguments tail_Sparse_polynom {F}.
Arguments pnorm {F} {FltF}.
Arguments pnorm_nil {F} {FltF}.
Arguments pnorm_cons {F} {FltF}.
Arguments pnorm_property {F} {FltF}.
Arguments scale_pnorm {F} {FltF}.
Arguments pdifference {F} {FltF}.
Arguments Polynomial_model_error_nonneg {F} {FltF}.
Arguments Models_extensional {F} {FltF}.
Arguments zero_PolynomialM {F} {FltF}.
Arguments constant_PolynomialM {F}.
Arguments tail_PolynomialM {F} {FltF}.
Arguments tail_PolynomialM_correct {F} {FltF}.
