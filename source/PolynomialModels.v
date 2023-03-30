(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
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

Variable Flt : Float.
Definition F := crr Flt.

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

Record Sparse_polynom: Type :=
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
    | fn :: p0 =>  (inj_R (snd fn) * (pow x (fst fn))) + ax_eval_polynom p0 x
    end.

Fixpoint ax_eval_polynom_F  (p: list (nat*F)) (z:F) {struct p} : F :=
    match p with
    | nil => f0
    | fn :: p0 =>  add_up (mult_up (snd fn) (pow_up z (fst fn))) (ax_eval_polynom_F p0 z)
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
                                          (inj_R (snd fn)) * (pow x (fst fn)) + ax_eval_Sparse_polynom (Build_Sparse_polynom p H2) x.
Proof.
 intros; trivial.
Qed.

Lemma ax_eval_Sparse_polynom_F_eq_1 :forall fn p H1 H2 z, 
  ax_eval_Sparse_polynom_F (Build_Sparse_polynom (fn :: p) H1) z =
    add_up (mult_up (snd fn) (pow_up z (fst fn))) (ax_eval_Sparse_polynom_F (Build_Sparse_polynom p H2) z).
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
    | {| polynom := Datatypes.nil |} => f0
    | {| polynom := (n0,a0) :: l |} => 
          add_up (abs_exact a0) (pnorm (tail_Sparse_polynom sp))
    end.
Proof.
 intros; simpl; 
 lia.
Qed.

Lemma pnorm_nil: forall H_p,
       pnorm {| polynom := Datatypes.nil; polynom_sorted := H_p |}  = f0.
Proof.
 intros H_p; rewrite pnorm_equation; trivial.
Qed.

Lemma pnorm_cons: forall n0 a0 l H_p, 
       pnorm {| polynom := (n0,a0) :: l; polynom_sorted := H_p |} = 
          add_up (abs_exact a0) (pnorm {| polynom := l; polynom_sorted := is_sorted_cons_inv _ _ _ H_p |}).
Proof.
 intros n0 a0 l H_p; rewrite pnorm_equation; trivial.
Qed.

Lemma Rpow_incr : forall (x y : R) (n : nat), 0<=x<=y -> x^n <= y^n.
Proof. apply pow_incr. Qed.

Lemma pnorm_property: forall sp x, -1 <= x <= 1 -> Rabs (ax_eval_Sparse_polynom sp x) <= inj_R (pnorm sp). 
Proof.
 intros [p H_p].
 intros x Hx.
 induction p as [|(n0,a0) p].

  simpl in *.
  rewrite pnorm_nil.
  rewrite flt_null; rewrite Rabs_R0; auto with real.

  rewrite pnorm_cons.
  simpl in *.
  apply Rle_trans with ( (inj_R (abs_exact a0)) + inj_R (pnorm
           {| polynom := p; polynom_sorted := is_sorted_cons_inv n0 a0 p H_p |})); [| apply flt_add_u].
  apply Rle_trans with ( (Rabs (inj_R a0 * (pow x n0))) + (Rabs (ax_eval_polynom p x))); [apply Rabs_triang|].
  apply Rplus_le_compat; [|apply IHp].
  rewrite flt_abs.
  rewrite Rabs_mult.
  stepr (Rabs (inj_R a0)*1) by ring.
  apply Rmult_le_compat_l; [apply Rabs_pos|].
  destruct Hx as [H1 H2].
  apply Rabs_pow_le_1.
  apply Rabs_le.
  auto.
Qed.

(* `multiplying' by polynomial norm *)
Definition scale_pnorm e sp := mult_up e (pnorm sp).

Definition pdifference t f x := f(x)-(ax_eval_Sparse_polynom t.(spolynom) x).

Definition Models t f := forall x, -1 <= x <= 1 -> Rabs ((ax_eval_Polynomial_model t x) - f(x)) <= inj_R (t.(error)) .

Lemma Models_extensional: forall t f1 f2, Models t f1 -> (forall x, f1 x = f2 x) -> Models t f2.
Proof.
 intros t f1 f2 H H_ext x hyp.
 specialize (H _ hyp).
 stepl (Rabs (ax_eval_Polynomial_model t x - f1 x)); trivial.
 f_equal; rewrite H_ext; reflexivity.
Qed.

Lemma Polynomial_model_error_nonneg : forall t f, Models t f -> 0<=inj_R t.(error).
Proof.
 intros t f hyp;
 apply Rle_trans with (Rabs (ax_eval_Polynomial_model t 0 - f 0));[ apply Rabs_pos| apply hyp; auto with real].
Qed.

Definition zero_PolynomialM : Polynomial_model := 
{| spolynom := {| polynom :=nil
                ;  polynom_sorted :=is_sorted_nil|}
 ; error:=f0 |}.

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
    polynom t.(spolynom) = (n,a) :: l -> Models (tail_PolynomialM t) (fun x=>f(x)- (inj_R a)*(pow x n)). 
Proof.
 intros [[[|(n0,a0) l0] H_p] e] f H_t n a l hyp; unfold Models in *; simpl in *.
  discriminate hyp.

  intros x Hx;
  specialize (H_t _ Hx); inversion hyp; subst n0; subst a0; subst l0;
  stepl (Rabs (inj_R a * x ^ n + ax_eval_polynom l x - f x)); trivial; f_equal; ring.
Qed.

End Polynomial_Models.

Arguments is_sorted_cons_lt {Flt}.
Arguments error {Flt}.
Arguments spolynom {Flt}.
Arguments Build_Sparse_polynom {Flt}.
Arguments Build_Polynomial_model {Flt}.
Arguments ax_eval_polynom {Flt}.
Arguments ax_eval_Sparse_polynom {Flt}.
Arguments ax_eval_Polynomial_model {Flt}.
Arguments Models {Flt}.
Arguments ax_eval_polynom_F {Flt}.
Arguments ax_eval_Sparse_polynom_F {Flt}.
Arguments ax_eval_Polynomial_model_F {Flt}.
Arguments tail_Sparse_polynom {Flt}.
Arguments pnorm {Flt}.
Arguments pnorm_nil {Flt}.
Arguments pnorm_cons {Flt}.
Arguments pnorm_property {Flt}.
Arguments scale_pnorm {Flt}.
Arguments pdifference {Flt}.
Arguments Polynomial_model_error_nonneg {Flt}.
Arguments Models_extensional {Flt}.
Arguments zero_PolynomialM {Flt}.
Arguments constant_PolynomialM {Flt}.
Arguments tail_PolynomialM {Flt}.
Arguments tail_PolynomialM_correct {Flt}.
