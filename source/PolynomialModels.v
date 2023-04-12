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

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Inductive is_sorted_fst {A:Type} : list (nat*A) -> Prop :=
   | is_sorted_fst_nil : is_sorted_fst nil
   | is_sorted_fst_one : forall m a, is_sorted_fst (cons (m,a) nil)
   | is_sorted_fst_cons : forall m (a:A) xs a0, head xs = Some a0 -> (m<fst a0)%nat -> is_sorted_fst xs -> is_sorted_fst (cons (m,a) xs).

Lemma is_sorted_fst_cons_inv : forall {A:Type} m (a:A) xs, is_sorted_fst (cons (m,a) xs) -> is_sorted_fst xs.
Proof.
 intros A m a xs H_ma; inversion H_ma; trivial; apply is_sorted_fst_nil.
Qed.

Lemma is_sorted_fst_cons_lt: forall a0 a1 (p2: list (nat*F)), is_sorted_fst (a0 :: a1 :: p2) -> (fst a0 < fst a1)%nat.
Proof.
 intros a0 a1 p2 H_aap; inversion H_aap; injection H1; intros H_; subst a1; assumption.
Qed.

Definition Polynomial := list (nat*F).

Definition Ptail p : list (nat * F) :=
  match p with
  | nil => nil
  | a0 :: p1 => p1
  end
.


Record PolynomialModel : Type :=
{ polynom : list (nat * F);
  polynom_sorted : is_sorted_fst polynom;
  error: F;
}.

Fixpoint Pax_eval (p:list (nat*F)) (x:R) : R :=
    match p with
    | nil => 0
    | fn :: p0 =>  (FinjR (snd fn) * (pow x (fst fn))) + Pax_eval p0 x
    end.

Lemma Pax_eval_eq_1 : forall t p x, 
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

Lemma Rpow_incr : forall (x y : R) (n : nat), 0<=x<=y -> x^n <= y^n.
Proof. apply pow_incr. Qed.

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

(* `multiplying' by polynomial norm *)
Definition Pscale_norm e sp := Fmul_up e (Pnorm sp).

Definition Pdifference (p:Polynomial) (f:R->R) (x:R) := 
  f(x)-(Pax_eval p x).

Definition PMmodels (t:PolynomialModel) (f:R->R) := forall x,
  -1 <= x <= 1 -> Rabs ((Pax_eval t.(polynom) x) - f(x)) <= FinjR (t.(error)) .

Lemma PMmodels_extensional: forall t f1 f2, PMmodels t f1 -> (forall x, f1 x = f2 x) -> PMmodels t f2.
Proof.
 intros t f1 f2 H H_ext x hyp.
 specialize (H _ hyp).
 stepl (Rabs (Pax_eval t.(polynom) x - f1 x)); trivial.
 f_equal; rewrite H_ext; reflexivity.
Qed.

Lemma PMerror_nonneg : forall t f, PMmodels t f -> 0<=FinjR t.(error).
Proof.
 intros t f hyp;
 apply Rle_trans with (Rabs (Pax_eval t.(polynom) 0 - f 0));[ apply Rabs_pos| apply hyp; auto with real].
Qed.

Definition PMzero : PolynomialModel :=
  {| polynom :=nil;  polynom_sorted :=is_sorted_fst_nil; error:=Fnull |}.

Definition PMconstant n a : PolynomialModel :=
  {| polynom := (n, a) :: nil; polynom_sorted := is_sorted_fst_one n a; error := a |}.


Definition PMtail t : PolynomialModel :=
  match t with
  | {| polynom := nil |} => PMzero
  | {| polynom := (n,a0) :: l; polynom_sorted := H_p; error :=e |} =>
        {| polynom := l; polynom_sorted := is_sorted_fst_cons_inv _ _ _ H_p; error := e |}
  end.

Theorem PMtail_correct:forall t f, PMmodels t f -> forall n a l,
  t.(polynom) = (n,a) :: l -> PMmodels (PMtail t) (fun x=>f(x)- (FinjR a)*(pow x n)).
Proof.
 intros [[|(n0,a0) l0] H_p e] f H_t n a l hyp.
  discriminate hyp.

  unfold PMmodels in *; simpl in *.
  intros x Hx.
  specialize (H_t _ Hx); inversion hyp; subst n0; subst a0; subst l0;
  stepl (Rabs (FinjR a * x ^ n + Pax_eval l x - f x)); trivial; f_equal. ring.
Qed.

Close Scope R_scope.

End Polynomial_Models.
