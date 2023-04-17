(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModels.
Require Export PolynomialModelAdd.
Require Export PolynomialModelScale.
Require Export PolynomialModelMonomialScale.
Require Import Recdef.
Require Import Lia.


Section Polynomial_Model_Multiply.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Function Pmul (p1 p2 : Polynomial) 
    {measure (fun p => length p) p1} : PolynomialModel :=
  match p1 with
  | nil => PMzero
  | (n0,c0) :: p1' =>
        PMadd (PMscal c0 (PMmonomial_scale n0 {| polynomial:=p2; error:=Fnull |}))
                          (Pmul (tail p1) p2)
  end.
Proof.
 intros; simpl; lia.
Qed.

Lemma Pmul_nil : forall p2,
  Pmul nil p2 = PMzero.
Proof.
 intros p2; rewrite Pmul_equation; trivial.
Qed.

Lemma Pmul_cons : forall n0 c0 p1 p2,
  Pmul ( (n0,c0) :: p1) p2 =
    PMadd (PMscal c0 (PMmonomial_scale n0 {| polynomial:=p2; error:=Fnull |}))
          (Pmul p1 p2).
Proof.
 intros n0 a0 p1 p2; rewrite Pmul_equation; trivial.
Qed.


Theorem Pmul_correct : forall p1 p2,
  PMmodels (Pmul p1 p2) (fun x=> (Pax_eval p1 x)*(Pax_eval p2 x)).
Proof.
  intros p1 p2.
  induction p1 as [|(n0,c0) p1].
    simpl in *.
    rewrite Pmul_nil.
    apply PMmodels_extensional with (f1:=fun x=> 0).
    2: intros; simpl; ring.
    intros x _; simpl.
    stepl (Rabs 0); [|f_equal; simpl; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

    rewrite Pmul_cons.
    simpl.
    apply PMmodels_extensional with (f1:=fun x=> ((FinjR c0)*((pow x n0)*(Pax_eval p2 x))) + ((Pax_eval p1 x))*(Pax_eval p2 x)) .
    2: intros; simpl; ring.
    apply PMadd_correct.
      apply PMscal_correct; apply PMmonomial_scale_correct.
      intros x _; simpl; stepl (Rabs 0); [|f_equal; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

    apply IHp1.
Qed.


Theorem Pscale_norm_error : forall t1 t2 f1 f2,
  PMmodels t1 f1 -> PMmodels t2 f2 ->
    PMmodels {| polynomial := nil; 
                error := (Fadd_up (Pscale_norm t1.(error) t2.(polynomial))
                              (Fadd_up (Pscale_norm t2.(error) t1.(polynomial))
                                      (Fmul_up t1.(error) t2.(error))))
           |}
 (fun x=> (Pdifference t1.(polynomial) f1 x)*(Pax_eval t2.(polynomial) x) +
          (Pdifference t2.(polynomial) f2 x)*(Pax_eval t1.(polynomial) x) +
          (Pdifference t1.(polynomial) f1 x)*(Pdifference t2.(polynomial) f2 x) ).
Proof.
 intros t1 t2 f1 f2 H1 H2 x Hx.
 specialize (H1 x Hx); specialize (H2 x Hx).
 simpl in *.
 rewrite <- Rabs_Ropp.
(*
 remember t1.(spolynomial) as sp1.
 remember t2.(spolynomial) as sp2.
*) 
 stepl (Rabs ( (Pdifference t1.(polynomial) f1 x)*(Pax_eval t2.(polynomial) x) +
               ( (Pdifference t2.(polynomial) f2 x)*(Pax_eval t1.(polynomial) x) +
                 (Pdifference t1.(polynomial) f1 x)*(Pdifference t2.(polynomial) f2 x) ))) by (f_equal; simpl; ring).
 apply Rle_trans with (    Rabs (Pdifference t1.(polynomial) f1 x * Pax_eval t2.(polynomial) x) +
                              (Rabs ( (Pdifference t2.(polynomial) f2 x * Pax_eval t1.(polynomial) x) +
                                       (Pdifference t1.(polynomial) f1 x * Pdifference t2.(polynomial) f2 x) ))); [apply Rabs_triang|].
 apply Rle_trans with (    Rabs (Pdifference t1.(polynomial) f1 x * Pax_eval t2.(polynomial) x) +
                           (Rabs (Pdifference t2.(polynomial) f2 x * Pax_eval t1.(polynomial) x) +
                            Rabs (Pdifference t1.(polynomial) f1 x * Pdifference t2.(polynomial) f2 x))); [apply Rplus_le_compat_l;apply Rabs_triang|].
 apply Rle_trans with  (FinjR (Pscale_norm t1.(error) t2.(polynomial)) +
                        FinjR (Fadd_up (Pscale_norm t2.(error) t1.(polynomial))
                                      (Fmul_up t1.(error) t2.(error)))); [|apply Rge_le; apply flt_add_up].
 apply Rle_trans with  (FinjR (Pscale_norm t1.(error) t2.(polynomial)) +
                        (FinjR (Pscale_norm t2.(error) t1.(polynomial)) +
                         FinjR (Fmul_up t1.(error) t2.(error)))); [|apply Rplus_le_compat_l; apply flt_add_up_le].
 assert (Hpd1:Rabs (Pdifference t1.(polynomial) f1 x) <= FinjR t1.(error));
  [unfold Pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (Pax_eval t1.(polynomial) x - f1 x)); trivial; f_equal; destruct t1; simpl; ring|].
 assert (Hpd2:Rabs (Pdifference t2.(polynomial) f2 x) <= FinjR t2.(error));
  [unfold Pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (Pax_eval t2.(polynomial) x - f2 x)); trivial; f_equal; destruct t2; simpl; ring|].
 repeat apply Rplus_le_compat; unfold Pscale_norm; rewrite Rabs_mult.
  apply Rle_trans with ( (FinjR t1.(error))*(FinjR (Pnorm t2.(polynomial)))). {
   apply Rmult_le_compat; try apply Rabs_pos; trivial. unfold Pnorm. simpl. apply Pnorm_property; trivial.
  } 
  apply Rle_trans with ( (FinjR t1.(error))*(FinjR (Pnorm t2.(polynomial)))); [| apply flt_mul_up_le].
   apply Rle_refl.
  apply Rle_trans with ( (FinjR t2.(error))*(FinjR (Pnorm t1.(polynomial)))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial; apply Pnorm_property; trivial.
  apply Rle_trans with ( (FinjR t1.(error))*(FinjR t2.(error))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial.
Qed.


Definition PMmul (t1 t2 : PolynomialModel) : PolynomialModel :=
    PMadd (Pmul t1.(polynomial) t2.(polynomial))
               {| polynomial := nil
                ; error:=  (Fadd_up (Pscale_norm t1.(error) t2.(polynomial))
                                   (Fadd_up (Pscale_norm t2.(error) t1.(polynomial))
                                           (Fmul_up t1.(error) t2.(error)))) |}.

Theorem PMmul_correct : forall (t1 t2 : PolynomialModel) (f1 f2 : R->R),
  PMmodels t1 f1 -> PMmodels t2 f2 -> PMmodels (PMmul t1 t2) (fun x=> f1(x)*f2(x)).
Proof.
 intros t1 t2 f1 f2 H1 H2.

 apply PMmodels_extensional with (f1:=fun x=>
               (Pax_eval t1.(polynomial) x)*(Pax_eval t2.(polynomial) x) +
                ( (Pdifference t1.(polynomial) f1 x)*(Pax_eval t2.(polynomial) x) +
                 (Pdifference t2.(polynomial) f2 x)*(Pax_eval t1.(polynomial) x) +
                   (Pdifference t1.(polynomial) f1 x)*(Pdifference t2.(polynomial) f2 x) ) ).
 2:intros x Hx; unfold Pdifference; ring.
 unfold PMmul.
 apply PMadd_correct.
  apply Pmul_correct.
  apply (@Pscale_norm_error t1 t2 f1 f2 H1 H2).
Qed.

Close Scope R_scope.

End Polynomial_Model_Multiply.
