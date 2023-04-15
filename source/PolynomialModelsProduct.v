(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModelsMonomial.
Require Export PolynomialModelsScalar.
Require Export PolynomialModelsSum.
Require Import Recdef.
Require Import Lia.


Section Polynomial_Models_Product.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.

Record SortedPolynomial : Type :=
{ polynom' : list (nat * F);
  polynom_sorted' : is_sorted_fst polynom';
}.

Definition SPtail sp :=
  match sp with
  | {| polynom' := nil |} => {| polynom' := nil; polynom_sorted' := is_sorted_fst_nil |}
  | {| polynom' := (n,a0) :: l; polynom_sorted' := H_p |} =>
        {| polynom' := l; polynom_sorted' := is_sorted_fst_cons_inv _ _ H_p |}
  end.

Function PMmultiply_polynomial (sp1 sp2 : SortedPolynomial) 
    {measure (fun sp => length sp.(@polynom')) sp1} : PolynomialModel :=
  match sp1 with
  | {| polynom' := nil |} => PMzero
  | {| polynom' := (n0,a0) :: l |} =>
        PMadd (PMscale a0 (PMmonomial_scale n0 {| polynom:=sp2.(polynom'); polynom_sorted:=sp2.(polynom_sorted'); error:=Fnull |}))
                          (PMmultiply_polynomial (SPtail sp1) sp2)
  end.
Proof.
 intros; simpl; lia.
Qed.

Lemma PMmultiply_polynomial_nil : forall H_p1 sp2,
  PMmultiply_polynomial {| polynom' := nil; polynom_sorted' := H_p1 |} sp2 = PMzero.
Proof.
 intros H_p1 sp2; rewrite PMmultiply_polynomial_equation; trivial.
Qed.

Lemma PMmultiply_polynomial_cons : forall n0 a0 l H_p1 sp2,
  PMmultiply_polynomial {| polynom' := (n0,a0) :: l; polynom_sorted' := H_p1 |} sp2 =
    PMadd (PMscale a0 (PMmonomial_scale n0 {| polynom:=sp2.(polynom'); polynom_sorted:=sp2.(polynom_sorted'); error:=Fnull |}))
          (PMmultiply_polynomial {| polynom' := l; polynom_sorted' := is_sorted_fst_cons_inv _ _ H_p1 |} sp2).
Proof.
 intros n0 a0 l H_p1 sp2; rewrite PMmultiply_polynomial_equation; trivial.
Qed.


Theorem PMmultiply_polynomial_correct : forall sp1 sp2,
 PMmodels (PMmultiply_polynomial sp1 sp2) (fun x=> (Pax_eval sp1.(polynom') x)*(Pax_eval sp2.(polynom') x)).
Proof.
 intros [p1 H_p1] sp2.
 induction p1 as [|(n0,a0) p1].
  simpl in *.
  rewrite PMmultiply_polynomial_nil.
  apply PMmodels_extensional with (f1:=fun x=> 0).
  2: intros; simpl; ring.
  intros x _; simpl.
  stepl (Rabs 0); [|f_equal; simpl; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

  rewrite PMmultiply_polynomial_cons.
  simpl.
  set (sp1:={| polynom' := p1; polynom_sorted' := is_sorted_fst_cons_inv (n0,a0) p1 H_p1 |}).
  apply PMmodels_extensional with (f1:=fun x=> ((FinjR a0)*((pow x n0)*(Pax_eval sp2.(polynom') x))) + ((Pax_eval sp1.(polynom') x))*(Pax_eval sp2.(polynom') x)) .
  2: intros; subst sp1; simpl; ring.
  apply PMadd_correct.
   apply PMscale_correct; apply PMmonomial_scale_correct.
   intros x _; simpl; stepl (Rabs 0); [|f_equal; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

  apply IHp1.
Qed.


Theorem Pscale_norm_error : forall t1 t2 f1 f2,
  PMmodels t1 f1 -> PMmodels t2 f2 ->
    PMmodels {| polynom := nil; polynom_sorted := is_sorted_fst_nil
           ; error := (Fadd_up (Pscale_norm t1.(error) t2.(polynom))
                              (Fadd_up (Pscale_norm t2.(error) t1.(polynom))
                                      (Fmul_up t1.(error) t2.(error))))
           |}
 (fun x=> (Pdifference t1.(polynom) f1 x)*(Pax_eval t2.(polynom) x) +
          (Pdifference t2.(polynom) f2 x)*(Pax_eval t1.(polynom) x) +
          (Pdifference t1.(polynom) f1 x)*(Pdifference t2.(polynom) f2 x) ).
Proof.
 intros t1 t2 f1 f2 H1 H2 x Hx.
 specialize (H1 x Hx); specialize (H2 x Hx).
 simpl in *.
 rewrite <- Rabs_Ropp.
(*
 remember t1.(spolynom) as sp1.
 remember t2.(spolynom) as sp2.
*) 
 stepl (Rabs ( (Pdifference t1.(polynom) f1 x)*(Pax_eval t2.(polynom) x) +
               ( (Pdifference t2.(polynom) f2 x)*(Pax_eval t1.(polynom) x) +
                 (Pdifference t1.(polynom) f1 x)*(Pdifference t2.(polynom) f2 x) ))) by (f_equal; simpl; ring).
 apply Rle_trans with (    Rabs (Pdifference t1.(polynom) f1 x * Pax_eval t2.(polynom) x) +
                              (Rabs ( (Pdifference t2.(polynom) f2 x * Pax_eval t1.(polynom) x) +
                                       (Pdifference t1.(polynom) f1 x * Pdifference t2.(polynom) f2 x) ))); [apply Rabs_triang|].
 apply Rle_trans with (    Rabs (Pdifference t1.(polynom) f1 x * Pax_eval t2.(polynom) x) +
                           (Rabs (Pdifference t2.(polynom) f2 x * Pax_eval t1.(polynom) x) +
                            Rabs (Pdifference t1.(polynom) f1 x * Pdifference t2.(polynom) f2 x))); [apply Rplus_le_compat_l;apply Rabs_triang|].
 apply Rle_trans with  (FinjR (Pscale_norm t1.(error) t2.(polynom)) +
                        FinjR (Fadd_up (Pscale_norm t2.(error) t1.(polynom))
                                      (Fmul_up t1.(error) t2.(error)))); [|apply Rge_le; apply flt_add_up].
 apply Rle_trans with  (FinjR (Pscale_norm t1.(error) t2.(polynom)) +
                        (FinjR (Pscale_norm t2.(error) t1.(polynom)) +
                         FinjR (Fmul_up t1.(error) t2.(error)))); [|apply Rplus_le_compat_l; apply flt_add_up_le].
 assert (Hpd1:Rabs (Pdifference t1.(polynom) f1 x) <= FinjR t1.(error));
  [unfold Pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (Pax_eval t1.(polynom) x - f1 x)); trivial; f_equal; destruct t1; simpl; ring|].
 assert (Hpd2:Rabs (Pdifference t2.(polynom) f2 x) <= FinjR t2.(error));
  [unfold Pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (Pax_eval t2.(polynom) x - f2 x)); trivial; f_equal; destruct t2; simpl; ring|].
 repeat apply Rplus_le_compat; unfold Pscale_norm; rewrite Rabs_mult.
  apply Rle_trans with ( (FinjR t1.(error))*(FinjR (Pnorm t2.(polynom)))). {
   apply Rmult_le_compat; try apply Rabs_pos; trivial. unfold Pnorm. simpl. apply Pnorm_property; trivial.
  } 
  apply Rle_trans with ( (FinjR t1.(error))*(FinjR (Pnorm t2.(polynom)))); [| apply flt_mul_up_le].
   apply Rle_refl.
  apply Rle_trans with ( (FinjR t2.(error))*(FinjR (Pnorm t1.(polynom)))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial; apply Pnorm_property; trivial.
  apply Rle_trans with ( (FinjR t1.(error))*(FinjR t2.(error))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial.
Qed.


Definition PMmultiply (t1 t2 : PolynomialModel) : PolynomialModel :=
    PMadd (PMmultiply_polynomial {| polynom':=t1.(polynom); polynom_sorted':=t1.(polynom_sorted) |} 
                                 {| polynom':=t2.(polynom); polynom_sorted':=t2.(polynom_sorted) |} )
               {| polynom := nil; polynom_sorted := is_sorted_fst_nil 
                ; error:=  (Fadd_up (Pscale_norm t1.(error) t2.(polynom))
                                   (Fadd_up (Pscale_norm t2.(error) t1.(polynom))
                                           (Fmul_up t1.(error) t2.(error)))) |}.

Theorem PMmultiply_correct : forall (t1 t2 : PolynomialModel) (f1 f2 : R->R),
  PMmodels t1 f1 -> PMmodels t2 f2 -> PMmodels (PMmultiply t1 t2) (fun x=> f1(x)*f2(x)).
Proof.
 intros t1 t2 f1 f2 H1 H2.

 apply PMmodels_extensional with (f1:=fun x=>
               (Pax_eval t1.(polynom) x)*(Pax_eval t2.(polynom) x) +
                ( (Pdifference t1.(polynom) f1 x)*(Pax_eval t2.(polynom) x) +
                 (Pdifference t2.(polynom) f2 x)*(Pax_eval t1.(polynom) x) +
                   (Pdifference t1.(polynom) f1 x)*(Pdifference t2.(polynom) f2 x) ) ).
 2:intros x Hx; unfold Pdifference; ring.
 unfold PMmultiply.
 apply PMadd_correct.
  apply PMmultiply_polynomial_correct.
  apply (@Pscale_norm_error t1 t2 f1 f2 H1 H2).
Qed.

Close Scope R_scope.

End Polynomial_Models_Product.
