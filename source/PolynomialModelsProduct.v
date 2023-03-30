(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModelsMonomial.
Require Export PolynomialModelsScalar.
Require Export PolynomialModelsSum.
Require Export Recdef.
Require Import Lia.

Set Arguments.
Section Polynomial_Models_Product.


Variable F: Float.
Ltac omega := lia.


(*  Polynomial multiplication: <p1,0>*<p2,0> *)
Function multiply_polynomial_PolynomialM (sp1 sp2: Sparse_polynom F)
   {measure (fun sp=> length sp.(@polynom F)) sp1} : Polynomial_model F :=
    match sp1 with
    | {| polynom := Datatypes.nil |} => zero_PolynomialM
    | {| polynom := (n0,a0) :: l |} => 
          add_PolynomialM (scale_PolynomialM a0 (monomial_scale_PolynomialM n0 {| spolynom:=sp2; error:=f0 |})) 
                          (multiply_polynomial_PolynomialM (tail_Sparse_polynom sp1) sp2)
    end.
Proof.
 intros; simpl; omega.
Qed.

Lemma multiply_polynomial_PolynomialM_nil: forall H_p1 sp2, 
       multiply_polynomial_PolynomialM {| polynom := Datatypes.nil; polynom_sorted := H_p1 |} sp2 = zero_PolynomialM.
Proof.
 intros H_p1 sp2; rewrite multiply_polynomial_PolynomialM_equation; trivial.
Qed.

Lemma multiply_polynomial_PolynomialM_cons: forall n0 a0 l H_p1 sp2, 
       multiply_polynomial_PolynomialM {| polynom := (n0,a0) :: l; polynom_sorted := H_p1 |} sp2 = 
              add_PolynomialM (scale_PolynomialM a0 (monomial_scale_PolynomialM n0 {| spolynom:=sp2; error:=f0 |})) 
                     (multiply_polynomial_PolynomialM {| polynom := l; polynom_sorted := is_sorted_cons_inv _ _ _ H_p1 |} sp2).
Proof.
 intros n0 a0 l H_p1 sp2; rewrite multiply_polynomial_PolynomialM_equation; trivial.
Qed.


Theorem multiply_polynomial_PolynomialM_correct:forall sp1 sp2,
             Models (multiply_polynomial_PolynomialM sp1 sp2) (fun x=> (ax_eval_Sparse_polynom sp1 x)*(ax_eval_Sparse_polynom sp2 x)).
Proof.
 intros [p1 H_p1] sp2.
 induction p1 as [|(n0,a0) p1].

  simpl in *.
  rewrite multiply_polynomial_PolynomialM_nil.
  apply Models_extensional with (f1:=fun x=> 0). 
  2: intros; ring.
  intros x _; simpl; stepl (Rabs 0); [|f_equal; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

  rewrite multiply_polynomial_PolynomialM_cons.
  simpl.
  set (sp1:={| polynom := p1; polynom_sorted := is_sorted_cons_inv n0 a0 p1 H_p1 |}).
  apply Models_extensional with (f1:=fun x=> ((inj_R a0)*((pow x n0)*(ax_eval_Sparse_polynom sp2 x))) + ((ax_eval_Sparse_polynom sp1 x))*(ax_eval_Sparse_polynom sp2 x)) .
  2: intros; subst sp1; simpl; ring.
  apply add_PolynomialM_correct.
   apply scale_PolynomialM_correct; apply monomial_scale_PolynomialM_correct.
   intros x _; simpl; stepl (Rabs 0); [|f_equal; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

  apply IHp1.
Qed.


Theorem scale_pnorm_error:forall t1 t2 f1 f2, @Models F t1 f1 -> Models t2 f2 -> 
    Models {| spolynom:={| polynom := Datatypes.nil; polynom_sorted := is_sorted_nil |}
           ; error := (add_up (scale_pnorm t1.(error) t2.(spolynom))
                              (add_up (scale_pnorm t2.(error) t1.(spolynom))
                                      (mult_up t1.(error) t2.(error)))) 
           |}
 (fun x=> (pdifference t1 f1 x)*(ax_eval_Sparse_polynom t2.(spolynom) x) +
          (pdifference t2 f2 x)*(ax_eval_Sparse_polynom t1.(spolynom) x) +
          (pdifference t1 f1 x)*(pdifference t2 f2 x) ).
Proof.
 intros t1 t2 f1 f2 H1 H2 x Hx.
 specialize (H1 x Hx); specialize (H2 x Hx).
 simpl in *.
 rewrite <- Rabs_Ropp.
 stepl (Rabs ( (pdifference t1 f1 x)*(ax_eval_Sparse_polynom t2.(spolynom) x) +
               ( (pdifference t2 f2 x)*(ax_eval_Sparse_polynom t1.(spolynom) x) +
                 (pdifference t1 f1 x)*(pdifference t2 f2 x) ))) by (f_equal; ring). 
 apply Rle_trans with (    Rabs (pdifference t1 f1 x * ax_eval_Sparse_polynom (spolynom t2) x) +
                              (Rabs ( (pdifference t2 f2 x * ax_eval_Sparse_polynom (spolynom t1) x) +
                                       (pdifference t1 f1 x * pdifference t2 f2 x) ))); [apply Rabs_triang|].
 apply Rle_trans with (    Rabs (pdifference t1 f1 x * ax_eval_Sparse_polynom (spolynom t2) x) +
                           (Rabs (pdifference t2 f2 x * ax_eval_Sparse_polynom (spolynom t1) x) +
                            Rabs (pdifference t1 f1 x * pdifference t2 f2 x))); [apply Rplus_le_compat_l;apply Rabs_triang|].
 apply Rle_trans with  (inj_R (scale_pnorm (error t1) (spolynom t2)) + 
                        inj_R (add_up (scale_pnorm (error t2) (spolynom t1))
                                      (mult_up (error t1) (error t2)))); [|apply flt_add_u].
 apply Rle_trans with  (inj_R (scale_pnorm (error t1) (spolynom t2)) + 
                        (inj_R (scale_pnorm (error t2) (spolynom t1)) + 
                         inj_R (mult_up (error t1) (error t2)))); [|apply Rplus_le_compat_l; apply flt_add_u].
 assert (Hpd1:Rabs (pdifference t1 f1 x) <= inj_R (error t1)); 
  [unfold pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (ax_eval_Polynomial_model t1 x - f1 x)); trivial; f_equal; unfold ax_eval_Polynomial_model; destruct t1; simpl; ring|].
 assert (Hpd2:Rabs (pdifference t2 f2 x) <= inj_R (error t2)); 
  [unfold pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (ax_eval_Polynomial_model t2 x - f2 x)); trivial; f_equal; unfold ax_eval_Polynomial_model; destruct t2; simpl; ring|].
 repeat apply Rplus_le_compat; unfold scale_pnorm; rewrite Rabs_mult.
  apply Rle_trans with ( (inj_R (error t1))*(inj_R (pnorm (spolynom t2)))); [| apply flt_mul_u].
   apply Rmult_le_compat; try apply Rabs_pos; trivial; apply pnorm_property; trivial.
  apply Rle_trans with ( (inj_R (error t2))*(inj_R (pnorm (spolynom t1)))); [| apply flt_mul_u].
   apply Rmult_le_compat; try apply Rabs_pos; trivial; apply pnorm_property; trivial.  
  apply Rle_trans with ( (inj_R (error t1))*(inj_R (error t2))); [| apply flt_mul_u].
   apply Rmult_le_compat; try apply Rabs_pos; trivial.
Qed.

Definition multiply_PolynomialM t1 t2 :=
    add_PolynomialM (multiply_polynomial_PolynomialM t1.(spolynom) t2.(spolynom))
               {| spolynom:= {| polynom := Datatypes.nil; polynom_sorted := is_sorted_nil |}
                ; error:=  (add_up (scale_pnorm t1.(error) t2.(spolynom))
                                   (add_up (scale_pnorm t2.(error) t1.(spolynom))
                                           (mult_up t1.(error) t2.(error)))) |}.

Theorem multiply_PolynomialM_correct:forall t1 t2 f1 f2, Models t1 f1 -> Models t2 f2 -> Models (multiply_PolynomialM t1 t2) (fun x=> f1(x)*f2(x)).
Proof.
 intros t1 t2 f1 f2 H1 H2.

 apply Models_extensional with (f1:=fun x=> 
               (ax_eval_Sparse_polynom t1.(spolynom) x)*(ax_eval_Sparse_polynom t2.(spolynom) x) +
                ( (pdifference t1 f1 x)*(ax_eval_Sparse_polynom t2.(spolynom) x) +
                 (pdifference t2 f2 x)*(ax_eval_Sparse_polynom t1.(spolynom) x) +
                   (pdifference t1 f1 x)*(pdifference t2 f2 x) ) ).
 2:intros x; unfold pdifference; ring.
 unfold multiply_PolynomialM.
 apply add_PolynomialM_correct.
  apply multiply_polynomial_PolynomialM_correct.

  apply (scale_pnorm_error t1 t2 f1 f2 H1 H2). 
Qed.

End Polynomial_Models_Product.

Unset Arguments.

Arguments multiply_polynomial_PolynomialM {F}.
Arguments multiply_polynomial_PolynomialM_nil {F}.
Arguments multiply_polynomial_PolynomialM_cons {F}.
Arguments multiply_polynomial_PolynomialM_correct {F}.
Arguments scale_pnorm_error {F}.
Arguments multiply_PolynomialM {F}.
Arguments multiply_PolynomialM_correct {F}.
