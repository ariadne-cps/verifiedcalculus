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
Require Import Recdef.
Require Import Lia.

Set Implicit Arguments.


Section Polynomial_Models_Product.

Open Scope R_scope.

Context `{F : Type} `{FltF : Float F}.


(*  Polynomial multiplication: <p1,0>*<p2,0> *)
Function multiply_polynomial_PolynomialM (sp1 sp2: Sparse_polynom)
   {measure (fun sp=> length sp.(@polynom F)) sp1} : Polynomial_model :=
    match sp1 with
    | {| polynom := Datatypes.nil |} => @zero_PolynomialM F FltF
    | {| polynom := (n0,a0) :: l |} => 
          add_PolynomialM (scale_PolynomialM a0 (monomial_scale_PolynomialM n0 {| spolynom:=sp2; error:=Fnull |})) 
                          (multiply_polynomial_PolynomialM (tail_Sparse_polynom sp1) sp2)
    end.
Proof.
 intros; simpl; lia.
Qed.

Lemma multiply_polynomial_PolynomialM_nil: forall H_p1 sp2, 
       multiply_polynomial_PolynomialM {| polynom := Datatypes.nil; polynom_sorted := H_p1 |} sp2 = @zero_PolynomialM F FltF.
Proof.
 intros H_p1 sp2; rewrite multiply_polynomial_PolynomialM_equation; trivial.
Qed.

Lemma multiply_polynomial_PolynomialM_cons: forall n0 a0 l H_p1 sp2, 
       multiply_polynomial_PolynomialM {| polynom := (n0,a0) :: l; polynom_sorted := H_p1 |} sp2 = 
              add_PolynomialM (scale_PolynomialM a0 (monomial_scale_PolynomialM n0 {| spolynom:=sp2; error:=Fnull |})) 
                     (multiply_polynomial_PolynomialM {| polynom := l; polynom_sorted := is_sorted_cons_inv _ _ _ H_p1 |} sp2).
Proof.
 intros n0 a0 l H_p1 sp2; rewrite multiply_polynomial_PolynomialM_equation; trivial.
Qed.


Theorem multiply_polynomial_PolynomialM_correct:forall sp1 sp2,
             @Models F FltF (multiply_polynomial_PolynomialM sp1 sp2) (fun x=> (ax_eval_Sparse_polynom sp1 x)*(ax_eval_Sparse_polynom sp2 x)).
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
  apply Models_extensional with (f1:=fun x=> ((FinjR a0)*((pow x n0)*(ax_eval_Sparse_polynom sp2 x))) + ((ax_eval_Sparse_polynom sp1 x))*(ax_eval_Sparse_polynom sp2 x)) .
  2: intros; subst sp1; simpl; ring.
  apply add_PolynomialM_correct.
   apply scale_PolynomialM_correct; apply monomial_scale_PolynomialM_correct.
   intros x _; simpl; stepl (Rabs 0); [|f_equal; ring]; rewrite flt_null; rewrite Rabs_R0; auto with real.

  apply IHp1.
Qed.


Theorem scale_pnorm_error : forall t1 t2 f1 f2, @Models F FltF t1 f1 -> @Models F FltF t2 f2 -> 
    @Models F FltF {| spolynom:={| polynom := Datatypes.nil; polynom_sorted := is_sorted_nil |}
           ; error := (Fadd_up (@scale_pnorm F FltF t1.(error) t2.(spolynom))
                              (Fadd_up (@scale_pnorm F FltF t2.(error) t1.(spolynom))
                                      (Fmul_up t1.(error) t2.(error)))) 
           |}
 (fun x=> (@pdifference F FltF t1 f1 x)*(ax_eval_Sparse_polynom t2.(spolynom) x) +
          (@pdifference F FltF t2 f2 x)*(ax_eval_Sparse_polynom t1.(spolynom) x) +
          (@pdifference F FltF t1 f1 x)*(@pdifference F FltF t2 f2 x) ).
Proof.
 intros t1 t2 f1 f2 H1 H2 x Hx.
 specialize (H1 x Hx); specialize (H2 x Hx).
 simpl in *.
 rewrite <- Rabs_Ropp.
 stepl (Rabs ( (@pdifference F FltF t1 f1 x)*(ax_eval_Sparse_polynom t2.(spolynom) x) +
               ( (@pdifference F FltF t2 f2 x)*(ax_eval_Sparse_polynom t1.(spolynom) x) +
                 (@pdifference F FltF t1 f1 x)*(@pdifference F FltF t2 f2 x) ))) by (f_equal; ring). 
 apply Rle_trans with (    Rabs (@pdifference F FltF t1 f1 x * ax_eval_Sparse_polynom (spolynom t2) x) +
                              (Rabs ( (@pdifference F FltF t2 f2 x * ax_eval_Sparse_polynom (spolynom t1) x) +
                                       (@pdifference F FltF t1 f1 x * @pdifference F FltF t2 f2 x) ))); [apply Rabs_triang|].
 apply Rle_trans with (    Rabs (@pdifference F FltF t1 f1 x * ax_eval_Sparse_polynom (spolynom t2) x) +
                           (Rabs (@pdifference F FltF t2 f2 x * ax_eval_Sparse_polynom (spolynom t1) x) +
                            Rabs (@pdifference F FltF t1 f1 x * @pdifference F FltF t2 f2 x))); [apply Rplus_le_compat_l;apply Rabs_triang|].
 apply Rle_trans with  (FinjR (@scale_pnorm F FltF (error t1) (spolynom t2)) + 
                        FinjR (Fadd_up (@scale_pnorm F FltF (error t2) (spolynom t1))
                                      (Fmul_up (error t1) (error t2)))); [|apply Rge_le; apply flt_add_up].
 apply Rle_trans with  (FinjR (@scale_pnorm F FltF (error t1) (spolynom t2)) + 
                        (FinjR (@scale_pnorm F FltF (error t2) (spolynom t1)) + 
                         FinjR (Fmul_up (error t1) (error t2)))); [|apply Rplus_le_compat_l; apply flt_add_up_le].
 assert (Hpd1:Rabs (pdifference t1 f1 x) <= FinjR (error t1)); 
  [unfold pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (ax_eval_Polynomial_model t1 x - f1 x)); trivial; f_equal; unfold ax_eval_Polynomial_model; destruct t1; simpl; ring|].
 assert (Hpd2:Rabs (pdifference t2 f2 x) <= FinjR (error t2)); 
  [unfold pdifference; rewrite <- Rabs_Ropp; stepl (Rabs (ax_eval_Polynomial_model t2 x - f2 x)); trivial; f_equal; unfold ax_eval_Polynomial_model; destruct t2; simpl; ring|].
 repeat apply Rplus_le_compat; unfold scale_pnorm; rewrite Rabs_mult.
  apply Rle_trans with ( (FinjR (error t1))*(FinjR (pnorm (spolynom t2)))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial; apply pnorm_property; trivial.
  apply Rle_trans with ( (FinjR (error t2))*(FinjR (pnorm (spolynom t1)))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial; apply pnorm_property; trivial.  
  apply Rle_trans with ( (FinjR (error t1))*(FinjR (error t2))); [| apply flt_mul_up_le].
   apply Rmult_le_compat; try apply Rabs_pos; trivial.
Qed.

Definition multiply_PolynomialM t1 t2 :=
    add_PolynomialM (multiply_polynomial_PolynomialM t1.(spolynom) t2.(spolynom))
               {| spolynom:= {| polynom := Datatypes.nil; polynom_sorted := is_sorted_nil |}
                ; error:=  (Fadd_up (scale_pnorm t1.(error) t2.(spolynom))
                                   (Fadd_up (scale_pnorm t2.(error) t1.(spolynom))
                                           (Fmul_up t1.(error) t2.(error)))) |}.

Theorem multiply_PolynomialM_correct:forall t1 t2 f1 f2, Models t1 f1 -> Models t2 f2 -> @Models F FltF (multiply_PolynomialM t1 t2) (fun x=> f1(x)*f2(x)).
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

  apply (@scale_pnorm_error t1 t2 f1 f2 H1 H2). 
Qed.

Close Scope R_scope.

End Polynomial_Models_Product.

Unset Implicit Arguments.

Arguments multiply_polynomial_PolynomialM {F} {FltF}.
Arguments multiply_polynomial_PolynomialM_nil {F} {FltF}.
Arguments multiply_polynomial_PolynomialM_cons {F} {FltF}.
Arguments multiply_polynomial_PolynomialM_correct {F} {FltF}.
Arguments scale_pnorm_error {F} {FltF}.
Arguments multiply_PolynomialM {F} {FltF}.
Arguments multiply_PolynomialM_correct {F} {FltF}.
