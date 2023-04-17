(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModels.
Require Import Recdef.
Require Import Lia.
Require Import Lra.



Section Polynomial_Model_Scale.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Fixpoint Pscal c p : list (nat* F) :=
  match p with
  | nil => nil
  | fn :: p' => ( fst fn , Fmul_near c (snd fn)) :: Pscal c p'
  end.


Lemma Pscal_eq_nil : forall c, Pscal c nil = nil.
Proof.
  intros; trivial.
Qed.

Lemma Pscal_eq_cons : forall c fn p, Pscal c (fn :: p) = (fst fn , Fmul_near c (snd fn)) :: Pscal c p.
Proof.
  intros; trivial.
Qed.

Lemma Pscal_sorted : forall c p, is_sorted_fst p -> is_sorted_fst (Pscal c p).
Proof.
  intros c;
  induction p as [|a0 [|a1 p]].
    (* nil *)
    intros H; trivial.
    (* a :: nil *)
    intros H_a; constructor 2.
    (* a :: p *)
    intros H_aap.
    assert (H_ap:is_sorted_fst (a1 :: p)); [apply is_sorted_fst_cons_inv with (fst a0, snd a0); rewrite <- (surjective_pairing); exact H_aap|].
  rewrite Pscal_eq_cons.
    apply (@is_sorted_fst_cons F (fst a0,Fmul_near c (snd a0)) (Pscal c (a1 :: p))
                         (fst a1, Fmul_near c (snd a1)) ); trivial.
      inversion H_aap; injection H1; intros; subst a1; trivial.
      apply IHp; assumption.
Qed.

Definition Pscal_error c : list (nat * F) -> F :=
  fold_right (fun nf=> Fadd_up (Fdiv2_up (Fsub_up (Fmul_up c (snd nf)) (Fmul_down c (snd nf))))) Fnull.

Definition PMscal_error c t : F :=
  Fadd_up (Fmul_up (Fabs_exact c) t.(error)) (Pscal_error c t.(polynomial)).

Definition PMscal (c:F) (t:PolynomialModel) : PolynomialModel :=
  {| polynomial := Pscal c t.(polynomial); 
     error := PMscal_error c t |}.

Lemma Pscal_error_nonneg : forall c (t: PolynomialModel), 0<= FinjR (Pscal_error c t.(polynomial)).
Proof.
 intros c [p e]; induction p; simpl in *.
  simpl; rewrite -> flt_null; auto with real.

  apply Rle_trans with (FinjR (Fdiv2_up (Fsub_up (Fmul_up c (snd a)) (Fmul_down c (snd a)))) +
                        FinjR (Pscal_error c p)); [|apply Rge_le; apply flt_add_up].
   apply Rplus_le_le_0_compat.
     generalize (snd a); intros x.

     apply Rle_trans with (Rabs ( (FinjR  (Fmul near c x))- ((FinjR c)*(FinjR x)) )).
       - apply Rabs_pos.
       - unfold Fmul_up, Fmul_down.
         replace (Fmul) with (Fapply Mul).
         replace (Rmult) with (Rapply Mul).
         apply flt_op_near_up_down_sub_hlf_up.
         trivial. trivial.

     - apply IHp; assumption.
Qed.

Lemma Pscal_error_correct : forall c (p:Polynomial) x,  -1 <= x <= 1 ->
   Rabs ((FinjR c)*Pax_eval p x - Pax_eval (Pscal c p) x) <=
        FinjR (Pscal_error c p).
Proof.
  intros c p.
  induction p; intros x Hx; simpl in *.
    stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; unfold Pax_eval; simpl; ring]].

(*
  assert (H_p:is_sorted_fst p); [apply is_sorted_fst_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H|].
*)
  apply Rle_trans with ( (FinjR (Fdiv2_up (Fsub_up (Fmul_up c (snd a)) (Fmul_down c (snd a)))) +
                                FinjR (Pscal_error c p))).
   2: apply Rge_le. 2: apply flt_add_up.

   stepl (Rabs ( ( (FinjR c * (FinjR (snd a))) - (FinjR (Fmul_near c (snd a))) ) * (pow x (fst a)) +
                 (FinjR c * Pax_eval p x - Pax_eval (Pscal c p) x) )).
    2:f_equal; simpl; auto; ring.
    apply Rle_trans with
     (Rabs (FinjR c * FinjR (snd a) - FinjR (Fmul_near c (snd a))) * Rabs (pow x (fst a)) +
      Rabs (FinjR c * Pax_eval p x - Pax_eval (Pscal c p) x));
     [rewrite <- Rabs_mult; apply Rabs_triang|].
    apply Rplus_le_compat; [| apply (IHp _ Hx)].
    rewrite Rabs_minus_sym.
     apply Rle_trans with (Rabs (FinjR (Fmul_near c (snd a)) - FinjR c * FinjR (snd a)) ).
     assert (H_xn_l:-1 <= (pow x (fst a)) ).
        apply pow_Rle_1. elim Hx. trivial.
     assert (H_xn_r:(pow x (fst a))<= 1 );[apply pow_Rle_1; elim Hx; trivial|].
     assert (H_xn_abs:=@Rabs_le_1 (pow x (fst a)) H_xn_l H_xn_r).
     stepr ((Rabs (FinjR (Fmul_near c (snd a)) - FinjR c * FinjR (snd a)))*1) by ring.
     apply Rmult_le_compat_l; trivial; apply Rabs_pos.
  unfold Fmul_up, Fmul_down, Fmul_near.
  replace Fmul with (Fapply Mul); [|trivial]. replace Rmult with (Rapply Mul); [|trivial].
  apply flt_op_near_up_down_sub_hlf_up.
Qed.


Theorem PMscal_correct : forall (c:F) (t:PolynomialModel) (f:R->R), 
  PMmodels t f -> PMmodels (PMscal c t) (fun x=> (FinjR c) * f(x)).
Proof.
 intros c t f H x hyp_x.
 specialize (H x hyp_x).
 assert (H_sum_err_nonneg:= Pscal_error_nonneg c t).
 apply Rle_trans with (Rabs (FinjR c) * FinjR (error t) + FinjR (Pscal_error c t.(polynomial))).

  2:apply Rle_trans with (Rabs (FinjR c) * FinjR (error t) + FinjR (Pscal_error c t.(polynomial)));
     [ apply Rplus_le_compat_l
     ; generalize (FinjR (Pscal_error c (polynomial t))) H_sum_err_nonneg; intros r H_r; lra
     | rewrite <- flt_abs_exact;
       apply Rle_trans with (FinjR (Fmul_up (Fabs c) (error t)) + FinjR (Pscal_error c (polynomial t)));
       [ apply Rplus_le_compat_r; apply Rge_le; apply flt_mul_up
       | apply Rge_le; apply flt_add_up
       ]
      ].

  destruct t as [p e].
  simpl in *.
  set (p_x:= Pax_eval p x) in *.
  set (cp_x:= Pax_eval (Pscal c p) x).
  rewrite Rabs_minus_sym.
  stepl ( Rabs ( (FinjR c) * f(x)  - (FinjR c) * p_x + ( (FinjR c) * p_x - cp_x) )); [|f_equal; ring].
  apply Rle_trans with ( Rabs ( (FinjR c) * f(x)  - (FinjR c) * p_x ) + Rabs ( (FinjR c) * p_x - cp_x));
    [apply Rabs_triang |].
  apply Rplus_le_compat.
   stepl ( Rabs(FinjR c) * Rabs (f(x) - p_x));
   [ rewrite Rabs_minus_sym; apply Rmult_le_compat_l; trivial; apply Rabs_pos
   | rewrite <- Rabs_mult; f_equal; auto; ring
   ].
   apply Pscal_error_correct; assumption.
Qed.

Close Scope R_scope.

End Polynomial_Model_Scale.
