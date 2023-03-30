(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export R_addenda.
Require Export PolynomialModels.
Require Import Recdef.
Require Import Lia.
Require Import Lra.


Set Implicit Arguments.


Section Polynomial_Models_Scalar.

Open Scope R_scope.

Context `{F : Type} `{FltF : Float F}.


Fixpoint pre_scale c p :  list (nat* F) :=
    match p with
    | nil => nil
    | fn :: p' => ( fst fn , Fmul_near c (snd fn)) :: pre_scale c p'
    end.


Lemma pre_scale_eq_nil: forall c, pre_scale c nil = nil.
Proof.
 intros; trivial.
Qed.

Lemma pre_scale_eq_cons: forall c fn p, pre_scale c (fn :: p) = (fst fn , Fmul_near c (snd fn)) :: pre_scale c p.
Proof.
 intros; trivial.
Qed.

Lemma pre_scale_sorted: forall c p, is_sorted p -> is_sorted (pre_scale c p).
Proof.
 intros c;
 induction p as [|a0 [|a1 p]].
  (* nil *)
  intros H; trivial.
  (* a :: nil *)
  intros H_a; constructor 2.
  (* a :: p *)
  intros H_aap.
  assert (H_ap:is_sorted (a1 :: p)); [apply is_sorted_cons_inv with (fst a0) (snd a0); rewrite <- (surjective_pairing); exact H_aap|].
 rewrite pre_scale_eq_cons.
  apply (@is_sorted_cons F (fst a0) (Fmul_near c (snd a0)) (pre_scale c (a1 :: p))
                         (fst a1, Fmul_near c (snd a1)) ); trivial.
   inversion H_aap; injection H1; intros; subst a1; trivial.
   apply IHp; assumption.
Qed.

Definition pre_error_scale c : list (nat * F) -> F :=
   fold_right (fun nf=> Fadd_up (Fdiv2_up (Fsub_up (Fmul_up c (snd nf)) (Fmul_down c (snd nf))))) Fnull.

Definition error_scale c t :  F :=
   Fadd_up (Fmul_up (Fabs_exact c) t.(error)) (pre_error_scale c t.(spolynom)).

Definition sp_scale c p : Sparse_polynom :=
       match p with
       | {| polynom:= p'; polynom_sorted:= H |} => {| polynom := pre_scale c p'; polynom_sorted:= @pre_scale_sorted c p' H |}
       end.

Definition scale_PolynomialM c t : Polynomial_model :=
 {| spolynom := sp_scale c t.(spolynom); error := error_scale c t |}.

Lemma pre_error_scale_nonneg:forall c (t: Polynomial_model), 0<= FinjR (pre_error_scale c t.(spolynom)).
Proof.
 intros c [[p H] e]; induction p; simpl in *.
  simpl; rewrite -> flt_null; auto with real.

  assert (H_p:is_sorted p); [apply is_sorted_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H|].
  apply Rle_trans with (FinjR (Fdiv2_up (Fsub_up (Fmul_up c (snd a)) (Fmul_down c (snd a)))) +
                        FinjR (pre_error_scale c p)); [|apply Rge_le; apply flt_add_up].
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

Lemma pre_error_scale_property: forall c (sp:Sparse_polynom) x,  -1 <= x <= 1 ->
   Rabs ((FinjR c)*@ax_eval_Sparse_polynom F FltF sp x - @ax_eval_Sparse_polynom F FltF (sp_scale c sp) x) <=
        FinjR (pre_error_scale c sp).
Proof.
  intros c [p H]. 
  induction p; intros x Hx; simpl in *.
    stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

  assert (H_p:is_sorted p); [apply is_sorted_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H|].
  apply Rle_trans with ( (FinjR (Fdiv2_up (Fsub_up (Fmul_up c (snd a)) (Fmul_down c (snd a)))) +
                                FinjR (pre_error_scale c p))).
   2: apply Rge_le. 2: apply flt_add_up.

   stepl (Rabs ( ( (FinjR c * (FinjR (snd a))) - (FinjR (Fmul_near c (snd a))) ) * (pow x (fst a)) +
                 (FinjR c * @ax_eval_polynom F FltF p x - @ax_eval_polynom F FltF (pre_scale c p) x) )).
    2:f_equal; simpl; auto. try ring.
    apply Rle_trans with
     (Rabs (FinjR c * FinjR (snd a) - FinjR (Fmul_near c (snd a))) * Rabs (pow x (fst a)) +
      Rabs (FinjR c * @ax_eval_polynom F FltF p x - @ax_eval_polynom F FltF (pre_scale c p) x));
     [rewrite <- Rabs_mult; apply Rabs_triang|].
    apply Rplus_le_compat; [| apply (IHp H_p _ Hx)].
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
  
  (* Add variables to simplify form of equations *)
  remember (@ax_eval_polynom F FltF (pre_scale c p) x) as cpx.
  remember (@ax_eval_polynom F FltF p x) as Rpx.
  remember (FinjR c) as Rc.
  remember (FinjR (snd a)) as Ra.
  remember (FinjR (Fmul_near c (snd a))) as Rcan.
  remember (FinjR c * FinjR (snd a)) as Rca.
  remember (x^(fst a)) as Rpowxa.
  assert ( (FinjR (Fmul_near c (snd a)) * x ^ fst a ) = Rcan * Rpowxa ) as Hpr. {
    rewrite -> HeqRcan. rewrite -> HeqRpowxa. reflexivity.
  }
  assert ((Rc * Ra - Rcan) * Rpowxa + (Rc*Rpx-cpx) = Rc * (Ra * Rpowxa + Rpx) - (Rcan * Rpowxa + cpx)) as Hd.
  { ring. }
  
  rewrite -> Hd. rewrite <- Hpr. reflexivity.
Qed.


Theorem scale_PolynomialM_correct:forall c t f, @Models F FltF t f ->
     @Models F FltF (scale_PolynomialM c t) (fun x=> (FinjR c)* f(x)).
Proof.
 intros c t f H x hyp_x.
 specialize (H x hyp_x).
 assert (H_sum_err_nonneg:= pre_error_scale_nonneg c t).
 apply Rle_trans with (Rabs (FinjR c) * FinjR (error t) + FinjR (pre_error_scale c t.(spolynom))).

  2:apply Rle_trans with (Rabs (FinjR c) * FinjR (error t) + FinjR (pre_error_scale c t.(spolynom)));
     [ apply Rplus_le_compat_l
     ; generalize (FinjR (pre_error_scale c (spolynom t))) H_sum_err_nonneg; intros r H_r; lra
     | rewrite <- flt_abs_exact;
       apply Rle_trans with (FinjR (Fmul_up (Fabs c) (error t)) + FinjR (pre_error_scale c (spolynom t)));
       [ apply Rplus_le_compat_r; apply Rge_le; apply flt_mul_up
       | apply Rge_le; apply flt_add_up
       ]
      ].

  destruct t as [sp e].
  simpl in *.
  set (p_x:= @ax_eval_Sparse_polynom F FltF sp x) in *.
  set (cp_x:= @ax_eval_Sparse_polynom F FltF (sp_scale c sp) x).
  rewrite Rabs_minus_sym.
  stepl ( Rabs ( (FinjR c) * f(x)  - (FinjR c) * p_x + ( (FinjR c) * p_x - cp_x) )); [|f_equal; ring].
  apply Rle_trans with ( Rabs ( (FinjR c) * f(x)  - (FinjR c) * p_x ) + Rabs ( (FinjR c) * p_x - cp_x));
    [apply Rabs_triang |].
  apply Rplus_le_compat.
   stepl ( Rabs(FinjR c) * Rabs (f(x) - p_x));
   [ rewrite Rabs_minus_sym; apply Rmult_le_compat_l; trivial; apply Rabs_pos
   | rewrite <- Rabs_mult; f_equal; auto; ring
   ].
   apply pre_error_scale_property; assumption.
Qed.

Close Scope R_scope.

End Polynomial_Models_Scalar.

Unset Implicit Arguments.
