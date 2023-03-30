(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModels.
Require Import Recdef.
Require Import Lia.
Require Import Lra.


Set Implicit Arguments.
Section Polynomial_Models_Scalar.

Require Export R_addenda.

Variable F : Float.

Fixpoint pre_scale c p :  list (nat* F) :=
    match p with
    | nil => nil
    | fn :: p' => ( fst fn , mult_near c (snd fn)) :: pre_scale c p'
    end.


Lemma pre_scale_eq_nil: forall c, pre_scale c nil = nil.
Proof.
 intros; trivial.
Qed.

Lemma pre_scale_eq_cons: forall c fn p, pre_scale c (fn :: p) = (fst fn , mult_near c (snd fn)) :: pre_scale c p.
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
  apply (@is_sorted_cons F (fst a0) (mult_near c (snd a0)) (pre_scale c (a1 :: p))
                         (fst a1, mult_near c (snd a1)) ); trivial.
   inversion H_aap; injection H1; intros; subst a1; trivial.
   apply IHp; assumption.
Qed.

Definition pre_error_scale c : list (nat * F) -> F :=
   fold_right (fun nf=> add_up (div2_up (minus_up (mult_up c (snd nf)) (mult_down c (snd nf))))) f0.

Definition error_scale c t :  F :=
   add_up (mult_up (abs_exact c) t.(error)) (pre_error_scale c t.(spolynom)).

Definition sp_scale c p : Sparse_polynom F :=
       match p with
       | {| polynom:= p'; polynom_sorted:= H |} => {| polynom := pre_scale c p'; polynom_sorted:= @pre_scale_sorted c p' H |}
       end.

Definition scale_PolynomialM c t : Polynomial_model F:=
 {| spolynom := sp_scale c t.(spolynom); error := error_scale c t |}.

Lemma pre_error_scale_nonneg:forall c (t: Polynomial_model F), 0<= inj_R (pre_error_scale c t.(spolynom)).
Proof.
 intros c [[p H] e]; induction p; simpl in *.
  simpl; rewrite flt_null; auto with real.

  assert (H_p:is_sorted p); [apply is_sorted_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H|].
  apply Rle_trans with (inj_R (div2_up (minus_up (mult_up c (snd a)) (mult_down c (snd a)))) +
                        inj_R (pre_error_scale c p)); [|apply flt_add_u].
   apply Rplus_le_le_0_compat.
     generalize (snd a); intros x.

     apply Rle_trans with (Rabs ( (inj_R  (mult_near c x))- ((inj_R c)*(inj_R x)) ));
        [apply Rabs_pos|apply flt_mul_n_u_d_div2].
     apply IHp; assumption.
Qed.

Check Rabs_le.

Lemma Rabs_le_1 (a:R) : (-1 <= a) -> (a <= 1) -> (Rabs a) <= 1.
Proof.
  assert (-1 <= a <= 1 -> Rabs a <=1). { apply Rabs_le. }
  auto.
Qed.

Lemma pre_error_scale_property: forall c (sp:Sparse_polynom F) x,  -1 <= x <= 1 ->
   Rabs ((inj_R c)*ax_eval_Sparse_polynom sp x - ax_eval_Sparse_polynom (sp_scale c sp) x) <=
        inj_R (pre_error_scale c sp).
Proof.
  intros c [p H]. 
  induction p; intros x Hx; simpl in *.
    stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

  assert (H_p:is_sorted p); [apply is_sorted_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H|].
  apply Rle_trans with ( (inj_R (div2_up (minus_up (mult_up c (snd a)) (mult_down c (snd a)))) +
                                inj_R (pre_error_scale c p))).
   2: apply flt_add_u.

   stepl (Rabs ( ( (inj_R c * (inj_R (snd a))) - (inj_R (mult_near c (snd a))) ) * (pow x (fst a)) +
                 (inj_R c * ax_eval_polynom p x - ax_eval_polynom (pre_scale c p) x) )).
    2:f_equal; simpl; auto. try ring.
    apply Rle_trans with
     (Rabs (inj_R c * inj_R (snd a) - inj_R (mult_near c (snd a))) * Rabs (pow x (fst a)) +
      Rabs (inj_R c * ax_eval_polynom p x - ax_eval_polynom (pre_scale c p) x));
     [rewrite <- Rabs_mult; apply Rabs_triang|].
    apply Rplus_le_compat; [| apply (IHp H_p _ Hx)].
    rewrite Rabs_minus_sym.
     apply Rle_trans with (Rabs (inj_R (mult_near c (snd a)) - inj_R c * inj_R (snd a)) ).
     assert (H_xn_l:-1 <= (pow x (fst a)) ).
        apply pow_Rle_1. elim Hx. trivial.
     assert (H_xn_r:(pow x (fst a))<= 1 );[apply pow_Rle_1; elim Hx; trivial|].
     assert (H_xn_abs:=@Rabs_le_1 (pow x (fst a)) H_xn_l H_xn_r).
     stepr ((Rabs (inj_R (mult_near c (snd a)) - inj_R c * inj_R (snd a)))*1) by ring.
     apply Rmult_le_compat_l; trivial; apply Rabs_pos.
  apply flt_mul_n_u_d_div2.
  
  (* Add variables to simplify form of equations *)
  remember (ax_eval_polynom (pre_scale c p) x) as cpx.
  remember (ax_eval_polynom p x) as Rpx.
  remember (inj_R c) as Rc.
  remember (inj_R (snd a)) as Ra.
  remember (inj_R (mult_near c (snd a))) as Rcan.
  remember (inj_R c * inj_R (snd a)) as Rca.
  remember (x^(fst a)) as Rpowxa.
  assert ( (inj_R (mult_near c (snd a)) * x ^ fst a ) = Rcan * Rpowxa ) as Hpr. {
    rewrite -> HeqRcan. rewrite -> HeqRpowxa. reflexivity.
  }
  assert ((Rc * Ra - Rcan) * Rpowxa + (Rc*Rpx-cpx) = Rc * (Ra * Rpowxa + Rpx) - (Rcan * Rpowxa + cpx)) as Hd.
  { ring. }
  rewrite -> Hd. rewrite <- Hpr. reflexivity.
Qed.


Theorem scale_PolynomialM_correct:forall c t f, Models t f ->
     Models (scale_PolynomialM c t) (fun x=> (inj_R c)* f(x)).
Proof.
 intros c t f H x hyp_x.
 specialize (H x hyp_x).
 assert (H_sum_err_nonneg:= pre_error_scale_nonneg c t).
 apply Rle_trans with (Rabs (inj_R c) * inj_R (error t) + inj_R (pre_error_scale c t.(spolynom))).

  2:apply Rle_trans with (Rabs (inj_R c) * inj_R (error t) + inj_R (pre_error_scale c t.(spolynom)));
     [ apply Rplus_le_compat_l
     ; generalize (inj_R (pre_error_scale c (spolynom t))) H_sum_err_nonneg; intros r H_r; lra
     | rewrite <- flt_abs;
       apply Rle_trans with (inj_R (mult_up (abs_exact c) (error t)) + inj_R (pre_error_scale c (spolynom t)));
       [ apply Rplus_le_compat_r; apply flt_mul_u
       |  apply flt_add_u
       ]
      ].

  destruct t as [sp e].
  simpl in *.
  set (p_x:= ax_eval_Sparse_polynom sp x) in *.
  set (cp_x:= ax_eval_Sparse_polynom (sp_scale c sp) x).
  rewrite Rabs_minus_sym.
  stepl ( Rabs ( (inj_R c) * f(x)  - (inj_R c) * p_x + ( (inj_R c) * p_x - cp_x) )); [|f_equal; ring].
  apply Rle_trans with ( Rabs ( (inj_R c) * f(x)  - (inj_R c) * p_x ) + Rabs ( (inj_R c) * p_x - cp_x));
    [apply Rabs_triang |].
  apply Rplus_le_compat.
   stepl ( Rabs(inj_R c) * Rabs (f(x) - p_x));
   [ rewrite Rabs_minus_sym; apply Rmult_le_compat_l; trivial; apply Rabs_pos
   | rewrite <- Rabs_mult; f_equal; auto; ring
   ].
   apply pre_error_scale_property; assumption.
Qed.

End Polynomial_Models_Scalar.

Unset Implicit Arguments.
