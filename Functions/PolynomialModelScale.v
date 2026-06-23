(******************************************************************************
 *  Functions/PolynomialModelsScale.v
 *
 *  Copyright 2010 Milad Niqui
 *            2023 Pieter Collins
 *
 ******************************************************************************)

(*
 * This file is part of the Verified Calculus Library.
 *
 * The Verified Calculus Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 *
 * The Verified Calculus Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
 * Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * the Verified Calculus Library. If not, see <https://www.gnu.org/licenses/>.
 *)


Require Export PolynomialModels.

From Stdlib Require Import Recdef.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.



Section Polynomial_Model_Scale.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Fixpoint Pscal c p : list (nat* F) :=
  match p with
  | nil => nil
  | fn :: p' => ( fst fn , F.mul_near c (snd fn)) :: Pscal c p'
  end.


Lemma Pscal_eq_nil : forall c, Pscal c nil = nil.
Proof.
  intros; trivial.
Qed.

Lemma Pscal_eq_cons : forall c fn p, Pscal c (fn :: p) = (fst fn , F.mul_near c (snd fn)) :: Pscal c p.
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
    apply (@is_sorted_fst_cons F (fst a0,F.mul_near c (snd a0)) (Pscal c (a1 :: p))
                         (fst a1, F.mul_near c (snd a1)) ); trivial.
      inversion H_aap; injection H1; intros; subst a1; trivial.
      apply IHp; assumption.
Qed.

Definition Pscal_error c : list (nat * F) -> F :=
  fold_right (fun nf=> F.add_up (F.div2_up (F.sub_up (F.mul_up c (snd nf)) (F.mul_down c (snd nf))))) F.null.

Definition PMscal_error c t : F :=
  F.add_up (F.mul_up (F.abs_exact c) t.(error)) (Pscal_error c t.(polynomial)).

Definition PMscal (c:F) (t:PolynomialModel F) : PolynomialModel F :=
  {| polynomial := Pscal c t.(polynomial);
     error := PMscal_error c t |}.

Lemma Pscal_error_nonneg : forall c (t: PolynomialModel F), 0<= F.injR (Pscal_error c t.(polynomial)).
Proof.
 intros c [p e]; induction p; simpl in *.
  simpl; rewrite -> F.null_spec; auto with real.

  apply Rle_trans with (F.injR (F.div2_up (F.sub_up (F.mul_up c (snd a)) (F.mul_down c (snd a)))) +
                        F.injR (Pscal_error c p)); [|apply Rge_le; apply F.add_up_spec].
   apply Rplus_le_le_0_compat.
     generalize (snd a); intros x.

     apply Rle_trans with (Rabs ( (F.injR  (F.mul near c x))- ((F.injR c)*(F.injR x)) )).
       - apply Rabs_pos.
       - unfold F.mul_up, F.mul_down.
         replace (F.mul) with (F.apply Mul).
         replace (Rmult) with (Rapply Mul).
         apply F.op_near_up_down_sub_hlf_up_spec.
         trivial. trivial.

     - apply IHp; assumption.
Qed.

Lemma Pscal_error_correct : forall c (p:Polynomial F) x,  -1 <= x <= 1 ->
   Rabs ((F.injR c)*Pax_eval p x - Pax_eval (Pscal c p) x) <=
        F.injR (Pscal_error c p).
Proof.
  intros c p.
  induction p; intros x Hx; simpl in *.
    stepl 0; [ rewrite F.null_spec; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; unfold Pax_eval; simpl; ring]].

(*
  assert (H_p:is_sorted_fst p); [apply is_sorted_fst_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H|].
*)
  apply Rle_trans with ( (F.injR (F.div2_up (F.sub_up (F.mul_up c (snd a)) (F.mul_down c (snd a)))) +
                                F.injR (Pscal_error c p))).
   2: apply Rge_le. 2: apply F.add_up_spec.

   stepl (Rabs ( ( (F.injR c * (F.injR (snd a))) - (F.injR (F.mul_near c (snd a))) ) * (pow x (fst a)) +
                 (F.injR c * Pax_eval p x - Pax_eval (Pscal c p) x) )).
    2:f_equal; simpl; auto; ring.
    apply Rle_trans with
     (Rabs (F.injR c * F.injR (snd a) - F.injR (F.mul_near c (snd a))) * Rabs (pow x (fst a)) +
      Rabs (F.injR c * Pax_eval p x - Pax_eval (Pscal c p) x));
     [rewrite <- Rabs_mult; apply Rabs_triang|].
    apply Rplus_le_compat; [| apply (IHp _ Hx)].
    rewrite Rabs_minus_sym.
     apply Rle_trans with (Rabs (F.injR (F.mul_near c (snd a)) - F.injR c * F.injR (snd a)) ).
     assert (H_xn_l:-1 <= (pow x (fst a)) ).
        apply pow_Rle_1. elim Hx. trivial.
     assert (H_xn_r:(pow x (fst a))<= 1 );[apply pow_Rle_1; elim Hx; trivial|].
     assert (H_xn_abs:=@Rabs_le_1 (pow x (fst a)) H_xn_l H_xn_r).
     stepr ((Rabs (F.injR (F.mul_near c (snd a)) - F.injR c * F.injR (snd a)))*1) by ring.
     apply Rmult_le_compat_l; trivial; apply Rabs_pos.
  unfold F.mul_up, F.mul_down, F.mul_near.
  replace F.mul with (F.apply Mul); [|trivial]. replace Rmult with (Rapply Mul); [|trivial].
  apply F.op_near_up_down_sub_hlf_up_spec.
Qed.


Theorem PMscal_correct : forall (c:F) (t:PolynomialModel F) (f:R->R),
  PMmodels t f -> PMmodels (PMscal c t) (fun x=> (F.injR c) * f(x)).
Proof.
 intros c t f H x hyp_x.
 specialize (H x hyp_x).
 assert (H_sum_err_nonneg:= Pscal_error_nonneg c t).
 apply Rle_trans with (Rabs (F.injR c) * F.injR (error t) + F.injR (Pscal_error c t.(polynomial))).

  2:apply Rle_trans with (Rabs (F.injR c) * F.injR (error t) + F.injR (Pscal_error c t.(polynomial)));
     [ apply Rplus_le_compat_l
     ; generalize (F.injR (Pscal_error c (polynomial t))) H_sum_err_nonneg; intros r H_r; lra
     | rewrite <- F.abs_exact_spec;
       apply Rle_trans with (F.injR (F.mul_up (F.abs c) (error t)) + F.injR (Pscal_error c (polynomial t)));
       [ apply Rplus_le_compat_r; apply Rge_le; apply F.mul_up_spec
       | apply Rge_le; apply F.add_up_spec
       ]
      ].

  destruct t as [p e].
  simpl in *.
  set (p_x:= Pax_eval p x) in *.
  set (cp_x:= Pax_eval (Pscal c p) x).
  rewrite Rabs_minus_sym.
  stepl ( Rabs ( (F.injR c) * f(x)  - (F.injR c) * p_x + ( (F.injR c) * p_x - cp_x) )); [|f_equal; ring].
  apply Rle_trans with ( Rabs ( (F.injR c) * f(x)  - (F.injR c) * p_x ) + Rabs ( (F.injR c) * p_x - cp_x));
    [apply Rabs_triang |].
  apply Rplus_le_compat.
   stepl ( Rabs(F.injR c) * Rabs (f(x) - p_x));
   [ rewrite Rabs_minus_sym; apply Rmult_le_compat_l; trivial; apply Rabs_pos
   | rewrite <- Rabs_mult; f_equal; auto; ring
   ].
   apply Pscal_error_correct; assumption.
Qed.

Close Scope R_scope.

End Polynomial_Model_Scale.
