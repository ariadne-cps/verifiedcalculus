(******************************************************************************
 *  functions/PolynomialModelsScale.v
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

Require Import Lra.

Section Polynomial_Model_Monomial_Scale.

Context `{F : Type} `{FltF : Float F}.


Open Scope nat_scope.

(* Multiply p by x^n *)
Fixpoint Pmonomial_scale (n : nat) (p : list (nat*F)) : list (nat*F) :=
    match p with
    | nil => nil
    | fn :: p' => ( n+(fst fn) , snd fn) :: Pmonomial_scale n p'
    end.

Lemma Pmonomial_scale_eq_nil : forall n, Pmonomial_scale n nil = nil.
Proof.
 intros; trivial.
Qed.

Lemma Pmonomial_scale_eq_cons : forall n fn p, Pmonomial_scale n (fn :: p) = (n+(fst fn) , snd fn) :: Pmonomial_scale n p.
Proof.
 intros; trivial.
Qed.

Lemma Pmonomial_scale_sorted : forall n p, is_sorted_fst p -> is_sorted_fst (Pmonomial_scale n p).
Proof.
 intros n;
 induction p as [|a0 [|a1 p]].
  (* nil *)
  intros H; trivial.
  (* a :: nil *)
  intros H_a; constructor 2.
  (* a :: p *)
  intros H_aap.
  assert (H_ap:is_sorted_fst (a1 :: p)); [apply is_sorted_fst_cons_inv with (fst a0,snd a0); rewrite <- (surjective_pairing); exact H_aap|].
  rewrite Pmonomial_scale_eq_cons.
  apply (is_sorted_fst_cons (n+(fst a0),snd a0) (Pmonomial_scale n (a1 :: p))
                         (n+(fst a1),snd a1) ); trivial.
   2: inversion H_aap; injection H1; intros; subst a1; trivial; apply IHp; assumption.
   apply Nat.add_lt_mono_l; exact (is_sorted_fst_cons_lt _ _ _ H_aap).
Qed.

Definition PMmonomial_scale (n : nat) (t : PolynomialModel) : PolynomialModel :=
 {| polynomial := Pmonomial_scale n t.(polynomial)
  ; error := t.(error) |}.

Close Scope nat_scope.


Open Scope R_scope.

Lemma Pmonomial_scale_ax_eval : forall (n : nat) (p : list (nat * F)) (x : R),
               Pax_eval (Pmonomial_scale n p) x = x ^ n * Pax_eval p x.
Proof.
 induction p; intros x; simpl.
  auto.
  ring.
  destruct a as [m y];
  rewrite Rmult_plus_distr_l; rewrite (IHp x); rewrite pow_add; auto.
  ring.
Qed.

Theorem PMmonomial_scale_correct : forall n t f, PMmodels t f ->
     PMmodels (PMmonomial_scale n t) (fun x => (pow x n)* f(x)).
Proof.
  intros n t f H x hyp_x.
  assert (H_err_nonneg:=PMerror_nonneg t f H).
  specialize (H x hyp_x).
  stepl (Rabs ((pow x n)*((Pax_eval t.(polynomial) x)-(f x)))).
    apply Rle_trans with (Rabs ((pow x n) * FinjR (error t))).
      do 2 rewrite Rabs_mult; apply Rmult_le_compat_l;
      [ apply Rabs_pos
      | apply Rle_trans with (FinjR (error t)); trivial; apply Rle_abs].

      rewrite Rabs_mult.
      rewrite (Rabs_pos_eq (FinjR (error t)) H_err_nonneg).
      stepr (1* (FinjR (error t))) by (simpl; ring).
      apply Rmult_le_compat_r; trivial.
      destruct hyp_x as [H1 H2].

      apply Rabs_Rle_1.
      split.
        apply pow_Rle_l_1; trivial.
        apply pow_Rle_r_1; trivial.
        lra.
  destruct t as [p e].
  simpl in *.
  set (p_x:= Pax_eval p x) in *.
  set (x_n_p_x:= Pax_eval (Pmonomial_scale n p) x).
  f_equal.
  assert(H_ev:x_n_p_x= (pow x n)*p_x); [subst x_n_p_x; subst p_x; simpl in *; apply Pmonomial_scale_ax_eval|].
  rewrite H_ev; ring.
Qed.

Close Scope R_scope.

End Polynomial_Model_Monomial_Scale.
