(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModels.


Section Polynomial_Models_Monomial.

Context `{F : Type} `{FltF : Float F}.


Open Scope nat_scope.

(* Multiply p by x^n *)
Fixpoint pre_monomial (n : nat) (p : list (nat*F)) : list (nat*F) :=
    match p with
    | nil => nil
    | fn :: p' => ( n+(fst fn) , snd fn) :: pre_monomial n p'
    end.

Lemma pre_monomial_eq_nil : forall n, pre_monomial n nil = nil.
Proof.
 intros; trivial.
Qed.

Lemma pre_monomial_eq_cons : forall n fn p, pre_monomial n (fn :: p) = (n+(fst fn) , snd fn) :: pre_monomial n p.
Proof.
 intros; trivial.
Qed.

Lemma pre_monomial_sorted : forall n p, is_sorted_fst p -> is_sorted_fst (pre_monomial n p).
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
  rewrite pre_monomial_eq_cons.
  apply (is_sorted_fst_cons (n+(fst a0),snd a0) (pre_monomial n (a1 :: p))
                         (n+(fst a1),snd a1) ); trivial.
   2: inversion H_aap; injection H1; intros; subst a1; trivial; apply IHp; assumption.
   apply Nat.add_lt_mono_l; exact (is_sorted_fst_cons_lt _ _ _ H_aap).
Qed.

Definition PMmonomial_scale (n : nat) (t : PolynomialModel) : PolynomialModel :=
 {| polynomial := pre_monomial n t.(polynomial)
  ; sorted := @pre_monomial_sorted n t.(polynomial) t.(sorted)
  ; error := t.(error) |}.

Close Scope nat_scope.


Open Scope R_scope.

Lemma ax_eval_pre_monomial : forall (n : nat) (p : list (nat * F)) (x : R),
               Pax_eval (pre_monomial n p) x = x ^ n * Pax_eval p x.
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
 destruct t as [p Hs e].
 simpl in *.
 set (p_x:= Pax_eval p x) in *.
 set (x_n_p_x:= Pax_eval (pre_monomial n p) x).
 f_equal.
 assert(H_ev:x_n_p_x= (pow x n)*p_x); [subst x_n_p_x; subst p_x; simpl in *; apply ax_eval_pre_monomial|].
 rewrite H_ev; ring.
Qed.

Close Scope R_scope.

End Polynomial_Models_Monomial.
