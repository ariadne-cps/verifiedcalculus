(******************************************************************************
 *  Functions/PolynomialModelsAntiderivative.v
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

Require Import Numbers.Calculus.
Require Import Numbers.Analysis.

Require Export PolynomialModels.



From Stdlib Require Import Recdef.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

Open Scope R_scope.

Definition RPolynomial := list (nat * R).

Fixpoint RPeval (p : RPolynomial) (x : R) : R :=
  match p with
  | nil => 0
  | (a,c) :: p' => c * x^a + RPeval p' x 
  end.

Lemma RPeval_cons : forall a (p : RPolynomial) x, 
  RPeval (a::p) x = (snd a) * x^(fst a) + RPeval p x.
Proof. destruct a; reflexivity. Qed.
Lemma RPeval_cons_pair : forall a c (p : RPolynomial) x, 
  RPeval ((a,c)::p) x = c * x^a + RPeval p x.
Proof. reflexivity. Qed.


Fixpoint RPantiderivative (p : RPolynomial) : RPolynomial :=
  match p with
  | nil => nil
  | (a,c) :: p' => ( S a , Rdiv c (INR (S a)) ) :: RPantiderivative p'
  end.

Lemma RPantiderivative_cons : forall a (p : RPolynomial), 
  RPantiderivative (a::p) = ( S (fst a) , Rdiv (snd a) (INR (S (fst a))) ) :: RPantiderivative p.
Proof. destruct a; reflexivity. Qed.
Lemma RPantiderivative_cons_pair : forall a c (p : RPolynomial), 
  RPantiderivative ((a,c)::p) = ( S a , Rdiv c (INR (S a)) ) :: RPantiderivative p.
Proof. reflexivity. Qed.

Lemma RPantiderivative_0 : forall (p : RPolynomial), RPeval (RPantiderivative p) 0 = 0.
Proof.
  intros p; induction p.
  - reflexivity.
  - destruct a; rewrite -> RPantiderivative_cons_pair, RPeval_cons_pair.
    rewrite -> pow_i. rewrite -> Rmult_0_r. rewrite -> Rplus_0_l. now rewrite -> IHp. 
    exact (Nat.lt_0_succ n).
Qed.

Theorem RPantiderivative_correct : forall (p : RPolynomial) (x : R),
  derivable_pt_lim (RPeval (RPantiderivative p)) x (RPeval p x) .
Proof.
  intros p x.
  induction p.
  - simpl. now apply derivable_pt_lim_const.
  - destruct a as (a,c). rewrite -> RPantiderivative_cons_pair.
    rewrite -> RPeval_cons.
    apply ( derivable_pt_lim_ext (plus_fct (fun x => c * (x^(S a)/(S a))) (RPeval (RPantiderivative p))) ).
      intro w; rewrite -> RPeval_cons_pair. unfold plus_fct. 
      simpl. lra.
    apply derivable_pt_lim_plus.
    -- apply derivable_pt_lim_scal.
       replace (fst (a,c)) with a by auto.
       replace (pow x a) with (((S a) * (pow x a)) / (S a)).
       apply derivable_pt_lim_div_scal.
       now apply derivable_pt_lim_pow.
       rewrite -> Rmult_div_swap, Rdiv_diag, Rmult_1_l; [reflexivity|now apply not_O_S_INR].
    -- exact IHp.
Qed.


Section Polynomial_Model_Antiderivative.

Context `{F : Type} `{FltF : Float F}.

Fixpoint Pantiderivative (p : Polynomial F) : Polynomial F :=
  match p with
  | nil => nil
  | (a,c) :: p' => ( S a , F.div near c (F.of_nat (S a)) ) :: Pantiderivative p'
  end.

Lemma Pantiderivative_nil : Pantiderivative nil = nil.
Proof. reflexivity. Qed.

Lemma Pantiderivative_cons : forall a p, 
  Pantiderivative (a::p) = ( S (fst a) , F.div_near (snd a) (F.of_nat (S (fst a))) ) :: Pantiderivative p.
Proof. destruct a. reflexivity. Qed.

Lemma Pantiderivative_cons_pair : forall a c p, 
  Pantiderivative ((a,c)::p) = ( S a , F.div_near c (F.of_nat (S a)) ) :: Pantiderivative p.
Proof. reflexivity. Qed.

Lemma is_sorted_fst_01 : forall (a0:nat*F) a1 p2, is_sorted_fst (a0::a1::p2) -> (fst a0 < fst a1)%nat.
Proof. 
  intros a0 a1 p2 Hs.
  remember (a0::a1::p2) as p.
  destruct Hs.
  - discriminate Heqp.
  - discriminate Heqp.
  - rename H0 into H01. injection Heqp. intros Hxs H0.
    rewrite -> Hxs in H. simpl in H. injection H; intro H1.
    rewrite <- H0, -> H1. exact H01.
Qed.

Lemma Pantiderivative_sorted : forall p, is_sorted_fst p -> is_sorted_fst (Pantiderivative p).
Proof.
  induction p as [|a0 [|a1 p]].
    (* nil *)
    intros H; trivial.
    (* a :: nil *)
    intros Ha. rewrite -> Pantiderivative_cons. constructor 2.
    (* a :: p *)
    intros H_aap.
    assert ((fst a0 < fst a1)%nat) as Ha01. 
      now apply (is_sorted_fst_01 a0 a1 p).
    assert (H_ap:is_sorted_fst (a1 :: p)); 
      [apply is_sorted_fst_cons_inv with (fst a0, snd a0); rewrite <- (surjective_pairing); exact H_aap|].
    rewrite Pantiderivative_cons.
    remember (S (fst a0), F.div near (snd a0) (F.of_nat (S (fst a0)))) as b0.
    remember (S (fst a1), F.div near (snd a1) (F.of_nat (S (fst a1)))) as b1.
    assert (hd_error (Pantiderivative (a1::p)) = Some b1) as Hhd. 
      unfold hd_error. rewrite -> Heqb1, Pantiderivative_cons. reflexivity.
    assert ((fst b0 < fst b1)%nat) as Hb01. 
      replace (fst b0) with (S (fst a0)) by now rewrite -> Heqb0.
      replace (fst b1) with (S (fst a1)) by now rewrite -> Heqb1.
      apply (proj1 (Nat.succ_lt_mono (fst a0) (fst a1))). exact Ha01.
    pose proof (@is_sorted_fst_cons F b0 (Pantiderivative (a1::p)) b1 Hhd Hb01 (IHp H_ap)) as H.
    rewrite -> Heqb0 in H.
    exact H. 
Qed.

Definition div_err_up x1 x2 := F.div2_up (F.sub_up (F.div_up x1 x2) (F.div_down x1 x2)).

Lemma div_err_up_correct : forall x1 x2, (F.injR x2 <> 0) ->
  Rdist (F.injR (F.div_near x1 x2)) (F.injR x1 / F.injR x2) <= F.injR (div_err_up x1 x2).
Proof. 
  intros x1 x2 Hx2.
  unfold div_err_up.
  set (rd := F.div_down x1 x2); 
  set (rn := F.div_near x1 x2);
  set (ru := F.div_up x1 x2).
  set (y1 := F.injR x1); set (y2 := F.injR x2).
  assert (Rdist (F.injR rn) (y1/y2) <= Rdist (F.injR ru) (y1/y2)) as Hnu. {
    apply F.div_near_spec. exact Hx2. }
  assert (Rdist (F.injR rn) (y1/y2) <= Rdist (F.injR rd) (y1/y2)) as Hnd. {
    apply F.div_near_spec. exact Hx2. }
  assert (y1/y2 <= F.injR (F.div_up x1 x2)) as Hu. {
    apply Rge_le; apply F.div_up_spec. exact Hx2. }
  assert (F.injR (F.div_down x1 x2) <= y1/y2) as Hd. {
    apply F.div_down_spec. exact Hx2. }
  transitivity ( (Rdist (F.injR ru) (y1/y2) + Rdist (F.injR rd) (y1/y2)) / 2).
    lra.
    transitivity ( (F.injR (F.sub_up ru rd)) / 2 ).
    rewrite -> Rdiv_def. apply Rmult_le_compat_r.
      apply Rlt_le. apply Rinv_pos. exact Rlt_0_2.
    unfold Rdist.
    rewrite -> Rabs_pos_eq.
    rewrite -> Rabs_neg_eq.
    stepl (F.injR ru - F.injR rd).
    apply Rge_le. now apply F.sub_up_spec.
    lra.
    now apply Rle_minus.
    now apply Rle_Rminus_zero.
    apply Rge_le. unfold F.div2_up, F.div2. 
    replace (2%R) with (F.injR (F.of_nat 2)).
    apply F.div_up_spec.
    rewrite -> F.ninjr_spec. exact (not_O_S_INR 1). 
    now rewrite -> F.ninjr_spec. 
Qed.


Definition Pantiderivative_error : Polynomial F -> F :=
  fold_right ( fun nf=> F.add_up (div_err_up (snd nf) (F.of_nat (S (fst nf)))) ) F.null.

Lemma Pantiderivative_error_cons  : forall a c (p : Polynomial F), 
  Pantiderivative_error ((a,c)::p) = F.add_up (div_err_up c (F.of_nat (S a))) (Pantiderivative_error p).
Proof. reflexivity. Qed.


Fixpoint PinjR (p : Polynomial F) : RPolynomial :=
  match p with
  | nil => nil
  | a::p => (fst a, F.injR (snd a)) :: (PinjR p)
  end.

Lemma PinjR_cons: forall a (p : Polynomial F), PinjR (a::p) =  (fst a, F.injR (snd a)) :: (PinjR p).
Proof. reflexivity. Qed.
Lemma PinjR_cons_pair : forall a c (p : Polynomial F), PinjR ((a,c)::p) =  (a, F.injR c) :: (PinjR p).
Proof. reflexivity. Qed.


Lemma Pantiderivative_error_correct : forall (p : Polynomial F) (x : R), -1 <= x <= 1 ->
  Rdist (Pax_eval (Pantiderivative p) x) (RPeval (RPantiderivative (PinjR p)) x) <= F.injR (Pantiderivative_error p).
Proof.
  intros p x Hx. induction p.
  - simpl. rewrite -> Rdist_eq. unfold F.null. rewrite -> F.ninjr_spec. now apply Rle_refl.
  - destruct a as (a,c). 
    rewrite -> Pantiderivative_cons_pair, Pax_eval_cons_pair.
    rewrite -> PinjR_cons. rewrite -> RPantiderivative_cons, RPeval_cons.
    rewrite -> Pantiderivative_error_cons.
    transitivity ( Rdist (F.injR (F.div_near c (F.of_nat (S a))) * Rpow x (S a)) (F.injR c / INR (S a) * Rpow x (S a))
      + Rdist (Pax_eval (Pantiderivative p) x) (RPeval (RPantiderivative (PinjR p)) x) ).
    2: transitivity ( (F.injR (div_err_up c (F.of_nat (S a)))) + (F.injR (Pantiderivative_error p)) ).
    -- apply Rdist_plus_compat.
    -- apply Rplus_le_compat.
       rewrite <- Rabs_dist_mult_r.
       transitivity ( Rdist (F.injR (F.div_near c (F.of_nat (S a)))) (F.injR c / INR (S a)) * 1).
       apply Rmult_le_compat_l.
       ---- apply Rge_le; now apply Rdist_pos.
       ---- apply Rabs_pow_le_1. now apply Rabs_le.
       ---- rewrite -> Rmult_1_r. 
            rewrite <- F.ninjr_spec.
            replace (INR (S a)) with (F.injR (F.of_nat (S a))).
            apply div_err_up_correct.
            rewrite -> F.ninjr_spec.
            now apply not_O_S_INR.
            now rewrite -> F.ninjr_spec.
       ---- exact IHp.
    -- apply Rge_le. now apply F.add_up_spec.
Qed.

Definition PMantiderivative_error t : F :=
  F.add_up (t.(error)) (Pantiderivative_error t.(polynomial)).

Definition PMantiderivative (t:PolynomialModel F) : PolynomialModel F :=
  {| polynomial := Pantiderivative t.(polynomial);
     error := PMantiderivative_error t |}.

Lemma Pax_eval_RP_eval_PinjR : forall p x, Pax_eval p x = RPeval (PinjR p) x.
Proof.
  intros p x. induction p. 1: reflexivity.
  rewrite -> Pax_eval_cons, PinjR_cons, RPeval_cons. now rewrite -> IHp.
Qed.

Lemma MVT_bounds_gt : forall f df e x (Hx0 : 0 < x), 
  f 0 = 0 -> (forall y, 0 <= y <= x -> derivable_pt_lim f y (df y)) ->
    (forall y, 0 <= y <= x -> Rabs (df y) <= e) -> Rabs (f x) <= (Rabs x) * e. 
Proof.
  intros f df e x Hx0 Hf0 Hdf He.
  assert (forall y, 0 <= y <= x -> derivable_pt f y) as Pdf'. {
    intros y Hy. exact (derivable_pt_of_lim f y (df y) (Hdf y Hy)). }
  assert (forall y, 0 < y < x -> derivable_pt f y) as Pdf. {
    intros y Hy; exact (Pdf' y (Rlt_le_rng Hy)). }
  assert (forall y, 0 <= y <= x -> continuity_pt f y) as Cf. {
    intros y Hy. exact (derivable_continuous_pt f y (Pdf' y Hy)). }
  pose proof (MVT1 f 0 x Hx0 Pdf Cf) as [c [Hcx Hc]].
  rewrite -> (proj2 (derive_pt_eq f c (df c) (Pdf c Hcx))) in Hc.
  rewrite -> Hf0, Rminus_0_r, Rminus_0_r in Hc.
  rewrite <- Hc, -> Rabs_mult. apply Rmult_le_compat_l.
  exact (Rabs_pos x).
  apply He. exact (Rlt_le_rng Hcx).
  exact (Hdf c (Rlt_le_rng Hcx)). 
Qed.

Lemma MVT_bounds : forall f df e b, 
  f 0 = 0 -> (forall y, - b <= y <= b -> derivable_pt_lim f y (df y)) ->
    (forall y, -b <= y <= b -> Rabs (df y) <= e) -> 
       (forall x, -b <= x <= b -> Rabs (f x) <= (Rabs x) * e). 
Proof.
  intros f df e b Hf0 Hdf He.
  intros x Hx.
  destruct (Rtotal_order 0 x) as [Hxgt0|[Hxeq0|Hxlt0]].
  - apply (MVT_bounds_gt f df e x Hxgt0 Hf0).
    intros y Hy; apply Hdf. lra.
    intros y Hy; apply He. lra.
  - rewrite <- Hxeq0, -> Hf0, Rabs_R0, Rmult_0_l. exact (Rle_refl 0).
  - remember (-x) as nx. assert (0 < nx) as Hnxgt0 by lra.
    set (g := fun x => f (-x));
    set (dg := fun x => - df (-x)).
    assert (f (-0) = 0) as Hfn0 by now rewrite -> Ropp_0.
    assert (forall y, 0 <= y <= nx -> derivable_pt_lim g y (dg y)) as Hdg. {
      intros y Hy. unfold g, dg. apply derivable_pt_lim_mirr_fwd.
      rewrite -> Ropp_involutive. apply Hdf. lra.
    }
    assert (forall y, 0 <= y <= nx -> Rabs (dg y) <= e) as Hge. {
      intros y Hy. unfold dg. rewrite -> Rabs_Ropp. apply He. lra. }
    pose proof (MVT_bounds_gt g dg e nx Hnxgt0 Hfn0 Hdg Hge) as H.
    unfold g in H; rewrite -> Heqnx in H. rewrite -> Ropp_involutive, Rabs_Ropp in H.
    exact H.
Qed.

Theorem PMantiderivative_correct : forall (t:PolynomialModel F) (f df : R->R),
  f 0 = 0 -> (forall x, derivable_pt_lim f x (df x)) -> 
    PMmodels t df -> PMmodels (PMantiderivative t) (f).
Proof.
  intros t f df Hf0 Hdf Ht.
  set (dp := PinjR t.(polynomial)).
  set (p := RPantiderivative dp).
  assert (forall x, derivable_pt_lim (RPeval p) x (RPeval dp x)) as Hdp.
    now apply RPantiderivative_correct.
  assert (forall (x : R), RPeval (PinjR t.(polynomial)) x = Pax_eval t.(polynomial) x) as Htp. {
    intro x. induction (t.(polynomial)).
    - reflexivity.
    - rewrite -> PinjR_cons, RPeval_cons, Pax_eval_cons.
      rewrite -> IHl. reflexivity.
      apply RPantiderivative_correct.
  }
  unfold PMmodels, PMantiderivative; simpl.
  unfold PMantiderivative_error.
  intros x Hx.
  transitivity ( Rdist (Pax_eval (Pantiderivative (polynomial t)) x) (RPeval p x) + (Rdist (RPeval p x) (f x)) ).
  apply Rdist_triang.
  transitivity (F.injR (Pantiderivative_error (polynomial t)) + F.injR (error t)).
  apply Rplus_le_compat.
  apply (Pantiderivative_error_correct _ x Hx).
  
  set (g := RPeval p). set (dg := RPeval dp). set (e := F.injR (error t)).
  assert (forall x, -1<=x<=1 -> Rdist (dg x) (df x) <= e) as Hfg. {
    clear x Hx; intros x Hx.
    unfold PMmodels in Ht.
    specialize (Ht x Hx).
    replace (Pax_eval (polynomial t) x) with (dg x) in Ht.
    exact Ht.
    unfold dg, dp.
    symmetry; now apply Pax_eval_RP_eval_PinjR.
  }
  set (h := minus_fct g f).
  set (dh := minus_fct dg df).
  assert (g 0 = 0) as Hg0. { unfold g, p. apply RPantiderivative_0. }
  assert (h 0 = 0) as Hh0. { unfold h, minus_fct. rewrite -> Hf0, Hg0. now rewrite -> Rminus_0_r. }
  assert (forall y, -1 <= y <= 1 -> derivable_pt_lim h y (dh y)) as Hdh. {
    intros y Hy. apply derivable_pt_lim_minus. apply Hdp. apply Hdf. }
  assert (forall y, -1 <= y <= 1 -> Rabs (dh y) <= e) as Hey. {
    intros y Hy. unfold dh, minus_fct. now apply Hfg. }
  pose proof (MVT_bounds h dh e 1 Hh0 Hdh Hey).
  unfold h, minus_fct in H.
  transitivity (Rabs x * e). apply H. exact Hx.
  transitivity (1*e). apply Rmult_le_compat_r.
  transitivity (Rdist (dg 0) (df 0)). 
    apply Rge_le; now apply Rdist_pos.
    apply Hfg; lra.
  now apply Rabs_le.
  rewrite -> Rmult_1_l; now apply Rle_refl.
  rewrite -> Rplus_comm. apply Rge_le. now apply F.add_up_spec.
Qed.


Close Scope R_scope.

End Polynomial_Model_Antiderivative.
