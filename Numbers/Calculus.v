(******************************************************************************
 *  Numbers/Calculus.v
 *
 *  Copyright 2023 Pieter Collins
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


From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

Require Import RealAddenda.



Section Calculus.


Open Scope R_scope.

Lemma strictly_increasing_implies_increasing : forall (f : R -> R),
  (forall (x y : R), x<y -> f x < f y) -> (forall (x y : R), x<=y -> f x <= f y).
Proof.
  intros f H x y. specialize (H x y).
  intro Hle. destruct Hle as [Hlt | Heq].
  - apply Rlt_le. exact (H Hlt).
  - apply Req_le. f_equal. exact Heq.
Qed.


Lemma continuity_pt_id : forall x : R, continuity_pt id x.
Proof.
  intro x. unfold continuity_pt, continue_in, limit1_in, limit_in, id.
  intros eps Heps. exists eps. split. exact Heps.
  intros y [_ Hy]. exact Hy.
Qed.
(*
From Stdlib Require Import Logic.PropExtensionality. *)

Theorem MVT1
  : forall (f : R -> R) (a b : R), a < b ->
      forall (pr : forall c : R, a < c < b -> derivable_pt f c),
      (forall c : R, a <= c <= b -> continuity_pt f c) ->
           exists (c : R) (P : a < c < b),
             (b - a) * derive_pt f c (pr c P) = (f b - f a).
Proof.
  set (g := id : R -> R).
  intros f a b Hab pr1 ct1.
  set (pr2 := (fun c _ => derivable_pt_id c)
    : forall c, a < c < b ->  derivable_pt g c ).
  assert (forall c, a <= c <= b -> continuity_pt g c) as ct2. {
    intros; now apply continuity_pt_id. }
  pose proof (MVT f g a b pr1 pr2 Hab ct1 ct2) as [c [P Hf]].
  exists c, P.
  replace (derive_pt g c (pr2 c P)) with 1 in Hf
    by exact (eq_sym (derive_pt_id c)).
  unfold g in Hf; rewrite -> Rmult_1_r in Hf.
  exact Hf.
Qed.

Lemma integral_positive :
  forall (f : R -> R), forall (a x : R), a <= x ->
    forall (Pdf : forall y, a <= y <= x -> derivable_pt f y),
      0 <= f a -> (forall y, forall P : a <= y <= x, 0 <= derive_pt f y (Pdf y P)) ->
        0 <= f x.
Proof.
  intros f a x Halex Pdf Hfapos Hdfpos.
  set (Hdfax := (fun c (P : a < c < x) => Pdf c (Rlt_le_rng P))).
  assert (forall c (P : a < c < x), 0 <= derive_pt f c (Pdf c (Rlt_le_rng P))) as Hdfipos. {
    intros c Plt. now apply (Hdfpos c (Rlt_le_rng Plt)). }
  assert (forall c, a <= c <= x -> continuity_pt f c) as Hctsfc. {
    intros c Hc. apply derivable_continuous_pt. exact (Pdf c Hc). }
  destruct (Rle_lt_or_eq _ _ Halex) as [Haltx|Haeqx].
  2: rewrite <- Haeqx; exact Hfapos.
  pose proof (MVT1 f a x Haltx Hdfax Hctsfc) as [c [P Hf]].
  revert Hf.
  intro Hf.
  remember (derive_pt f c (Pdf c (Rlt_le_rng P))) as dfc.
  specialize (Hdfipos c P).
  unfold Hdfax in Hf.
  rewrite <- Heqdfc in Hf.
  replace (f x) with ((f a) + (x - a) * dfc) by lra.
  apply Rplus_le_le_0_compat.
  - exact Hfapos.
  - apply Rle_mult_nonneg_nonneg.
    -- apply Rle_Rminus_zero. now apply Rlt_le.
    -- rewrite -> Heqdfc. now apply Hdfipos.
Qed.

Lemma integral_comparison :
  forall (f g : R -> R), forall (a x : R), a <= x ->
     forall (Pdf : forall y, a <= y <= x -> derivable_pt f y)
            (Pdg : forall y, a <= y <= x -> derivable_pt g y),
       (f a <= g a) -> (forall y (P : a <= y <= x), derive_pt f y (Pdf y P) <= derive_pt g y (Pdg y P)) ->
         f x <= g x.
Proof.
  intros f g a x Hax Pdf Pdg Hfga Hdfg.
  set (h := minus_fct g f).
  apply Rle_zero_Rminus.
  replace (g x - f x) with (h x) by reflexivity.
  set (Pdh := fun y P => derivable_pt_minus g f y (Pdg y P) (Pdf y P)).
  apply (integral_positive h a x Hax Pdh).
  - apply Rle_Rminus_zero. exact Hfga.
  - intros y P. unfold h, Pdh. rewrite -> derive_pt_minus.
    apply Rle_Rminus_zero. exact (Hdfg y P).
Qed.


Lemma derivable_pt_of_lim : forall f x dfx, 
  derivable_pt_lim f x dfx -> derivable_pt f x.
Proof.
  unfold derivable_pt, derivable_pt_abs.
  intros f x dfx Hdfx. exists dfx. exact Hdfx.
Qed.

Lemma integral_positive_lim : forall (f : R -> R) (df : R -> R),
  forall (a x : R), a <= x ->
    (forall y, a <= y <= x -> derivable_pt_lim f y (df y)) ->
      0 <= f a -> (forall y, a <= y <= x -> 0 <= df y) ->
        0 <= f x.
Proof.
  intros f df a x Hax Hfdf Hf Hdf.
  set (Pdf := fun (y : R) => fun (P : a <= y <= x) => derivable_pt_of_lim f y (df y) (Hfdf y P)).
  apply (integral_positive f a x Hax Pdf Hf).
  intros y P.
  unfold proj1_sig, Pdf; simpl.
  apply (Rle_eq_trans _ (df y) _ (Hdf y P)).
  symmetry; apply derive_pt_eq_0. exact (Hfdf y P).
Qed.

Lemma integral_comparison_lim : forall (f g : R -> R) (df dg : R -> R),
  forall (a x : R), a <= x ->
    (forall y, a <= y <= x -> derivable_pt_lim f y (df y)) ->
    (forall y, a <= y <= x -> derivable_pt_lim g y (dg y)) ->
      f a <= g a -> (forall y, a <= y <= x -> df y <= dg y) ->
        f x <= g x.
Proof.
  intros f g df dg a x Hax Hfdf Hgdg Hfg Hdfg.
  set (h := minus_fct g f).
  set (dh := minus_fct dg df).
  apply Rle_zero_Rminus.
  replace (g x - f x) with (h x) by reflexivity.
  apply (integral_positive_lim h dh a x Hax).
  - intros y P. apply derivable_pt_lim_minus. exact (Hgdg y P). exact (Hfdf y P).
  - apply Rle_Rminus_zero. exact Hfg.
  - intros y P. unfold dh. apply Rle_Rminus_zero. exact (Hdfg y P).
Qed.

Local Lemma integral_comparison_lim_opp : forall f g df dg,
  (forall x, x <= 0 -> derivable_pt_lim f x (df x)) -> 
  (forall x, x <= 0 -> derivable_pt_lim g x (dg x)) -> 
    f 0 <= g 0 ->
      (forall x, 0 <= x -> dg (-x) <= df (-x)) -> 
        (forall x, 0 <= x -> f (-x) <= g (-x)).
Proof.
  intros f g df dg Hdf Hdg H0 H x Hx.
  apply ( integral_comparison_lim
          (fun x => f (-x)) (fun x => g (-x))
          (fun x => - df (-x)) (fun x => - dg (-x)) 0 x Hx).
  - intros y Hy.
    apply derivable_pt_lim_mirr_fwd.
    rewrite -> Ropp_involutive.
    apply Hdf.
    now apply Ropp_0_le_le_contravar. 
  - intros y Hy.
    apply derivable_pt_lim_mirr_fwd.
    rewrite -> Ropp_involutive.
    apply Hdg.
    now apply Ropp_0_le_le_contravar. 
  - rewrite -> Ropp_0. now apply H0.
  - intros y Hy.
    assert (-y <= 0) as Hny. now apply Ropp_0_le_le_contravar.
    apply Ropp_le_contravar.
    now apply H.
Qed.

Lemma integral_comparison_lim_neg : forall f g df dg,
  (forall x, x <= 0 -> derivable_pt_lim f x (df x)) -> 
  (forall x, x <= 0 -> derivable_pt_lim g x (dg x)) -> 
    f 0 <= g 0 ->
      (forall x, x <= 0 -> dg x <= df x) -> 
        (forall x, x <= 0 -> f x <= g x).
Proof.
  intros f g df dg Hdf Hdg H0 H x Hx.
  assert (forall nx, 0 <= nx -> dg (-nx) <= df (-nx)) as Hdfg. {
    intros nx Hnx. apply H. now apply Ropp_0_le_le_contravar. }
  set (nx := -x).
  assert (0 <= nx) as Hnx. apply Ropp_0_ge_le_contravar. apply Rle_ge. exact Hx.
  assert (x = -nx) as Enx. unfold nx. now rewrite -> Ropp_involutive.
  rewrite -> Enx.
  exact (integral_comparison_lim_opp f g df dg Hdf Hdg H0 Hdfg nx Hnx).
Qed.


Lemma derivable_pt_lim_pow_succ : 
  forall n x, derivable_pt_lim (fun x => pow x (S n)) x (INR (S n) * x ^ n).
Proof.
  intros n x.
  replace (INR (S n) * x^n) with (INR (S n) * Rpow x (Init.Nat.pred (S n))).
  apply derivable_pt_lim_pow.
  auto.
Qed.

Lemma derivable_pt_lim_pow_div_fact : 
  forall n x, derivable_pt_lim (fun x => x^(S n) / Rfact (S n)) x (x^n / Rfact n).
Proof.
  intros n x.
  replace (x^n / Rfact n) with ((INR (S n)) * x^n / Rfact (S n)).
  apply derivable_pt_lim_div_scal.
  now apply derivable_pt_lim_pow_succ.
  rewrite -> Rfact_succ.
  rewrite -> Rdiv_mult_distr.
  apply Rdiv_eq_compat_r.
  rewrite -> Rmult_div_swap.
  rewrite -> Rdiv_diag by now apply not_O_S_INR.
  rewrite -> Rmult_1_l.
  reflexivity.
Qed.

Lemma derivable_pt_lim_cnst_mul_pow_div_fact : 
  forall c n x, derivable_pt_lim (fun x => c * x^(S n) / Rfact (S n)) x (c * x^n / Rfact n).
Proof.
  intros c n x.
  apply ( derivable_pt_lim_ext (fun x =>  (Rpow x (S n) / Rfact (S n)) * c) ).
  intro z; rewrite <- (Rmult_comm c); now rewrite -> Rmult_div_assoc.
  replace (c * Rpow x n / Rfact n) with ((Rpow x n / Rfact n) * c).
  2: rewrite <- (Rmult_comm c); now rewrite -> Rmult_div_assoc.
  apply derivable_pt_lim_scal_right.
  now apply derivable_pt_lim_pow_div_fact.
Qed.

Definition smooth_pt_lim (fd : nat -> R -> R) (x : R) : Prop :=
  forall n, derivable_pt_lim (fd n) x (fd (S n) x).

Fixpoint taylor_series (fd : nat -> R -> R) (Pdf : forall y, smooth_pt_lim fd y) (n : nat) (x0 : R) : R -> R :=
  fun x =>
    match n with 
    | O => fd O x0
    | S m => taylor_series fd Pdf m x0 x + fd (S m) x0 * (x - x0)^(S m) / Rfact (S m)
    end.

Lemma taylor_series_zero : forall fd Pdf x0 x, 
  taylor_series fd Pdf O x0 x = fd O x0.
Proof. reflexivity. Qed.

Lemma taylor_series_succ : forall fd Pdf n x0 x, 
  taylor_series fd Pdf (S n) x0 x = taylor_series fd Pdf n x0 x + fd (S n) x0 * (x - x0)^(S n) / Rfact (S n).
Proof. reflexivity. Qed.


Local Lemma derivable_pt_lim_eq : forall y1 f x y2, y1 = y2 ->
derivable_pt_lim f x y1 -> derivable_pt_lim f x y2.
Proof.
  intros y1 f x y2 Hy12 H. now rewrite <- Hy12.
Qed.

Local Lemma derivative_pt_lim_mult_eq :
  forall l1 l2 f1 f2 x l, 
    l1 * (f2 x) + (f1 x) * l2 = l ->
      derivable_pt_lim f1 x l1 -> 
        derivable_pt_lim f2 x l2 -> 
          derivable_pt_lim (mult_fct f1 f2) x l.
Proof.
  intros l1 l2 f1 f2 x l Hl Hf1 Hf2.
  rewrite <- Hl. now apply derivable_pt_lim_mult.
Qed.

Local Lemma derivable_pt_lim_pow_succ_eq :
  forall n x l, 
    (INR (S n)) * Rpow x n = l ->
      derivable_pt_lim (fun x => Rpow x (S n)) x l.
Proof.
  intros n x l Hl.
  rewrite <- Hl.
  now apply derivable_pt_lim_pow.
Qed.

Local Lemma derivative_pt_lim_mirr_fwd_eq :
  forall l' f x l, 
    -l' = l ->
      derivable_pt_lim f (-x) l' -> 
        derivable_pt_lim (mirr_fct f) x l.
Proof.
  intros l' f x l Hl Hf.
  rewrite <- Hl. apply derivable_pt_lim_mirr_fwd.
  now rewrite -> Ropp_involutive.
Qed.

Local Lemma derivable_pt_lim_comp_eq :
  forall l1 l2 f1 f2 x l,
    l2 * l1 = l ->
      derivable_pt_lim f1 x l1 ->
       derivable_pt_lim f2 (f1 x) l2 ->
         derivable_pt_lim (comp f2 f1) x l.
Proof. intros l1 l2 f1 f2 x l Hl Hf1 Hf2. rewrite <- Hl. now apply derivable_pt_lim_comp. Qed.

Lemma derivable_pt_lim_affine : forall a0 a1 x, 
  derivable_pt_lim (fun x => a0 + a1 * x) x a1.
Proof. 
  intros a0 a1 x.
  set (f := plus_fct (fun x => a0) (mult_real_fct a1 id)).
  set (df := fun x : R => a1).
  replace (a1) with (0 + a1 * 1) by lra. 
  unfold f. apply derivable_pt_lim_plus.
  - now apply derivable_pt_lim_const.
  - replace (0+a1*1) with (a1) by lra.
    apply derivable_pt_lim_scal.
    now apply derivable_pt_lim_id.
Qed.

Local Lemma derivable_pt_lim_cnst_plus :
  forall f c x l,
    derivable_pt_lim f (c+x) l ->
      derivable_pt_lim (fun x => f (c+x)) x l.
Proof. 
  intros f c x l H.
  apply (derivable_pt_lim_ext (comp f (fun x => c + 1*x))).
  1: intro z. unfold comp. now rewrite -> Rmult_1_l.
  replace l with (l*1) by lra.
  apply derivable_pt_lim_comp.
  - apply derivable_pt_lim_affine.
  - rewrite -> Rmult_1_l. exact H.
Qed.



Local Definition taylor_series_reverse fd Pdf n x : R -> R := 
  fun t => taylor_series fd Pdf n t x.

Local Lemma taylor_series_reverse_succ : forall fd Pdf n x t, 
  taylor_series_reverse fd Pdf (S n) x t
    = taylor_series_reverse fd Pdf n x t + fd (S n) t * (x - t)^(S n) / Rfact (S n).
Proof. reflexivity. Qed.
 
Local Lemma taylor_series_reverse_derivable_pt_lim fd Pdf :
  forall n x t, derivable_pt_lim (taylor_series_reverse fd Pdf n x) t
    ((fd (S n) t) * (x-t)^n / (Rfact n)) .
Proof.
  intros n x t; induction n.
  - unfold taylor_series_reverse, taylor_series.
    pose proof (Pdf t O) as H.
    apply (derivable_pt_lim_eq (fd (S O) t)). 2: exact H.
    set (f := fd O) in *; set (df := fd (S O)) in *.
    rewrite -> Rpow_zero, Rfact_0. lra.
  - apply ( derivable_pt_lim_ext (plus_fct (taylor_series_reverse fd Pdf n x) 
      (fun t => fd (S n) t * (x-t)^(S n) / Rfact (S n))) ).
    1: reflexivity.
    replace (fd (S (S n)) t * Rpow (x - t) (S n) / Rfact (S n)) with 
      ( (fd (S n) t * Rpow (x - t) n / Rfact n) 
          + (fd (S (S n)) t * (Rpow (x - t) (S n) / Rfact (S n))
              + fd (S n) t * ( - Rpow (x - t) n) / Rfact n) ).
    2: rewrite -> Rfact_succ; lra.
    apply derivable_pt_lim_plus.
    1: exact IHn.
    clear IHn.
    apply (derivable_pt_lim_ext (mult_fct (fd (S n)) (mirr_fct (fun t => Rpow (x+t) (S n) / Rfact (S n))))).
    1: intro z; unfold mult_fct; simpl. 1: unfold mirr_fct; rewrite <- Rminus_def; lra.
    apply (derivative_pt_lim_mult_eq (fd (S (S n)) t) ( - (x-t)^n / Rfact n)).
    unfold mirr_fct; rewrite <- Rminus_def; lra.
    apply Pdf.
    apply (derivative_pt_lim_mirr_fwd_eq (( INR (S n) * Rpow (x+(-t)) n / Rfact (S n)))).
    -- rewrite <- Rminus_def.
       rewrite -> Rfact_succ_cancel.
       now rewrite -> Rdiv_opp_l.
    -- apply derivable_pt_lim_div_scal.
       apply (derivable_pt_lim_cnst_plus (fun z => Rpow z (S n))).
       now apply derivable_pt_lim_pow_succ.
Qed.


Local Lemma derivable_pt_ext : forall f1 f2 (H : forall x, f1 x = f2 x) x,
  derivable_pt f1 x -> derivable_pt f2 x.
Proof.
  unfold derivable_pt, derivable_pt_abs.
  intros f1 f2 H x [l Hl1]. exists l. 
  exact (derivable_pt_lim_ext f1 f2 x l H Hl1).
Qed.


Local Lemma  taylor_reverse_series_remainder :
  forall fd Pdf n x0 x, 
    let F := (taylor_series_reverse fd Pdf n x) in
    let dF := (fun t => (fd (S n) t) * (x-t)^n / (Rfact n)) in
    let G := fun t => Rpow (x-t) (S n) / Rfact (S n) in
    let dG := (fun t => - Rpow (x-t) n / Rfact n) in
  forall t, x0 < t <= x -> 
     exists c (Hc : x0 < c < t),
       dF c / dG c = (F t - F x0) / (G t - G x0).
Proof.
  intros fd Pdf n x0 x.
  intros F dF G dG.
  intros t Ht.
  assert (forall y, derivable_pt_lim F y (dF y)) as HFd. {
    exact (taylor_series_reverse_derivable_pt_lim fd Pdf n x).
  }
  assert (forall y, derivable_pt_lim G y (dG y)) as HGd. {
    intro y. unfold G, dG.
    replace (fun t => Rpow (x - t) (S n) / Rfact (S n)) with
      (comp (fun t => Rpow t (S n) / Rfact (S n)) (fun t => x - t)).
    2: reflexivity.
    replace (- Rpow (x - y) n / Rfact n) with ((Rpow (x - y) n / Rfact n) *(-1)).
    2: lra.
    apply derivable_pt_lim_comp.
    -- replace (-1) with (0-1) by lra.
       apply derivable_pt_lim_minus.
       now apply derivable_pt_lim_const.
       now apply derivable_pt_lim_id.
    -- now apply derivable_pt_lim_pow_div_fact.
  }
  assert (HdF : forall y, x0 < y < t -> derivable_pt F y).
    intros y _. exact (derivable_pt_of_lim _ _ _ (HFd y)).
  assert (HdG : forall y, x0 < y < t -> derivable_pt G y).
    intros y _. exact (derivable_pt_of_lim _ _ _ (HGd y)).
   assert (HcF : forall y, x0 <= y <= t -> continuity_pt F y). 
     intros y _. apply derivable_continuous_pt. exact (derivable_pt_of_lim _ _ _ (HFd y)).
   assert (HcG : forall y, x0 <= y <= t -> continuity_pt G y). 
     intros y _. apply derivable_continuous_pt. exact (derivable_pt_of_lim _ _ _ (HGd y)).
  pose proof (MVT F G x0 t HdF HdG (proj1 Ht) HcF HcG) as mvt.
  destruct mvt as [c [Hr Hc]].
  exists c, Hr.
  replace (derive_pt F c (HdF c Hr)) with (dF c) in Hc.
  2: symmetry; apply derive_pt_eq; exact (HFd c).
  replace (derive_pt G c (HdG c Hr)) with (dG c) in Hc.
  2: symmetry; apply derive_pt_eq; exact (HGd c).
  assert (dG c <> 0) as HdGc. {
    unfold dG. apply Rlt_not_eq. rewrite -> Rdiv_opp_l.
    apply Ropp_lt_gt_0_contravar.
    apply Rdiv_lt_0_compat.
    apply pow_lt. apply Rlt_Rminus_zero.
      apply (Rlt_le_trans _ t). exact (proj2 Hr). exact (proj2 Ht).
    exact (Rfact_pos n).
  }
  assert (G t - G x0 <> 0)  as HGtx0. {
    unfold G.
    apply Rlt_not_eq. apply Rlt_minus. apply Rdiv_lt_compat_r. 
    now apply Rfact_pos.
    apply Rpow_succ_strict_incr.
    - apply Rle_Rminus_zero. exact (proj2 Ht).
    - lra.
  }
  apply (Rmult_Rdiv _ _ _ _ HdGc HGtx0).
  rewrite -> (Rmult_comm (dF c)).
  exact Hc.
Qed.

Lemma taylor_series_centre : forall f Pdf n x0,
  taylor_series f Pdf n x0 x0 = f O x0.
Proof.
  intros f Pdf n x0.
  induction n.
  - reflexivity.
  - rewrite -> taylor_series_succ, -> IHn.
    now rewrite -> Rminus_diag, Rpow_0_succ, Rmult_0_r, Rdiv_0_l, Rplus_0_r.
Qed.     

Theorem taylor_series_remainder :
  forall fd Pdf n x0 x (Hx0 : x0 < x), exists c, x0 < c < x /\
    fd O x = taylor_series fd Pdf n x0 x + fd (S n) c * (x - x0)^(S n) / Rfact (S n).
Proof.
  unfold smooth_pt_lim.
  intros fd Pdf n x0 x Hx0.
  assert (x0 < x <= x) as Hx. {
    split. assumption. reflexivity. }
  pose proof (taylor_reverse_series_remainder fd Pdf n x0 x x Hx) as Hrev.
  destruct Hrev as [c [Pc Hc]].  
  exists c.
  split. 1: exact Pc.
  unfold taylor_series_reverse in Hc.
  replace (taylor_series fd Pdf n x x) with (fd O x) in Hc.
  replace (Rpow (x-x) (S n)) with (0) in Hc.
  rewrite -> Rdiv_0_l, Rminus_0_l in Hc.
  rewrite -> Rdiv_opp_l in Hc.
  rewrite -> Rdiv_opp_r in Hc.
  rewrite -> Rdiv_opp_r in Hc.
  apply Ropp_eq_reg in Hc.
  rewrite <- Rmult_div_assoc in Hc.
  rewrite <- Rmult_div_assoc in Hc.
  rewrite -> Rdiv_diag in Hc.
  rewrite -> Rmult_1_r in Hc.
  rewrite -> Rdiv_mult_eqv in Hc.
  rewrite -> Rminus_plus_eqv in Hc.
  rewrite -> Rplus_comm in Hc.
  rewrite -> Rmult_div_assoc in Hc.
  apply eq_sym in Hc.
  exact Hc.
  - apply Rdiv_integral_contrapositive.
    apply pow_nonzero. apply Rgt_not_eq. apply Rgt_minus. exact (proj1 Hx).
    apply Rfact_nonzero.
  - apply Rdiv_integral_contrapositive.
    apply pow_nonzero. apply Rgt_not_eq. apply Rgt_minus. exact (proj2 Pc).
    apply Rfact_nonzero.
  - rewrite -> Rminus_diag, pow_i. reflexivity.
    exact (Nat.lt_0_succ n).
  - now rewrite -> taylor_series_centre.
Qed.


End Calculus.
