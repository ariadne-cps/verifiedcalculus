(******************************************************************************
 *  Numbers/Analysis.v
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
Require Import Calculus.


Section Analysis.

Ltac step mid := (apply Rle_trans with mid).


Open Scope R_scope.



(* If w1 and w2 approximate y1 and y2 with errors d1 and d2, *)
(* then w1+w2 approximates y1+y2 with error (add_err d1 d1). *)
Definition add_err (w1 w2 d1 d2 : R) := d1 + d2.

Lemma add_err_correct : forall w1 w2 d1 d2 y1 y2,
  Rdist w1 y1 <= d1 -> Rdist w2 y2 <= d2 ->
    Rdist (w1+w2) (y1+y2) <= add_err w1 w2 d1 d2.
Proof.
  intros w1 w2 d1 d2 y1 y2 H1 H2; unfold add_err.
  step (Rdist w1 y1 + Rdist w2 y2).
  - apply Rdist_plus_compat.
  - apply Rplus_le_compat; [exact H1|exact H2].
Qed.


Definition sub_err (w1 w2 d1 d2 : R) := d1 + d2.

Lemma sub_err_correct : forall w1 w2 d1 d2 y1 y2,
  Rdist w1 y1 <= d1 -> Rdist w2 y2 <= d2 ->
    Rdist (w1-w2) (y1-y2) <= sub_err w1 w2 d1 d2.
Proof.
  intros w1 w2 d1 d2 y1 y2 H1 H2; unfold sub_err.
  step (Rdist w1 y1 + Rdist w2 y2).
  - apply Rdist_minus_compat.
  - apply Rplus_le_compat; [exact H1|exact H2].
Qed.



Definition mul_err w1 w2 d1 d2 :=
  Rabs w1 * d2 + d1 * Rabs w2 + d1 * d2.

Lemma mul_err_correct : forall w1 w2 d1 d2 y1 y2,
  Rdist w1 y1 <= d1 -> Rdist w2 y2 <= d2 ->
    Rdist (w1*w2) (y1*y2) <= mul_err w1 w2 d1 d2.
Proof.
  unfold mul_err, Rdist.
  intros w1 w2 d1 d2 y1 y2 H1 H2.
  replace (w1*w2-y1*y2) with (w1 * (w2-y2) + (w1-y1) * w2 - (w1-y1) * (w2-y2))
    by (ring).
  step ( Rabs (w1*(w2-y2)) + Rabs ((w1-y1)*w2) + (Rabs (-((w1-y1)*(w2-y2)))) ).
  - step ( Rabs (w1*(w2-y2)+(w1-y1)*w2) + Rabs (-((w1-y1)*(w2-y2))) ).
    -- apply Rabs_triang.
    -- apply Rplus_le_compat_r; apply Rabs_triang.
  - apply Rplus_le_compat.
    apply Rplus_le_compat.
    -- rewrite -> Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos|exact H2].
    -- rewrite -> Rabs_mult; apply Rmult_le_compat_r; [apply Rabs_pos|exact H1].
    -- rewrite -> Rabs_Ropp; rewrite -> Rabs_mult.
       apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact H1|exact H2].
Qed.





(* If |y1-w1|<=d1 and |y2-w2|<=d2, then                      *)
(* |y1/y2 - w1/w2| <= |y1*w2-y2*w1|/|y2|/|w2|                *)
(*                 <= |(y1-w1)*w2-(y2-w2)*w1|/|w2|/(|w2|-d2) *)
(*                 <= (d1+d2*|w1|/|w2|)/(|w2|-d2)            *)
Definition div_err w1 w2 d1 d2 :=
(*
  (d1+d2*(Rabs w1 / Rabs w2)) / (Rabs w2 - d2).
*)
  (d1 * Rabs w2 + Rabs w1 * d2) / (Rabs w2 * (Rabs w2 - d2)).

Lemma div_err_correct : forall w1 w2 d1 d2 y1 y2,
  d2 < Rabs w2 -> Rdist w1 y1 <= d1 -> Rdist w2 y2 <= d2 ->
    Rdist (w1/w2) (y1/y2) <= div_err w1 w2 d1 d2.
Proof.
  unfold div_err, Rdist.
  intros w1 w2 d1 d2 y1 y2 Hp H1 H2.
  set (aw1:=Rabs w1); set (aw2:=Rabs w2); set (ay1:=Rabs y1); set (ay2:=Rabs y2).
  assert (-d1 <= w1-y1 <= d1) as Hd1. {
    apply Rabs_ivl. exact H1. }
  assert (-d2 <= w2-y2 <= d2) as Hd2. {
    apply Rabs_ivl. exact H2. }
  assert (0<=d1) as Hd1p. {
    step (Rabs (w1-y1)). apply Rabs_pos. exact H1. }
  assert (0<=d2) as Hd2p. {
    step (Rabs (w2-y2)). apply Rabs_pos. exact H2. }
  assert (aw2-d2 <= ay2) as Hwdy2. {
    apply Rplus_le_reg_r with (d2-ay2).
    replace ((aw2-d2)+(d2-ay2)) with (aw2-ay2) by ring.
    replace (ay2+(d2-ay2)) with (d2) by ring.
    step (Rabs (w2-y2)). apply Rabs_triang_inv. apply H2. }
  assert (0<aw2) as Haw2p. {
    apply Rle_lt_trans with (d2). apply Hd2p. apply Hp. }
  assert (0<aw2-d2) as Hawd2p. {
    apply Rplus_lt_reg_r with (d2). rewrite -> Rplus_0_l. unfold Rminus.
    rewrite -> Rplus_assoc. rewrite -> Rplus_opp_l. rewrite -> Rplus_0_r. exact Hp. }
  assert (0<ay2) as Hay2p. {
    apply Rlt_le_trans with (aw2-d2). exact Hawd2p.
    apply Rplus_le_reg_r with (d2-ay2). replace ((aw2-d2)+(d2-ay2)) with (aw2-ay2) by (ring).
    replace (ay2+(d2-ay2)) with (d2) by (ring).
    step (Rabs (w2-y2)). apply Rabs_triang_inv. apply H2. }
(*
  assert (0<w*y) as Hwyp. { apply Rlt_mult_pos_pos. exact Hwp. exact Hyp. }
*)
  assert (0<aw2*ay2) as Hwy2p. {
    apply Rlt_mult_pos_pos. exact Haw2p. exact Hay2p. }
(*
  assert (w<>0) as Hwnz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hwp. }
  assert (y<>0) as Hynz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hyp. }
  assert (w-d<>0) as Hwdnz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hwdp. }
*)
  assert (aw2<>0) as Haw2nz. { apply Rgt_not_eq. apply Rlt_gt. exact Haw2p. }
  assert (w2<>0) as Hw2nz. {
    unfold aw2 in *. intros Hw2. rewrite -> Hw2 in Haw2nz. rewrite -> Rabs_R0 in Haw2nz. contradiction. }
  assert (y2<>0) as Hy2nz. {
    unfold ay2 in *. intros Hy2. rewrite -> Hy2 in Hay2p. rewrite -> Rabs_R0 in Hay2p. apply Rlt_irrefl in Hay2p. contradiction. }
  assert (aw2-d2<>0) as Hawd2nz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hawd2p. }
  assert (0 <= d1 * aw2 + aw1 * d2) as Hn12p. {
    apply Rplus_le_le_0_compat;
    apply Rle_mult_nonneg_nonneg;
      [ assumption|apply Rabs_pos | apply Rabs_pos|assumption ].
  }
  apply Rmult_le_reg_r with (aw2 * ay2). { exact Hwy2p. }
  replace (Rabs (w1/w2-y1/y2)*(aw2 * ay2)) with (Rabs (w1*(y2-w2)-(y1-w1)*w2)).
  2: {
       unfold aw2, ay2.
       rewrite <- Rabs_mult. rewrite <- Rabs_mult.
       f_equal. field. split. exact Hy2nz. exact Hw2nz.
  }
  rewrite -> Rabs_minus_sym.
  set (n12 := d1 * aw2 + aw1 * d2).
  step (n12).
  - unfold n12, aw2, aw1.
    step (Rabs ((y1-w1)*w2) + Rabs (w1 * (y2-w2))).
    -- rewrite <- (Rabs_Ropp (w1*(y2-w2))).
       apply Rabs_triang.
    -- apply Rplus_le_compat.
       rewrite -> Rabs_mult.
       apply Rmult_le_compat_r.
         apply Rabs_pos.
         rewrite -> Rabs_minus_sym; exact H1.
       rewrite -> Rabs_mult.
       apply Rmult_le_compat_l.
         apply Rabs_pos.
         rewrite -> Rabs_minus_sym; exact H2.
  - replace ( (n12) / (aw2 * (aw2 - d2)) * (aw2 * ay2) )
        with ( (n12) * (ay2 / (aw2 - d2)) ).
    2: { field. split. exact Hawd2nz. exact Haw2nz. }
    stepl (n12*1%R) by (apply Rmult_1_r).
    apply Rmult_le_compat_l. { apply Hn12p. }
    apply Rmult_le_reg_r with (aw2-d2). { exact Hawd2p. }
    rewrite -> Rmult_1_l.
    replace (ay2/(aw2-d2)*(aw2-d2)) with (ay2). 2: { field. exact Hawd2nz. }
    exact Hwdy2.
Qed.



(* If |y-w|<=d, then |1/y - 1/w| <= |y-w|/|y|/|w| <= d/|w|/(|w|-d) *)
Definition rec_err w d :=
  d / ( (Rabs w) * ((Rabs w)-d) ).

Lemma rec_err_correct : forall w d y,
  d < Rabs w -> Rdist w y <= d ->
    Rdist (/w) (/y) <= rec_err w d.
Proof.
  intros w d y Hp.
  pose proof (div_err_correct 1 w 0 d 1 y) as H.
  unfold rec_err; unfold div_err in H.
  unfold Rdiv in *.
  rewrite -> Rabs_R1 in H.
  rewrite -> Rmult_0_l in H.
  rewrite -> Rplus_0_l in H.
  repeat (rewrite -> Rmult_1_l in H).
  apply H.
  exact Hp.
  rewrite -> Rdist_eq.
  apply Rle_refl.
Qed.

Lemma rec_err_correct' : forall w d y,
  d < Rabs w -> Rdist w y <= d ->
    Rdist (/w) (/y) <= rec_err w d.
Proof.
  unfold rec_err, Rdist.
  intros w d y Hp H.
  set (aw:=Rabs w); set (ay:=Rabs y).
  assert (-d <= w-y <= d) as Hd. {
    apply Rabs_ivl. exact H. }
  assert (0<=d) as Hdp. {
    step (Rabs (w-y)). apply Rabs_pos. exact H. }
  assert (aw-d <= ay) as Hwdy. {
    apply Rplus_le_reg_r with (d-ay).
    replace ((aw-d)+(d-ay)) with (aw-ay) by ring.
    replace (ay+(d-ay)) with (d) by ring.
    step (Rabs (w-y)). apply Rabs_triang_inv. apply H. }
  assert (0<aw) as Hwp. {
    apply Rle_lt_trans with (d). apply Hdp. apply Hp. }
  assert (0<aw-d) as Hwdp. {
    apply Rplus_lt_reg_r with (d). rewrite -> Rplus_0_l. unfold Rminus.
    rewrite -> Rplus_assoc. rewrite -> Rplus_opp_l. rewrite -> Rplus_0_r. exact Hp. }
  assert (0<ay) as Hyp. {
    apply Rlt_le_trans with (aw-d). exact Hwdp.
    apply Rplus_le_reg_r with (d-ay). replace ((aw-d)+(d-ay)) with (aw-ay) by (ring).
    replace (ay+(d-ay)) with (d) by (ring).
    step (Rabs (w-y)). apply Rabs_triang_inv. apply H. }
(*
  assert (0<w*y) as Hwyp. { apply Rlt_mult_pos_pos. exact Hwp. exact Hyp. }
*)
  assert (0<aw*ay) as Hwyp. {
    apply Rlt_mult_pos_pos. exact Hwp. exact Hyp. }
(*
  assert (w<>0) as Hwnz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hwp. }
  assert (y<>0) as Hynz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hyp. }
  assert (w-d<>0) as Hwdnz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hwdp. }
*)
  assert (aw<>0) as Hawnz. { apply Rgt_not_eq. apply Rlt_gt. exact Hwp. }
  assert (w<>0) as Hwnz. {
    unfold aw in *. intros Hw. rewrite -> Hw in Hawnz. rewrite -> Rabs_R0 in Hawnz. contradiction. }
  assert (y<>0) as Hynz. {
    unfold ay in *. intros Hy. rewrite -> Hy in Hyp. rewrite -> Rabs_R0 in Hyp. apply Rlt_irrefl in Hyp. contradiction. }
  assert (aw-d<>0) as Hawdnz. {
    apply Rgt_not_eq. apply Rlt_gt. exact Hwdp. }
  apply Rmult_le_reg_r with (aw * ay). { exact Hwyp. }
  replace (Rabs (/w-/y)*(aw * ay)) with (Rabs (y-w)).
  2: {
       unfold aw, ay.
       rewrite <- Rabs_mult. rewrite <- Rabs_mult.
       f_equal. field. split. exact Hynz. exact Hwnz.
  }
  rewrite -> Rabs_minus_sym.
  step d. exact H.
  replace (d / (aw*(aw-d))*(aw*ay)) with (d * (ay/(aw-d))).
  2: { field. split. exact Hawdnz. exact Hawnz. }
  stepl (d*1%R) by (apply Rmult_1_r).
  apply Rmult_le_compat_l. { apply Hdp. }
  apply Rmult_le_reg_r with (aw-d). { exact Hwdp. }
  rewrite -> Rmult_1_l.
  replace (ay/(aw-d)*(aw-d)) with (ay). 2: { field. exact Hawdnz. }
  exact Hwdy.
Qed.


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


Lemma exp_strict_incr :  forall (x y : R), x<y -> exp x < exp y.
Proof.
  exact Rpower.exp_increasing.
Qed.

Lemma exp_incr :  forall (x y : R), x<=y -> exp x <= exp y.
Proof.
  exact (strictly_increasing_implies_increasing exp exp_strict_incr).
Qed.


Lemma exp_hlf_sqr : forall (x : R), exp x = Rsqr (exp (x/2)).
Proof.
  intro x.
  replace (exp x) with (exp (x/2 + x/2)). 2: f_equal; lra.
  rewrite -> exp_plus.
  now rewrite <- Rsqr_def.
Qed.

Lemma exp_ge : forall (x : R), 1+x <= exp(x).
Proof.
  exact exp_ineq1_le.
Qed.

Lemma exp_le : forall (x : R), x<1 -> exp(x) <= / (1-x).
Proof.
  intros x Hxlt1.
  unfold Rminus.
  assert (1 + (-x) <= exp (-x)) as Hnegx. { exact (exp_ineq1_le (-x)). }
  rewrite -> exp_Ropp in Hnegx.
  assert (0 < 1+-x) as H1minusx. { apply Rlt_Rminus_zero. exact Hxlt1. }
  assert (0 < exp x) as Hexpxpos. { exact (exp_pos x). }
  apply Rinv_le_contravar in Hnegx.
  rewrite -> Rinv_inv in Hnegx.
  - exact Hnegx.
  - exact H1minusx.
Qed.


(* If |y-w|<=d, then |e^y - e^w| <= e^w|e^(y-w)-1| <= e^w(e^d-1) *)
Definition exp_err w d :=
  ((exp d) - 1) * (exp w).

Lemma exp_err_correct : forall w d y,
  Rdist w y <= d ->
    Rdist (exp w) (exp y) <= exp_err w d.
Proof.
  intros w d y H.
  rewrite -> Rdist_sym in H.
  unfold Rdist in H.
  apply Rabs_ivl in H.
  unfold exp_err.
  assert ((y-w)+w=y) as Hy; [apply Rminus_plus_cancel|].
  rewrite <- Hy.
  rewrite -> exp_plus.
  assert (forall x y, Rdist y (x*y) = Rdist (1*y) (x*y)) as H1. {
    intros; rewrite -> Rmult_1_l; reflexivity. }
  rewrite -> H1.
  rewrite <- Rdist_mult_r; [|apply Rlt_le; apply exp_pos].
  apply Rmult_le_compat_r; [apply Rlt_le; apply exp_pos|].
  unfold Rdist.
  apply Rabs_le.
  split.
  - rewrite -> Ropp_minus_distr.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    apply exp_incr.
    apply H.
  - apply Rle_trans with (r2 := 1-exp (-d)).
    -- apply Ropp_le_cancel.
       rewrite -> Ropp_minus_distr.
       rewrite -> Ropp_minus_distr.
       apply Rplus_le_compat_r.
       apply exp_incr.
       apply H.
    -- rewrite -> exp_Ropp.
       set (x := exp d).
       assert (0<x) as Hx; [apply exp_pos|].
       apply Rmult_le_reg_r with (r:=x); [exact Hx|].
       rewrite -> Rmult_minus_distr_r, Rmult_1_l.
       rewrite <- Rinv_l_sym; [|apply Rgt_not_eq; exact Hx].
       apply Rle_zero_Rminus.
       set (z:=x-1); replace x with (z+1); [|exact (Rminus_plus_cancel x 1)].
       rewrite -> Rmult_plus_distr_l, Rmult_1_r.
       rewrite -> Rplus_minus_cancel.
       now apply Rmult_mult_nonneg.
Qed.



Lemma exp_le_deg_0 : forall (x b c : R), x <= b -> exp b <= c -> exp x <= c.
Proof.
  intros x b c Hx Hc.
  transitivity (exp b).
  now apply exp_incr.
  exact Hc.
Qed.

Lemma exp_le_deg_1 : forall (x b c : R), 0 <= x <= b -> exp b <= c -> exp x <= 1+c*x.
Proof.
  intros x b c Hx Hc.
  set (f := plus_fct (fun x => 1) (mult_real_fct c id)).
  set (df := fun x : R => c).
  apply (integral_comparison_lim exp f exp df 0 x).
  - apply Hx.
  - intros y _. now apply derivable_pt_lim_exp.
  - intros y _. unfold df. replace (c) with (0 + c * 1) by lra. unfold f. apply derivable_pt_lim_plus.
    -- now apply derivable_pt_lim_const.
    -- apply derivable_pt_lim_scal.
       now apply derivable_pt_lim_id.
  - rewrite -> exp_0. unfold f, plus_fct, mult_real_fct, id. simpl. lra.
  - intros y Hy. apply (exp_le_deg_0 y b). transitivity x. now apply Hy. now apply Hx.
    unfold df; simpl. exact Hc.
Qed.


Lemma smooth_pt_lim_exp : forall x, smooth_pt_lim (fun n y => exp y) x.
Proof.
  unfold smooth_pt_lim. intros x _. exact (derivable_pt_lim_exp x).
Qed.


Fixpoint taylor_exp n x :=
  match n with | 0 => 1 | S m => taylor_exp m x + x^(S m) / Rfact (S m) end.

Lemma taylor_exp_zero : forall x, taylor_exp O x = 1.
Proof. intros x; reflexivity. Qed.

Lemma taylor_exp_succ : forall n x, taylor_exp (S n) x = taylor_exp n x + x^(S n) / Rfact (S n).
Proof. intros n x; reflexivity. Qed.

Lemma taylor_exp_0 : forall n, taylor_exp n 0 = 1.
Proof. induction n. reflexivity. rewrite -> taylor_exp_succ, IHn, pow_i. lra. now apply Nat.lt_0_succ. Qed.



Lemma derivable_pt_lim_taylor_exp : forall n x,
  derivable_pt_lim (taylor_exp (S n)) x (taylor_exp n x).
Proof.
  induction n.
  - intro x.
    unfold taylor_exp.
    apply (derivable_pt_lim_ext (fun x => 1 + 1 * x)).
    intro z. unfold Rfact. replace (Factorial.fact 1) with 1%nat by reflexivity.
    replace (INR 1) with 1 by reflexivity.
    lra.
    now apply derivable_pt_lim_affine.
  - intro x.
    rewrite -> (taylor_exp_succ n).
    apply (derivable_pt_lim_ext (fun x => taylor_exp (S n) x + x^(S (S n)) / Rfact (S (S n)))).
    -- intro z. rewrite -> (taylor_exp_succ (S n)). reflexivity.
    -- apply derivable_pt_lim_plus. now apply IHn.
       apply (derivable_pt_lim_ext (fun x => x^(S (S n)) / (INR (S (S n))) / (Rfact (S n)))).
       intro z; rewrite -> (Rfact_succ (S n)).
       now rewrite -> Rdiv_mult_distr.
       apply derivable_pt_lim_div_scal.
       replace (x^(S n)) with ((INR (S (S n))) * x^(S n) / (INR (S (S n)))).
       apply derivable_pt_lim_div_scal.
       now apply derivable_pt_lim_pow.
       rewrite -> Rmult_div_r. reflexivity. now apply not_O_S_INR.
Qed.

Lemma exp_ge_taylor_pos : forall n, forall (x : R), 0 <= x -> taylor_exp n x <= exp x.
Proof.
  induction n.
  - intros x Hx.
    unfold taylor_exp. rewrite <- exp_0. apply exp_incr. exact Hx.
  - intros x Hx.
    apply (integral_comparison_lim (taylor_exp (S n)) exp (taylor_exp n) exp 0 x Hx).
    -- intros y _. now apply derivable_pt_lim_taylor_exp.
    -- intros y _; now apply derivable_pt_lim_exp.
    -- now rewrite -> taylor_exp_0, exp_0.
    -- intros y Hy. apply IHn. now apply Hy.
Qed.


Lemma exp_le_taylor_up_pos : forall (n : nat) (x b c : R), 0 <= x <= b -> exp b <= c ->
  exp x <= taylor_exp n x + c * x^(S n) / Rfact (S n).
Proof.
  induction n.
  - intros x b c Hx Hc.
    rewrite -> taylor_exp_zero. rewrite -> pow_1. rewrite -> Rfact_1. rewrite -> Rdiv_1_r.
    apply ( integral_comparison_lim exp (fun x => 1+c*x) exp (fun _ => c) 0 x (proj1 Hx)).
    -- intros y _; now apply derivable_pt_lim_exp.
    -- intros y _; now apply derivable_pt_lim_affine.
    -- rewrite -> exp_0; lra.
    -- intros y Hy. transitivity (exp b).
       apply exp_incr; transitivity x; [now apply Hy|now apply Hx]. exact Hc.
  - intros x b c Hx Hc.
    set ( f := fun x => taylor_exp (S n) x + c * Rpow x (S (S n)) / Rfact (S (S n)) ).
    set ( df := fun x => taylor_exp n x + c * Rpow x (S n) / Rfact (S n) ).
    apply ( integral_comparison_lim exp f exp df 0 x (proj1 Hx)).
    -- intros y _; now apply derivable_pt_lim_exp.
    -- intros y Hy; unfold f, df.
       apply ( derivable_pt_lim_ext (plus_fct (taylor_exp (S n)) (fun x => c * pow x (S (S n)) / Rfact (S (S n)))) ).
       --- intro z. unfold plus_fct. reflexivity.
       --- apply derivable_pt_lim_plus.
           ---- now apply derivable_pt_lim_taylor_exp.
           ---- now apply derivable_pt_lim_cnst_mul_pow_div_fact.
    -- unfold f; rewrite -> taylor_exp_0, -> pow_i, -> Rmult_0_r, -> Rdiv_0_l, Rplus_0_r. 
       2: now apply Nat.lt_0_succ.
       rewrite -> exp_0. now apply Rle_refl.
    -- intros y Hy. apply (IHn y b c).
       --- split. now apply Hy. transitivity x; [now apply Hy|now apply Hx].
       --- exact Hc.
Qed.




Local Lemma exp_le_ge_taylor_even_odd_neg : forall n,
  (forall x, x <= 0 -> exp x <= taylor_exp (2*n) x) /\
    (forall x, x <= 0 -> taylor_exp (2*n+1) x <= exp x).
Proof.
  induction n.
  - assert (forall x, x <= 0 -> exp x <= taylor_exp 0 x) as H0. {
      intros x Hx. rewrite -> taylor_exp_zero. rewrite <- exp_0. apply exp_incr. exact Hx. }
    split. now apply H0.
    intros x Hx.
    replace (2*0+1)%nat with (1%nat) by reflexivity.
    apply (integral_comparison_lim_neg (taylor_exp 1) (exp) (taylor_exp 0) (exp)).
    -- intros y _. now apply derivable_pt_lim_taylor_exp.
    -- intros y _. now apply derivable_pt_lim_exp.
    -- rewrite -> taylor_exp_0. rewrite -> exp_0. now apply Rle_refl.
    -- exact H0.
    -- exact Hx.
  - assert (forall x, x <= 0 -> exp x <= taylor_exp (2*(S n)) x) as He. {
      intros x Hx.
      replace ((2 * (S n))%nat) with (S (2*n+1)).
        2: rewrite -> Nat.mul_succ_r; symmetry; now apply Nat.add_succ_r.
      apply (integral_comparison_lim_neg (exp) (taylor_exp (S (2*n+1))) (exp) (taylor_exp (2 * n + 1)) ).
      -- intros y _. now apply derivable_pt_lim_exp.
      -- intros y _. now apply derivable_pt_lim_taylor_exp.
      -- rewrite -> taylor_exp_0. rewrite -> exp_0. now apply Rle_refl.
      -- now apply IHn.
      -- exact Hx.
    }
    split. now apply He.
    intros x Hx.
    replace (2*(S n)+1)%nat with (S (2 * (S n))) by now rewrite -> Nat.add_1_r.
    apply (integral_comparison_lim_neg (taylor_exp (S (2*(S n)))) (exp) (taylor_exp (2*(S n))) (exp)).
    -- intros y _. now apply derivable_pt_lim_taylor_exp.
    -- intros y _. now apply derivable_pt_lim_exp.
    -- rewrite -> taylor_exp_0. rewrite -> exp_0. now apply Rle_refl.
    -- exact He.
    -- exact Hx.
Qed.

Theorem exp_le_taylor_even_neg : forall n x, x <= 0 -> exp x <= taylor_exp (2*n) x.
Proof. now apply exp_le_ge_taylor_even_odd_neg. Qed.

Theorem exp_ge_taylor_odd_neg : forall n x, x <= 0 -> taylor_exp (2*n+1) x <= exp x.
Proof. now apply exp_le_ge_taylor_even_odd_neg. Qed.

Theorem exp_ge_taylor_odd : forall n x, taylor_exp (2*n+1) x <= exp x.
  intros n x. destruct (Rle_or_le 0 x).
   - now apply exp_ge_taylor_pos.
   - now apply exp_ge_taylor_odd_neg.
Qed.

Theorem exp_le_taylor_even_up : forall n x b c, x <= b -> exp b <= c -> 1 <= c ->
  exp x <= taylor_exp (2*n+1) x + c * x^(2*(S n)) / Rfact (2*(S n)).
Proof.
  intros n x b c Hxb Hc H1c.
  replace (2*(S n))%nat with (S (2*n+1)). 2: now rewrite -> Nat.mul_succ_r.
  destruct (Rle_or_le 0 x) as [Hxge0|Hxlex].
   - assert (0 <= x <= b) as Hx. split; [assumption|assumption].
     exact (exp_le_taylor_up_pos (2*n+1) x b c Hx Hc).
   - transitivity (taylor_exp (2 * (S n)) x).
     -- now apply exp_le_taylor_even_neg.
     -- replace (2*(S n))%nat with (S (2*n+1)). 2: now rewrite -> Nat.mul_succ_r.
        rewrite -> taylor_exp_succ. apply Rplus_le_compat_l.
        replace (S (2*n+1)) with  (2*(S n))%nat. 2: now rewrite -> Nat.mul_succ_r.
        apply Rdiv_le_compat_r.
        unfold Rfact. now apply INR_fact_lt_0.
        assert (0 <= Rpow x (2*(S n))) as Hf. {
          rewrite -> pow_Rsqr. apply pow_le. now apply Rle_0_sqr. }
        pose proof (Rmult_le_compat_r (Rpow x (2 * S n)) 1 c Hf H1c) as H.
        rewrite -> Rmult_1_l in H.
        exact H.
Qed.

End Analysis.
