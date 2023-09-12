(******************************************************************************
 * Copyright 2023 Pieter Collins
 *
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
 ******************************************************************************)


Require Import Reals.
Require Import Lra.

Require Import R_addenda.



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


End Analysis.
