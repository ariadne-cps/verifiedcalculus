(******************************************************************************
 *  Numbers/FixedDyadic.v
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
From Stdlib Require Import Reals.Rbase.
From Stdlib Require Import Reals.Rfunctions.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rdefinitions.

Require Import RealAddenda.

Require Import Floats(Rounding,up,near,down,Rapply).

(*
Require FixedDyadic.
Require Export Floats.
*)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.Zorder.
From Stdlib Require Import ZArith.Zbool.
From Stdlib Require Import ZArith.ZArith_dec.

Open Scope Z_scope.

Definition Zdist a b := Z.abs (Z.sub a b).

Lemma dist_IZR : forall a b, Rdist (IZR a) (IZR b) = IZR (Zdist a b).
Proof. intros; unfold Zdist, Rdist; rewrite -> abs_IZR, minus_IZR; reflexivity. Qed.


Definition Zpow2 (n : nat) := Z.pow 2 (Z.of_nat n).

Lemma Zpow2n_gt_0 : forall (n : nat), (0 < Zpow2 n).
Proof. intro n; apply Z.pow_pos_nonneg; [exact Z.lt_0_2|exact (Zle_0_nat n)]. Qed.
Lemma Zpow2n_neq_0 : forall (n : nat), (Zpow2 n <> 0).
Proof. intro n; apply not_eq_sym; apply Z.lt_neq. apply Zpow2n_gt_0. Qed.
Lemma pow2n_gt_0 : forall (n : nat), (0 < IZR (Zpow2 n))%R.
Proof. intros n; apply IZR_lt; exact (Zpow2n_gt_0 n). Qed.
Lemma pow2n_ge_0 : forall (n : nat), (0 <= IZR (Zpow2 n))%R.
Proof. intros n; apply Rlt_le; exact (pow2n_gt_0 n). Qed.
Lemma pow2n_neq_0 : forall (n : nat), (IZR (Zpow2 n) <> 0%R).
Proof. intros n; apply Rgt_not_eq; apply Rlt_gt; exact (pow2n_gt_0 n). Qed.


Lemma max_IZR: forall a b, IZR (Z.max a b) = Rmax (IZR a) (IZR b).
Proof.
  intros a b.
  assert (a<=b \/ b<=a) as Hz; [apply Z.le_ge_cases|].
  destruct Hz.
  - assert ((IZR a <= IZR b)%R) as Hr; [apply IZR_le; exact H|].
    rewrite -> Z.max_r by (exact H).
    rewrite -> Rmax_right by (exact Hr).
    reflexivity.
  - assert ((IZR b <= IZR a)%R) as Hr; [apply IZR_le; exact H|].
    rewrite -> Z.max_l by (exact H).
    rewrite -> Rmax_left by (exact Hr).
    reflexivity.
Qed.

Lemma min_IZR: forall a b, IZR (Z.min a b) = Rmin (IZR a) (IZR b).
Proof.
  intros a b.
  assert (a<=b \/ b<=a) as Hz; [apply Z.le_ge_cases|].
  destruct Hz.
  - assert ((IZR a <= IZR b)%R) as Hr; [apply IZR_le; exact H|].
    rewrite -> Z.min_l by (exact H).
    rewrite -> Rmin_left by (exact Hr).
    reflexivity.
  - assert ((IZR b <= IZR a)%R) as Hr; [apply IZR_le; exact H|].
    rewrite -> Z.min_r by (exact H).
    rewrite -> Rmin_right by (exact Hr).
    reflexivity.
Qed.

Lemma div_IZR_pos : forall (z1 z2 : Z),
  0<z2 -> Rle (IZR (Z.div z1 z2)) (Rdiv (IZR z1) (IZR z2)).
Proof.
  intros z1 z2 Hz2p.
  assert ((0 < IZR z2)%R) as Hr2p; [apply IZR_lt; exact Hz2p|];
  assert ((IZR z2 <> 0)%R) as Hr2neq; [apply Rlt_not_eq'; exact Hr2p|].
  apply Rmult_le_reg_l with (IZR z2); [exact Hr2p|].
  stepr (IZR z1).
  - rewrite <- mult_IZR.
    apply IZR_le.
    apply Z.mul_div_le; [exact Hz2p].
  - unfold Rdiv; rewrite <- Rmult_assoc.
    symmetry; apply Rinv_r_simpl_m; [exact Hr2neq].
Qed.

Lemma div_IZR_neg : forall (z1 z2 : Z),
  (z2<0) -> Rle (IZR (Z.div z1 z2)) (Rdiv (IZR z1) (IZR z2)).
Proof.
  intros z1 z2 Hz2lt0.
  assert (0 < -z2) as H0ltnz2; [apply Z.opp_pos_neg; exact Hz2lt0|].
  assert (z2 <> 0) as Hz2neq0; [apply Z.lt_neq; exact Hz2lt0|].
  assert (IZR z2 <> 0%R) as Hr2neq0; [intro Heq; apply eq_IZR in Heq; contradiction|].
  rewrite <- Z.div_opp_opp; [|exact Hz2neq0].
  stepr (Rdiv (Ropp (IZR z1)) (Ropp (IZR z2))).
  - repeat (rewrite <- opp_IZR).
    apply div_IZR_pos; [exact H0ltnz2].
  - field; [exact Hr2neq0].
Qed.

Lemma div_IZR : forall (z1 z2 : Z),
  (z2<>0) -> Rle (IZR (Z.div z1 z2)) (Rdiv (IZR z1) (IZR z2)).
Proof.
  intros z1 z2 Hz2neq0.
  assert ({z2<0}+{z2>0}+{z2=0}) as Hz2; [apply Z_dec|].
  destruct Hz2 as [[Hlt|Hgt]|Heq].
  - apply div_IZR_neg; exact Hlt.
  - apply div_IZR_pos; apply Z.gt_lt; exact Hgt.
  - contradiction.
Qed.


Lemma Zgeb_ge_false : forall a b, ~ (a >= b) -> a>=?b = false.
Proof.
  intros a b H.
  remember (a>=?b) as c.
  destruct c.
  - apply eq_sym in Heqc.
    apply Z.geb_ge in Heqc.
    contradiction.
  - reflexivity.
Qed.


Lemma Zlt_le_sub_1 : forall a b, a<b -> a <= b-1.
Proof. intros a b H. rewrite -> Z.sub_1_r. apply Z.lt_le_pred. exact H. Qed.

Lemma Zle_neq_lt : forall a b : Z, a<=b -> a<>b -> a<b.
Proof.
  intros a b Hle Hneq.
  apply Z.le_lteq in Hle.
  destruct Hle.
  - assumption.
  - contradiction.
Qed.



Definition Zdiv_rnd rnd p q :=
  match rnd with
  | down => p / q
  | near => (2*p+q)/(2*q)
  | up => if (q>=?0) then (p+(q-1))/q else (p+(q+1))/q
  end.


Lemma Zdiv_rnd_down_pos : forall a b, 0 < b -> b * Zdiv_rnd down a b <= a.
Proof. unfold Zdiv_rnd; exact Z.mul_div_le. Qed.

Lemma Zdiv_rnd_down_neg : forall a b, b < 0 -> a <= b * Zdiv_rnd down a b.
Proof.
  intros a b Hblt0.
  assert ((-b) * Zdiv_rnd down (-a) (-b) <= (-a)). {
    apply Zdiv_rnd_down_pos. apply Z.opp_pos_neg. exact Hblt0.
  }
  assert (b<>0) as Hbne0. { apply Z.lt_neq. exact Hblt0. }
  unfold Zdiv_rnd in *.
  rewrite -> Z.div_opp_opp in H; [|exact Hbne0].
  apply Z.opp_le_mono.
  rewrite <- Z.mul_opp_l.
  exact H.
Qed.

Lemma Zdiv_rnd_near : forall a b s,
  (b <> 0) -> Zdist (b * Zdiv_rnd near a b) a <= Zdist (b * s) a.
Proof.
  unfold Zdist.
  intros a b s Hbne0. unfold Zdiv_rnd.
  assert (2*b <> 0) as H0ne2b. {
    intros H2b. apply Z.mul_eq_0 in H2b. destruct H2b.
    discriminate. contradiction.
  }
  assert (Z.abs b <> 0) as H0neab. {
    intros H. apply (Z.abs_0_iff b) in H. contradiction.
  }
  assert (0 < Z.abs b) as H0ltab. {
    apply Zle_neq_lt. apply Z.abs_nonneg. apply not_eq_sym. exact H0neab.
  }
  remember ((2*a+b)/(2*b)) as q.
  assert ( (2*a+b) = (2*b) * q + (2*a+b) mod (2*b) ) as Hmod. {
    rewrite -> Heqq. apply (Z.div_mod (2*a+b) (2*b)). exact H0ne2b. }
  remember ( (2*a+b) mod (2*b) ) as r.
  assert (r= 2*a+b - 2*b*q) as Hreq. { apply Z.add_move_l. apply eq_sym. exact Hmod. }
  assert (2*(b*q-a) = b-r). { rewrite -> Hreq. ring. }
  assert ( Z.abs (b*(q-s)) - Z.abs (b*q-a) <= Z.abs (b*s-a) ) as Htriang. {
    replace (Z.abs (b*s-a)) with (Z.abs (a-b*s)).
    apply Z.le_stepr with (Z.abs (b*(q-s)-(b*q-a))).
    - apply Z.abs_sub_triangle.
    - f_equal. ring.
    - rewrite <- Z.abs_opp. f_equal. ring.
  }
  assert ({q=s}+{q<>s}) as Heq_dec. { apply Z.eq_dec. }
  destruct Heq_dec as [Heq|Hneq].
    rewrite <- Heq. apply Z.le_refl.
  apply Z.le_trans with (Z.abs(b*(q-s))-Z.abs (b*q-a)); [|apply Htriang].
  apply Z.le_add_le_sub_l.
  rewrite -> Z.add_diag.
  rewrite <- (Z.abs_eq 2) by (exact Z.le_0_2).
  rewrite <- Z.abs_mul.
  replace (2*(b*q-a)) with (b-r).
  assert (Z.abs (b-r) <= Z.abs b) as Hab. {
    assert ({b<0}+{b>0}+{b=0}) as Hb. { apply Z_dec. }
    destruct Hb as [[Hlt|Hgt]|Heq].
    - assert (2*b < r <= 0) as Hr. {
        rewrite -> Heqr. apply Z.mod_neg_bound.
        apply Z.mul_pos_neg. exact Z.lt_0_2. exact Hlt.
      }
      apply Z.abs_le.
      rewrite -> Z.abs_neq; [|apply Z.lt_le_incl; exact Hlt].
      rewrite -> Z.opp_involutive.
      split.
      -- apply Z.add_le_mono_l with (r-b).
         replace (r-b+b) with (r) by ring.
         replace (r-b+(b-r)) with (0%Z) by ring.
         apply Hr.
      -- apply Z.add_le_mono_l with (b+r).
         replace ((b+r)+(b-r)) with (2*b) by ring.
         replace (b+r+-b) with (r) by ring.
         apply Z.lt_le_incl.
         apply Hr.
    - assert (0 <= r < 2*b) as Hr. {
        rewrite -> Heqr. apply Z.mod_pos_bound.
        apply Z.mul_pos_pos. exact Z.lt_0_2. apply Z.gt_lt. exact Hgt.
      }
      apply Z.abs_le.
      rewrite -> Z.abs_eq; [|apply Z.lt_le_incl; apply Z.gt_lt; exact Hgt].
      split.
      -- apply Z.add_le_mono_l with (r+b).
         replace (r+b+-b) with (r) by ring.
         replace (r+b+(b-r)) with (2*b) by ring.
         apply Z.lt_le_incl.
         apply Hr.
      -- apply Z.add_le_mono_l with (r-b).
         replace ((r-b)+(b-r)) with (0%Z) by ring.
         replace (r-b+b) with (r) by ring.
         apply Hr.
    - contradiction.
  }
  apply Z.le_trans with (Z.abs b).
  - exact Hab.
  - rewrite -> Z.abs_mul.
    apply Z.le_mul_diag_r; [exact H0ltab|].
    set (d:=q-s).
    assert ({d<0}+{d>0}+{d=0}) as Hd. { apply Z_dec. }
    destruct Hd as [[Hlt|Hgt]|Heq].
    -- assert (d<=0-1). { apply Zlt_le_sub_1. exact Hlt. }
       rewrite -> Z.abs_neq.
       apply Z.add_le_mono_r with (d-1).
       replace (1+(d-1)) with d by ring.
       replace (-d + (d-1)) with (0-1) by ring.
       assumption.
       apply Z.lt_le_incl.
       exact Hlt.
    -- apply Z.gt_lt in Hgt.
       assert (0<=d-1). { apply Zlt_le_sub_1. exact Hgt. }
       rewrite -> Z.abs_eq.
       apply Zle_0_minus_le.
       assumption.
       apply Z.lt_le_incl.
       exact Hgt.
    -- unfold d in Heq.
       apply Zminus_eq in Heq.
       contradiction.
Qed.

Lemma Zdiv_rnd_up_pos_le : forall a b,
  0 < b -> a <= b * Zdiv_rnd up a b.
Proof.
  intros a b H0ltb.
  unfold Zdiv_rnd.
  assert (b<>0) as Hbne0. { apply not_eq_sym. apply Z.lt_neq. exact H0ltb. }
  assert (b>=?0 = true) as Ht. { apply Z.geb_ge. apply Z.le_ge. apply Z.lt_le_incl. exact H0ltb. }
  rewrite -> Ht.
  rewrite -> (Z.add_le_mono_r a _ (b-1)).
  replace (a+(b-1)) with (a+b-1) by ring.
  apply Z.le_trans with (b * ((a+b-1)/b) + (a+b-1) mod b).
  - rewrite <- (Z.div_mod _ b Hbne0).
    apply Z.le_refl.
  - apply Z.add_le_mono_l.
    apply Zlt_le_sub_1.
    apply Z.mod_pos_bound.
    exact H0ltb.
Qed.

Lemma Zdiv_rnd_up_pos : forall a b,
  0 < b -> b * Zdiv_rnd up a b >= a.
Proof.
  intros a b Hb. apply Z.le_ge. apply Zdiv_rnd_up_pos_le. exact Hb.
Qed.

Lemma Zdiv_rnd_up_neg : forall a b,
  b < 0 -> b * Zdiv_rnd up a b <= a.
Proof.
  intros a b Hblt0.
  assert (-a <= (-b) * Zdiv_rnd up (-a) (-b)). {
    apply Zdiv_rnd_up_pos_le. apply Z.opp_pos_neg. exact Hblt0. }
  assert (b<>0) as Hbne0. { apply Z.lt_neq. exact Hblt0. }
  unfold Zdiv_rnd in *.
  replace (-b>=?0) with true in H. 2: {
    apply eq_sym. apply Z.geb_ge. apply Z.le_ge.
    apply Z.opp_nonneg_nonpos. apply Z.lt_le_incl. exact Hblt0.
  }
  replace (b>=?0) with false. 2: {
    apply eq_sym. apply Zgeb_ge_false.
    intros Hb. apply Z.ge_le in Hb.
    apply Z.lt_gt in Hblt0. apply Zgt_not_le in Hblt0.
    contradiction.
  }
  replace (-a + (-b-1)) with (-(a+(b+1))) in H by ring.
  rewrite -> Z.div_opp_opp in H; [|exact Hbne0].
  apply Z.opp_le_mono.
  rewrite <- Z.mul_opp_l.
  exact H.
Qed.


Close Scope Z_scope.




Open Scope Z_scope.

Module W.

Inductive FixedDyadic (n : nat) : Type
  := make (p:Z).


Definition mantissa {n : nat} (x : FixedDyadic n) : Z :=
  match x with (make _ p) => p end.
Definition exponent {n : nat} (x : FixedDyadic n) : nat :=
  n.

Definition of_nat (n : nat) :=
  fun k => make n ((Z.of_nat k) * Z.pow 2 (Z.of_nat n)).

Definition injR {n : nat} (x : FixedDyadic n) : R :=
  IZR (mantissa x) / IZR (Zpow2 n).


Definition neg {n : nat} (x : FixedDyadic n) : (FixedDyadic n) :=
  make n (- mantissa x).

Definition abs {n : nat} (x : FixedDyadic n) : (FixedDyadic n) :=
  make n ( Z.abs (mantissa x) ).

Definition max {n : nat} (x1 : FixedDyadic n) (x2 : FixedDyadic n) : (FixedDyadic n) :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
    make n (Z.max (mantissa x1) (mantissa x2)).

Definition min {n : nat} (x1 : FixedDyadic n) (x2 : FixedDyadic n) : (FixedDyadic n) :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
    make n (Z.min (mantissa x1) (mantissa x2)).

Definition add {n : nat} (_ : Rounding) (x1 : FixedDyadic n) (x2 : FixedDyadic n) : (FixedDyadic n) :=
  make n (mantissa x1 + mantissa x2).

Definition sub {n : nat} (_ : Rounding) (x1 : FixedDyadic n) (x2 : FixedDyadic n) : (FixedDyadic n) :=
  make n (mantissa x1 - mantissa x2).

Definition mul {n : nat}
  (rnd : Rounding) (x1 : FixedDyadic n) (x2 : FixedDyadic n) : (FixedDyadic n) :=
    let p1 := mantissa x1 in
      let p2 := mantissa x2 in
        let m:=Zpow2 n in
          make n (Zdiv_rnd rnd (p1*p2) m).

Definition div {n : nat}
  (rnd : Rounding) (x1 : FixedDyadic n) (x2 : FixedDyadic n) : (FixedDyadic n) :=
    let p1 := mantissa x1 in
      let p2 := mantissa x2 in
        let m:=Zpow2 n in
          make n (Zdiv_rnd rnd (m*p1) p2).

Definition rec {n : nat}
  (rnd : Rounding) (x : FixedDyadic n) : (FixedDyadic n) :=
    let p := mantissa x in
      let m:=Zpow2 n in
        make n (Zdiv_rnd rnd (m*m) p).

Definition ltb {n1 n2 : nat} (x1 : FixedDyadic n1) (x2 : FixedDyadic n2) : bool :=
  let p1 := mantissa x1 in
    let p2 := mantissa x2 in
      let m1:=Zpow2 n1 in
        let m2:=Zpow2 n2 in
          (p1 * m2) <? (p2 * m1).

Definition leb {n1 n2 : nat} (x1 : FixedDyadic n1) (x2 : FixedDyadic n2) : bool :=
  let p1 := mantissa x1 in
    let p2 := mantissa x2 in
      let m1:=Zpow2 n1 in
        let m2:=Zpow2 n2 in
          (p1 * m2) <=? (p2 * m1).

Definition lt {n1 n2 : nat} (x1 : FixedDyadic n1) (x2 : FixedDyadic n2) : Prop :=
  ltb x1 x2 = true.

Definition toQ {n : nat} (x : FixedDyadic n) : Q :=
  Qdiv (inject_Z (mantissa x)) (inject_Z (Zpow2 n)).

Close Scope Z_scope.



Open Scope R_scope.

(*
Definition is_rounded (X : Type) (x : R) (r : R) : Prop :=
  match rnd with
  | down => x <= r
  | near => forall (s : X), Rdist x r <= Rdist s r
  | up   => x >= r
  end.
*)

Definition is_rounded {n : nat} (rnd : Rounding) (x : FixedDyadic n) (r : R) : Prop :=
  match rnd with
  | down => injR x <= r
  | near => forall (s : FixedDyadic n), Rdist (injR x) r <= Rdist (injR s) r
  | up   => injR x >= r
  end.

Lemma injR_correct : forall n (k : nat),
  injR (of_nat n k) = INR k.
Proof.
  intros n k.
  unfold injR, of_nat, mantissa, Zpow2.
  rewrite -> mult_IZR.
  rewrite -> INR_IZR_INZ.
  field.
  exact (pow2n_neq_0 n).
Qed.

Lemma leb_correct : forall n (w1 w2 : FixedDyadic n),
  leb w1 w2 = true <-> Rle (injR w1) (injR w2).
Proof.
  intros n w1 w2.
  unfold leb.
  destruct w1 as [p1]; destruct w2 as [p2].
  simpl.
  split.
  -- intros Hb.
     apply Rmult_Rdiv_pos_Rle; [apply pow2n_gt_0|apply pow2n_gt_0|].
     rewrite <- mult_IZR; rewrite <- mult_IZR.
     apply IZR_le.
     apply Zle_bool_imp_le.
     exact Hb.
  -- intros H.
     apply Zle_imp_le_bool.
     apply le_IZR.
     rewrite -> mult_IZR; rewrite -> mult_IZR.
     apply Rdiv_Rmult_pos_pos_Rle; [apply pow2n_gt_0|apply pow2n_gt_0|].
     exact H.
Qed.

Lemma neg_exact : forall n (w : FixedDyadic n), injR (neg w) = Ropp (injR w).
Proof.
  intros n w; unfold neg, injR; simpl.
  rewrite -> opp_IZR.
  field.
  apply pow2n_neq_0.
Qed.

Lemma abs_exact : forall n (w : FixedDyadic n), injR (abs w) = Rabs (injR w).
Proof.
  intros n w; unfold abs, injR; simpl.
  rewrite -> abs_IZR.
  unfold Rdiv.
  rewrite -> Rabs_mult.
  rewrite -> Rabs_inv.
  replace (Rabs (IZR (Zpow2 n))) with (IZR (Zpow2 n)).
  reflexivity.
  rewrite -> Rabs_pos_eq.
  reflexivity.
  apply Rlt_le.
  apply pow2n_gt_0.
Qed.

Lemma max_exact : forall n (w1 w2 : FixedDyadic n), injR (max w1 w2) = Rmax (injR w1) (injR w2).
Proof.
  intros n w1 w2.
  unfold max, injR.
  set (p1 := mantissa w1); set (p2 := mantissa w2); set (m:=Zpow2 n).
  simpl.
  rewrite -> max_IZR.
  unfold Rdiv; rewrite -> Rmult_comm.
  rewrite <- RmaxRmult by (apply Rlt_le; apply Rinv_pos; apply pow2n_gt_0).
  f_equal; apply Rmult_comm.
Qed.

Lemma RminRmult : forall p q r : R,
  (0 <= r) -> Rmin (r * p) (r * q) = (r * Rmin p q).
Proof.
  intros p q r Hr.
  rewrite <- (Ropp_involutive (Rmin p q)).
  rewrite -> Ropp_Rmin.
  rewrite <- Ropp_mult_distr_r.
  rewrite <- RmaxRmult by (apply Hr).
  rewrite -> Ropp_Rmax.
  rewrite <- Ropp_mult_distr_r, <- Ropp_mult_distr_r.
  rewrite -> Ropp_involutive, -> Ropp_involutive.
  reflexivity.
Qed.

Lemma min_exact : forall n (w1 w2 : FixedDyadic n), injR (min w1 w2) = Rmin (injR w1) (injR w2).
Proof.
  intros n w1 w2.
  unfold min, injR.
  set (p1 := mantissa w1); set (p2 := mantissa w2); set (m:=Zpow2 n).
  simpl.
  rewrite -> min_IZR.
  unfold Rdiv; rewrite -> Rmult_comm.
  rewrite <- RminRmult by (apply Rlt_le; apply Rinv_pos; apply pow2n_gt_0).
  f_equal; apply Rmult_comm.
Qed.

Lemma add_exact : forall n rnd (w1 w2 : FixedDyadic n),
  injR (add rnd w1 w2) = Rplus (injR w1) (injR w2).
Proof.
  intros n rnd w1 w2.
  unfold injR, add; simpl.
  rewrite -> plus_IZR.
  field; apply pow2n_neq_0.
Qed.

Lemma sub_exact : forall n rnd (w1 w2 : FixedDyadic n),
  injR (sub rnd w1 w2) = Rminus (injR w1) (injR w2).
Proof.
  intros n rnd w1 w2.
  unfold injR, sub; simpl.
  rewrite -> minus_IZR.
  field; apply pow2n_neq_0.
Qed.

Lemma mul_down : forall n (w1 w2 : FixedDyadic n),
  injR (mul down w1 w2) <= Rmult (injR w1) (injR w2).
Proof.
  intros n x y.
  unfold mul, injR; simpl.
  set (px := mantissa x); set (py := mantissa y); set (m:=Zpow2 n).
  apply Rmult_le_reg_l with (IZR m); [apply pow2n_gt_0|].
  apply Rmult_le_reg_r with (IZR m); [apply pow2n_gt_0|].
  stepl (Rmult (IZR m) (IZR (px*py / m)%Z)); [|field; apply pow2n_neq_0].
  stepr ((IZR px) * (IZR py)); [|field; apply pow2n_neq_0].
  rewrite <- mult_IZR; rewrite <- mult_IZR.
  apply IZR_le.
  apply Zdiv_rnd_down_pos.
  apply Zpow2n_gt_0.
Qed.

Lemma mul_near : forall n (w1 w2 wr : FixedDyadic n),
  Rdist (injR (mul near w1 w2)) (Rmult (injR w1) (injR w2))
    <= Rdist (injR wr) (Rmult (injR w1) (injR w2)).
Proof.
  intros n x y z.
  unfold mul, injR.
  set (px := mantissa x); set (py := mantissa y); set (pz := mantissa z).
  set (m:=Zpow2 n).
  unfold Rapply.
  unfold mantissa.

  apply Rmult_le_reg_l with (IZR m); [apply pow2n_gt_0|].
  apply Rmult_le_reg_r with (IZR m); [apply pow2n_gt_0|].
  stepl (Rdist (IZR m * IZR (Zdiv_rnd near (px*py) m)) (IZR px * IZR py)).
  stepr (Rdist (IZR (m*pz)) (IZR px * IZR py)).
  - rewrite <- mult_IZR; rewrite <- mult_IZR.
    rewrite -> dist_IZR; rewrite -> dist_IZR.
    apply IZR_le.
    apply Zdiv_rnd_near; [apply Zpow2n_neq_0].
  - rewrite -> Rdist_mult_l; [|apply pow2n_ge_0].
    rewrite -> Rdist_mult_r; [|apply pow2n_ge_0].
    f_equal.
    rewrite -> mult_IZR.
    field; apply pow2n_neq_0.
    field; apply pow2n_neq_0.
  - rewrite -> Rdist_mult_l; [|apply pow2n_ge_0].
    rewrite -> Rdist_mult_r; [|apply pow2n_ge_0].
    f_equal.
    field; apply pow2n_neq_0.
    field; apply pow2n_neq_0.
Qed.

Lemma mul_up : forall n (w1 w2 : FixedDyadic n),
  injR (mul up w1 w2) >= Rmult (injR w1) (injR w2).
Proof.
  intros n x y.
  set (z:=mul up x y).
  unfold mul, injR, Rapply.
  apply Rle_ge.
  set (px := mantissa x); set (py := mantissa y);
  set (pz := mantissa z); set (m:=Zpow2 n).
  apply Rmult_le_reg_l with (IZR m); [apply pow2n_gt_0|].
  apply Rmult_le_reg_r with (IZR m); [apply pow2n_gt_0|].
  stepr ((IZR m) * (IZR pz)); [|field; apply pow2n_neq_0].
  stepl ((IZR px) * (IZR py)); [|field; apply pow2n_neq_0].
  rewrite <- mult_IZR; rewrite <- mult_IZR.
  apply IZR_le.
  apply Zdiv_rnd_up_pos_le.
  apply Zpow2n_gt_0.
Qed.


Lemma neq_0_Zmantissa : forall n (w : FixedDyadic n),
  injR w <> 0 -> ((mantissa w) <> 0)%Z.
Proof.
  intros n w Hw.
  unfold injR in Hw.
  remember (mantissa w) as p.
  intros Hp.
  rewrite -> Hp in Hw.
  unfold Rdiv in Hw.
  rewrite -> Rmult_0_l in Hw.
  contradiction.
Qed.

Lemma neq_0_Rmantissa : forall n (w : FixedDyadic n),
  injR w <> 0 -> (IZR (mantissa w) <> 0).
Proof.
  intros n w Hw.
  intro Hp. apply eq_IZR_R0 in Hp; revert Hp.
  apply (neq_0_Zmantissa n w Hw).
Qed.


Definition is_rounded_mul {n : nat} (rnd : Rounding) (x : FixedDyadic n) (r : R) (c : R) : Prop :=
  match rnd with
  | down => c * injR x <= c * r
  | near => forall (s : FixedDyadic n), Rdist (c*(injR x)) (c*r) <= Rdist (c*(injR s)) (c*r)
  | up   => c * injR x >= c * r
  end.

Lemma is_rounded_mul_correct : forall {n} rnd (w : FixedDyadic n) r c,
    0<c -> (is_rounded_mul rnd w r c) -> is_rounded rnd w r.
Proof.
  intros n rnd w r c Hc H.
  unfold is_rounded_mul, is_rounded in *.
  destruct rnd.
  - apply Rmult_le_reg_l in H; [exact H | exact Hc].
  - intros s. specialize (H s).
    rewrite <- Rdist_mult_l in H; [|apply Rlt_le; exact Hc].
    rewrite <- Rdist_mult_l in H; [|apply Rlt_le; exact Hc].
    apply Rmult_le_reg_l in H; [|exact Hc].
    exact H.
  - apply Rge_le in H; apply Rmult_le_reg_l in H; apply Rle_ge in H; [exact H | exact Hc].
Qed.


Lemma div_correct : forall n rnd (w1 w2 : FixedDyadic n),
  (injR w2<>0) -> is_rounded rnd (div rnd w1 w2) (Rdiv (injR w1) (injR w2)).
Proof.
  intros n rnd w1 w2 Hw2.
  unfold injR.
(*
  set (p1 := mantissa w1); set (p2 := mantissa w2); set (m:=Zpow2 n).
*)
  remember (mantissa w1) as p1; remember (mantissa w2) as p2; remember (Zpow2 n) as m.
  assert ((0<m)%Z) as Hm; [rewrite -> Heqm; apply Zpow2n_gt_0|].
  assert (0<IZR m) as Hn; [apply IZR_lt; exact Hm|].
  assert (IZR m<>0) as Hn'; [apply not_eq_sym; apply Rlt_not_eq; exact Hn|].
  assert (IZR p2 <> 0) as Hr2'. { rewrite -> Heqp2. apply neq_0_Rmantissa. exact Hw2. }
  assert ((p2<>0)%Z) as Hp2'. { rewrite -> Heqp2. apply neq_0_Zmantissa. exact Hw2. }
  assert ((Z.abs p2<>0)%Z) as Hap2'. { intro. apply (Z.abs_0_iff p2) in H. contradiction. }
  assert (IZR (Z.abs p2)<>0) as Har2'. { intro H. apply eq_IZR in H. contradiction. }
  assert ((0<Z.abs p2)%Z) as Hap2. { apply Zle_neq_lt. apply Z.abs_nonneg. apply not_eq_sym. exact Hap2'. }
  assert (0<IZR (Z.abs p2)) as Har2. { apply IZR_lt. exact Hap2. }
  apply is_rounded_mul_correct with (IZR m * IZR (Z.abs p2));
    [apply Rlt_mult_pos_pos; assumption|].
  replace (IZR p1 / IZR m / (IZR (Z.abs p2) / IZR m)) with (IZR p1 / IZR (Z.abs p2));
    [|field; split; assumption].
  destruct rnd; simpl; unfold injR, div.
  -- simpl.
     stepl (IZR (Z.sgn p2) * (IZR p2 * IZR (Zdiv_rnd down (m*p1) p2))).
     stepr (IZR (Z.sgn p2) * (IZR m * IZR p1)).
     --- repeat (rewrite <- mult_IZR).
         apply IZR_le.
         set (Hs := Z.sgn_spec p2).
         destruct Hs as [Hlt|[Heq|Hgt]].
         - destruct Hlt as [Hp2 Hs1].
           apply Z.mul_le_mono_nonneg_l; [rewrite -> Hs1; apply Z.le_0_1|].
           apply Zdiv_rnd_down_pos; [exact Hp2].
         - destruct Heq as [Hp2 Hs0].
           rewrite -> Hs0.
           repeat (rewrite -> Z.mul_0_l).
           apply Z.le_refl.
         - destruct Hgt as [Hp2 Hs1].
           apply Z.mul_le_mono_nonpos_l; [rewrite -> Hs1; apply Z.lt_le_incl; exact Z.lt_m1_0|].
           apply Zdiv_rnd_down_neg; [exact Hp2].
     --- rewrite <- Z.sgn_abs. rewrite -> mult_IZR. field. split. exact Hn'. exact Hr2'.
     --- rewrite <- Heqp1, <- Heqp2, <- Heqm.
         rewrite <- Z.sgn_abs.
         rewrite -> mult_IZR.
         unfold Zdiv_rnd. field. exact Hn'.
  -- assert (forall a b c, ((c<>0) -> Zdist ((Z.sgn c)*a) ((Z.sgn c)*b) = Zdist a b)%Z) as HZdist. {
       intros a b c Hc.
       unfold Zdist.
       rewrite <- Z.mul_sub_distr_l.
       rewrite -> Z.abs_mul.
       assert (forall z, (z<>0 -> Z.abs (Z.sgn z) = 1)%Z). {
         intros z H; unfold Z.abs, Z.sgn.
         destruct z; [contradiction|reflexivity|reflexivity].
       }
       rewrite -> H; [|exact Hc].
       rewrite -> Zmult_1_l.
       reflexivity.
     }
     intros s.
     stepl (Rdist (IZR (Z.sgn p2) * ((IZR p2) * IZR (Zdiv_rnd near (m*p1)%Z p2))) (IZR (Z.sgn p2) * (IZR m * IZR p1))).
     stepr (Rdist (IZR (Z.sgn p2) * ((IZR p2) * IZR (mantissa s))) (IZR (Z.sgn p2) * (IZR m * IZR p1))).
     --- repeat (rewrite <- mult_IZR).
         repeat (rewrite -> dist_IZR).
         repeat (rewrite -> HZdist).
         apply IZR_le.
         apply Zdiv_rnd_near.
         exact Hp2'.
         exact Hp2'.
         exact Hp2'.
     --- remember (mantissa s) as q.
         rewrite <- Z.sgn_abs.
         rewrite <- Heqm.
         repeat (rewrite -> mult_IZR).
         f_equal.  field. exact Hn'. field. split. exact Hn'. exact Hr2'.
     --- rewrite <- Heqp1, <- Heqp2, <- Heqm.
         remember (Zdiv_rnd near (m*p1) p2) as q.
         unfold mantissa.
         rewrite <- Z.sgn_abs.
         repeat (rewrite -> mult_IZR).
         f_equal. field. exact Hn'. field. split. exact Hn'. exact Hr2'.
  -- simpl.
     apply Rle_ge.
     stepr (IZR (Z.sgn p2) * (IZR p2 * IZR (Zdiv_rnd up (m*p1) p2))).
     stepl (IZR (Z.sgn p2) * (IZR m * IZR p1)).
     --- repeat (rewrite <- mult_IZR).
         apply IZR_le.
         set (Hs := Z.sgn_spec p2).
         destruct Hs as [Hlt|[Heq|Hgt]].
         - destruct Hlt as [Hp2 Hs1].
           apply Z.mul_le_mono_nonneg_l; [rewrite -> Hs1; apply Z.le_0_1|].
           apply Zdiv_rnd_up_pos_le; [exact Hp2].
         - destruct Heq as [Hp2 Hs0].
           rewrite -> Hs0.
           repeat (rewrite -> Z.mul_0_l).
           apply Z.le_refl.
         - destruct Hgt as [Hp2 Hs1].
           apply Z.mul_le_mono_nonpos_l; [rewrite -> Hs1; apply Z.lt_le_incl; exact Z.lt_m1_0|].
           apply Zdiv_rnd_up_neg; [exact Hp2].
     --- rewrite <- Z.sgn_abs. rewrite -> mult_IZR. field. split. exact Hn'. exact Hr2'.
     --- rewrite <- Heqp1, <- Heqp2, <- Heqm.
         rewrite <- Z.sgn_abs. rewrite -> mult_IZR.
         unfold Zdiv_rnd. field. exact Hn'.
Qed.


Lemma rec_correct : forall n rnd (w : FixedDyadic n),
  (injR w<>0) -> is_rounded rnd (rec rnd w) (Rinv (injR w)).
Proof.
  intros n rnd w Hn.
  set (p := mantissa w); set (m:=Zpow2 n).
  set (one := make n m).
  assert (rec rnd w = div rnd one w) as Hw. { trivial. }
  assert (injR one = 1%R) as H1. {
    unfold injR, one, m, mantissa. field. apply pow2n_neq_0.
  }
  assert (Rinv (injR w) = Rdiv (injR one) (injR w)) as Hr.  {
    rewrite -> H1. field. exact Hn.
  }
  rewrite -> Hw.
  rewrite -> Hr.
  apply (div_correct n rnd).
  exact Hn.
Qed.

End W.

Export W(FixedDyadic).
