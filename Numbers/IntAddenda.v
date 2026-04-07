(******************************************************************************
 *  numbers/Z_addenda.v
 *
 *  Copyright 2023-26 Pieter Collins
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


From Stdlib Require Import NArith.
From Stdlib Require Import ZArith.

From Stdlib Require Import Reals.
From Stdlib Require Import Reals.Rbase.
From Stdlib Require Import Reals.Rfunctions.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Rdefinitions.

From Stdlib Require Import QArith.


Require Export RealAddenda.


Module Pos.

Definition pow2 (n : N) : positive := 
  match (2^n)%N with | N0 => xH | N.pos p => p end.

End Pos.


Module N.

Definition pow2 (n : N) : N := N.pow 2 n.

Lemma pow2_ne_0 : forall n : N, N.pow2 n <> 0%N. 
Proof. 
  intro n. unfold N.pow2. 
  assert (2 <> 0)%N as H2ne0 by discriminate.
  exact (N.pow_nonzero 2 n H2ne0).
Qed.

End N.


Module Z.

Definition pow2 (n : N) : Z := Z.of_N (N.pow2 n).

Lemma pow2_ne_0 : forall n : N, pow2 n <> 0%Z. 
Proof. 
  unfold Z.pow2, Z.of_N.
  intros n Hp.
  apply (N.pow2_ne_0 n).
  destruct (N.pow2).
  - reflexivity.
  - apply N2Z.inj; simpl. exact Hp.
Qed.

Lemma pow2_add_r : forall n1 n2 : N, (Z.pow2 n1 * Z.pow2 n2)%Z = Z.pow2 (n1+n2)%N.
Proof. 
  intros n1 n2.
  unfold Z.pow2, N.pow2.
  rewrite -> N.pow_add_r.
  now rewrite -> N2Z.inj_mul.
Qed.

End Z.



Open Scope Z_scope.

Definition Zdist a b := Z.abs (Z.sub a b).

Lemma dist_IZR : forall a b, Rdist (IZR a) (IZR b) = IZR (Zdist a b).
Proof. intros; unfold Zdist, Rdist; rewrite -> abs_IZR, minus_IZR; reflexivity. Qed.

(*
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
*)

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





Lemma Npos_inj : forall p1 p2, N.pos p1 = N.pos p2 -> p1 = p2.
Proof. intros p1 p2 Hp; now injection Hp. Qed.

Lemma Pos_N_mul : forall p1 p2, N.pos (Pos.mul p1 p2) = (N.mul (N.pos p1) (N.pos p2)).
Proof. intros p1 p2; reflexivity. Qed.

Lemma Pos_N_pow : forall p1 p2, N.pos (Pos.pow p1 p2) = (N.pow (N.pos p1) (N.pos p2)).
Proof. intros p1 p2; reflexivity. Qed.


Lemma Pos_iter_xH { A : Type} (f : A -> A) (a : A) : Pos.iter f a xH  = f a. 
Proof. reflexivity. Qed.
Lemma Pos_iter_xO { A : Type} (f : A -> A) (a : A) (n : positive) : Pos.iter f a (xO n)  = Pos.iter f (Pos.iter f a n) n. 
Proof. reflexivity. Qed.
Lemma Pos_iter_xI { A : Type} (f : A -> A) (a : A) (n : positive) : Pos.iter f a (xI n)  = f (Pos.iter f (Pos.iter f a n) n). 
Proof. reflexivity. Qed.

Lemma Pos_mul_xH {q : positive} : Pos.mul xH q = q. 
Proof. reflexivity. Qed.
Lemma Pos_mul_xO {p q : positive} : Pos.mul (xO p) q = xO (Pos.mul p q). 
Proof. reflexivity. Qed.

Lemma Pos_mul_2_l : forall p : positive, Pos.mul 2 p = xO p.
Proof. intro p. unfold Pos.mul. reflexivity. Qed.



Lemma Pos_iter_extensional {X : Type} : forall {f g : X -> X} (Hfg : forall x, f x = g x) (x0 : X) (n : positive), 
  Pos.iter f x0 n = Pos.iter g x0 n.
Proof.
  intros f g Hfg x0 n; revert x0; induction n.
  - intro x0; now rewrite -> Pos_iter_xI, IHn, IHn, Hfg.
  - intro x0; now rewrite -> Pos_iter_xO, IHn, IHn.
  - intro x0; now rewrite -> Pos_iter_xH, Hfg.
Qed.

Lemma Pos_iter_xO_mul : forall n y1 y2 : positive, Pos.mul (Pos.iter xO y1 n) y2 = Pos.iter xO (Pos.mul y1 y2) n.
Proof.
  induction n.
  - intros y1 y2; now rewrite -> Pos_iter_xI, Pos_mul_xO, IHn, IHn.
  - intros y1 y2; now rewrite -> Pos_iter_xO, IHn, IHn.
  - intros y1 y2; now rewrite -> Pos_iter_xH.
Qed.

Lemma Pos_mul_iter_xO : forall n y : positive, Pos.mul (Pos.iter xO xH n) y = Pos.iter xO y n.
Proof. intros n y; now rewrite -> (Pos_iter_xO_mul n xH y), -> Pos.mul_1_l. Qed.

Lemma Pos_mul_pow2_shiftl : forall n y : positive, Pos.mul (Pos.pow 2 n) y = Pos.shiftl y (N.pos n).  
Proof. 
  intros n y. 
  unfold Pos.pow, Pos.shiftl.
  rewrite -> (Pos_iter_extensional Pos_mul_2_l).
  now rewrite -> Pos_mul_iter_xO.
Qed.

Lemma Pos_mul_pow2_N_shiftl : forall (n : N) (y : positive), Pos.mul (Pos.pow2 n) y = Pos.shiftl y n.  
Proof. 
  intros n y. 
  destruct n.
  - unfold Pos.pow2. replace (2^0)%N  with 1%N. reflexivity.
    unfold N.pow; reflexivity.
  - unfold Pos.pow2. rewrite <- Pos_mul_pow2_shiftl. reflexivity. 
Qed.

Lemma Pos_pow2_spec : forall p, Pos.pow2 (Npos p) = Pos.pow 2 p.
Proof. intro p; reflexivity. Qed.

Lemma Pos_pow2_spec_N : forall n, Npos (Pos.pow2 n) = N.pow 2 n.
Proof. 
  intro n; destruct n.
  - reflexivity.  
  - unfold Pos.pow2, N.pow; reflexivity. 
Qed.


Lemma Pos_pow2_add_r : forall n1 n2, Pos.pow2 (n1+n2) = Pos.mul (Pos.pow2 n1) (Pos.pow2 n2).
Proof.
  intros n1 n2.
  apply Npos_inj.
  rewrite -> Pos_pow2_spec_N.
  rewrite -> N.pow_add_r.
  rewrite <- Pos_pow2_spec_N.
  rewrite <- Pos_pow2_spec_N.
  reflexivity.
Qed.

Lemma Pos_pow2_shiftl_1 : forall p : positive, (Pos.pow 2 p) = Pos.shiftl 1 (N.pos p).
Proof. intros p. rewrite <- (Pos_mul_pow2_shiftl p xH). now rewrite -> Pos.mul_1_r. Qed.

Lemma Pos_pow2_N_shiftl_1 : forall (n : N), (Pos.pow2 n) = Pos.shiftl 1 n.  
Proof. intro n. rewrite <- Pos_mul_pow2_N_shiftl. now rewrite -> Pos.mul_1_r. Qed.

Lemma Pos_shiftl_compose : forall (p : positive) (n1 n2 : N), Pos.shiftl (Pos.shiftl p n1) n2 = Pos.shiftl p (n1+n2).
Proof. 
  intros p n1 n2.
  rewrite <- Pos_mul_pow2_N_shiftl.
  rewrite <- Pos_mul_pow2_N_shiftl.
  rewrite <- Pos_mul_pow2_N_shiftl.
  rewrite -> Pos.mul_assoc.
  f_equal.
  rewrite -> Pos_pow2_add_r.
  now apply Pos.mul_comm.
Qed.

Lemma Pos_shiftl_1_add_r : forall (n1 n2 : N), Pos.mul (Pos.shiftl 1 n1) (Pos.shiftl 1 n2) = Pos.shiftl 1 (n1+n2).
Proof. 
  intros n1 n2.
  rewrite <- (Pos_mul_pow2_N_shiftl n1), <- (Pos_mul_pow2_N_shiftl n2).
  rewrite Pos.mul_1_r, Pos.mul_1_r.
  rewrite <- Pos_pow2_add_r.
  now rewrite -> Pos_pow2_N_shiftl_1.
Qed.

Lemma Npow2_shiftl : forall n : N, N.pow2 n = N.pos (Pos.shiftl xH n).
Proof. 
  intro n. unfold N.pow2, N.pow.
  destruct n.
  - unfold Pos.shiftl; reflexivity.
  - now rewrite Pos_pow2_shiftl_1.
Qed.

Lemma Zpow2_shiftl : forall n : N, Z.pow2 n = Z.pos (Pos.shiftl xH n).
Proof. 
  intros n. 
  unfold Z.pow2, N.pow, Z.of_N.
  destruct n.
  - reflexivity.
  - now rewrite <- Pos_pow2_shiftl_1.
Qed.

Lemma Pos_shiftl_succ : forall (n : N) (y : positive), Pos.shiftl y (N.succ n) = xO (Pos.shiftl y n).  
Proof. 
  intros n y.
  apply Npos_inj.
  repeat rewrite <- Pos_mul_pow2_N_shiftl.
  rewrite -> Pos_N_mul.
  rewrite -> Pos_pow2_spec_N.
  rewrite -> N.pow_succ_r'.
  rewrite <- N.mul_assoc.
  replace (2^n)%N with (N.pos (Pos.pow2 n)).
  rewrite <- Pos_N_mul.
  rewrite <- Pos_N_mul.
  rewrite -> Pos.mul_assoc.
  now rewrite -> (Pos_mul_2_l (Pos.pow2 n)).
  now apply Pos_pow2_spec_N.
Qed.



Close Scope Z_scope.
