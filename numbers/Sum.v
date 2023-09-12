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


Require Import Rbase.
Require Import Rdefinitions.
Require Import Rbasic_fun.
Require Import Rfunctions.

Require Import PartSum.
Require Import Lra.

Require Export R_addenda.

Section Sum.

(*
sum_incr:
  forall (n : nat) (f : nat -> R),
  sum_f_R0 f (S n) = (sum_f_R0 f n + f (S n))%R
sum_eq:
  forall (An Bn : nat -> R) (N : nat),
  (forall i : nat, (i <= N)%nat -> An i = Bn i) ->
  sum_f_R0 An N = sum_f_R0 Bn N
Nat.add_sub
  : forall n m : nat, n + m - m = n
Nat.sub_add:
  forall n m : nat, n <= m -> m - n + n = m.
Nat.sub_succ_l:
  forall n m : nat, n <= m -> S m - n = S (m - n)
*)


Lemma sum_incr_R0 : forall (f:nat->R) (n:nat), sum_f_R0 f (n+1) = Rplus (sum_f_R0 f n) (f (n+1)).
Proof.
  intros n f. rewrite -> Nat.add_1_r. unfold sum_f_R0. reflexivity.
Qed.

Lemma sum_incr : forall (s n:nat) (f:nat->R), (s<=n) -> sum_f s (n+1) f = Rplus (sum_f s n f) (f (n+1)).
Proof.
  intros s n f. intro Hslen. unfold sum_f.
  assert ((n+1 - s) = ((n-s)+1)) as Hns. {
    rewrite -> Nat.add_1_r. rewrite -> Nat.sub_succ_l; [|exact Hslen]. rewrite -> Nat.add_1_r. reflexivity.
  }
  rewrite -> Hns. rewrite -> sum_incr_R0.
  apply f_equal. apply f_equal.
  rewrite <- Hns.
  rewrite -> Nat.sub_add. reflexivity.
  apply Nat.le_trans with n.
  exact Hslen.
  apply Nat.le_add_r.
Qed.

Lemma sum_start : forall (n:nat) (f:nat->R), sum_f 0 (n+1) f = Rplus (f 0) (sum_f 1 (n+1) f).
Proof.
  intros n f.
  unfold sum_f.
  rewrite -> Nat.sub_0_r.
  induction n.
  - unfold sum_f_R0; simpl; reflexivity.
  - rewrite -> sum_incr_R0.
    rewrite <- Nat.add_1_r.
    rewrite -> IHn.
    assert (forall n, n+1 - 1 = n) as Hs1. { intro n'. apply Nat.add_sub. }
    rewrite -> Hs1. rewrite -> Hs1.
    rewrite -> sum_incr_R0.
    rewrite -> Nat.add_0_r.
    rewrite -> Nat.add_1_r.
    apply Rplus_assoc.
Qed.


Open Scope R_scope.

Lemma geometric_sum : forall (n : nat) (x : R), (x<>1%R) -> sum_f 0 n (fun k => pow x k) = ((1-x^(n+1)) / (1-x))%R.
Proof.
  intros n x Hxne1.
  assert (forall s n c f, sum_f s n (fun k => (f k) * c) = c * sum_f s n f) as Hscal_sum. {
    intros s n' c f'. unfold sum_f. apply eq_sym. apply scal_sum with (x:=c) (N:=(n'-s)%nat) (An := (fun x0 => f'(plus x0 s))).
  }
  assert (forall k, x^k * x = x^(k+1)) as Hpow_x_1. {
    intro k. rewrite -> pow_add. rewrite -> pow_1. reflexivity.
  }
  assert (x * (sum_f 0 n (fun k => x^k)) = sum_f 0 n (fun k => x^(k+1))) as H0. {
    rewrite <- Hscal_sum. apply sum_eq. intros i Hilen. rewrite -> Hpow_x_1. reflexivity.
  }
  assert (sum_f 0 n (fun k => x^(k+1)) = sum_f 1 (n+1) (fun k => x^k)) as H1. {
    unfold sum_f. rewrite -> Nat.sub_0_r. rewrite -> Nat.add_sub. apply sum_eq. intros i Hilen. rewrite -> Nat.add_0_r. reflexivity.
  }
  assert (sum_f 1 (n+1) (fun k => x^k) = sum_f 0 n (fun k => x^k) + x^(n+1) - 1) as H2. {
    rewrite <- sum_incr; [|apply Nat.le_0_l].
    rewrite -> sum_start.
    ring.
  }

  remember (sum_f 0 n (fun k => x^k)) as s.

  assert (x * s = s + x^(n+1)-1) as Hxs. {
    rewrite -> H0. rewrite -> H1. rewrite -> H2. ring.
  }
  rewrite -> Rmult_comm in Hxs.
  assert (s*(1-x)=1-x^(n+1)) as Hsp. {
    rewrite -> Rmult_minus_distr_l. rewrite -> Hxs. ring.
  }
  assert (s * (1-x) / (1-x) = (1-x^(n+1))/(1-x)) as Hsq. {
    rewrite -> Hsp. reflexivity.
  }
  rewrite <- Hsq.
  field.
  apply Rminus_eq_contra. auto.
Qed.


Fixpoint Rgeometric n x :=
  match n with
  | O => 1%R
  | S m => Rplus 1%R (Rmult x (Rgeometric m x))
  end
.

Fixpoint Fgeometric n (f : R -> R) : (R -> R) :=
  match n with
  | O => fun x => 1%R
  | S m => fun x => Rplus 1%R (Rmult (f x) (Fgeometric m f x))
  end
.

Lemma FRgeometric_equal : forall n f x, Fgeometric n f x = Rgeometric n (f x).
Proof.
  intros n f x. induction n.
  - trivial.
  - simpl. rewrite -> IHn. trivial.
Qed.





Lemma Rgeometric_eq : forall n x, x<>1 -> Rgeometric n x = (1 - x^(n+1)) / (1-x).
Proof.
  intros n x Hx.
  assert (1-x <> 0) as Hx0. { lra. }
  induction n.
  - simpl. field. exact Hx0.
  - simpl. rewrite -> IHn. field. exact Hx0.
Qed.

Lemma Rgeometric_approx : forall n (w d : R),
  d<1 -> Rabs w <= d -> Rabs ( /(1-w) - Rgeometric n w ) <= d^(n+1)/(1-d).
Proof.
  intros n w d Hd1 Hwd.
  assert (-d <= w <= d) as Hdwd. { apply Rabs_ivl. exact Hwd. }
  rewrite -> Rgeometric_eq by (lra).
  assert (/(1-w)-(1-w^(n+1))/(1-w) = w^(n+1)*/(1-w)) as Heq. { field. lra. }
  rewrite -> Heq.
  rewrite -> Rabs_mult.
  rewrite -> Rabs_inv.
  (*  |w^(n+1)|/|1-w| <= d^(n+1)/(1-d)  *)
  apply Rmult_le_compat.
  - apply Rabs_pos.
  - apply Rlt_le. apply Rinv_pos. assert (0<1-w); [lra|]. rewrite -> Rabs_pos_eq. exact H. apply Rlt_le. apply H.
  - rewrite <- RPow_abs. apply pow_incr. split. apply Rabs_pos. exact Hwd.
  - apply Rinv_le_contravar.
    lra.
    rewrite -> Rabs_pos_eq. lra. lra.
Qed.

Lemma Fgeometric_approx : forall n (f : R -> R) (d : R),
  (d<1) -> (forall x, -1<=x<=1 -> Rabs (f x) <= d) ->
    (forall x, -1<=x<=1 -> Rabs ( /(1-f x) - Rgeometric n (f x) ) <= d^(n+1)/(1-d) ).
Proof.
  intros n f d.
  intros Hd Hy.
  intros x Hx.
  apply (Rgeometric_approx _ _ _ Hd).
  apply (Hy _ Hx).
Qed.



Close Scope R_scope.

End Sum.
