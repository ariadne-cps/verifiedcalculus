(******************************************************************************
 *  numbers/Dyadic.v
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
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import QArith.Qminmax.

From Stdlib Require Import Lra.

Require Export IntAddenda.


(* A Dyadic number of the form p / 2^q  *)
Record Q2 : Set := Q2make {Q2man : Z; Q2exp : N}.
Notation Dyadic := Q2.

Declare Scope Q2_scope.
Delimit Scope Q2_scope with Q2.
Bind Scope Q2_scope with Q2.
Arguments Q2make _%_Z _%_N.

Register Q2 as rat.Q2.type.
Register Q2make as rat.Q2.Q2make.

Open Scope Q2_scope.
Ltac simpl_mult := rewrite ?Pos2Z.inj_mul.

Open Scope N_scope.
Open Scope Z_scope.

Definition Q2mantissa (x : Q2) : Z :=
  match x with (Q2make p _) => p end.
Definition Q2exponent (x : Q2) : N :=
  match x with (Q2make _ q) => q end.

Coercion BinNat.N.of_nat : nat >-> N.

Definition Q2of_nat (n : nat) :=
  Q2make (Z.of_nat n) (0:nat).

Coercion Q2of_nat : nat >-> Q2.

Definition ZinjQ2 (n : Z) : Q2 :=
  Q2make n (0%nat).

Definition Q2injQ (x : Q2) : Q :=
  (Q2mantissa x) # (Pos.shiftl (1 : positive) (Q2exponent x)).
(*
Definition seven_fourths := Q2injQ (Q2make 14 (3:nat)).
Compute seven_fourths.
*)

Definition Q2compare (x1 : Q2) (x2 : Q2) : comparison :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
  let m1:= Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (Z.mul p1 m2) ?= (Z.mul p2 m1).

Definition Q2eqb (x1 : Q2) (x2 : Q2) : bool :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
  let m1:=Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (p1 * m2) =? (p2 * m1).

Definition Q2ltb (x1 : Q2) (x2 : Q2) : bool :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
  let m1:=Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (p1 * m2) <? (p2 * m1).

Definition Q2leb (x1 : Q2) (x2 : Q2) : bool :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
  let m1:=Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (p1 * m2) <=? (p2 * m1).

Definition Q2eq (x1 : Q2) (x2 : Q2) : Prop :=
  Q2eqb x1 x2 = true.

Definition Q2le (x1 : Q2) (x2 : Q2) : Prop :=
  Q2leb x1 x2 = true.

Definition Q2lt (x1 : Q2) (x2 : Q2) : Prop :=
  Q2ltb x1 x2 = true.

Definition Q2neg (x : Q2) : Q2 :=
  Q2make (- Q2mantissa x) (Q2exponent x).

Definition Q2abs (x : Q2) : Q2 :=
  Q2make ( Z.abs (Q2mantissa x) ) (Q2exponent x).

Definition Q2max (x1 : Q2) (x2 : Q2) : (Q2) :=
  (GenericMinMax.gmax Q2compare) x1 x2.

Definition Q2min (x1 : Q2) (x2 : Q2) : (Q2) :=
  if Q2leb x1 x2 then x1 else x2.

(* If q1>q2, then p1 / 2^q1 + p2 / 2^q2 = (p1 + p2 * 2^(q1-q2)) / 2^q1 *)
Definition Q2add (x1 : Q2) (x2 : Q2) : Q2 :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
  if (n1 <=? n2)%N 
    then Q2make (p1 * Z.pow2 (n2-n1)%N + p2) (n2)
    else Q2make (p1 + p2 * Z.pow2 (n1-n2)%N) (n1).

Definition Q2sub (x1 : Q2) (x2 : Q2) : Q2 :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
  if (n1 <=? n2)%N 
    then Q2make (p1 * Z.pow2 (n2-n1)%N - p2) (n2)
    else Q2make (p1 - p2 * Z.pow2 (n1-n2)%N) (n1).

Definition Q2mul (x1 : Q2) (x2 : Q2) : Q2 :=
  let p1 := Q2mantissa x1 in let p2 := Q2mantissa x2 in
  let n1 := Q2exponent x1 in let n2 := Q2exponent x2 in
    Q2make (p1*p2) (n1+n2)%N.

Definition Q2hlf (x : Q2) : Q2 :=
  let p := Q2mantissa x in let n := Q2exponent x in 
    Q2make p  (N.succ n).

Definition Q2toQ (x : Dyadic) : Q :=
  Qdiv (inject_Z (Q2mantissa x)) (inject_Z (Z.pow2 (Q2exponent x))).

Close Scope Z_scope.



Open Scope Q_scope.

Lemma ZinjQ2injQ_correct : forall (n : Z),
  Q2injQ (ZinjQ2 n) = inject_Z n.
Proof.
  intros n.
  unfold Q2injQ, ZinjQ2, inject_Z.
  simpl. reflexivity.
Qed.

Lemma Qdiv_1 : forall q : Q, Qdiv q 1 == q.
Proof.
  intro q. 
  replace q with (q * 1). 
  - rewrite -> Qdiv_mult_l. symmetry. exact (Qmult_1_r q).
    exact Q_apart_0_1.
  - unfold Qmult. simpl. rewrite Zmult_1_r. rewrite Pos.mul_1_r. 
    destruct q. simpl. reflexivity.
Qed.

Lemma ZinjQ2toQ_correct : forall (n : Z),
  Q2toQ (ZinjQ2 n) == inject_Z n.
Proof.
  intros n.
  unfold Q2toQ, ZinjQ2, inject_Z; simpl.
  assert (Z.pow2 N0 = 1%Z) as H. { now unfold Z.pow2. }
  rewrite H.
  now rewrite Qdiv_1.
Qed.


Lemma Zpos_pow2 : forall n, Z.pos (Pos.pow2 n) = Z.pow2 n.
Proof. 
  intro n. 
  unfold Z.pow2, N.pow2, Pos.pow2, Z.of_N.
  pose proof (N.pow2_ne_0 n) as Hpne0.
  remember (2^n)%N as p.
  destruct p.
  - exfalso; apply Hpne0; now rewrite -> Heqp.
  - reflexivity.
Qed.

Lemma Q2injQ_inj : forall (w1 w2 : Q2),
  Qeq (Q2injQ w1) (Q2injQ w2) -> Q2eq w1 w2.
Proof.
  unfold Q2injQ, Qeq, Q2eq, Q2eqb; simpl.
  intros w1 w2 HQ.
  repeat rewrite <- Pos_pow2_N_shiftl_1, -> Zpos_pow2 in HQ; simpl.
  rewrite -> HQ.  
  now apply Z.eqb_refl.
Qed.


Lemma Q2ltb_compare : forall x1 x2 : Q2, 
  Q2ltb x1 x2 = true <-> Q2compare x1 x2 = Lt.
Proof.
  intros x1 x2. unfold Q2compare, Q2ltb. 
  unfold Z.ltb.
  remember (Q2mantissa x1 * Z.pow2 (Q2exponent x2) ?= Q2mantissa x2 * Z.pow2 (Q2exponent x1))%Z as cmp.
  split.
  - intro H. destruct cmp. discriminate H. reflexivity. discriminate H.
  - intro H. now rewrite -> H.
Qed.

Lemma Q2leb_compare : forall x1 x2 : Q2, 
  Q2leb x1 x2 = true <-> Q2compare x1 x2 <> Gt.
Proof.
  intros x1 x2. unfold Q2compare, Q2leb. 
  unfold Z.leb.
  remember (Q2mantissa x1 * Z.pow2 (Q2exponent x2) ?= Q2mantissa x2 * Z.pow2 (Q2exponent x1))%Z as cmp.
  split.
  - intro H. destruct cmp. discriminate. discriminate. discriminate H.
  - intro H. destruct cmp. reflexivity. reflexivity. contradiction.
Qed.
 

Lemma Q2compare_correct : forall (w1 w2 : Q2),
  Q2compare w1 w2 = Qcompare (Q2injQ w1) (Q2injQ w2).
Proof.
  intros w1 w2.
  unfold Q2compare, Qcompare, Q2injQ.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2].
  simpl.
  now rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
Qed.

Lemma Q2eqb_correct : forall (w1 w2 : Q2),
  Q2eqb w1 w2 = Qeq_bool (Q2injQ w1) (Q2injQ w2).
Proof.
  intros w1 w2.
  unfold Q2eqb, Qeq_bool, Q2injQ.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2].
  simpl.
  now rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
Qed.

Lemma Q2leb_correct : forall (w1 w2 : Q2),
  Q2leb w1 w2 = Qle_bool (Q2injQ w1) (Q2injQ w2).
Proof.
  intros w1 w2.
  unfold Q2leb, Qle_bool, Q2injQ.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2].
  simpl.
  now rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
Qed.

Lemma Q2neg_correct : forall (w : Q2), Q2injQ (Q2neg w) == Qopp (Q2injQ w).
Proof.
  intros w; unfold Q2neg, Qopp, Q2injQ; simpl. reflexivity.
Qed.

Lemma Q2abs_correct : forall (w : Q2), Q2injQ (Q2abs w) == Qabs (Q2injQ w).
Proof.
  intros w; unfold Q2abs, Qabs, Q2injQ; simpl. reflexivity.
Qed.

Lemma Q2max_correct : forall (w1 w2 : Q2), Q2injQ (Q2max w1 w2) == Qmax (Q2injQ w1) (Q2injQ w2).
Proof.
  intros w1 w2.
  unfold Q2max, Qmax, GenericMinMax.gmax.
  rewrite -> Q2compare_correct; simpl.
  destruct (Qcompare (Q2injQ w1) (Q2injQ w2)).
  all: reflexivity.
Qed.

Lemma Q2min_correct : forall (w1 w2 : Q2), Q2injQ (Q2min w1 w2) == Qmin (Q2injQ w1) (Q2injQ w2).
Proof.
  assert (forall p : Prop, false = true -> p) as exfalse. {
    intros p Hc; discriminate Hc. }
  intros w1 w2.
  unfold Q2min, Qmin, GenericMinMax.gmin; simpl.
  rewrite <- Q2compare_correct.
  remember (Q2leb w1 w2) as b.
  pose proof (Q2leb_compare w1 w2) as H.  
  rewrite <- Heqb in H.
  destruct H as [Ht Hf].
  destruct b.
  - assert (Q2compare w1 w2 <> Gt) as HnGt by now apply Ht. 
    destruct (Q2compare w1 w2).
    reflexivity. reflexivity. contradiction.
  - destruct (Q2compare w1 w2).
    apply exfalse; apply Hf; discriminate.        
    apply exfalse; apply Hf; discriminate.        
    reflexivity.
Qed.



Lemma Q2add_correct : forall (w1 w2 : Dyadic),
  Q2injQ (Q2add w1 w2) == Qplus (Q2injQ w1) (Q2injQ w2).
Proof.
  intros w1 w2.
  unfold Q2add, Qplus, Q2injQ; simpl.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2]; simpl.
  rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
  unfold Qeq; simpl.
  rewrite -> Pos2Z.inj_mul.
  rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
  remember (N.leb n1 n2) as n1_le_n2.
  destruct (n1_le_n2); simpl.
  - rewrite <- (Zpow2_shiftl n2).
    rewrite -> Z.mul_assoc. 
    apply Z.mul_cancel_r.
    apply Z.pow2_ne_0.
    rewrite -> Z.mul_add_distr_r.
    apply Z.add_cancel_r.
    rewrite <- Z.mul_assoc.
    rewrite -> Z.pow2_add_r.
    assert ((n1 <= n2)%N) as Hn1len2. { apply N.leb_le; symmetry; assumption. }
    assert ( (n2 - n1 +n1)%N = n2) as Hn2. { apply (N.sub_add _ _ Hn1len2). }
    now rewrite -> Hn2.
  - rewrite <- (Zpow2_shiftl n1).
    rewrite -> (Z.mul_comm _ (Z.pow2 n2)).
    rewrite -> Z.mul_assoc.
    apply Z.mul_cancel_r.
    apply Z.pow2_ne_0.
    rewrite -> Z.mul_add_distr_r.
    apply Z.add_cancel_l.
    rewrite <- Z.mul_assoc.
    rewrite -> Z.pow2_add_r.
    assert ((n2 <= n1)%N) as Hn2len2. { apply N.lt_le_incl. apply N.lt_nge. apply N.leb_nle. symmetry; assumption. }
    assert ( (n1 - n2 +n2)%N = n1) as Hn1. { apply N.sub_add. exact Hn2len2. }
    now rewrite -> Hn1.
Qed.

Lemma Q2mul_correct : forall (w1 w2 : Q2),
  Q2injQ (Q2mul w1 w2) == Qmult (Q2injQ w1) (Q2injQ w2).
Proof.
  intros w1 w2.
  unfold Q2add, Qmult, Q2injQ; simpl.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2]; simpl.
  now rewrite <- Pos_shiftl_1_add_r.
Qed.

Theorem Qeq_refl' x y : x = y -> x == y.
Proof. intro H; rewrite <- H; exact (Qeq_refl x). Qed.

Lemma Q2hlf_correct : forall (w : Q2),
  Q2injQ (Q2hlf w) == Qdiv (Q2injQ w) (2).
Proof.
  intros w.
  unfold Q2injQ.
  unfold Q2hlf, Qdiv, Qmult, Qinv, Q2injQ; simpl.
  destruct w as [p n]; simpl.
  apply Qeq_refl'. f_equal.
  - symmetry; now apply Z.mul_1_r.
  - rewrite -> Pos_shiftl_succ.
    rewrite -> Pos.mul_comm.
    now rewrite -> (Pos_mul_2_l (Pos.shiftl 1 n)).
Qed.

Lemma Q2eq_0_mantissa : forall {w : Q2},
  (Q2mantissa w = 0)%Z -> Q2injQ w == 0.
Proof.
  intros w Hw.
  unfold Q2injQ, Qeq.
  now rewrite -> Hw.
Qed.

Lemma Q2neq_0_mantissa : forall {w : Q2},
  ~ (Q2injQ w == 0) -> (Q2mantissa w <> 0)%Z.
Proof.
  intros w Hq Hnw; apply Hq; clear Hq.
  now apply (Q2eq_0_mantissa).
Qed.

Lemma Q2add_comm : forall {w1 w2 : Q2}, 
  Q2eq (Q2add w1 w2) (Q2add w2 w1).
Proof.
  intros w1 w2.
  apply Q2injQ_inj.
  repeat rewrite -> Q2add_correct.
  now apply Qplus_comm.
Qed.

Lemma Q2add_assoc : forall {w1 w2 w3 : Q2}, 
  Q2eq (Q2add w1 (Q2add w2 w3)) (Q2add (Q2add w1 w2) w3).
Proof.
  intros w1 w2 w3.
  apply Q2injQ_inj.
  repeat rewrite -> Q2add_correct.
  now apply Qplus_assoc.
Qed.

Lemma Q2mul_comm : forall {w1 w2 : Q2}, 
  Q2eq (Q2mul w1 w2) (Q2mul w2 w1).
Proof.
  intros w1 w2.
  apply Q2injQ_inj.
  repeat rewrite -> Q2mul_correct.
  now apply Qmult_comm.
Qed.

Lemma Q2mul_add_distr_l : forall {w1 w2 w3 : Q2}, 
  Q2eq (Q2mul w1 (Q2add w2 w3)) (Q2add (Q2mul w1 w2) (Q2mul w1 w3)).
Proof.
  intros w1 w2 w3.
  apply Q2injQ_inj.
  repeat rewrite -> Q2mul_correct.
  repeat rewrite -> Q2add_correct.
  repeat rewrite -> Q2mul_correct.
  now apply Qmult_plus_distr_r.
Qed.


Close Scope Z_scope.
