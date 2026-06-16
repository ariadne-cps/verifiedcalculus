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

Module Q2.

(* A Dyadic number of the form p / 2^q  *)
Record Dyadic : Set := make {man : Z; exp : N}.

Declare Scope Q2_scope.
Delimit Scope Q2_scope with Q2.
Bind Scope Q2_scope with Dyadic.
Arguments make _%_Z _%_N.

Register Dyadic as rat.Q2.type.
Register make as rat.Q2.make.

Open Scope Q2_scope.
Ltac simpl_mult := rewrite ?Pos2Z.inj_mul.

Open Scope N_scope.
Open Scope Z_scope.

Definition mantissa (x : Dyadic) : Z :=
  match x with (make p _) => p end.
Definition exponent (x : Dyadic) : N :=
  match x with (make _ q) => q end.

Coercion BinNat.N.of_nat : nat >-> N.

Definition of_nat (n : nat) :=
  make (Z.of_nat n) (0:nat).

Coercion of_nat : nat >-> Dyadic.

Definition ZinjQ2 (n : Z) : Dyadic :=
  make n (0%nat).

Definition injQ (x : Dyadic) : Q :=
  (mantissa x) # (Pos.shiftl (1 : positive) (exponent x)).
(*
Definition seven_fourths := injQ (make 14 (3:nat)).
Compute seven_fourths.
*)
  
Definition compare (x1 : Dyadic) (x2 : Dyadic) : comparison :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
  let m1:= Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (Z.mul p1 m2) ?= (Z.mul p2 m1).

Definition eqb (x1 : Dyadic) (x2 : Dyadic) : bool :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
  let m1:=Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (p1 * m2) =? (p2 * m1).

Definition ltb (x1 : Dyadic) (x2 : Dyadic) : bool :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
  let m1:=Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (p1 * m2) <? (p2 * m1).

Definition leb (x1 : Dyadic) (x2 : Dyadic) : bool :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
  let m1:=Z.pow2 n1 in let m2:=Z.pow2 n2 in
    (p1 * m2) <=? (p2 * m1).

Definition eq (x1 : Dyadic) (x2 : Dyadic) : Prop :=
  eqb x1 x2 = true.

Definition le (x1 : Dyadic) (x2 : Dyadic) : Prop :=
  leb x1 x2 = true.

Definition lt (x1 : Dyadic) (x2 : Dyadic) : Prop :=
  ltb x1 x2 = true.

Definition neg (x : Dyadic) : Dyadic :=
  make (- mantissa x) (exponent x).

Definition abs (x : Dyadic) : Dyadic :=
  make ( Z.abs (mantissa x) ) (exponent x).

Definition max (x1 : Dyadic) (x2 : Dyadic) : Dyadic :=
  (GenericMinMax.gmax compare) x1 x2.

Definition min (x1 : Dyadic) (x2 : Dyadic) : Dyadic :=
  if leb x1 x2 then x1 else x2.

(* If q1>q2, then p1 / 2^q1 + p2 / 2^q2 = (p1 + p2 * 2^(q1-q2)) / 2^q1 *)
Definition add (x1 : Dyadic) (x2 : Dyadic) : Dyadic :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
  if (n1 <=? n2)%N 
    then make (p1 * Z.pow2 (n2-n1)%N + p2) (n2)
    else make (p1 + p2 * Z.pow2 (n1-n2)%N) (n1).

Definition sub (x1 : Dyadic) (x2 : Dyadic) : Dyadic :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
  if (n1 <=? n2)%N 
    then make (p1 * Z.pow2 (n2-n1)%N - p2) (n2)
    else make (p1 - p2 * Z.pow2 (n1-n2)%N) (n1).

Definition mul (x1 : Dyadic) (x2 : Dyadic) : Dyadic :=
  let p1 := mantissa x1 in let p2 := mantissa x2 in
  let n1 := exponent x1 in let n2 := exponent x2 in
    make (p1*p2) (n1+n2)%N.

Definition hlf (x : Dyadic) : Dyadic :=
  let p := mantissa x in let n := exponent x in 
    make p  (N.succ n).

Definition toQ (x : Dyadic) : Q :=
  Qdiv (inject_Z (mantissa x)) (inject_Z (Z.pow2 (exponent x))).

Close Scope Z_scope.



Open Scope Q_scope.

Lemma ZinjQ2injQ_correct : forall (n : Z),
  injQ (ZinjQ2 n) = inject_Z n.
Proof.
  intros n.
  unfold injQ, ZinjQ2, inject_Z.
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
  toQ (ZinjQ2 n) == inject_Z n.
Proof.
  intros n.
  unfold toQ, ZinjQ2, inject_Z; simpl.
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

Lemma injQ_inj : forall (w1 w2 : Dyadic),
  Qeq (injQ w1) (injQ w2) -> eq w1 w2.
Proof.
  unfold injQ, Qeq, eq, eqb; simpl.
  intros w1 w2 HQ.
  repeat rewrite <- Pos_pow2_N_shiftl_1, -> Zpos_pow2 in HQ; simpl.
  rewrite -> HQ.  
  now apply Z.eqb_refl.
Qed.


Lemma ltb_compare : forall x1 x2 : Dyadic, 
  ltb x1 x2 = true <-> compare x1 x2 = Lt.
Proof.
  intros x1 x2. unfold compare, ltb. 
  unfold Z.ltb.
  remember (mantissa x1 * Z.pow2 (exponent x2) ?= mantissa x2 * Z.pow2 (exponent x1))%Z as cmp.
  split.
  - intro H. destruct cmp. discriminate H. reflexivity. discriminate H.
  - intro H. now rewrite -> H.
Qed.

Lemma leb_compare : forall x1 x2 : Dyadic, 
  leb x1 x2 = true <-> compare x1 x2 <> Gt.
Proof.
  intros x1 x2. unfold compare, leb. 
  unfold Z.leb.
  remember (mantissa x1 * Z.pow2 (exponent x2) ?= mantissa x2 * Z.pow2 (exponent x1))%Z as cmp.
  split.
  - intro H. destruct cmp. discriminate. discriminate. discriminate H.
  - intro H. destruct cmp. reflexivity. reflexivity. contradiction.
Qed.
 

Lemma compare_correct : forall (w1 w2 : Dyadic),
  compare w1 w2 = Qcompare (injQ w1) (injQ w2).
Proof.
  intros w1 w2.
  unfold compare, Qcompare, injQ.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2].
  simpl.
  now rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
Qed.

Lemma eqb_correct : forall (w1 w2 : Dyadic),
  eqb w1 w2 = Qeq_bool (injQ w1) (injQ w2).
Proof.
  intros w1 w2.
  unfold eqb, Qeq_bool, injQ.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2].
  simpl.
  now rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
Qed.

Lemma leb_correct : forall (w1 w2 : Dyadic),
  leb w1 w2 = Qle_bool (injQ w1) (injQ w2).
Proof.
  intros w1 w2.
  unfold leb, Qle_bool, injQ.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2].
  simpl.
  now rewrite <- (Zpow2_shiftl n1), <- (Zpow2_shiftl n2).
Qed.

Lemma neg_correct : forall (w : Dyadic), injQ (neg w) == Qopp (injQ w).
Proof.
  intros w; unfold neg, Qopp, injQ; simpl. reflexivity.
Qed.

Lemma abs_correct : forall (w : Dyadic), injQ (abs w) == Qabs (injQ w).
Proof.
  intros w; unfold abs, Qabs, injQ; simpl. reflexivity.
Qed.

Lemma max_correct : forall (w1 w2 : Dyadic), injQ (max w1 w2) == Qmax (injQ w1) (injQ w2).
Proof.
  intros w1 w2.
  unfold max, Qmax, GenericMinMax.gmax.
  rewrite -> compare_correct; simpl.
  destruct (Qcompare (injQ w1) (injQ w2)).
  all: reflexivity.
Qed.

Lemma min_correct : forall (w1 w2 : Dyadic), injQ (min w1 w2) == Qmin (injQ w1) (injQ w2).
Proof.
  assert (forall p : Prop, false = true -> p) as exfalse. {
    intros p Hc; discriminate Hc. }
  intros w1 w2.
  unfold min, Qmin, GenericMinMax.gmin; simpl.
  rewrite <- compare_correct.
  remember (leb w1 w2) as b.
  pose proof (leb_compare w1 w2) as H.  
  rewrite <- Heqb in H.
  destruct H as [Ht Hf].
  destruct b.
  - assert (compare w1 w2 <> Gt) as HnGt by now apply Ht. 
    destruct (compare w1 w2).
    reflexivity. reflexivity. contradiction.
  - destruct (compare w1 w2).
    apply exfalse; apply Hf; discriminate.        
    apply exfalse; apply Hf; discriminate.        
    reflexivity.
Qed.



Lemma add_correct : forall (w1 w2 : Dyadic),
  injQ (add w1 w2) == Qplus (injQ w1) (injQ w2).
Proof.
  intros w1 w2.
  unfold add, Qplus, injQ; simpl.
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

Lemma mul_correct : forall (w1 w2 : Dyadic),
  injQ (mul w1 w2) == Qmult (injQ w1) (injQ w2).
Proof.
  intros w1 w2.
  unfold add, Qmult, injQ; simpl.
  destruct w1 as [p1 n1]; destruct w2 as [p2 n2]; simpl.
  now rewrite <- Pos_shiftl_1_add_r.
Qed.

Theorem Qeq_refl' x y : x = y -> x == y.
Proof. intro H; rewrite <- H; exact (Qeq_refl x). Qed.

Lemma hlf_correct : forall (w : Dyadic),
  injQ (hlf w) == Qdiv (injQ w) (2).
Proof.
  intros w.
  unfold injQ.
  unfold hlf, Qdiv, Qmult, Qinv, injQ; simpl.
  destruct w as [p n]; simpl.
  apply Qeq_refl'. f_equal.
  - symmetry; now apply Z.mul_1_r.
  - rewrite -> Pos_shiftl_succ.
    rewrite -> Pos.mul_comm.
    now rewrite -> (Pos_mul_2_l (Pos.shiftl 1 n)).
Qed.

Lemma eq_0_mantissa : forall {w : Dyadic},
  (mantissa w = 0)%Z -> injQ w == 0.
Proof.
  intros w Hw.
  unfold injQ, Qeq.
  now rewrite -> Hw.
Qed.

Lemma neq_0_mantissa : forall {w : Dyadic},
  ~ (injQ w == 0) -> (mantissa w <> 0)%Z.
Proof.
  intros w Hq Hnw; apply Hq; clear Hq.
  now apply (eq_0_mantissa).
Qed.

Lemma add_comm : forall {w1 w2 : Dyadic}, 
  eq (add w1 w2) (add w2 w1).
Proof.
  intros w1 w2.
  apply injQ_inj.
  repeat rewrite -> add_correct.
  now apply Qplus_comm.
Qed.

Lemma add_assoc : forall {w1 w2 w3 : Dyadic}, 
  eq (add w1 (add w2 w3)) (add (add w1 w2) w3).
Proof.
  intros w1 w2 w3.
  apply injQ_inj.
  repeat rewrite -> add_correct.
  now apply Qplus_assoc.
Qed.

Lemma mul_comm : forall {w1 w2 : Dyadic}, 
  eq (mul w1 w2) (mul w2 w1).
Proof.
  intros w1 w2.
  apply injQ_inj.
  repeat rewrite -> mul_correct.
  now apply Qmult_comm.
Qed.

Lemma mul_add_distr_l : forall {w1 w2 w3 : Dyadic}, 
  eq (mul w1 (add w2 w3)) (add (mul w1 w2) (mul w1 w3)).
Proof.
  intros w1 w2 w3.
  apply injQ_inj.
  repeat rewrite -> mul_correct.
  repeat rewrite -> add_correct.
  repeat rewrite -> mul_correct.
  now apply Qmult_plus_distr_r.
Qed.


Close Scope Z_scope.

End Q2.

