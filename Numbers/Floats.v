(******************************************************************************
 *  Numbers/Floats.v
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
(*  * published by the Free Software Foundation, either version 3 of the License, *)
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

From Stdlib Require Import List.

Require Export RealAddenda.

(*
Module Floats.
*)



Open Scope R_scope.


Lemma or_impl_compat : forall p1 p2 p3 p4 : Prop,
  (p1 -> p3) -> (p2 -> p4) -> (p1 \/ p2) -> (p3 \/ p4).
Proof.
  intros p1 p2 p3 p4 Hp13 Hp24 Hor.
  apply or_ind with (A:=p1) (B:=p2).
  - left. apply Hp13. exact H.
  - right. apply Hp24. exact H.
  - exact Hor.
Qed.


(*
INR_eq: forall n m : nat, INR n = INR m -> n = m
not_O_S_INR: forall n : nat, INR (S n) <> 0
plus_INR: forall n m : nat, INR (n + m) = INR n + INR m
not_0_INR: forall n : nat, n <> 0%nat -> INR n <> 0
INR_not_0: forall n : nat, INR n <> 0 -> n <> 0%nat
S_O_plus_INR: forall n : nat, INR (1 + n) = INR 1 + INR n
S_INR: forall n : nat, INR (S n) = INR n + 1
minus_INR: forall n m : nat, (m <= n)%nat -> INR (n - m) = INR n - INR m
*)

Lemma INR_0 : INR 0%nat = 0%R.
Proof.
  unfold INR. reflexivity.
Qed.

Lemma INR_1 : INR 1%nat = 1%R.
Proof.
  unfold INR. reflexivity.
Qed.








Coercion INR : nat >-> R.


Inductive Rounding := down | near | up.

Local Definition opposite rnd :=
  match rnd with | up => down | near => near | down => up end.



Inductive BinOp := Add | Sub | Mul.
(* Inductive BinOp := Add | Sub | Mul | Div. *)


Definition Rapply (fval:BinOp) : R -> R -> R :=
  match fval with
    | Add => Rplus | Sub => Rminus | Mul => Rmult (* | Div => Rdiv *)
  end
.


Module F.

Class Float (F : Type) :=
{
  of_nat : nat -> F;
  injR : F -> R;

  null := of_nat 0;
  unit := of_nat 1;

  F0 := null;
  F1 := unit;

  neg : F -> F;
  abs : F -> F;

  add : Rounding -> F -> F -> F;
  sub : Rounding -> F -> F -> F;
  mul : Rounding -> F -> F -> F;
  div : Rounding -> F -> F -> F;

  rec : Rounding -> F -> F;

  div_nat_spec : Rounding -> F -> nat -> F := fun r x n => div r x (of_nat n);

  shft : Rounding -> F -> Z -> F;

  min : F -> F -> F;
  max : F -> F -> F;

  leb : F -> F -> bool;


  neg_exact := neg;
  abs_exact := abs;

  add_up := add up;
  add_down := add down;
  add_near := add near;

  sub_up := sub up;
  sub_down := sub down;
  sub_near := sub near;

  mul_up := mul up;
  mul_down := mul down;
  mul_near := mul near;

  div_up := div up;
  div_down := div down;
  div_near := div near;

  rec_up := rec up;
  rec_down := rec down;
  rec_near := rec near;

(*
  apply (fop : BinOp) : Rounding -> F -> F -> F :=
    match fop with | Add => add | Sub => sub | Mul => mul | Div => div end;
*)
  apply (fop : BinOp) : Rounding -> F -> F -> F :=
    match fop with | Add => add | Sub => sub | Mul => mul end;


  val_is_exact (fval : F) (rval : R) :=
    injR fval = rval;
  unary_op_is_exact (fop : F -> F) (rop : R -> R) :=
     forall x : F, injR (fop x) = rop (injR x);
  op_is_exact (fop : F -> F -> F) (rop : R -> R -> R) :=
     forall x1 x2 : F, injR (fop x1 x2)  = rop (injR x1) (injR x2);

  val_is_rounded (fval : F) (rval : R) (rnd : Rounding) :=
    match rnd with
    | down => injR fval <= rval
    | near => forall w, Rdist (injR fval) rval <= Rdist (injR w) rval
    | up   => injR fval >= rval
    end;
  nullary_op_is_rounded (fop : Rounding -> F) (rop : R) (rnd : Rounding) :=
    val_is_rounded (fop rnd) (rop) rnd;
  unary_op_is_rounded (fop : Rounding -> F -> F) (rop : R -> R) (rnd : Rounding) :=
    forall (x : F), val_is_rounded (fop rnd x) (rop (injR x)) rnd;
  binary_op_is_rounded (fop : Rounding -> F -> F -> F) (rop : R -> R -> R) (rnd : Rounding) :=
    forall (x1 x2 : F), val_is_rounded (fop rnd x1 x2) (rop (injR x1) (injR x2)) rnd;


  ninjr_spec : forall n : nat, injR (of_nat n) = INR n;

  leb_spec : forall (x1 x2 : F), (leb x1 x2 = true) <-> (injR x1) <= (injR x2);

  neg_exact_spec : forall x : F, injR (neg x) = Ropp (injR x);
  abs_exact_spec : forall x : F, injR (abs x) = Rabs (injR x);

  min_exact_spec : forall x1 x2 : F, injR (min x1 x2) = Rmin (injR x1) (injR x2);
  max_exact_spec : forall x1 x2 : F, injR (max x1 x2) = Rmax (injR x1) (injR x2);

  add_rounded_spec : forall rnd, (binary_op_is_rounded add Rplus) rnd;
  sub_rounded_spec : forall rnd, (binary_op_is_rounded sub Rminus) rnd;
  mul_rounded_spec : forall rnd, (binary_op_is_rounded mul Rmult) rnd;
  div_rounded_spec : forall (rnd : Rounding) (x1 x2 : F),
    (injR x2 <> 0%R) -> (val_is_rounded (div rnd x1 x2) (Rdiv (injR x1) (injR x2)) rnd);
  rec_rounded_spec : forall (rnd : Rounding) (x : F),
    (injR x <> 0%R) -> (val_is_rounded (rec rnd x) (Rinv (injR x)) rnd);

  shft_rounded_spec : forall (rnd : Rounding) (x : F) (n : Z),
    (val_is_rounded (shft rnd x n) (Rshft (injR x) n) rnd);

  add_down_spec := add_rounded_spec down;
  add_near_spec := add_rounded_spec near;
  add_up_spec   := add_rounded_spec up;

  sub_down_spec := sub_rounded_spec down;
  sub_near_spec := sub_rounded_spec near;
  sub_up_spec   := sub_rounded_spec up;

  mul_down_spec := mul_rounded_spec down;
  mul_near_spec := mul_rounded_spec near;
  mul_up_spec   := mul_rounded_spec up;

  div_down_spec := div_rounded_spec down;
  div_near_spec := div_rounded_spec near;
  div_up_spec   := div_rounded_spec up;

  rec_down_spec := rec_rounded_spec down;
  rec_near_spec := rec_rounded_spec near;
  rec_up_spec   := rec_rounded_spec up;
}.

(* Coercion (forall F : `Float F), F.injR : F >-> R. *)

Definition div2 {F} {Flt : Float F} (r : Rounding) (x:F) := div r x (of_nat 2).

Definition div2_up {F} {Flt : Float F} := div2 up.

Fixpoint sum {F} {Flt : Float F} (r : Rounding) (xs : list F) :=
  match xs with | nil => F.null | hd::tl => add r hd (sum r tl) end.

Definition sum_snd_add {I} {F} {Flt : Float F} (r : Rounding) : list (I * F) -> F
  := fold_right (fun nf=> add r (snd nf)) F.null.

Fixpoint pow_pos {F} {Flt : Float F} (r : Rounding) (x:F) (n:nat) :=
  match n with
    | O => unit
    | S n' => mul r x (pow_pos r x n')
    end.

Definition pow {F} {Flt : Float F} (r : Rounding) (x:F) (n:nat) :=
  let m := Nat.div2 n in
  let o := opposite r in
  if F.leb F.null x
    then pow_pos r x n
    else if Nat.even n
      then pow_pos r (mul r x x) m
      else mul r x (pow_pos o (mul o x x) m).


Section Float_defs.


Context `{F : Type} `{FltF : Float F}.

Lemma null_spec : F.injR (F.null) = 0%R.
Proof.
  unfold F.null. apply ninjr_spec.
Qed.

Lemma unit_spec : F.injR (F.unit) = 1%R.
Proof.
  unfold F.unit. apply ninjr_spec.
Qed.

Lemma leb_false_spec : forall x y, F.leb x y = false <-> F.injR x > F.injR y.
Proof. intros x y. split.
  intro H. apply Rnot_le_gt. intro Hle; revert H.
    apply Bool.not_false_iff_true. now apply leb_spec.
  intro H. apply Bool.not_true_is_false. intro Ht; revert H.
    rewrite -> leb_spec in Ht. now apply Rle_not_gt.
Qed.


Lemma add_up_le_spec : forall x y, F.injR x + F.injR y <= F.injR (F.add up x y).
Proof. intros x y; apply Rge_le; now apply add_up_spec. Qed.

Lemma sub_up_le_spec : forall x y, F.injR x - F.injR y <= F.injR (F.sub up x y).
Proof. intros x y; apply Rge_le; now apply sub_up_spec. Qed.

Lemma mul_up_le_spec : forall x y, F.injR x * F.injR y <= F.injR (F.mul up x y).
Proof. intros x y; apply Rge_le; now apply mul_up_spec. Qed.

Lemma div_up_le_spec : forall x y, 
  injR y <> 0 -> F.injR x / F.injR y <= F.injR (F.div up x y).
Proof. intros x y Hy; apply Rge_le; now apply div_up_spec. Qed.


Lemma pow_pos_up_spec : forall x n,
  (F.injR x >= 0) -> F.injR (pow_pos up x n) >= (F.injR x)^n.
Proof.
  intros x n Hp.
  induction n.
  - simpl. apply Req_ge. apply ninjr_spec.
  - simpl.
    apply Rge_trans with (F.injR x * F.injR (pow_pos up x n)).
    -- apply mul_up_spec.
    -- apply Rmult_ge_compat_l.  exact Hp. exact IHn.
Qed.

Lemma pow_pos_down_spec : forall x n,
  (F.injR x >= 0) -> F.injR (pow_pos down x n) <= (F.injR x)^n.
Proof.
  intros x n Hp.
  induction n.
  - simpl. rewrite -> unit_spec. now apply Rle_refl.
  - simpl.
    apply Rle_trans with (F.injR x * F.injR (pow_pos down x n)).
    -- apply mul_down_spec.
    -- apply Rmult_le_compat_l. apply Rge_le; exact Hp. exact IHn.
Qed.

Axiom mul_self_down_pos : forall x, injR (mul down x x) >= 0.

Lemma pow_up_spec : forall x n,
  F.injR (pow up x n) >= (F.injR x)^n.
Proof.
  intros x n.
  remember (F.leb F.null x) as b. destruct b.
  - assert (0 <= injR x). {
      rewrite <- null_spec. now apply F.leb_spec. }
    unfold pow. rewrite <- Heqb. simpl. apply pow_pos_up_spec.
    now apply Rle_ge.
  - assert (injR x <= 0) as Hxle0. {
      rewrite <- null_spec. apply Rge_le, Rgt_ge. now apply leb_false_spec. }
    destruct (Nat.Even_Odd_dec n) as [He|Ho].
    -- unfold pow.
       rewrite <- Heqb.
       rewrite -> (proj2 (Nat.even_spec n) He).
       destruct He as [m Hm].
       replace (Nat.div2 n) with m.
       rewrite -> Hm.
       rewrite -> pow_Rsqr, Rsqr_def.
       transitivity (Rpow (injR (mul up x x)) m).
       --- apply pow_pos_up_spec.
           transitivity ((injR x) * (injR x)).
           now apply mul_up_spec.
           apply Rle_ge; now apply Rmult_mult_nonneg.
       --- apply Rle_ge; apply pow_incr.
           split. now apply Rmult_mult_nonneg. now apply mul_up_le_spec.
       --- rewrite -> Hm. symmetry; now apply Nat.div2_even.
    -- unfold pow.
       rewrite <- Heqb.
       assert (Nat.even n = false) as Hnev. {
         rewrite <- Nat.negb_odd. apply Bool.negb_false_iff. now apply Nat.odd_spec. }
       rewrite -> Hnev.
       destruct Ho as [m Hm].
       replace (Nat.div2 n) with m.
       rewrite -> Hm.
       rewrite -> pow_add, Rmult_comm.
       rewrite -> pow_1.
       transitivity ((injR x) * injR ((pow_pos down (mul down x x) m))).
       now apply mul_up_spec.
       apply Rle_ge; apply Rmult_le_opp_compat_l. exact Hxle0.
       rewrite -> pow_Rsqr, Rsqr_def.
       transitivity (Rpow (injR (mul down x x)) m).
       --- apply pow_pos_down_spec.
             now apply mul_self_down_pos.
       --- apply pow_incr.
           split. apply Rge_le; now apply mul_self_down_pos.
           now apply mul_down_spec.
       --- rewrite -> Hm. symmetry.
           replace ((2*m+1)%nat) with (S (2*m)%nat).
           now apply Nat.div2_succ_double.
           symmetry; now apply Nat.add_1_r.
Qed.

Lemma pow_up_le_spec : forall x n,
  (F.injR x)^n <= F.injR (pow up x n).
Proof. intros x n; apply Rge_le; now apply pow_up_spec. Qed.

Lemma pow_down_spec : forall x n,
  F.injR (pow down x n) <= (F.injR x)^n.
Proof.
  intros x n.
  remember (F.leb F.null x) as b. destruct b.
  - assert (0 <= injR x). {
      rewrite <- null_spec. now apply F.leb_spec. }
    unfold pow. rewrite <- Heqb. simpl. apply pow_pos_down_spec.
    now apply Rle_ge.
  - assert (injR x <= 0) as Hxle0. {
      rewrite <- null_spec. apply Rge_le, Rgt_ge. now apply leb_false_spec. }
    destruct (Nat.Even_Odd_dec n) as [He|Ho].
    -- unfold pow.
       rewrite <- Heqb.
       rewrite -> (proj2 (Nat.even_spec n) He).
       destruct He as [m Hm].
       replace (Nat.div2 n) with m.
       rewrite -> Hm.
       rewrite -> pow_Rsqr, Rsqr_def.
       transitivity (Rpow (injR (mul down x x)) m).
       --- apply pow_pos_down_spec.
           now apply mul_self_down_pos.
       --- apply pow_incr.
           split. apply Rge_le; now apply mul_self_down_pos.
           now apply mul_down_spec.
       --- rewrite -> Hm; symmetry; now apply Nat.div2_even.
    -- unfold pow.
       rewrite <- Heqb.
       assert (Nat.even n = false) as Hnev. {
         rewrite <- Nat.negb_odd. apply Bool.negb_false_iff. now apply Nat.odd_spec. }
       rewrite -> Hnev.
       destruct Ho as [m Hm].
       replace (Nat.div2 n) with m.
       rewrite -> Hm.
       rewrite -> pow_add, Rmult_comm.
       rewrite -> pow_1.
       transitivity ((injR x) * injR ((pow_pos up (mul up x x) m))).
       now apply mul_down_spec.
       apply Rmult_le_opp_compat_l. exact Hxle0.
       rewrite -> pow_Rsqr, Rsqr_def.
       transitivity (Rpow (injR (mul up x x)) m).
       --- apply pow_incr.
           split. now apply Rmult_mult_nonneg.
           now apply mul_up_le_spec.
       --- apply Rge_le; apply pow_pos_up_spec.
           transitivity ((injR x) * (injR x)).
           now apply mul_up_spec.
           apply Rle_ge; now apply Rmult_mult_nonneg.
       --- rewrite -> Hm. symmetry.
           replace ((2*m+1)%nat) with (S (2*m)%nat).
           now apply Nat.div2_succ_double.
           symmetry; now apply Nat.add_1_r.
Qed.



Lemma val_near_up_abs_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= Rdist (F.injR (x up)) y.
Proof.
  intros x y H.
  specialize (H near).
  apply H.
Qed.

Lemma val_near_down_abs_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= Rdist (F.injR (x down)) y.
Proof.
  intros x y H.
  apply (H near).
Qed.

Lemma val_near_up_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= F.injR (x up) - y.
Proof.
  intros x y H.
  apply Rle_trans with (Rdist (F.injR (x up)) y).
  - apply val_near_up_abs_spec; exact H.
  - unfold Rdist. rewrite Rabs_pos_eq.
    -- apply Rle_refl.
    -- apply Rge_le. apply Rge_minus. apply (H up).
Qed.

Lemma val_near_down_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= y - F.injR (x down).
Proof.
  intros x y H.
  apply Rle_trans with (Rabs (F.injR (x down) - y)).
  - apply val_near_down_abs_spec; exact H.
  - rewrite -> Rabs_minus_sym. rewrite Rabs_pos_eq.
    -- apply Rle_refl.
    -- apply Rge_le. apply Rge_minus. apply Rle_ge. apply (H down).
Qed.


Lemma val_near_up_down_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= ( F.injR (x up) - F.injR (x down) ) / 2.
Proof.
  intros x y H. unfold Rdist.
  apply Rmult_le_reg_l with 2. exact Rlt_0_2.
  stepr ( (F.injR (x up) - y) + (y - F.injR (x down)) ) by field.
  - stepl ( Rabs (F.injR (x near) - y) + Rabs (F.injR (x near) - y) ) by ring.
    apply Rplus_le_compat.
    -- apply val_near_up_spec; exact H.
    -- apply val_near_down_spec; exact H.
Qed.

Lemma op_near_up_down_sub_up_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= F.injR (F.sub up (x up) (x down)) / 2%R.
Proof.
  intros x y H.
  apply Rle_trans with (((F.injR (x up))-(F.injR (x down)))/2).
  apply val_near_up_down_spec; exact H.
  apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_pos; exact Rlt_0_2|].
  apply Rge_le. apply sub_up_spec.
Qed.

Lemma val_near_up_down_sub_hlf_up_spec : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= F.injR (F.div2 up (F.sub up (x up) (x down))).
Proof.
  intros x y H.
  apply Rle_trans with ((F.injR (F.sub up (x up) (x down)))/2).
  apply op_near_up_down_sub_up_spec; exact H.
  assert (F.injR (F.of_nat 2%nat) = 2) as H2. {
    rewrite -> ninjr_spec. reflexivity. }
  assert (F.injR (F.of_nat 2%nat) <> 0%R) as H2ne0. {
    rewrite -> ninjr_spec. apply not_O_S_INR. }
  replace (2) with (F.injR (F.of_nat 2)).
  apply Rge_le; unfold F.div2; apply div_up_spec; apply H2ne0.
Qed.

(*
Lemma val_near_up_down_sub_hlf_up_spec' : forall x y, (forall rnd, nullary_op_is_rounded x y rnd) ->
  Rdist (F.injR (x near)) y <= F.injR (F.div2 up (F.sub up (x up) (x down))).
Proof.
  intros x y Hrnd.
  assert (F.injR (x down) <= y) as Hd. { exact (Hrnd down). }
  assert (forall w, Rdist (F.injR (x near)) y <= Rdist (F.injR w) y) as Hn. { exact (Hrnd near). }
  assert (F.injR (x up) >= y) as Hu. { exact (Hrnd up). }
  assert (2<>0) as Hneq_2_0. { apply not_eq_sym. apply Rlt_not_eq. exact Rlt_0_2. }
  apply Rle_trans with ((F.injR (x up) - F.injR (x down))/2).
  - apply Rmult_le_reg_r with (2) ; [exact Rlt_0_2|].
    unfold Rdiv. rewrite -> Rmult_assoc. rewrite -> Rinv_l; [|exact Hneq_2_0]. rewrite -> Rmult_1_r.
    replace (F.injR (x up) - F.injR (x down)) with (Rdist (F.injR (x up)) y + Rdist (F.injR (x down)) y).
    rewrite -> Rmult_comm. rewrite -> double.
    apply Rplus_le_compat; apply Hn.
    unfold Rdist.
    rewrite -> Rabs_pos_eq. rewrite -> Rabs_neg_eq. ring.
    apply Rle_minus; exact Hd.
    apply Rle_Rminus_zero. apply Rge_le. exact Hu.
  - apply Rge_le.
    apply Rge_trans with (F.injR (F.sub up (x up) (x down)) / F.injR (F.of_nat 2)).
    -- unfold F.div2; apply div_up_spec; [rewrite -> ninjr_spec; trivial].
    -- rewrite -> ninjr_spec.
       replace (INR 2%nat) with (2%R); [|trivial].
       apply Rmult_ge_compat_r; [apply Rle_ge; apply Rlt_le; apply pos_half_prf|].
       apply sub_up_spec.
Qed.
*)

Lemma op_near_up_down_sub_hlf_up_spec : forall fval x1 x2,
    Rdist (F.injR  (F.apply fval near x1 x2)) (Rapply fval (F.injR x1) (F.injR x2))
      <=  F.injR (F.div2 up (F.sub up (F.apply fval up x1 x2) (F.apply fval down x1 x2))).
Proof.
  intros fval x1 x2.
  apply (val_near_up_down_sub_hlf_up_spec (fun rnd => F.apply fval rnd x1 x2) (Rapply fval (F.injR x1) (F.injR x2))).
  unfold nullary_op_is_rounded; destruct rnd; destruct fval; simpl.
  - apply (add_down_spec x1 x2).
  - apply (sub_down_spec x1 x2).
  - apply (mul_down_spec x1 x2).
  - apply (add_near_spec x1 x2).
  - apply (sub_near_spec x1 x2).
  - apply (mul_near_spec x1 x2).
  - apply (add_up_spec   x1 x2).
  - apply (sub_up_spec   x1 x2).
  - apply (mul_up_spec   x1 x2).
Qed.

Lemma div_near_up_down_sub_hlf_up_spec : forall x1 x2, (F.injR x2 <> 0) ->
  Rdist (F.injR  (F.div near x1 x2)) (Rdiv (F.injR x1) (F.injR x2))
    <=  F.injR (F.div2 up (F.sub up (F.div up x1 x2) (F.div down x1 x2))).
Proof.
  intros x1 x2 Hx2.
  apply (val_near_up_down_sub_hlf_up_spec (fun rnd => F.div rnd x1 x2) (Rdiv (F.injR x1) (F.injR x2))).
  intros rnd; apply div_rounded_spec; exact Hx2.
Qed.

Lemma rec_near_up_down_sub_hlf_up_spec : forall x, (F.injR x <> 0) ->
  Rdist (F.injR  (F.rec near x)) (Rinv (F.injR x))
    <=  F.injR (F.div2 up (F.sub up (F.rec up x) (F.rec down x))).
Proof.
  intros x Hx.
  apply (val_near_up_down_sub_hlf_up_spec (fun rnd => F.rec rnd x) (Rinv (F.injR x))).
  intros rnd; apply rec_rounded_spec; exact Hx.
Qed.


Lemma add_down_step : forall x1 x2 r1 r2,
  F.injR x1 <= r1 -> F.injR x2 <= r2
    -> F.injR (F.add down x1 x2) <= (r1 + r2).
Proof. intros x1 x2 r1 r2 Hx1 Hx2.
  transitivity ((F.injR x1) + (F.injR x2)).
  now apply F.add_down_spec.
  now apply Rplus_le_compat.
Qed.

Lemma add_up_step : forall x1 x2 r1 r2,
  r1 <= F.injR x1 -> r2 <= F.injR x2
    -> r1 + r2 <= F.injR (F.add up x1 x2).
Proof. intros x1 x2 r1 r2 Hx1 Hx2.
  transitivity ((F.injR x1) + (F.injR x2)).
  now apply Rplus_le_compat.
  now apply add_up_le_spec.
Qed.

Lemma sub_down_step : forall x1 x2 r1 r2,
  F.injR x1 <= r1 -> r2 <= F.injR x2
    -> F.injR (F.sub down x1 x2) <= (r1 - r2).
Proof. intros x1 x2 r1 r2 Hx1 Hx2.
  transitivity ((F.injR x1) - (F.injR x2)).
  now apply F.sub_down_spec.
  now apply Rminus_le_compat.
Qed.

Lemma sub_up_step : forall x1 x2 r1 r2,
  r1 <= F.injR x1 -> F.injR x2 <= r2
    -> r1 - r2 <= F.injR (F.sub up x1 x2).
Proof. intros x1 x2 r1 r2 Hx1 Hx2.
  transitivity ((F.injR x1) - (F.injR x2)).
  now apply Rminus_le_compat.
  now apply sub_up_le_spec.
Qed.

Lemma mul_up_step : forall x1 x2 r1 r2,
  0 <= r1 -> 0 <= r2 -> r1 <= F.injR x1 -> r2 <= F.injR x2
    -> r1 * r2 <= F.injR (F.mul up x1 x2).
Proof. intros x1 x2 r1 r2 Hp1 Hp2 Hx1 Hx2.
  transitivity ((F.injR x1) * (F.injR x2)).
  now apply Rmult_le_compat.
  now apply mul_up_le_spec.
Qed.

Lemma mul_down_step : forall x1 x2 r1 r2,
  0 <= F.injR x1 -> 0 <= F.injR x2 -> F.injR x1 <= r1 -> F.injR x2 <= r2
    -> F.injR (F.mul down x1 x2) <= r1 * r2.
Proof. intros x1 x2 r1 r2 Hp1 Hp2 Hx1 Hx2.
  transitivity ((F.injR x1) * (F.injR x2)).
  now apply mul_down_spec.
  now apply Rmult_le_compat.
Qed.

Lemma div_down_step : forall x1 x2 r1 r2,
  0 <= F.injR x1 -> 0 < r2 -> F.injR x1 <= r1 -> r2 <= F.injR x2
    -> F.injR (F.div down x1 x2) <= r1 / r2.
Proof. intros x1 x2 r1 r2 Hp1 Hp2 Hx1 Hx2.
  transitivity ((F.injR x1) / (F.injR x2)).
  - apply div_down_spec.
    apply Rgt_not_eq. apply Rlt_gt. apply (Rlt_le_trans _ r2). exact Hp2. exact Hx2.
  - rewrite -> Rdiv_def. apply Rmult_le_compat.
    -- exact Hp1.
    -- apply Rlt_le; apply Rinv_pos. apply (Rlt_le_trans _ r2).
       exact Hp2. exact Hx2.
    -- exact Hx1.
    -- apply Rinv_le_contravar.
       exact Hp2. exact Hx2.
Qed.

Lemma div_up_step : forall x1 x2 r1 r2,
  0 <= r1 -> 0 < F.injR x2 -> r1 <= F.injR x1 -> F.injR x2 <= r2
    -> r1 / r2 <= F.injR (F.div up x1 x2).
Proof. intros x1 x2 r1 r2 Hp1 Hp2 Hx1 Hx2.
  transitivity ((F.injR x1) / (F.injR x2)).
  - rewrite -> Rdiv_def. apply Rmult_le_compat.
    -- exact Hp1.
    -- apply Rlt_le; apply Rinv_pos. apply (Rlt_le_trans _ (F.injR x2)).
       exact Hp2. exact Hx2.
    -- exact Hx1.
    -- apply Rinv_le_contravar.
       exact Hp2. exact Hx2.
  - apply div_up_le_spec.
    apply Rgt_not_eq. apply Rlt_gt. exact Hp2.
Qed.

Lemma pow_down_step : forall x r n,
  0 <= F.injR x -> F.injR x <= r ->
    F.injR (F.pow down x n) <= Rpow r n.
Proof. intros x r n Hr Hx.
  transitivity (Rpow (F.injR x) n).
  - now apply pow_down_spec.
  - now apply pow_incr.
Qed.

Lemma pow_up_step : forall x r n,
  0 <= r -> r <= F.injR x ->
    Rpow r n <= F.injR (F.pow up x n).
Proof. intros x r n Hr Hx.
  transitivity (Rpow (F.injR x) n).
  - now apply pow_incr.
  - now apply pow_up_le_spec.
Qed.

End Float_defs.

Close Scope R_scope.

End F.

Export F(Float).