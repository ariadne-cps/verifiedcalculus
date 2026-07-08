(******************************************************************************
 *  Numbers/Bounds.v
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
Require Import Floats.
Require Import Analysis.

Module Bnds.

Inductive Bounds {F:Type} {FltF : Float F} :=
  bounds (lower:F) (upper:F).

Arguments Bounds (F) {FltF}.

Check bounds.


Section Bounds_section.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Definition models : Bounds F -> R -> Prop :=
  fun x y => match x with bounds l u => F.injR l <= y /\ y <= F.injR u end.

Definition lower (x : Bounds F) : F := match x with | bounds l _ => l end.
Definition upper (x : Bounds F) : F := match x with | bounds _ u => u end.

Definition of_nat (n : nat) : Bounds F := bounds (F.of_nat n) (F.of_nat n).

Lemma of_nat_correct : forall n, models (of_nat n) (INR n).
Proof.
  intros n. unfold models, of_nat.
  rewrite -> F.ninjr_spec.
  split; exact (Rle_refl n).
Qed.


Definition neg : Bounds F -> Bounds F :=
  fun x => match x with bounds l u => bounds (F.neg u) (F.neg l) end.

Lemma neg_correct :
  forall (x : Bounds F) (y : R),
    models x y -> models (neg x) (-y).
Proof.
  intros x y H.
  destruct x as (l & u).
  unfold models in H;
  unfold models; unfold neg.
  split.
  - rewrite -> F.neg_exact_spec.
    now apply Ropp_le_contravar.
  - rewrite -> F.neg_exact_spec.
    now apply Ropp_le_contravar.
Qed.


Definition add : Bounds F -> Bounds F -> Bounds F :=
  fun x1 x2 =>
    match x1 with bounds l1 u1
      => match x2 with bounds l2 u2
        => bounds (F.add down l1 l2) (F.add up u1 u2) end end.
(*
  fun (bounds l1 u1) (bounds l2 u2) bounds (add down l1 l2) (add up u1 u2).
*)

Lemma add_correct :
  forall (x1 x2 : Bounds F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (add x1 x2) (y1+y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  unfold models in H1,H2;
  unfold models; unfold add.
  split.
  - apply Rle_trans with (r2:=F.injR l1 + F.injR l2).
    -- apply F.add_down_spec.
    -- apply Rplus_le_compat; [apply H1|]; apply H2.
  - apply Rle_trans with (r2:=F.injR u1 + F.injR u2).
    -- apply Rplus_le_compat; [apply H1|]; apply H2.
    -- apply Rge_le; apply F.add_up_spec.
Qed.


Definition sub (x1 x2 : Bounds F) : Bounds F :=
  match x1 with bounds l1 u1 => match x2 with bounds l2 u2
      => bounds (F.sub down l1 u2) (F.sub up u1 l2) end end.

Lemma sub_correct :
  forall (x1 x2 : Bounds F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (sub x1 x2) (y1-y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  unfold models in H1,H2.
  unfold models; unfold sub.
  split.
  - apply Rle_trans with (r2:=F.injR l1 - F.injR u2).
    -- apply F.sub_down_spec.
    -- apply Rminus_le_compat; [apply H1|]; apply H2.
  - apply Rle_trans with (r2:=F.injR u1 - F.injR l2).
    -- apply Rminus_le_compat; [apply H1|]; apply H2.
    -- apply Rge_le; apply F.sub_up_spec.
Qed.


Definition mul (x1 x2 : Bounds F) : Bounds F :=
  match x1 with bounds l1 u1 =>
    match x2 with bounds l2 u2 =>
      if F.leb F.null l1 then
        if F.leb F.null l2 then
          bounds (F.mul down l1 l2) (F.mul up u1 u2)
        else if F.leb u2 F.null then
          bounds (F.mul down u1 l2) (F.mul up l1 u2)
        else
          bounds (F.mul down u1 l2) (F.mul up u1 u2)
      else if F.leb u1 F.null then
        if F.leb F.null l2 then
          bounds (F.mul down l1 u2) (F.mul up u1 l2)
        else if F.leb u2 F.null then
          bounds (F.mul down u1 u2) (F.mul up l1 l2)
        else
          bounds (F.mul down l1 u2) (F.mul up l1 l2)
      else
        if F.leb F.null l2 then
          bounds (F.mul down l1 u2) (F.mul up u1 u2)
        else if F.leb u2 F.null then
          bounds (F.mul down u1 l2) (F.mul up l1 l2)
        else
          bounds (F.min (F.mul down l1 u2) (F.mul down u1 l2))
                 (F.max (F.mul up l1 l2) (F.mul up u1 u2))
    end
  end
.


Local Lemma Fnot_leb :
  forall (x1 x2 : F), (false = F.leb x1 x2) -> (F.injR x2 < F.injR x1).
Proof.
  intros x1 x2. intro H.
  assert (F.injR x1 <= F.injR x2 -> False). {
     intros Hge.
     apply F.leb_spec in Hge.
     destruct (F.leb x1 x2); discriminate.
  }
  now apply Rnot_le_lt.
Qed.

Lemma Fnot_leb_le :
  forall (x1 x2 : F), (false = F.leb x1 x2) -> (F.injR x2 <= F.injR x1).
Proof.
  intros x1 x2 H.
  apply Rlt_le.
  now apply Fnot_leb.
Qed.

Local Lemma Fgeb_0 :
  forall (x:F), (true = F.leb F.null x) -> (0 <= F.injR x).
Proof.
   intro x. intro H.
   replace 0 with (F.injR (F.of_nat 0%nat)) by (apply F.ninjr_spec).
   apply F.leb_spec. apply eq_sym. exact H.
Qed.

Local Lemma Fleb_0 :
  forall (x:F), (true = F.leb x F.null) -> (F.injR x <= 0).
Proof.
   intro x. intro H.
   replace 0 with (F.injR (F.of_nat 0%nat)) by (apply F.ninjr_spec).
   apply F.leb_spec. apply eq_sym. exact H.
Qed.

Local Lemma Fnot_geb_0 :
  forall (x:F), (false = F.leb F.null x) -> (F.injR x <= 0).
Proof.
  intro x. replace 0 with (F.injR (F.of_nat 0%nat)) by (apply F.ninjr_spec). apply Fnot_leb_le.
Qed.

Local Lemma Fnot_leb_0 :
  forall (x:F), (false = F.leb x F.null) -> (0 <= F.injR x).
Proof.
  intro x. replace 0 with (F.injR (F.of_nat 0%nat)) by (apply F.ninjr_spec); apply Fnot_leb_le.
Qed.

Lemma mul_correct :
  forall (x1 x2 : Bounds F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (mul x1 x2) (y1*y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  destruct H1 as (H1l,H1u), H2 as (H2l,H2u);
  remember (conj H1l H1u) as H1; remember (conj H2l H2u) as H2.
  unfold models in H1,H2.
  unfold models.
  unfold mul.
  remember (F.leb F.null l1) as bl1.
  remember (F.leb u1 F.null) as bu1.
  remember (F.leb F.null l2) as bl2.
  remember (F.leb u2 F.null) as bu2.

  destruct bl1.
    (* Cases 0<=l1 *)
    assert (0<=F.injR l1) as Hl1; [apply Fgeb_0; exact Heqbl1|].
    assert (0<=y1) as Hy1 by (apply (Rle_trans _ (F.injR l1) _ Hl1 H1l)).
    assert (0<=F.injR u1) as Hu1 by (apply (Rle_trans _ y1 _ Hy1 H1u)).
    destruct bl2.
    {
      (* Case 0<=l1 /\ 0<=l2 *)
      assert (0<=F.injR l2) as Hl2; [apply Fgeb_0; exact Heqbl2|].
      assert (0<=y2) as Hy2 by (apply (Rle_trans _ (F.injR l2) _ Hl2 H2l)).
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR l2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := (F.injR l1) * y2).
         apply (Rmult_le_compat_l _ _ _ Hl1 H2l).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR u2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := (F.injR u1) * y2).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1u).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2u).
    }
    destruct bu2.
    {
      (* Case 0<=l1 /\ u2<=0 *)
      assert (F.injR u2<=0) as Hu2; [apply Fleb_0; exact Heqbu2|].
      assert (y2<=0) as Hy2. apply Rle_trans with (r2:=F.injR u2). exact H2u. exact Hu2.
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR l2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := (F.injR u1) * y2).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR u2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := (F.injR l1) * y2).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rmult_le_compat_l _ _ _ Hl1 H2u).
    }
    {
      (* Case 0<=l1 /\ l2<0<u2 *)
      assert (F.injR l2<=0) as Hl2; [apply Fnot_geb_0; exact Heqbl2|].
      assert (0<=F.injR u2) as Hu2; [apply Fnot_leb_0; exact Heqbu2|].
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR l2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := y1 * (F.injR l2)).
         apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1u).
         apply (Rmult_le_compat_l _ _ _ Hy1 H2l).
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR u2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := y1 * (F.injR u2)).
         apply (Rmult_le_compat_l _ _ _ Hy1 H2u).
         apply (Rmult_le_compat_r _ _ _ Hu2 H1u).
    }
  destruct bu1.
    (* Cases u1 <= 0 *)
    assert (F.injR u1<=0) as Hu1; [apply Fleb_0; exact Heqbu1|].
    assert (y1<=0) as Hy1. apply Rle_trans with (r2:=F.injR u1). exact H1u. exact Hu1.
    destruct bl2.
    {
      (* Case u1 <= 0 /\ 0 <= l2 *)
      assert (0<=F.injR l2) as Hl2; [apply Fgeb_0; exact Heqbl2|].
      assert (0<=y2) as Hy2. apply Rle_trans with (r2:=F.injR l2). exact Hl2. exact H2l.
      assert (0<=F.injR u2) as Hu2. apply Rle_trans with (r2:=y2). exact Hy2. exact H2u.
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR u2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := y1 * (F.injR u2)).
         apply (Rmult_le_compat_r _ _ _ Hu2 H1l).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2u).
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR l2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := (F.injR u1) * y2).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1u).
         apply (Rmult_le_opp_compat_l _ _ _ Hu1 H2l).
    }
    destruct bu2.
    {
      (* Case u1 <= 0 /\ u2 <= 0 *)
      assert (F.injR u2<=0) as Hu2; [apply Fleb_0; exact Heqbu2|].
      assert (y2<=0) as Hy2. apply Rle_trans with (r2:=F.injR u2). exact H2u. exact Hu2.
      assert (F.injR l2<=0) as Hl2. apply Rle_trans with (r2:=y2). exact H2l. exact Hy2.
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR u2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := (F.injR u1) * y2).
         apply (Rmult_le_opp_compat_l _ _ _ Hu1 H2u).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR l2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := y1 * (F.injR l2)).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1l).
    }
    {
      (* Case u1 <=0 /\ l2 <= 0 <= u2 *)
      assert (F.injR l2<=0) as Hl2; [apply Fnot_geb_0; exact Heqbl2|].
      assert (0<=F.injR u2) as Hu2; [apply Fnot_leb_0; exact Heqbu2|].
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR u2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := y1 * (F.injR u2)).
         apply (Rmult_le_compat_r _ _ _ Hu2 H1l).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2u).
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR l2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := y1 * (F.injR l2)).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1l).
    }

    (* Cases l1 <= 0 <= u1 *)
    assert (F.injR l1<=0) as Hl1; [apply Fnot_geb_0; exact Heqbl1|].
    assert (0<=F.injR u1) as Hu1; [apply Fnot_leb_0; exact Heqbu1|].
    destruct bl2.
    {
      (* Case l1 <= 0 <= u1 /\ 0 <= l2 *)
      assert (0<=F.injR l2) as Hl2; [apply Fgeb_0; exact Heqbl2|].
      assert (0<=y2) as Hy2. apply Rle_trans with (r2:=F.injR l2). apply Hl2. apply H2.
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR u2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := (F.injR l1) * y2).
         apply (Rmult_le_opp_compat_l _ _ _ Hl1 H2u).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR u2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := (F.injR u1) * y2).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1u).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2u).
    }
    destruct bu2.
    {
      (* Case l1 <= 0 <= u1 /\ u2 <= 0 *)
      assert (F.injR u2<=0) as Hu2; [apply Fleb_0; exact Heqbu2|].
      assert (y2<=0) as Hy2. apply Rle_trans with (r2:=F.injR u2). exact H2u. exact Hu2.
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) * (F.injR l2)).
         1: apply F.mul_down_spec.
         apply Rle_trans with (r2 := (F.injR u1) * y2).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (F.injR l1) * (F.injR l2)).
         2: apply F.mul_up_le_spec.
         apply Rle_trans with (r2 := (F.injR l1) * y2).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rmult_le_opp_compat_l _ _ _ Hl1 H2l).
    }
    {
      (* Case l1 <= 0 <= u1 /\ l2 <= 0 <= u2 *)
      assert (F.injR l2<=0) as Hl2; [apply Fnot_geb_0; exact Heqbl2|].
      assert (0<=F.injR u2) as Hu2; [apply Fnot_leb_0; exact Heqbu2|].
      assert (y1 <= 0 \/ 0 <= y1) as Hdisjy1. apply Rle_or_le.
      split.
      -- rewrite-> F.min_exact_spec.
         apply Rle_trans with ( r2 := Rmin ((F.injR l1) * (F.injR u2)) ((F.injR u1) * (F.injR l2)) ).
         assert (F.injR (F.mul down l1 u2) <= F.injR l1 * F.injR u2) as Hl1u2; [apply F.mul_down_spec|].
         assert (F.injR (F.mul down u1 l2) <= F.injR u1 * F.injR l2) as Hu1l2; [apply F.mul_down_spec|].
         apply Rle_min_compat; apply F.mul_down_spec; apply F.mul_down_spec.
         assert (0<=y1 -> F.injR u1 * F.injR l2 <= y1 * y2) as H0ley1. {
           intros Hy1;
           apply Rle_trans with (r2 := y1 * F.injR l2).
           apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1u).
           apply (Rmult_le_compat_l _ _ _ Hy1 H2l).
         }
         assert (y1<=0 -> F.injR l1 * F.injR u2 <= y1 * y2) as H0gey1. {
           intros Hy1.
           apply Rle_trans with (r2 := y1 * F.injR u2).
           apply (Rmult_le_compat_r _ _ _ Hu2 H1l).
           apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2u).
         }
         remember ((F.injR l1)*(F.injR u2)) as wlu.
         remember ((F.injR u1)*(F.injR l2)) as wul.
         assert (0<=y1 -> Rmin wlu wul <= y1 * y2) as Hy1pos. {
           intros Hy1.
           apply Rle_trans with (r2 := wul).
           apply Rmin_r.
           apply H0ley1. exact Hy1.
         }
         assert (y1<=0 -> Rmin wlu wul <= y1 * y2) as Hy1neg. {
           intros Hy1.
           apply Rle_trans with (r2 := wlu).
           apply Rmin_l.
           apply H0gey1. exact Hy1.
         }
         apply (@or_ind (y1<=0) (0<=y1)). exact Hy1neg. exact Hy1pos. exact Hdisjy1.
      -- rewrite-> F.max_exact_spec.
         apply Rle_trans with ( r2 := Rmax ((F.injR l1) * (F.injR l2)) ((F.injR u1) * (F.injR u2)) ).
         assert (F.injR l1 * F.injR l2 <= F.injR (F.mul up l1 l2)) as Hl1l2; [apply Rge_le; apply F.mul_up_spec|].
         assert (F.injR u1 * F.injR u2 <= F.injR (F.mul up u1 u2)) as Hu1u2; [apply Rge_le; apply F.mul_up_spec|].
         2: apply Rle_max_compat. 2: apply F.mul_up_le_spec. 2: apply F.mul_up_le_spec.
         assert (0<=y1 -> y1 * y2 <= F.injR u1 * F.injR u2) as H0ley1. {
           intros Hy1.
           apply Rle_trans with (r2 := y1 * F.injR u2).
           apply (Rmult_le_compat_l _ _ _ Hy1 H2u).
           apply (Rmult_le_compat_r _ _ _ Hu2 H1u).
           (* apply Rmult_le_compat_l. exact Hy1. apply H2.
              apply Rmult_le_compat_r. exact Hu2. apply H1.
            *)
         }
         assert (y1<=0 -> y1 * y2 <= F.injR l1 * F.injR l2) as H0gey1. {
           intros Hy1.
           apply Rle_trans with (r2 := y1 * F.injR l2).
           apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2l).
           apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1l).
           (* apply Rmult_le_opp_compat_l. exact Hy1. apply H2.
            * apply Rmult_le_opp_compat_r. exact Hl2. apply H1.
            *)
         }
         remember ((F.injR l1)*(F.injR l2)) as wll.
         remember ((F.injR u1)*(F.injR u2)) as wuu.
         assert (0<=y1 -> y1 * y2 <= Rmax wll wuu) as Hy1pos. {
           intros Hy1. apply Rle_trans with (r2:=wuu). apply H0ley1. exact Hy1. apply Rmax_r.
         }
         assert (y1<=0 -> y1 * y2 <= Rmax wll wuu) as Hy1neg. {
           intros Hy1. apply Rle_trans with (r2:=wll). apply H0gey1. exact Hy1. apply Rmax_l.
         }
         apply or_ind with (B:=0<=y1) (A:=y1<=0). exact Hy1neg. exact Hy1pos. exact Hdisjy1.
     }
Qed.


Definition div (x1 x2 : Bounds F) : Bounds F :=
  match x1 with bounds l1 u1 =>
    match x2 with bounds l2 u2 =>
      if F.leb F.null l1 then
        if F.leb F.null l2 then
          bounds (F.div down l1 u2) (F.div up u1 l2)
        else
          bounds (F.div down u1 u2) (F.div up l1 l2)
      else if F.leb u1 F.null then
        if F.leb F.null l2 then
          bounds (F.div down l1 l2) (F.div up u1 u2)
        else
          bounds (F.div down u1 l2) (F.div up l1 u2)
      else
        if F.leb F.null l2 then
          bounds (F.div down l1 l2) (F.div up u1 l2)
        else
          bounds (F.div down u1 u2) (F.div up l1 u2)
    end
  end
.

Lemma Ropp_0_lt_contravar : forall r : R, r < 0 <-> 0 < - r.
Proof.
  intro r. split.
  - intro Hlt. apply Ropp_0_gt_lt_contravar. apply Rlt_gt. exact Hlt.
  - intro Hngt. rewrite <- (Ropp_involutive r). apply Ropp_lt_gt_0_contravar. apply Rlt_gt. exact Hngt.
Qed.

(* Rinv_pos : forall r : R, 0 < r -> 0 < / r *)

Lemma Rinv_neg : forall r : R, r < 0 -> / r < 0.
Proof.
  intro r. intro Hlt0.
  rewrite -> Ropp_0_lt_contravar. rewrite <- Rinv_opp. apply Rinv_pos. rewrite <- Ropp_0_lt_contravar. exact Hlt0.
Qed.

Lemma Rinv_le_compat : forall r1 r2 : R, (0 < r1 \/ r2 < 0) -> r1 <= r2 ->  / r2 <=  / r1.
Proof.
  intros r1 r2 Hne0 H.
  destruct Hne0.
  - apply Rinv_le_contravar. exact H0. exact H.
  - apply Ropp_le_cancel. rewrite <- Rinv_opp. rewrite <- Rinv_opp. apply Rinv_le_contravar.
    -- apply Ropp_0_lt_contravar. exact H0.
    -- apply Ropp_le_contravar. exact H.
Qed.

Lemma Rdiv_le_compat_l : forall r r1 r2 : R, 0 <= r -> (0 < r1 \/ r2 < 0) -> r1 <= r2 -> r / r2 <= r / r1.
Proof.
  intros r r1 r2 Hge0 Hor H. unfold Rdiv.
  apply Rmult_le_compat_l; [apply Hge0|]. exact (Rinv_le_compat _ _ Hor H).
Qed.

Lemma Rdiv_le_compat_r : forall r r1 r2 : R, 0 < r -> r1 <= r2 -> r1 / r <= r2 / r.
Proof.
  intros r r1 r2 Hgt0 H. unfold Rdiv.
  apply Rmult_le_compat_r. { apply Rlt_le. apply Rinv_pos. exact Hgt0. } exact H.
Qed.

Lemma Rdiv_le_opp_compat_l : forall r r1 r2 : R, r <= 0 -> (0 < r1 \/ r2 < 0) -> r1 <= r2 -> r / r1 <= r / r2.
Proof.
  intros r r1 r2 Hle0 Hor H. unfold Rdiv.
  apply Rmult_le_opp_compat_l; [apply Hle0|]. exact (Rinv_le_compat _ _ Hor H).
Qed.

Lemma Rdiv_le_opp_compat_r : forall r r1 r2 : R, r < 0 -> r1 <= r2 -> r2 / r <= r1 / r.
Proof.
  intros r r1 r2 Hlt0 H. unfold Rdiv.
  apply Rmult_le_opp_compat_r. { apply Rlt_le. apply Rinv_neg. exact Hlt0. } exact H.
Qed.

Lemma Rle_not_eq_lt : forall r : R, r<=0 -> r<>0 -> r<0.
Proof.
  unfold Rle. intros r Hle0 Hne0.
  apply or_ind with (A:=r<0) (B:=r=0).
  - trivial.
  - intro Heq0. contradiction.
  - exact Hle0.
Qed.

Lemma Rge_not_eq_gt : forall r : R, 0<=r -> r<>0 -> 0<r.
Proof.
  unfold Rle. intros r Hge0 Hne0.
  apply or_ind with (A:=0<r) (B:=0=r).
  - trivial.
  - intro Heq0. assert (r=0). { apply eq_sym. exact Heq0. } contradiction.
  - exact Hge0.
Qed.

Local Lemma Fdiv_up_le : forall (x1 x2 : F),
  (F.injR x2 <> 0) -> (F.injR x1) / (F.injR x2) <= F.injR (F.div up x1 x2).
Proof.
  intros x1 x2 Hne0. apply Rge_le. apply F.div_up_spec. exact Hne0.
Qed.

Lemma div_correct :
  forall (x1 x2 : Bounds F) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> (0 < F.injR (lower x2) \/ F.injR (upper x2) < 0) -> models (div x1 x2) (y1/y2).
Proof.
  intros x1 x2 y1 y2 H1 H2 Hor.
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  destruct H1 as (H1l,H1u), H2 as (H2l,H2u);
  remember (conj H1l H1u) as H1; remember (conj H2l H2u) as H2.
  unfold lower in Hor; unfold upper in Hor.
  unfold models in H1,H2.
  unfold models.
  unfold div.
  remember (F.leb F.null l1) as bl1.
  remember (F.leb u1 F.null) as bu1.
  remember (F.leb F.null l2) as bl2.
  remember (F.leb u2 F.null) as bu2.

  assert (0 < y2 \/ F.injR u2 < 0) as Horu. {
    apply or_ind with (A:=0<F.injR l2) (B:=F.injR u2<0).
    - intro Hl2gt0. left. apply Rlt_le_trans with (r2:=F.injR l2). exact Hl2gt0. exact H2l.
    - intro Hu2lt0. right. exact Hu2lt0.
    - exact Hor.
  }
  assert (0 < F.injR l2 \/ y2 < 0) as Horl. {
    apply or_ind with (A:=0<F.injR l2) (B:=F.injR u2<0).
    - intro Hl2gt0. left. exact Hl2gt0.
    - intro Hu2lt0. right. apply Rle_lt_trans with (r2:=F.injR u2). exact H2u. exact Hu2lt0.
    - exact Hor.
  }
  assert (F.injR l2 <= F.injR u2) as Hl2leu2. { apply Rle_trans with (r2:=y2). exact H2l. exact H2u. }

  assert (F.injR l2 <> 0%R) as Hl2ne0. {
    apply or_ind with (A:= 0 < F.injR l2) (B:=F.injR u2 < 0).
    - intro Hl2gt0. apply Rgt_not_eq. apply Rlt_gt. exact Hl2gt0.
    - intro Hu2lt0. apply Rlt_not_eq. apply Rle_lt_trans with (r2:=F.injR u2). exact Hl2leu2. exact Hu2lt0.
    - exact Hor.
  }
  assert (F.injR u2 <> 0%R) as Hu2ne0. {
    apply or_ind with (A:= 0 < F.injR l2) (B:=F.injR u2 < 0).
    - intro Hl2gt0. apply Rgt_not_eq. apply Rlt_gt. apply Rlt_le_trans with (r2:=F.injR l2). exact Hl2gt0. exact Hl2leu2.
    - intro Hu2lt0. apply Rlt_not_eq. exact Hu2lt0.
    - exact Hor.
  }

  destruct bl2.
    (* Cases 0<l2 *)
    assert (0<=F.injR l2) as Hl2'; [apply Fgeb_0; exact Heqbl2|].
    assert (0<F.injR l2) as Hl2. { apply Rge_not_eq_gt. exact Hl2'. exact Hl2ne0. }
    assert (0<y2) as Hy2 by (apply (Rlt_le_trans _ (F.injR l2) _ Hl2 H2l)).
    assert (0<F.injR u2) as Hu2. apply Rlt_le_trans with (r2:=y2). exact Hy2. exact H2u.

    destruct bl1.
    {
      (* Case 0<=l1 /\ 0<l2 *)
      assert (0<=F.injR l1) as Hl1; [apply Fgeb_0; exact Heqbl1|].
      assert (0<=y1) as Hy1 by (apply (Rle_trans _ (F.injR l1) _ Hl1 H1l)).
      assert (0<=F.injR u1) as Hu1 by (apply (Rle_trans _ y1 _ Hy1 H1u)).
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) / (F.injR u2)).
         1: apply F.div_down_spec.
         1: apply Hu2ne0.
         apply Rle_trans with (r2 := (F.injR l1) / y2).
         apply (Rdiv_le_compat_l _ _ _ Hl1 Horu H2u).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (F.injR u1) / (F.injR l2)).
         2: apply Fdiv_up_le.
         2: apply Hl2ne0.
         apply Rle_trans with (r2 := (F.injR u1) / y2).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1u).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horl H2l).
    }
    destruct bu1.
    {
      (* Case u1 <= 0 /\ 0 < l2 *)
      assert (F.injR u1<=0) as Hu1; [apply Fleb_0; exact Heqbu1|].
      assert (y1<=0) as Hy1. apply Rle_trans with (r2:=F.injR u1). exact H1u. exact Hu1.
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) / (F.injR l2)).
         1: apply F.div_down_spec.
         1: apply Hl2ne0.
         apply Rle_trans with (r2 := y1 / (F.injR l2)).
         apply (Rdiv_le_compat_r _ _ _ Hl2 H1l).
         apply (Rdiv_le_opp_compat_l _ _ _ Hy1 Horl H2l).
      -- apply Rle_trans with (r2 := (F.injR u1) / (F.injR u2)).
         2: apply Fdiv_up_le.
         2: apply Hu2ne0.
         apply Rle_trans with (r2 := (F.injR u1) / y2).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1u).
         apply (Rdiv_le_opp_compat_l _ _ _ Hu1 Horu H2u).
    }
    {
      (* Case l1 <= 0 <= u1 /\ 0 < l2 *)
      assert (F.injR l1<=0) as Hl1; [apply Fnot_geb_0; exact Heqbl1|].
      assert (0<=F.injR u1) as Hu1; [apply Fnot_leb_0; exact Heqbu1|].
      split.
      -- apply Rle_trans with (r2 := (F.injR l1) / (F.injR l2)).
         1: apply F.div_down_spec.
         1: apply Hl2ne0.
         apply Rle_trans with (r2 := (F.injR l1) / y2).
         apply (Rdiv_le_opp_compat_l _ _ _ Hl1 Horl H2l).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (F.injR u1) / (F.injR l2)).
         2: apply Fdiv_up_le.
         2: apply Hl2ne0.
         apply Rle_trans with (r2 := (F.injR u1) / y2).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1u).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horl H2l).
    }

  destruct bu2.
    (* Cases u2<0 *)
    assert (F.injR u2<=0) as Hu2'; [apply Fleb_0; exact Heqbu2|].
    assert (F.injR u2<0) as Hu2. { apply Rle_not_eq_lt. exact Hu2'. exact Hu2ne0. }
    assert (y2<0) as Hy2. apply Rle_lt_trans with (r2:=F.injR u2). exact H2u. exact Hu2.
    assert (F.injR l2<0) as Hl2. apply Rle_lt_trans with (r2:=y2). exact H2l. exact Hy2.

    destruct bl1.
    {
      (* Case 0<=l1 /\ u2<0 *)
      assert (0<=F.injR l1) as Hl1; [apply Fgeb_0; exact Heqbl1|].
      assert (0<=y1) as Hy1 by (apply (Rle_trans _ (F.injR l1) _ Hl1 H1l)).
      assert (0<=F.injR u1) as Hu1 by (apply (Rle_trans _ y1 _ Hy1 H1u)).
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) / (F.injR u2)).
         1: apply F.div_down_spec.
         1: apply Hu2ne0.
         apply Rle_trans with (r2 := (F.injR u1) / y2).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horu H2u).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (F.injR l1) / (F.injR l2)).
         2: apply Fdiv_up_le.
         2: apply Hl2ne0.
         apply Rle_trans with (r2 := (F.injR l1) / y2).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rdiv_le_compat_l _ _ _ Hl1 Horl H2l).
    }
    destruct bu1.
    {
      (* Case u1<=0 /\ u2<0 *)
      assert (F.injR u1<=0) as Hu1; [apply Fleb_0; exact Heqbu1|].
      assert (y1<=0) as Hy1. apply Rle_trans with (r2:=F.injR u1). exact H1u. exact Hu1.
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) / (F.injR l2)).
         1: apply F.div_down_spec.
         1: apply Hl2ne0.
         apply Rle_trans with (r2 := (F.injR u1) / y2).
         apply (Rdiv_le_opp_compat_l _ _ _ Hu1 Horl H2l).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (F.injR l1) / (F.injR u2)).
         2: apply Fdiv_up_le.
         2: apply Hu2ne0.
         apply Rle_trans with (r2 := y1 / (F.injR u2)).
         apply (Rdiv_le_opp_compat_l _ _ _ Hy1 Horu H2u).
         apply (Rdiv_le_opp_compat_r _ _ _ Hu2 H1l).
    }
    {
      (* Case l1 <= 0 <= u1 /\ u2 < 0 *)
      assert (F.injR l1<=0) as Hl1; [apply Fnot_geb_0; exact Heqbl1|].
      assert (0<=F.injR u1) as Hu1; [apply Fnot_leb_0; exact Heqbu1|].
      split.
      -- apply Rle_trans with (r2 := (F.injR u1) / (F.injR u2)).
         1: apply F.div_down_spec.
         1: apply Hu2ne0.
         apply Rle_trans with (r2 := (F.injR u1) / y2).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horu H2u).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (F.injR l1) / (F.injR u2)).
         2: apply Fdiv_up_le.
         2: apply Hu2ne0.
         apply Rle_trans with (r2 := (F.injR l1) / y2).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rdiv_le_opp_compat_l _ _ _ Hl1 Horu H2u).
    }

    {
      (* Cases l2<0<u2 *)
      assert (F.injR l2<=0) as Hl2; [apply Fnot_geb_0; exact Heqbl2|].
      assert (0<=F.injR u2) as Hu2; [apply Fnot_leb_0; exact Heqbu2|].
      assert (False). {
        apply or_ind with (A:=0<F.injR l2) (B:=F.injR u2<0).
        - apply Rle_not_lt. exact Hl2.
        - apply Rle_not_lt. exact Hu2.
        - exact Hor.
      }
      contradiction.
    }
Qed.


Definition rec (x : Bounds F) : Bounds F :=
  match x with bounds l u =>
    bounds (F.rec down u) (F.rec up l)
  end
.

Lemma rec_correct :
  forall (x : Bounds F) (y : R),
    models x y -> (0 < F.injR (lower x) \/ F.injR (upper x) < 0) -> models (rec x) (/y).
Proof.
  intros x y H Hor.
  destruct x as (l & u).
  destruct H as (Hl,Hu).
  remember (conj Hl Hu) as H.
  unfold lower in Hor; unfold upper in Hor.
  unfold models.
  unfold rec.
  assert (F.injR l <= F.injR u) as Hlleu. {
    apply Rle_trans with (r2:=y). exact Hl. exact Hu. }
  destruct Hor as [H0ltl|Hult0].
  - assert (0 < y) as H0lty. {
      apply Rlt_le_trans with (r2:=F.injR l). exact H0ltl. exact Hl. }
    assert (F.injR l <> 0%R) as Hlne0. {
      apply Rgt_not_eq. apply Rlt_gt. exact H0ltl. }
    assert (F.injR u <> 0%R) as Hune0. {
      apply Rgt_not_eq. apply Rlt_gt. apply Rlt_le_trans with (r2:=F.injR l). exact H0ltl. exact Hlleu. }
    split.
    -- transitivity (/ F.injR u).
       apply F.rec_down_spec. exact Hune0.
       apply Rinv_le_contravar. exact H0lty. exact Hu.
    -- transitivity (/ F.injR l).
       apply Rinv_le_contravar. exact H0ltl. exact Hl.
       apply Rge_le; apply F.rec_up_spec. exact Hlne0.
  - assert (y < 0) as Hylt0. {
      apply Rle_lt_trans with (r2:=F.injR u). exact Hu. exact Hult0. }
    assert (F.injR u <> 0%R) as Hune0. {
      apply Rlt_not_eq. exact Hult0. }
    assert (F.injR l <> 0%R) as Hlne0. {
      apply Rlt_not_eq. apply Rle_lt_trans with (r2:=F.injR u). exact Hlleu. exact Hult0. }
    split.
    -- transitivity (/ F.injR u).
       apply F.rec_down_spec. exact Hune0.
       apply Rinv_le_compat. right. exact Hult0. exact Hu.
    -- transitivity (/ F.injR l).
       apply Rinv_le_compat. right. exact Hylt0. exact Hl.
       apply Rge_le; apply F.rec_up_spec. exact Hlne0.
Qed.


Fixpoint pow (x : Bounds F) (n:nat) : Bounds F :=
  match n with
  | O => bounds F.unit F.unit
  | S m => mul x (pow x m)
  end.

Lemma pow_succ : forall x n, pow x (S n) = mul x (pow x n).
Proof. intros. simpl. auto. Qed.

Lemma pow_correct : forall (x : Bounds F) (n:nat) (y : R),
    models x y -> models (pow x n) (Rpow y n).
Proof.
  intros x n y H.
  induction n as [|n Hn].
  - simpl. unfold F.unit.
    rewrite -> F.ninjr_spec.
    split; apply Rle_refl.
  - rewrite -> pow_succ.
    replace (y ^ (S n)) with (y * y^n).
    apply mul_correct; [exact H|exact Hn].
    rewrite <- Nat.add_1_l.
    rewrite -> Rdef_pow_add.
    rewrite -> pow_1.
    reflexivity.
Qed.


Definition mag (x : Bounds F) : F :=
  F.max (F.neg (lower x)) (upper x).

Lemma mag_correct : forall x r, models x r -> Rabs r <= F.injR (mag x).
Proof.
  unfold models, mag.
  intros x r Hxr.
  destruct x as [l u]; simpl.
  rewrite -> F.max_exact_spec, F.neg_exact_spec.
  set (F.injR l) as yl; set (F.injR u) as yu.
  destruct (Rle_or_le r 0) as [Hrle0|H0ler].
  - rewrite -> Rabs_neg_eq. transitivity (-yl).
    apply Ropp_le_contravar; exact (proj1 Hxr). exact (Rmax_l _ _). exact Hrle0.
  - rewrite -> Rabs_pos_eq. transitivity yu.
    exact (proj2 Hxr). exact (Rmax_r _ _). exact H0ler.
Qed.


Lemma sig_log2_up : forall (x : F), { n : nat | (2 : R) ^ n > F.injR (F.abs x) }.
Proof.
  intro x.
  set (y := F.injR (F.abs x)).
  pose proof (INR_unbounded y) as Hy.
  apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat_direct in Hy.
  - destruct Hy as [n Hyn].
    set (m := Nat.log2_up n).
    assert (0 <= m)%nat as H0lem by now apply Nat.le_0_l.
    exists m.
    apply (Rge_gt_trans _ n _).
    -- apply Rle_ge.
       replace (Rpow 2 m) with (INR (Nat.pow 2 m)) by now apply pow_INR.
       apply le_INR.
       destruct (Nat.eq_0_gt_0_cases n).
       --- rewrite -> H; now apply Nat.le_0_l.
       --- unfold m. apply Nat.log2_up_le_pow2. exact H. now apply Nat.le_refl.
    -- assumption.
  - intro n.
    remember (F.leb (F.of_nat n) (F.abs x)) as b.
    destruct b.
    -- right.
       apply Rle_not_gt.
       apply eq_sym in Heqb.
       apply F.leb_spec in Heqb.
       unfold y.
       rewrite <- F.ninjr_spec.
       exact Heqb.
    -- left.
       apply Rlt_gt.
       apply Fnot_leb in Heqb.
       unfold y.
       rewrite <- F.ninjr_spec.
       exact Heqb.
Qed.


Axiom Fhlf : F -> F.
Axiom Fhlf_exact_spec : forall x, F.injR (Fhlf x) = (F.injR x) / 2.
Axiom Fsub_down_less : forall u, F.injR u < 1 -> F.injR (F.sub down F.unit u) > 0.

Definition sqr : Bounds F -> Bounds F :=
  fun x => match x with bounds l u =>
    if F.leb F.null l then
      bounds (F.mul down l l) (F.mul up u u)
    else if F.leb u F.null then
      bounds (F.mul down u u) (F.mul up l l)
    else
      bounds (F.null) (F.max (F.mul up l l) (F.mul up u u))
  end.

Lemma sqr_correct : forall x y, models x y -> models (sqr x) (Rsqr y).
Proof.
  intros x y H. destruct x as (l & u). destruct H as [Hl Hu].
  unfold sqr, models in *.
  remember (F.leb F.null l) as bl.
  remember (F.leb u F.null) as bu.
  destruct bl.
  2: destruct bu.
  - assert (0 <= F.injR l) as Hl0. apply Fgeb_0. exact Heqbl.
    assert (0 <= y) as Hy0. transitivity (F.injR l); assumption.
    split.
    -- transitivity (Rsqr (F.injR l)).
       rewrite -> Rsqr_def. apply F.mul_down_spec.
       apply Rsqr_pos_incr. exact Hl0. exact Hl.
    -- transitivity (Rsqr (F.injR u)).
       apply Rsqr_pos_incr. exact Hy0. exact Hu.
       rewrite -> Rsqr_def. apply F.mul_up_le_spec.
  - assert (F.injR u <= 0) as Hu0. apply Fleb_0. exact Heqbu.
    assert (y <= 0) as Hy0. transitivity (F.injR u); assumption.
    split.
    -- transitivity (Rsqr (F.injR u)).
       rewrite -> Rsqr_def. apply F.mul_down_spec.
       apply Rsqr_neg_decr. exact Hu0. exact Hu.
    -- transitivity (Rsqr (F.injR l)).
       apply Rsqr_neg_decr. exact Hy0. exact Hl.
       rewrite -> Rsqr_def. apply F.mul_up_le_spec.
  - assert (F.injR l <= 0) as Hl0. apply Fnot_geb_0. exact Heqbl.
    assert (0 <= F.injR u) as Hu0. apply Fnot_leb_0. exact Heqbu.
    split.
    -- rewrite -> F.null_spec. exact (Rle_0_sqr y).
    -- rewrite -> Rsqr_def.
       rewrite -> F.max_exact_spec.
       destruct (Rle_or_le y 0) as [Hyle0|H0ley].
       --- transitivity (F.injR (F.mul up l l)).
           transitivity (Rsqr (F.injR l)).
           ---- apply Rsqr_neg_decr. exact Hyle0. exact Hl.
           ---- rewrite -> Rsqr_def. apply F.mul_up_le_spec.
           ---- now apply Rmax_l.
       --- transitivity (F.injR (F.mul up u u)).
           transitivity (Rsqr (F.injR u)).
           ---- apply Rsqr_pos_incr. exact H0ley. exact Hu.
           ---- rewrite -> Rsqr_def. apply F.mul_up_le_spec.
           ---- now apply Rmax_r.
Qed.


Definition hlf : Bounds F -> Bounds F :=
  fun x => match x with bounds l u => bounds (Fhlf l) (Fhlf u) end.

Lemma hlf_correct : forall x y, models x y -> models (hlf x) (y/2).
Proof.
  intros x y H.
  destruct x as (l,u).
  unfold hlf.
  unfold models in *.
  repeat rewrite -> Fhlf_exact_spec.
  lra.
Qed.

Lemma mag_hlf :
  forall x, (F.injR (mag (hlf x))) = F.injR (Fhlf (mag x)).
Proof.
  intro x. destruct x as (l, u). unfold mag, hlf; simpl.
  rewrite -> F.max_exact_spec, F.neg_exact_spec, Fhlf_exact_spec, Fhlf_exact_spec.
  rewrite -> Fhlf_exact_spec, F.max_exact_spec, F.neg_exact_spec.
  rewrite <- Rdiv_opp_l. repeat rewrite -> Rdiv_mult_inv.
  rewrite -> (Rmult_comm (-F.injR l)), (Rmult_comm  (F.injR u)).
  rewrite -> RmaxRmult.
  now apply Rmult_comm.
  apply Rlt_le.
  exact pos_half_prf.
Qed.


Definition Rexp : R -> R := exp.

Definition exp_unit : Bounds F -> Bounds F :=
  fun x =>
    match x with bounds l u
      => bounds (F.add down F.unit l) (F.rec up (F.sub down F.unit u)) end.

Lemma exp_unit_correct :
  forall (x : Bounds F) (y : R),
    models x y -> (F.injR (F.sub down F.unit (upper x)) > 0) -> models (exp_unit x) (exp y).
Proof.
  intros x y H H1mu.
  destruct x as (l & u).
  simpl in H1mu.
  assert (F.injR u < 1) as Hu. {
    apply Rlt_zero_Rminus; apply Rgt_lt.
    rewrite <- F.unit_spec.
    apply Rge_gt_trans with (r2 := F.injR (F.sub down F.unit u)).
    - apply Rle_ge. apply F.sub_down_spec.
    - apply H1mu.
  }
  unfold models in H.
  unfold models; unfold exp_unit; simpl.
  split.
  - apply Rle_trans with (r2:=1+y).
    apply Rle_trans with (r2:=F.injR F.unit + F.injR l).
    -- apply F.add_down_spec.
    -- apply Rplus_le_compat.
       rewrite -> F.unit_spec. apply Rle_refl.
       apply H.
    -- apply exp_ge.
  - apply Rle_trans with (r2:=/ (1%R-F.injR u)).
    apply Rle_trans with (r2:=exp (F.injR u)).
    -- apply exp_incr. apply H.
    -- apply exp_le. exact Hu.
    -- apply Rle_trans with (r2:=/ F.injR (F.sub down F.unit u)).
       --- apply Rinv_le_contravar.
           exact H1mu.
           rewrite <- F.unit_spec.
           apply F.sub_down_spec.
       --- apply Rge_le.
           apply F.rec_up_spec.
           apply Rgt_not_eq. exact H1mu.
Qed.


Fixpoint exp_reduce (n : nat) : Bounds F -> Bounds F :=
  fun x => match n with | O => exp_unit x | S m => sqr (exp_reduce m (hlf x)) end.

Lemma exp_reduce_correct :
  forall (n : nat) (x : Bounds F) (y : R),
    F.injR (mag x) < Rpow 2 n ->
      models x y -> models (exp_reduce n x) (Rexp y).
Proof.
  induction n.
  - intros x y H0 H.
    destruct x as (l & u).
    assert (F.injR (F.sub down F.unit u) > 0) as Hu. {
      replace (2^0) with 1 in H0 by lra.
      unfold mag in H0.
      rewrite -> F.max_exact_spec in H0.
        apply Fsub_down_less.
      now apply (Rle_lt_trans _ _ _ (Rmax_r _ _) H0).
    }
    unfold exp_reduce.
    now apply exp_unit_correct.
  - intros x y HSn Hx.
    simpl.
    assert (F.injR (mag (hlf x)) < 2^n) as Hhlfx. {
      replace (2^n) with (2^(S n)/2). 2: simpl; lra.
      rewrite -> mag_hlf.
      rewrite -> Fhlf_exact_spec.
      apply Rdiv_lt_compat_r. lra. exact HSn.
    }
    assert (models (hlf x) (y/2)) as Hhlfy. {
      now apply hlf_correct.
    }
    specialize (IHn (hlf x) (y / 2)).
    specialize (IHn Hhlfx Hhlfy).
    replace (Rexp y) with (Rsqr (Rexp (y/2))).
    2: apply eq_sym; now apply exp_hlf_sqr.
    apply sqr_correct.
    exact IHn.
Qed.


Definition exp : Bounds F -> Bounds F :=
  fun x => exp_reduce (proj1_sig (sig_log2_up (F.max (F.neg (lower x)) (upper x)))) x.

Lemma exp_correct :
  forall (x : Bounds F) (y : R),
    models x y -> models (exp x) (Rexp y).
Proof.
  intros x y H.
  destruct x as (l & u).
  unfold exp; simpl.
  apply exp_reduce_correct. 2: exact H.
  unfold mag.
  remember (F.max (F.neg l) u) as w.
  remember (sig_log2_up w) as Hz.
  destruct Hz as [z Hz].
  simpl.
  apply (Rle_lt_trans _ (F.injR (F.abs w)) _).
  - rewrite <- Heqw. rewrite -> F.abs_exact_spec.
    now apply Rle_abs.
  - now apply (Rgt_lt _ _ Hz).
Qed.

Close Scope R_scope.

End Bounds_section.

End Bnds.

Export Bnds(Bounds,bounds).

Declare Scope Bounds_scope.
Notation "- x" := (Bnds.neg x) : Bounds_scope.
Infix "+" := Bnds.add : Bounds_scope.
Infix "-" := Bnds.sub : Bounds_scope.
Infix "*" := Bnds.mul : Bounds_scope.
Infix "/" := Bnds.div : Bounds_scope.
