(************************************************************************)
(* Copyright 2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Import Reals.

Require Import R_addenda.
Require Import Floats.

Module FloatBounds.

Open Scope R_scope.


Inductive Bounds {F:Type} {cf : Float F} := 
  bounds (lower:F) (upper:F).

Check bounds.

Definition models {F} {cF : Float F} : (@Bounds F cF) -> R -> Prop :=
  fun x y => match x with bounds l u => FinjR l <= y /\ y <= FinjR u end.


Definition add_bounds {F} {cF : Float F} : Bounds -> Bounds -> Bounds :=
  fun x1 x2 => 
    match x1 with bounds l1 u1 
      => match x2 with bounds l2 u2
        => bounds (Fadd down l1 l2) (Fadd up u1 u2) end end.
(*

  fun (bounds l1 u1) (bounds l2 u2) bounds (add down l1 l2) (add up u1 u2). 
*)

Lemma add_bounds_correct {F} {cF : Float F} :
  forall (x1 x2 : Bounds) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (add_bounds x1 x2) (y1+y2).
Proof.
  intros x1 x2 y1 y2 H1 H2. 
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  unfold models in H1,H2;
  unfold models; unfold add_bounds.
  split.
  - apply Rle_trans with (r2:=FinjR l1 + FinjR l2).
    -- apply flt_add_down.
    -- apply Rplus_le_compat; [apply H1|]; apply H2.
  - apply Rle_trans with (r2:=FinjR u1 + FinjR u2).
    -- apply Rplus_le_compat; [apply H1|]; apply H2.
    -- apply Rge_le; apply flt_add_up.
Qed.
  
(* Definition sub_bounds {F} {cF : Float F} ((bounds l1 u1) : Bounds) (x2 : Bounds) : Bounds *)
Definition sub_bounds {F} {cF : Float F} (x1 x2 : Bounds) : Bounds :=
  match x1 with bounds l1 u1 => match x2 with bounds l2 u2
      => bounds (Fsub down l1 u2) (Fsub up u1 l2) end end.

Lemma Rminus_le_compat:
  forall r1 r2 r3 r4 : R, r1 <= r2 -> r4 <= r3 -> r1 - r3 <= r2 - r4.
Proof.
  intros r1 r2 r3 r4 H12 H34;
  lra.
Qed. 

Lemma sub_bounds_correct {F} {cF : Float F} :
  forall (x1 x2 : Bounds) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (sub_bounds x1 x2) (y1-y2).
Proof.
  intros x1 x2 y1 y2 H1 H2. 
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  unfold models in H1,H2.
  unfold models; unfold sub_bounds.
  split.
  - apply Rle_trans with (r2:=FinjR l1 - FinjR u2).
    -- apply flt_sub_down.
    -- apply Rminus_le_compat; [apply H1|]; apply H2.
  - apply Rle_trans with (r2:=FinjR u1 - FinjR l2).
    -- apply Rminus_le_compat; [apply H1|]; apply H2.
    -- apply Rge_le; apply flt_sub_up.
Qed.
  


Definition mul_bounds {F} {cF : Float F} (x1 x2 : Bounds) : Bounds :=
  match x1 with bounds l1 u1 => 
    match x2 with bounds l2 u2 => 
      if Fleb Fnull l1 then
        if Fleb Fnull l2 then
          bounds (Fmul down l1 l2) (Fmul up u1 u2)
        else if Fleb u2 Fnull then
          bounds (Fmul down u1 l2) (Fmul up l1 u2)
        else 
          bounds (Fmul down u1 l2) (Fmul up u1 u2)
      else if Fleb u1 Fnull then
        if Fleb Fnull l2 then
          bounds (Fmul down l1 u2) (Fmul up u1 l2)
        else if Fleb u2 Fnull then
          bounds (Fmul down u1 u2) (Fmul up l1 l2)
        else 
          bounds (Fmul down l1 u2) (Fmul up l1 l2)
      else
        if Fleb Fnull l2 then
          bounds (Fmul down l1 u2) (Fmul up u1 u2)
        else if Fleb u2 Fnull then
          bounds (Fmul down u1 l2) (Fmul up l1 l2)
        else 
          bounds (Fmin (Fmul down l1 u2) (Fmul down u1 l2)) 
                 (Fmax (Fmul up l1 l2) (Fmul up u1 u2))
    end
  end
.      


(* Unused *)
Lemma Rle_or_ge : forall (x1 x2 : R), x1<=x2 \/ x1 >=x2.
Proof.
  intros x1 x2.
  apply or_ind with (A:=x1<x2) (B:=x1=x2\/x1>x2).
  - left. unfold Rle. left. assumption.
  - right. unfold Rge. destruct H. right. assumption. left. assumption.
  - apply Rtotal_order.
Qed.


Lemma Rle_or_le : forall (x1 x2 : R), x1<=x2 \/ x2 <=x1.
Proof.
  intros x1 x2.
  apply or_ind with (A:=x1<x2) (B:=x1=x2\/x1>x2).
  - left. unfold Rle. left. assumption.
  - intro H. destruct H. left. unfold Rle. right. assumption. right. unfold Rle. left. apply Rgt_lt. assumption.
  - apply Rtotal_order.
Qed.



Lemma flt_not_leb {F} {cF : Float F} : 
  forall (x1 x2 : F), (false = Fleb x1 x2) -> (FinjR x2 <= FinjR x1).
Proof.
  intros x1 x2. intro H.
  assert (FinjR x1 <= FinjR x2 -> False). { 
     intros Hge.
     apply flt_leb in Hge.
     destruct (Fleb x1 x2); discriminate.
  }
  apply or_ind with (A:=FinjR x1 <= FinjR x2) (B:=FinjR x2 <= FinjR x1).
  - contradiction.
  - auto. 
  - exact (Rle_or_le (FinjR x1) (FinjR x2)).
Qed.

Lemma flt_geb_0 {F} {cF : Float F} : 
  forall (x:F), (true = Fleb Fnull x) -> (0 <= FinjR x).
Proof.
   intro x. intro H.
   replace 0 with (FinjR (NinjF 0%nat)) by (apply flt_ninjr). 
   apply flt_leb. apply eq_sym. exact H.
Qed.

Lemma flt_leb_0 {F} {cF : Float F} : 
  forall (x:F), (true = Fleb x Fnull) -> (FinjR x <= 0).
Proof.
   intro x. intro H.
   replace 0 with (FinjR (NinjF 0%nat)) by (apply flt_ninjr).
   apply flt_leb. apply eq_sym. exact H.
Qed.

Lemma flt_not_geb_0 {F} {cF : Float F} : 
  forall (x:F), (false = Fleb Fnull x) -> (FinjR x <= 0).
Proof.
  intro x. replace 0 with (FinjR (NinjF 0%nat)) by (apply flt_ninjr); apply flt_not_leb.
Qed.

Lemma flt_not_leb_0 {F} {cF : Float F} : 
  forall (x:F), (false = Fleb x Fnull) -> (0 <= FinjR x).
Proof.
  intro x. replace 0 with (FinjR (NinjF 0%nat)) by (apply flt_ninjr); apply flt_not_leb.
Qed.



Lemma Rle_min_compat : forall (r1 r2 r3 r4 : R), r1<=r3 -> r2<=r4 -> Rmin r1 r2 <= Rmin r3 r4.
Proof.
  intros r1 r2 r3 r4 H13 H24.
  apply Rle_trans with (r2 := Rmin r1 r4).
  apply Rle_min_compat_l; exact H24.
  apply Rle_min_compat_r; exact H13.
Qed.
   
Lemma Rle_max_compat : forall (r1 r2 r3 r4 : R), r1<=r3 -> r2<=r4 -> Rmax r1 r2 <= Rmax r3 r4.
Proof.
  intros r1 r2 r3 r4 H13 H24.
  apply Rle_trans with (r2 := Rmax r1 r4).
  apply Rle_max_compat_l; exact H24.
  apply Rle_max_compat_r; exact H13.
Qed.



Lemma flt_mul_up_le {F} {FltF : Float F} : forall (x1 x2 : F),
  (FinjR x1) * (FinjR x2) <= FinjR (Fmul up x1 x2).
Proof.
  intros x1 x2. apply Rge_le. apply flt_mul_up.
Qed.



Lemma Rmult_le_opp_compat_l : forall (r r1 r2 : R), r<=0 -> r1 <= r2 -> r*r2 <= r*r1.
Proof.
  intros r r1 r2 Hr0 Hr12.
  assert (0 <= -r) as H0r. { apply Ropp_0_ge_le_contravar. apply Rle_ge. exact Hr0. }
  apply Ropp_le_cancel;
  rewrite -> Ropp_mult_distr; rewrite -> Ropp_mult_distr. 
  apply Rmult_le_compat_l; [exact H0r|]; exact Hr12.
Qed.

Lemma Rmult_le_opp_compat_r : forall (r r1 r2 : R), r<=0 -> r1 <= r2 -> r2*r <= r1*r.
Proof.
  intros r r1 r2 Hr0 Hr12.
  assert (r1 * r = r * r1) as H1c; [apply Rmult_comm|].
  assert (r2 * r = r * r2) as H2c; [apply Rmult_comm|].
  rewrite -> H1c; rewrite -> H2c.
  apply Rmult_le_opp_compat_l. assumption. assumption.
Qed.



Lemma mul_bounds_correct {F} {cF : Float F} :
  forall (x1 x2 : Bounds) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> models (mul_bounds x1 x2) (y1*y2).
Proof.
  intros x1 x2 y1 y2 H1 H2.
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  destruct H1 as (H1l,H1u), H2 as (H2l,H2u);
  remember (conj H1l H1u) as H1; remember (conj H2l H2u) as H2.
  unfold models in H1,H2.
  unfold models.
  unfold mul_bounds.
  remember (Fleb Fnull l1) as bl1.
  remember (Fleb u1 Fnull) as bu1.
  remember (Fleb Fnull l2) as bl2.
  remember (Fleb u2 Fnull) as bu2.

  destruct bl1. 
    (* Cases 0<=l1 *) 
    assert (0<=FinjR l1) as Hl1; [apply flt_geb_0; exact Heqbl1|].
    assert (0<=y1) as Hy1 by (apply (Rle_trans _ (FinjR l1) _ Hl1 H1l)).
    assert (0<=FinjR u1) as Hu1 by (apply (Rle_trans _ y1 _ Hy1 H1u)).
    destruct bl2.
    {
      (* Case 0<=l1 /\ 0<=l2 *) 
      assert (0<=FinjR l2) as Hl2; [apply flt_geb_0; exact Heqbl2|].
      assert (0<=y2) as Hy2 by (apply (Rle_trans _ (FinjR l2) _ Hl2 H2l)).
      split.
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR l2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := (FinjR l1) * y2).
         apply (Rmult_le_compat_l _ _ _ Hl1 H2l).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR u2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := (FinjR u1) * y2).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1u).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2u).
    }
    destruct bu2.
    {
      (* Case 0<=l1 /\ u2<=0 *) 
      assert (FinjR u2<=0) as Hu2; [apply flt_leb_0; exact Heqbu2|].
      assert (y2<=0) as Hy2. apply Rle_trans with (r2:=FinjR u2). exact H2u. exact Hu2.
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR l2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := (FinjR u1) * y2).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR u2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := (FinjR l1) * y2).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rmult_le_compat_l _ _ _ Hl1 H2u).
    }
    {
      (* Case 0<=l1 /\ l2<0<u2 *)
      assert (FinjR l2<=0) as Hl2; [apply flt_not_geb_0; exact Heqbl2|].
      assert (0<=FinjR u2) as Hu2; [apply flt_not_leb_0; exact Heqbu2|].
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR l2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := y1 * (FinjR l2)).
         apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1u).
         apply (Rmult_le_compat_l _ _ _ Hy1 H2l).
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR u2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := y1 * (FinjR u2)).
         apply (Rmult_le_compat_l _ _ _ Hy1 H2u).
         apply (Rmult_le_compat_r _ _ _ Hu2 H1u).
    }
  destruct bu1.
    (* Cases u1 <= 0 *)
    assert (FinjR u1<=0) as Hu1; [apply flt_leb_0; exact Heqbu1|].
    assert (y1<=0) as Hy1. apply Rle_trans with (r2:=FinjR u1). exact H1u. exact Hu1.
    destruct bl2.
    {
      (* Case u1 <= 0 /\ 0 <= l2 *)
      assert (0<=FinjR l2) as Hl2; [apply flt_geb_0; exact Heqbl2|].
      assert (0<=y2) as Hy2. apply Rle_trans with (r2:=FinjR l2). exact Hl2. exact H2l.
      assert (0<=FinjR u2) as Hu2. apply Rle_trans with (r2:=y2). exact Hy2. exact H2u.
      split.
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR u2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := y1 * (FinjR u2)).
         apply (Rmult_le_compat_r _ _ _ Hu2 H1l).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2u).
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR l2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := (FinjR u1) * y2).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1u).
         apply (Rmult_le_opp_compat_l _ _ _ Hu1 H2l).
    }
    destruct bu2.
    {
      (* Case u1 <= 0 /\ u2 <= 0 *)
      assert (FinjR u2<=0) as Hu2; [apply flt_leb_0; exact Heqbu2|].
      assert (y2<=0) as Hy2. apply Rle_trans with (r2:=FinjR u2). exact H2u. exact Hu2. 
      assert (FinjR l2<=0) as Hl2. apply Rle_trans with (r2:=y2). exact H2l. exact Hy2.
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR u2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := (FinjR u1) * y2).
         apply (Rmult_le_opp_compat_l _ _ _ Hu1 H2u).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR l2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := y1 * (FinjR l2)).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1l).
    }
    {
      (* Case u1 <=0 /\ l2 <= 0 <= u2 *)
      assert (FinjR l2<=0) as Hl2; [apply flt_not_geb_0; exact Heqbl2|].
      assert (0<=FinjR u2) as Hu2; [apply flt_not_leb_0; exact Heqbu2|].
      split. 
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR u2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := y1 * (FinjR u2)).
         apply (Rmult_le_compat_r _ _ _ Hu2 H1l).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2u).
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR l2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := y1 * (FinjR l2)).
         apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1l).
    }

    (* Cases l1 <= 0 <= u1 *)
    assert (FinjR l1<=0) as Hl1; [apply flt_not_geb_0; exact Heqbl1|].
    assert (0<=FinjR u1) as Hu1; [apply flt_not_leb_0; exact Heqbu1|].
    destruct bl2.
    {
      (* Case l1 <= 0 <= u1 /\ 0 <= l2 *)
      assert (0<=FinjR l2) as Hl2; [apply flt_geb_0; exact Heqbl2|].
      assert (0<=y2) as Hy2. apply Rle_trans with (r2:=FinjR l2). apply Hl2. apply H2.
      split. 
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR u2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := (FinjR l1) * y2).
         apply (Rmult_le_opp_compat_l _ _ _ Hl1 H2u).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR u2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := (FinjR u1) * y2).
         apply (Rmult_le_compat_r _ _ _ Hy2 H1u).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2u).
    }
    destruct bu2.
    {
      (* Case l1 <= 0 <= u1 /\ u2 <= 0 *)
      assert (FinjR u2<=0) as Hu2; [apply flt_leb_0; exact Heqbu2|].
      assert (y2<=0) as Hy2. apply Rle_trans with (r2:=FinjR u2). exact H2u. exact Hu2.
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) * (FinjR l2)).
         1: apply flt_mul_down.
         apply Rle_trans with (r2 := (FinjR u1) * y2).
         apply (Rmult_le_compat_l _ _ _ Hu1 H2l).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (FinjR l1) * (FinjR l2)).
         2: apply flt_mul_up_le.
         apply Rle_trans with (r2 := (FinjR l1) * y2).
         apply (Rmult_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rmult_le_opp_compat_l _ _ _ Hl1 H2l).    
    }
    {
      (* Case l1 <= 0 <= u1 /\ l2 <= 0 <= u2 *)
      assert (FinjR l2<=0) as Hl2; [apply flt_not_geb_0; exact Heqbl2|].
      assert (0<=FinjR u2) as Hu2; [apply flt_not_leb_0; exact Heqbu2|].
      assert (y1 <= 0 \/ 0 <= y1) as Hdisjy1. apply Rle_or_le.
      split.
      -- rewrite-> flt_min_exact.
         apply Rle_trans with ( r2 := Rmin ((FinjR l1) * (FinjR u2)) ((FinjR u1) * (FinjR l2)) ).
         assert (FinjR (Fmul down l1 u2) <= FinjR l1 * FinjR u2) as Hl1u2; [apply flt_mul_down|].
         assert (FinjR (Fmul down u1 l2) <= FinjR u1 * FinjR l2) as Hu1l2; [apply flt_mul_down|].
         apply Rle_min_compat; apply flt_mul_down; apply flt_mul_down.
         assert (0<=y1 -> FinjR u1 * FinjR l2 <= y1 * y2) as H0ley1. {
           intros Hy1;
           apply Rle_trans with (r2 := y1 * FinjR l2).
           apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1u). 
           apply (Rmult_le_compat_l _ _ _ Hy1 H2l). 
         }
         assert (y1<=0 -> FinjR l1 * FinjR u2 <= y1 * y2) as H0gey1. { 
           intros Hy1.
           apply Rle_trans with (r2 := y1 * FinjR u2).
           apply (Rmult_le_compat_r _ _ _ Hu2 H1l). 
           apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2u). 
         }
         remember ((FinjR l1)*(FinjR u2)) as wlu.
         remember ((FinjR u1)*(FinjR l2)) as wul.
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
      -- rewrite-> flt_max_exact.
         apply Rle_trans with ( r2 := Rmax ((FinjR l1) * (FinjR l2)) ((FinjR u1) * (FinjR u2)) ).
         assert (FinjR l1 * FinjR l2 <= FinjR (Fmul up l1 l2)) as Hl1l2; [apply Rge_le; apply flt_mul_up|].
         assert (FinjR u1 * FinjR u2 <= FinjR (Fmul up u1 u2)) as Hu1u2; [apply Rge_le; apply flt_mul_up|].
         2: apply Rle_max_compat. 2: apply flt_mul_up_le. 2: apply flt_mul_up_le.
         assert (0<=y1 -> y1 * y2 <= FinjR u1 * FinjR u2) as H0ley1. {
           intros Hy1.
           apply Rle_trans with (r2 := y1 * FinjR u2).
           apply (Rmult_le_compat_l _ _ _ Hy1 H2u). 
           apply (Rmult_le_compat_r _ _ _ Hu2 H1u). 
           (* apply Rmult_le_compat_l. exact Hy1. apply H2.
              apply Rmult_le_compat_r. exact Hu2. apply H1.
            *)
         }
         assert (y1<=0 -> y1 * y2 <= FinjR l1 * FinjR l2) as H0gey1. {
           intros Hy1.
           apply Rle_trans with (r2 := y1 * FinjR l2).
           apply (Rmult_le_opp_compat_l _ _ _ Hy1 H2l). 
           apply (Rmult_le_opp_compat_r _ _ _ Hl2 H1l). 
           (* apply Rmult_le_opp_compat_l. exact Hy1. apply H2.
            * apply Rmult_le_opp_compat_r. exact Hl2. apply H1.
            *)
         }
         remember ((FinjR l1)*(FinjR l2)) as wll.
         remember ((FinjR u1)*(FinjR u2)) as wuu.
         assert (0<=y1 -> y1 * y2 <= Rmax wll wuu) as Hy1pos. {
           intros Hy1. apply Rle_trans with (r2:=wuu). apply H0ley1. exact Hy1. apply Rmax_r.
         }
         assert (y1<=0 -> y1 * y2 <= Rmax wll wuu) as Hy1neg. {
           intros Hy1. apply Rle_trans with (r2:=wll). apply H0gey1. exact Hy1. apply Rmax_l.
         }
         apply or_ind with (B:=0<=y1) (A:=y1<=0). exact Hy1neg. exact Hy1pos. exact Hdisjy1.
     }
Qed.


Definition div_bounds {F} {cF : Float F} (x1 x2 : Bounds) : Bounds :=
  match x1 with bounds l1 u1 => 
    match x2 with bounds l2 u2 => 
      if Fleb Fnull l1 then
        if Fleb Fnull l2 then
          bounds (Fdiv down l1 u2) (Fdiv up u1 l2)
        else 
          bounds (Fdiv down u1 u2) (Fdiv up l1 l2)
      else if Fleb u1 Fnull then
        if Fleb Fnull l2 then
          bounds (Fdiv down l1 l2) (Fdiv up u1 u2)
        else 
          bounds (Fdiv down u1 l2) (Fdiv up l1 u2)
      else 
        if Fleb Fnull l2 then
          bounds (Fdiv down l1 l2) (Fdiv up u1 l2)
        else 
          bounds (Fdiv down u1 u2) (Fdiv up l1 u2)
    end
  end
.

Definition lower {F} {cF : Float F} (x : @Bounds F cF) : F := match x with bounds l _ => l end.
Definition upper {F} {cF : Float F} (x : @Bounds F cF) : F := match x with bounds _ u => u end.

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
  rewrite -> Ropp_0_lt_contravar. rewrite -> Ropp_inv_permute. apply Rinv_pos. rewrite <- Ropp_0_lt_contravar. exact Hlt0.
  apply Rlt_not_eq. exact Hlt0.
Qed.

Lemma Rinv_le_compat : forall r1 r2 : R, (0 < r1 \/ r2 < 0) -> r1 <= r2 ->  / r2 <=  / r1.
Proof.
  intros r1 r2 Hne0 H.
  destruct Hne0.
  - apply Rinv_le_contravar. exact H0. exact H.
  - apply Ropp_le_cancel. rewrite -> Ropp_inv_permute. rewrite -> Ropp_inv_permute. apply Rinv_le_contravar. 
    -- apply Ropp_0_lt_contravar. exact H0.
    -- apply Ropp_le_contravar. exact H.
    -- apply Rlt_not_eq. exact H0.
    -- apply Rlt_not_eq. apply Rle_lt_trans with (r2 := r2). exact H. exact H0.
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
 
Lemma flt_div_up_le {F} {FltF : Float F} : forall (x1 x2 : F),
  (FinjR x2 <> 0) -> (FinjR x1) / (FinjR x2) <= FinjR (Fdiv up x1 x2).
Proof.
  intros x1 x2 Hne0. apply Rge_le. apply flt_div_up. exact Hne0.
Qed.




Lemma div_bounds_correct {F} {cF : Float F} :
  forall (x1 x2 : Bounds) (y1 y2 : R),
    models x1 y1 -> models x2 y2 -> (0 < FinjR (lower x2) \/ FinjR (upper x2) < 0) -> models (div_bounds x1 x2) (y1/y2).
Proof.
  intros x1 x2 y1 y2 H1 H2 Hor.
  destruct x1 as (l1 & u1), x2 as (l2 & u2).
  destruct H1 as (H1l,H1u), H2 as (H2l,H2u);
  remember (conj H1l H1u) as H1; remember (conj H2l H2u) as H2.
  unfold lower in Hor; unfold upper in Hor. 
  unfold models in H1,H2.
  unfold models.
  unfold div_bounds.
  remember (Fleb Fnull l1) as bl1.
  remember (Fleb u1 Fnull) as bu1.
  remember (Fleb Fnull l2) as bl2.
  remember (Fleb u2 Fnull) as bu2.
 
  assert (0 < y2 \/ FinjR u2 < 0) as Horu. { 
    apply or_ind with (A:=0<FinjR l2) (B:=FinjR u2<0).
    - intro Hl2gt0. left. apply Rlt_le_trans with (r2:=FinjR l2). exact Hl2gt0. exact H2l. 
    - intro Hu2lt0. right. exact Hu2lt0.  
    - exact Hor. 
  }
  assert (0 < FinjR l2 \/ y2 < 0) as Horl. { 
    apply or_ind with (A:=0<FinjR l2) (B:=FinjR u2<0).
    - intro Hl2gt0. left. exact Hl2gt0.
    - intro Hu2lt0. right. apply Rle_lt_trans with (r2:=FinjR u2). exact H2u. exact Hu2lt0. 
    - exact Hor. 
  }
  assert (FinjR l2 <= FinjR u2) as Hl2leu2. { apply Rle_trans with (r2:=y2). exact H2l. exact H2u. }

  assert (FinjR l2 <> 0%R) as Hl2ne0. {
    apply or_ind with (A:= 0 < FinjR l2) (B:=FinjR u2 < 0).
    - intro Hl2gt0. apply Rgt_not_eq. apply Rlt_gt. exact Hl2gt0.
    - intro Hu2lt0. apply Rlt_not_eq. apply Rle_lt_trans with (r2:=FinjR u2). exact Hl2leu2. exact Hu2lt0.
    - exact Hor.
  }
  assert (FinjR u2 <> 0%R) as Hu2ne0. {
    apply or_ind with (A:= 0 < FinjR l2) (B:=FinjR u2 < 0).
    - intro Hl2gt0. apply Rgt_not_eq. apply Rlt_gt. apply Rlt_le_trans with (r2:=FinjR l2). exact Hl2gt0. exact Hl2leu2.
    - intro Hu2lt0. apply Rlt_not_eq. exact Hu2lt0.
    - exact Hor.
  }

  destruct bl2.
    (* Cases 0<l2 *) 
    assert (0<=FinjR l2) as Hl2'; [apply flt_geb_0; exact Heqbl2|].
    assert (0<FinjR l2) as Hl2. { apply Rge_not_eq_gt. exact Hl2'. exact Hl2ne0. }
    assert (0<y2) as Hy2 by (apply (Rlt_le_trans _ (FinjR l2) _ Hl2 H2l)).
    assert (0<FinjR u2) as Hu2. apply Rlt_le_trans with (r2:=y2). exact Hy2. exact H2u.
 
    destruct bl1. 
    {
      (* Case 0<=l1 /\ 0<l2 *) 
      assert (0<=FinjR l1) as Hl1; [apply flt_geb_0; exact Heqbl1|].
      assert (0<=y1) as Hy1 by (apply (Rle_trans _ (FinjR l1) _ Hl1 H1l)).
      assert (0<=FinjR u1) as Hu1 by (apply (Rle_trans _ y1 _ Hy1 H1u)).
      split.
      -- apply Rle_trans with (r2 := (FinjR l1) / (FinjR u2)).
         1: apply flt_div_down.
         1: apply Hu2ne0.
         apply Rle_trans with (r2 := (FinjR l1) / y2).
         apply (Rdiv_le_compat_l _ _ _ Hl1 Horu H2u).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (FinjR u1) / (FinjR l2)).
         2: apply flt_div_up_le.
         2: apply Hl2ne0.
         apply Rle_trans with (r2 := (FinjR u1) / y2).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1u).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horl H2l).
    }
    destruct bu1.
    {
      (* Case u1 <= 0 /\ 0 < l2 *)
      assert (FinjR u1<=0) as Hu1; [apply flt_leb_0; exact Heqbu1|].
      assert (y1<=0) as Hy1. apply Rle_trans with (r2:=FinjR u1). exact H1u. exact Hu1.
      split.
      -- apply Rle_trans with (r2 := (FinjR l1) / (FinjR l2)).
         1: apply flt_div_down.
         1: apply Hl2ne0.
         apply Rle_trans with (r2 := y1 / (FinjR l2)).
         apply (Rdiv_le_compat_r _ _ _ Hl2 H1l).
         apply (Rdiv_le_opp_compat_l _ _ _ Hy1 Horl H2l).
      -- apply Rle_trans with (r2 := (FinjR u1) / (FinjR u2)).
         2: apply flt_div_up_le.
         2: apply Hu2ne0.
         apply Rle_trans with (r2 := (FinjR u1) / y2).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1u).
         apply (Rdiv_le_opp_compat_l _ _ _ Hu1 Horu H2u).
    }
    {
      (* Case l1 <= 0 <= u1 /\ 0 < l2 *)
      assert (FinjR l1<=0) as Hl1; [apply flt_not_geb_0; exact Heqbl1|].
      assert (0<=FinjR u1) as Hu1; [apply flt_not_leb_0; exact Heqbu1|].
      split. 
      -- apply Rle_trans with (r2 := (FinjR l1) / (FinjR l2)).
         1: apply flt_div_down.
         1: apply Hl2ne0.         
         apply Rle_trans with (r2 := (FinjR l1) / y2).
         apply (Rdiv_le_opp_compat_l _ _ _ Hl1 Horl H2l).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1l).
      -- apply Rle_trans with (r2 := (FinjR u1) / (FinjR l2)).
         2: apply flt_div_up_le.
         2: apply Hl2ne0.         
         apply Rle_trans with (r2 := (FinjR u1) / y2).
         apply (Rdiv_le_compat_r _ _ _ Hy2 H1u).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horl H2l).
    }
  
  destruct bu2. 
    (* Cases u2<0 *) 
    assert (FinjR u2<=0) as Hu2'; [apply flt_leb_0; exact Heqbu2|].
    assert (FinjR u2<0) as Hu2. { apply Rle_not_eq_lt. exact Hu2'. exact Hu2ne0. }
    assert (y2<0) as Hy2. apply Rle_lt_trans with (r2:=FinjR u2). exact H2u. exact Hu2.
    assert (FinjR l2<0) as Hl2. apply Rle_lt_trans with (r2:=y2). exact H2l. exact Hy2.

    destruct bl1. 
    {
      (* Case 0<=l1 /\ u2<0 *) 
      assert (0<=FinjR l1) as Hl1; [apply flt_geb_0; exact Heqbl1|].
      assert (0<=y1) as Hy1 by (apply (Rle_trans _ (FinjR l1) _ Hl1 H1l)).
      assert (0<=FinjR u1) as Hu1 by (apply (Rle_trans _ y1 _ Hy1 H1u)).
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) / (FinjR u2)).
         1: apply flt_div_down.
         1: apply Hu2ne0.
         apply Rle_trans with (r2 := (FinjR u1) / y2).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horu H2u).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (FinjR l1) / (FinjR l2)).
         2: apply flt_div_up_le.
         2: apply Hl2ne0.
         apply Rle_trans with (r2 := (FinjR l1) / y2).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rdiv_le_compat_l _ _ _ Hl1 Horl H2l).
    }
    destruct bu1.
    {
      (* Case u1<=0 /\ u2<0 *) 
      assert (FinjR u1<=0) as Hu1; [apply flt_leb_0; exact Heqbu1|].
      assert (y1<=0) as Hy1. apply Rle_trans with (r2:=FinjR u1). exact H1u. exact Hu1.
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) / (FinjR l2)).
         1: apply flt_div_down.
         1: apply Hl2ne0.
         apply Rle_trans with (r2 := (FinjR u1) / y2).
         apply (Rdiv_le_opp_compat_l _ _ _ Hu1 Horl H2l).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (FinjR l1) / (FinjR u2)).
         2: apply flt_div_up_le.
         2: apply Hu2ne0.
         apply Rle_trans with (r2 := y1 / (FinjR u2)).
         apply (Rdiv_le_opp_compat_l _ _ _ Hy1 Horu H2u).
         apply (Rdiv_le_opp_compat_r _ _ _ Hu2 H1l).
    }
    {
      (* Case l1 <= 0 <= u1 /\ u2 < 0 *)
      assert (FinjR l1<=0) as Hl1; [apply flt_not_geb_0; exact Heqbl1|].
      assert (0<=FinjR u1) as Hu1; [apply flt_not_leb_0; exact Heqbu1|].
      split.
      -- apply Rle_trans with (r2 := (FinjR u1) / (FinjR u2)).
         1: apply flt_div_down.
         1: apply Hu2ne0.         
         apply Rle_trans with (r2 := (FinjR u1) / y2).
         apply (Rdiv_le_compat_l _ _ _ Hu1 Horu H2u).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1u).
      -- apply Rle_trans with (r2 := (FinjR l1) / (FinjR u2)).
         2: apply flt_div_up_le.
         2: apply Hu2ne0.
         apply Rle_trans with (r2 := (FinjR l1) / y2).
         apply (Rdiv_le_opp_compat_r _ _ _ Hy2 H1l).
         apply (Rdiv_le_opp_compat_l _ _ _ Hl1 Horu H2u).    
    }

    {
      (* Cases l2<0<u2 *)
      assert (FinjR l2<=0) as Hl2; [apply flt_not_geb_0; exact Heqbl2|].
      assert (0<=FinjR u2) as Hu2; [apply flt_not_leb_0; exact Heqbu2|].
      assert (False). {
        apply or_ind with (A:=0<FinjR l2) (B:=FinjR u2<0).
        - apply Rle_not_lt. exact Hl2.
        - apply Rle_not_lt. exact Hu2. 
        - exact Hor.
      } 
      contradiction.
    }
Qed.

End FloatBounds.