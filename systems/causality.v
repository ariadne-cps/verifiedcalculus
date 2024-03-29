(******************************************************************************
 *  systems/cauality.v
 *
 *  Copyright 2023 Sacha L. Sindorf
 *                 Master's Thesis Artificial Intelligence
 *                 Maastricht University
 *
 *  Copyright 2023 Pieter Collins
 *
 *  Definitions and results on causality (nonanticipatingness) of systems.
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


(* ---------------------------------------------------------------- *)


Require Import Coq.Arith.PeanoNat.

Module causality.

(* A behaviour is a function from input sequences to output sequences. *)
Definition Behaviour {U:Type} {Y:Type} : Type := (nat -> U) -> (nat -> Y).

(* A behaviour is causal if the output up to time n depends only on the input up to time n. *)
Definition causal {U:Type} {Y:Type}
  (b : @Behaviour U Y) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m <= n -> u m = u' m)
       -> (forall m:nat, m <= n -> (b u) m = (b u') m)
.

(* A weaker definition of causality which turns out to be equivalent. *)
Definition causal' {U:Type} {Y:Type}
  (b : @Behaviour U Y) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m <= n -> u m = u' m)
       -> (b u) n = (b u') n
.


(* A behaviour is strictly causal if the output up to time n depends only on the input before time n. *)
Definition strictly_causal {U:Type} {Y:Type}
  (b : @Behaviour U Y) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m < n -> u m = u' m)
       -> (forall m:nat, m <= n -> (b u) m = (b u') m)
.

(* A weaker definition of strict causality which turns out to be equivalent. *)
(* A behaviour is struct causal if the output at time n depends only on the input up to time n. *)
Definition strictly_causal' {U:Type} {Y:Type}
  (b : @Behaviour U Y) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m < n -> u m = u' m)
       -> (b u) n = (b u') n
.

(* Show that the two definitions of causality are actually equivalent. *)
Lemma strictly_causal_equivalent : forall {U:Type} {Y:Type}
  (b : @Behaviour U Y), strictly_causal' b <-> strictly_causal b.
Proof.
  intros U Y. intro b.
  unfold strictly_causal. unfold strictly_causal'.
  split.
  - (* Case: strictly_causal' b -> strictly_causal b *)
    intro Hscb'.
    intros u u'. intro n.
    intro Hmltn.
    intro m. intro Hmlen.
    apply Hscb'.
    intro m0. intro Hm0ltm. apply Hmltn.
    assert (m0<m -> m<=n -> m0<n) as H. { apply Nat.lt_le_trans. }
    apply H. assumption. assumption.
  - (* Case: strictly_causal b -> strictly_causal b *)
    intro Hscb.
    intros u u'. intro n.
    intro Hmltn.
    apply Hscb with (n:=n).
    exact Hmltn.
    apply Nat.le_refl.
Qed.


(* Show that the two definitions of causality are actually equivalent. *)
Lemma causal_equivalent : forall {U:Type} {Y:Type}
  (b : @Behaviour U Y), causal' b <-> causal b.
Proof.
  intros U Y. intro b.
  unfold causal. unfold causal'.
  split.
  - (* Case: causal' b -> causal b *)
    intro Hscb'.
    intros u u'. intro n.
    intro Hmltn.
    intro m. intro Hmlen.
    apply Hscb'.
    intro m0. intro Hm0ltm. apply Hmltn.
    (* assert (m0<m -> m<=n -> m0<n) as H. { apply Nat.lt_le_trans. } *)
    assert (m0<=m -> m<=n -> m0<=n) as H. { apply Nat.le_trans. }
    apply H. assumption. assumption.
  - (* Case: causal b -> causal b *)
    intro Hscb.
    intros u u'. intro n.
    intro Hmltn.
    apply Hscb with (n:=n).
    exact Hmltn.
    apply Nat.le_refl.
Qed.

(* A behaviour is causal if the output up to time n depends only on the input up to time n. *)
Definition old_mixed_causal {UA UD Y : Type}
  (b : @Behaviour (UA*UD) Y)
  : Prop :=
    forall (ua ua':nat->UA) (ud ud':nat->UD) (n:nat),
      (forall m0:nat, m0 <= n -> ua m0 = ua' m0) ->
      (forall m1:nat, m1 < n -> ud m1 = ud' m1) ->
      (forall m0:nat, m0 <= n ->
        (b (fun k => (ua k, ud k))) m0 =
        (b (fun k => (ua' k, ud' k))) m0)
.

Definition mixed_causal {UA UD Y : Type}
  (b : @Behaviour (UA*UD) Y)
  : Prop :=
    forall (u u':nat->UA*UD) (n:nat),
      (forall m0:nat, m0 <= n -> fst (u m0) = fst (u' m0)) ->
      (forall m1:nat, m1 < n -> snd (u m1) = snd (u' m1)) ->
      (forall m0:nat, m0 <= n ->
        (b u m0 = b u' m0))
.


(* Weaker definition *)
Definition old_mixed_causal' {UA UD Y : Type}
  (b : @Behaviour (UA*UD) Y)
  : Prop :=
    forall (ua ua':nat->UA) (ud ud':nat->UD) (n:nat),
      (forall m0:nat, m0 <= n -> ua m0 = ua' m0) ->
      (forall m1:nat, m1 < n -> ud m1 = ud' m1) ->
      (b (fun k => (ua k, ud k))) n =
      (b (fun k => (ua' k, ud' k))) n
.

Definition mixed_causal' {UA UD Y : Type}
  (b : @Behaviour (UA*UD) Y)
  : Prop :=
    forall (u u':nat->UA*UD) (n:nat),
      (forall m0:nat, m0 <= n -> fst (u m0) = fst (u' m0)) ->
      (forall m1:nat, m1 < n -> snd (u m1) = snd (u' m1)) ->
      (b u n = b u' n)
.

(* Show that the two definitions of causality are actually equivalent. *)
Lemma mixed_causal_equivalent :
  forall  {UA UD Y : Type}
    (b : @Behaviour (UA*UD) Y),
      mixed_causal' b <-> mixed_causal b.
Proof.
  intros UA UD Y. intro b.
  unfold mixed_causal. unfold mixed_causal'.
  split.
  - (* Case: causal' b -> causal b *)
    intro Hscb'.
    intros u u'. intro n.
    intros Hmlen0 Hmltn.
    intro m0. intro Hmlen1.
    apply Hscb'.
    + intro m1. intro Hm0ltm. apply Hmlen0.
      assert (m1<=m0 -> m0<=n -> m1<=n) as H. { apply Nat.le_trans. }
      apply H. assumption. assumption.
    + intro m1. intro Hm0ltm. apply Hmltn.
      assert (m1<m0 -> m0<=n -> m1<n) as H. { apply Nat.lt_le_trans. }
      apply H. assumption. assumption.
  - (* Case: causal b -> causal b *)
    intro Hscb.
    intros u u'. intro n.
    intros Hmlen Hmltn.
    apply Hscb with (n:=n).
    + exact Hmlen.
    + exact Hmltn.
    + apply Nat.le_refl.
Qed.


Definition extensional {U Y : Type} (b : @Behaviour U Y) :=
  forall u u', (forall n, u n = u' n) -> (forall n, (b u) n = (b u') n).

Lemma strictly_causal_behaviour_extensional {U Y} : forall (b :@Behaviour U Y),
  strictly_causal b -> extensional b.
Proof.
  unfold strictly_causal, extensional.
  intros b Hc. intros u u' Hu n. apply (Hc u u' n).
  intros m Hm. apply Hu. apply Nat.le_refl.
Qed.


Lemma mixed_causal_behaviour_extensional {UA UD Y} : forall (b : @Behaviour (UA*UD) Y),
  mixed_causal b -> extensional b.
Proof.
  unfold mixed_causal, extensional.
  intros b Hc. intros u u' Hu n. apply (Hc u u' n).
  intros m Hm. rewrite <- Hu. reflexivity.
  intros m Hm. rewrite <- Hu. reflexivity.
  apply Nat.le_refl.
Qed.

Lemma mixed_causal_equivalent_behaviours {UA UD Y} : forall (b b' : @Behaviour (UA*UD) Y),
  (forall u n, b u n = b' u n) -> mixed_causal b -> mixed_causal b'.
Proof.
  intros b b' He Hcb.
  unfold mixed_causal in *.
  intros u u' n Hua Hud.
  specialize (Hcb u u' n Hua Hud).
  intros m Hm.
  rewrite <- He, <- He.
  exact (Hcb m Hm).
Qed.



End causality.
