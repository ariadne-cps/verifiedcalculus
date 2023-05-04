(* ---------------------------------------------------------------- *)
(* Author:       SINDORF, S.L. & COLLINS, P.
   Date:         20221231
   Supervisor:   COLLINS, P.
   Description:  Coq, Gallina-code

                 Proof that behavior of composed system is composed
                 behavior of components.

                 Master's Thesis Artificial Intelligence
                 Maastricht University
*)
(* ---------------------------------------------------------------- *)


Require Import Coq.Program.Syntax.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Require Import List.
Import ListNotations.

Module definitions.

(* A behaviour is causal if the output up to time n depends only on the input up to time n. *)
Definition causal {U:Type} {Y:Type}
  (b : (nat -> U) -> (nat -> Y)) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m <= n -> u m = u' m)
       -> (forall m:nat, m <= n -> (b u) m = (b u') m)
.

(* A weaker definition of causality which turns out to be equivalent. *)
Definition causal' {U:Type} {Y:Type}
  (b : (nat -> U) -> (nat -> Y)) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m <= n -> u m = u' m)
       -> (b u) n = (b u') n
.


(* A behaviour is strictly causal if the output up to time n depends only on the input before time n. *)
Definition strictly_causal {U:Type} {Y:Type}
  (b : (nat -> U) -> (nat -> Y)) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m < n -> u m = u' m)
       -> (forall m:nat, m <= n -> (b u) m = (b u') m)
.

(* A weaker definition of strict causality which turns out to be equivalent. *)
(* A behaviour is struct causal if the output at time n depends only on the input up to time n. *)
Definition strictly_causal' {U:Type} {Y:Type}
  (b : (nat -> U) -> (nat -> Y)) : Prop :=
   forall u u' : nat -> U, forall n:nat, (forall m:nat, m < n -> u m = u' m)
       -> (b u) n = (b u') n
.

(* Search for some theorems involving lt < and le <= *) Search lt le.
Check Nat.lt_le_trans.

(* Show that the two definitions of causality are actually equivalent. *)
Lemma strictly_causal_equivalent : forall {U:Type} {Y:Type}
  (b : (nat -> U) -> (nat -> Y)), strictly_causal' b <-> strictly_causal b.
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
  (b : (nat -> U) -> (nat -> Y)), causal' b <-> causal b.
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
Definition mixed_causal {UA UD Y : Type}
  (b : (nat->UA*UD)->(nat->Y))
  : Prop :=
    forall (ua ua':nat->UA) (ud ud':nat->UD) (n:nat),
      (forall m0:nat, m0 <= n -> ua m0 = ua' m0) ->
      (forall m1:nat, m1 < n -> ud m1 = ud' m1) ->
      (forall m0:nat, m0 <= n ->
        (b (fun k => (ua k, ud k))) m0 =
        (b (fun k => (ua' k, ud' k))) m0)
.

(* Weaker definition *)
Definition mixed_causal' {UA UD Y : Type}
  (b : (nat->UA*UD)->(nat->Y))
  : Prop :=
    forall (ua ua':nat->UA) (ud ud':nat->UD) (n:nat),
      (forall m0:nat, m0 <= n -> ua m0 = ua' m0) ->
      (forall m1:nat, m1 < n -> ud m1 = ud' m1) ->
      (b (fun k => (ua k, ud k))) n =
      (b (fun k => (ua' k, ud' k))) n
.

Check mixed_causal'.

(* Show that the two definitions of causality are actually equivalent. *)
Lemma mixed_causal_equivalent :
  forall  {UA UD Y : Type}
    (b : (nat->UA*UD) -> (nat -> Y)),
      mixed_causal' b <-> mixed_causal b.
Proof.
  intros UA UD Y. intro b.
  unfold mixed_causal. unfold mixed_causal'.
  split.
  - (* Case: causal' b -> causal b *)
    intro Hscb'.
    intros ua ua' ud ud'. intro n.
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
    intros ua ua' ud ud'. intro n.
    intros Hmlen Hmltn.
    apply Hscb with (n:=n).
    + exact Hmlen.
    + exact Hmltn.
    + apply Nat.le_refl.
Qed.

End definitions.
