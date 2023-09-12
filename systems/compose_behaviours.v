(******************************************************************************
 * Copyright 2023 Sacha L. Sindorf
 *           2023 Pieter Collins
 *
 *                Proof that behavior of composed system is composed
 *                behavior of components.
 *
 *                Master's Thesis Artificial Intelligence
 *                Maastricht University
 *
 *                Definition and correctness proof of composition of
 *                mixed causal behaviours.
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


(************************************************************************)
(* Copyright 2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Import Coq.Arith.PeanoNat.

Require Export causality.
Require Export behaviour_composition.

Notation causal := causality.causal.
Notation causal' := causality.causal'.
Notation strictly_causal := causality.strictly_causal.
Notation strictly_causal' := causality.strictly_causal'.
Notation strictly_causal_equivalent := causality.strictly_causal_equivalent.
Notation mixed_causal := causality.mixed_causal.
Notation extensional := causality.extensional.
Notation strictly_causal_behaviour_extensional := causality.strictly_causal_behaviour_extensional.
Notation mixed_causal_behaviour_extensional := causality.mixed_causal_behaviour_extensional.
Notation mixed_causal_equivalent_behaviours := causality.mixed_causal_equivalent_behaviours.
Notation is_composed_behaviour := behaviour_composition.is_composed_behaviour.

(* Think of a better name than 'combine', maybe 'function_compose' *)
Definition combine_behaviours_noinputs
  {Y1 Y2 : Type}
  (b1 : @Behaviour Y2 Y1)
  (b2 : @Behaviour Y1 Y2)
  : @Behaviour Y1 Y1 := fun y1s => b1 (b2 y1s) .


Fixpoint iterated_behaviours_noinputs
  {Y : Type}
  (b : @Behaviour Y Y)
  (y_default : Y)
  (n : nat)
  : (nat->Y) :=
    match n with
    | O => b (fun _ => y_default)
    | S n' => b (iterated_behaviours_noinputs b y_default n')
    end.

Definition fixed_behaviour_noinputs
  {Y : Type}
  (b : @Behaviour Y Y)
  (y_default : Y)
  : (nat->Y) := fun n => (iterated_behaviours_noinputs b y_default (S n)) n.

Definition zip {Y1 Y2 : Type} (y1s : nat->Y1) (y2s : nat->Y2) : nat->(Y1*Y2)
  := fun n => (y1s n, y2s n).

Definition extend_behaviour_noinputs
  {Y1 Y2 : Type}
  (y1s : (nat->Y1))
  (b2 : @Behaviour Y1 Y2)
  : (nat->(Y1*Y2)) := zip y1s (b2 y1s).
(*  let y2s := b2 y1s in (y1s n, y2s n). *)

(* Maybe call 'parallel_compose_behaviours_noinputs' *)
Definition compose_behaviours_noinputs
  {Y1 Y2 : Type}
  (b1 : @Behaviour Y2 Y1)
  (b2 : @Behaviour Y1 Y2)
  (y_default : Y1)
  : (nat->Y1*Y2) :=
    let b := combine_behaviours_noinputs b1 b2 in
    let y1s := fixed_behaviour_noinputs b y_default in
    extend_behaviour_noinputs y1s b2
.

Definition is_composed_behaviour_noinputs {Y1 Y2 : Type}
  (b1 : @Behaviour Y2 Y1)
  (b2 : @Behaviour Y1 Y2)
  (b12 : (nat->Y1*Y2))
  : Prop :=
  forall (n:nat),
     ( b1 (fun k => snd (b12 k)) n = fst (b12 n) ) /\
     ( b2 (fun k => fst (b12 k)) n = snd (b12 n) )
.

Definition is_fixed_behaviour_noinputs {Y : Type} (b : @Behaviour Y Y) (ys : nat->Y) : Prop
  := forall (n:nat), (b ys) n = ys n.

(* Show that the fixed behaviour of the combined behaviour extends to the composed behaviour. *)
Lemma combined_behaviour_causal_noinputs {Y1 Y2 : Type} :
  forall (b1 : @Behaviour Y2 Y1)
         (b2 : @Behaviour Y1 Y2),
         (strictly_causal b1) -> (causal b2) ->
         (strictly_causal (combine_behaviours_noinputs b1 b2))
.
Proof.
  intros b1 b2.
  unfold strictly_causal.
  unfold causal.
  intros Hscb1 Hcb2.
  intros u u' n H0 m H1.
  unfold combine_behaviours_noinputs.

  (* Valid from Hcb2 *)
  assert(forall n0: nat,
    (forall m0 : nat, m0 < n0 -> u m0 = u' m0) ->
    (forall m1 : nat, m1 < n0 -> b2 u m1 = b2 u' m1)
  ) as Hcb2short.
  { intros n0 H2.
    induction n0 as [|n' IHn' ].
    - intros m1 H3.
      apply Nat.nlt_0_r in H3.
      exfalso. apply H3.
    - intros m1 H3.
      apply Hcb2 with (n:=n'). (* !!! *)
      + intros m0 H4.
        apply H2.
        apply Nat.lt_succ_r.
        apply H4.
      + apply (Nat.lt_succ_r m1 n') in H3.
        apply H3.
  }

  apply Hscb1 with (n:=n) (u:=(b2 u)) (u':=(b2 u')).
  - intros m0 H2.
    apply Hcb2short with (n0:=n).
    + intros m1 H3.
      apply H0. apply H3.
    + apply H2.
  - apply H1.

Qed.

Lemma causal_fixed_noinputs_zero {Y : Type} :
  forall (b : @Behaviour Y Y)
         (u u' : nat -> Y),
         (strictly_causal b) -> b u 0 = b u' 0.
Proof.
  intros b u u'.
  unfold strictly_causal.
  intros Hscb.
  apply Hscb with (n:=0).
  - intros m H0.
    apply Nat.nlt_0_r in H0.
    exfalso. apply H0.
  - reflexivity.
Qed.

Lemma causal_fixed_noinputs_succ {Y : Type} :
  forall (b : @Behaviour Y Y)
         (u u' : nat -> Y) (n : nat),
         (strictly_causal b) -> (forall m:nat, m<=n -> u m = u' m) -> b u (S n) = b u' (S n).
Proof.
  intros b u u' n.
  unfold strictly_causal.
  intros Hscb H0.
  apply Hscb with (n:= S n).
  - intros m H1.
    apply (Nat.lt_succ_r m n) in H1.
    apply H0. apply H1.
  - reflexivity.
Qed.

(*---------------------------------------------------------------------------*)

(* Intermediate Lemmas  needed for Proposition causal_fixed_noinputs.

zij=yj

w00 w01 w02 w03 w04 ...
z10 w11 w12 w13 w14 ...
z20 z21 w22 w23 w24 ...
z30 z31 z32 w33 w34 ...
z40 z31 z42 z43 w44 ...
z50 z51 z52 z53 z54 ...

let B : iterated_behaviours b y_default.

forall n m, B (S n) m = b (B n) m. [Definition of B]
forall n m, m<n -> B (S n) m = B n m. [Causality of b; induction?]
  [From here, should work for any table B]
forall n m k, m<n -> B (n+k) m = B n m. [Induction on k]
forall n1 n2 m, m<n1<=n2 -> B n2 m = B n1 m. [n<=n+k]
forall n m, m<=n -> B (S n) m = B (S m) m. [n1=S m, n2=S n]
forall n m, m<n -> B n m = B (S m) m. []

*)


Lemma table {Y : Type} (B:nat->nat->Y) :
  (forall n m, m<n -> B (S n) m = B n m) ->
   forall n m, m<n -> B n m = B (S m) m.
Proof.
  intros H0.

  assert (forall n m k, m<n -> B (n+k) m = B n m) as H1.
  { intros n m. induction k.
    - auto.
    - intro Hmltn.
       assert ((n + S k) = S (n+k)) as HS. auto.
       rewrite -> HS. rewrite <- IHk.
       + apply H0.
         apply Nat.lt_le_trans with n; [exact Hmltn|].
         apply Nat.le_add_r.
       + exact Hmltn.
  }

  assert (forall n1 n2 m, m<n1 -> n1<=n2 -> B n2 m = B n1 m) as H2. { (* [n<=n+k] *)
    intros n n' m.
    remember (n'-n) as k.
    intros Hmltn Hnltn'.
    rewrite <- (H1 n m k).
    - assert (n'=n+k) as H3.
      { rewrite Heqk.
        rewrite Nat.add_comm.
        symmetry.
        apply Nat.sub_add with (m:=n') (n:=n).
        exact Hnltn'.
      }
      rewrite <- H3.
      reflexivity.
    - exact Hmltn.
  }

  assert(forall n m, m<=n -> B (S n) m = B (S m) m ) as H3. (* [n1=S m, n2=S n] *)
  { intros n m H4.
    apply H2 with (n2:=S n) (n1:=S m).
    - apply Nat.lt_succ_diag_r.
    - rewrite <- Nat.succ_le_mono.
      apply H4.
  }

  intros n m H4.
  induction n as [|n' IHn'].
  - apply Nat.nlt_0_r in H4.
    exfalso. exact H4.
  - apply H3.
    apply (Nat.lt_succ_r m n') in H4.
    exact H4.
Qed.


(*
Lemma table {Y : Type} (B:nat->nat->Y) :
  (forall n m, m<n -> B (S n) m = B n m) ->
   forall n m, m<n -> B n m = B (S m) m.
*)

Lemma causal_iterated_behaviours_noinputs {Y : Type} (b : @Behaviour Y Y) (y_default : Y) :
  (strictly_causal b) -> (forall n, forall m, m<n ->
    iterated_behaviours_noinputs b y_default n m =
    iterated_behaviours_noinputs b y_default (S m) m).
Proof.
  intros Hscb.

  (* Condition in table *)
  assert (forall n m,
     m<n ->
      iterated_behaviours_noinputs b y_default (S n) m =
      iterated_behaviours_noinputs b y_default n m
  ) as Hdef.
  { intros n. (* m H0. *)
    induction n as [|n' IHn'].
    - intros m H0.
      apply Nat.nlt_0_r in H0. exfalso. exact H0.
    - intros m H0. simpl.
      assert (strictly_causal' b) as Hscb'.
      { rewrite strictly_causal_equivalent.
        exact Hscb.
      }
      apply Hscb'.
      simpl in IHn'.
      intros m0 H1.
      rewrite IHn'.
      + reflexivity.
      + apply (Nat.lt_succ_r m n') in H0.
        apply Nat.lt_le_trans with (m:=m).
        * exact H1.
        * exact H0.
  }

  intros n m H0.
  rewrite table.
  - reflexivity.
  - intros n0 m0 H1.
    rewrite Hdef.
    + reflexivity.
    + exact H1.
  - exact H0.
Qed.

(*----------------------------------------------------------------------------*)

(* Show that the fixed behaviour is indeed a fixed-point. *)
Proposition causal_fixed_noinputs {Y : Type} :
  forall (b : @Behaviour Y Y)
         (y_default : Y),
         (strictly_causal b) ->
         is_fixed_behaviour_noinputs b (fixed_behaviour_noinputs b y_default)
.
Proof.
  intros b y_default.
  intros Hscb.
  unfold is_fixed_behaviour_noinputs.
  intros n.
  unfold fixed_behaviour_noinputs.

  induction n as [| n' IHn'].
  - simpl.
    apply causal_fixed_noinputs_zero.
    exact Hscb.
  - simpl.
    (* simpl in IHn'. *)

    apply causal_fixed_noinputs_succ.
    + exact Hscb.
    + intros m H0.

      assert(forall n0 : nat,
        b (iterated_behaviours_noinputs b y_default n0) =
        (iterated_behaviours_noinputs b y_default (S n0))
      ) as Hit0.
      { intros n0. simpl. reflexivity. }
      rewrite Hit0 with (n0:=m). rewrite Hit0 with (n0:=n').
      symmetry.

      rewrite <- causal_iterated_behaviours_noinputs with
        (b:=b) (y_default:=y_default) (n:=S n') (m:=m).

      * reflexivity.
      * exact Hscb.
      * rewrite Nat.lt_succ_r.
        exact H0.
Qed.


(* Show that the fixed behaviour of the combined behaviour extends to the composed behaviour. *)
Lemma causal_fixed_is_composed_noinputs {Y1 Y2 : Type} :
  forall (b1 : @Behaviour Y2 Y1)
         (b2 : @Behaviour Y1 Y2)
         (y1s : nat->Y1),
         (strictly_causal b1) -> (causal b2) ->
         is_fixed_behaviour_noinputs (combine_behaviours_noinputs b1 b2) y1s ->
         is_composed_behaviour_noinputs b1 b2 (extend_behaviour_noinputs y1s b2)
.
Proof.
  intros b1 b2 y1s Hscb2 Hcb2.
  unfold is_fixed_behaviour_noinputs.
  unfold is_composed_behaviour_noinputs.
  unfold combine_behaviours_noinputs .
  simpl. intros H0 n. split.
  - apply H0.
  - auto.
Qed.

(* Show that composition of behaviours is composed *)
Theorem causal_composed_noinputs {Y1 Y2 : Type} :
  forall (b1 : @Behaviour Y2 Y1)
         (b2 : @Behaviour Y1 Y2)
         (y_default : Y1) ,
         (strictly_causal b1) -> (causal b2) ->
           is_composed_behaviour_noinputs b1 b2
           (compose_behaviours_noinputs b1 b2 y_default)
.
Proof.
  intros b1 b2 y_default Hscb2 Hcb2.
  unfold compose_behaviours_noinputs.

  apply causal_fixed_is_composed_noinputs.
  - exact Hscb2.
  - exact Hcb2.
  - apply causal_fixed_noinputs.
    apply combined_behaviour_causal_noinputs.
    + exact Hscb2.
    + exact Hcb2.
Qed.

(* Show composed behaviour is unique.
   Can probably be omitted, since the case with inputs covers this case.

   Sacha: Omit for now. Write report.
*)
Proposition causal_composed_unique_noinputs {Y1 Y2 : Type} :
  forall (b1 : @Behaviour Y2 Y1)
         (b2 : @Behaviour Y1 Y2)
         (b12 : nat->Y1*Y2)
         (b12' : nat->Y1*Y2)
         (y_default : Y1) ,
         (strictly_causal b1) -> (causal b2) ->
           is_composed_behaviour_noinputs b1 b2 b12 ->
           is_composed_behaviour_noinputs b1 b2 b12' ->
           (forall n : nat, b12 n = b12' n)
.
Proof.
Admitted.



Definition compose_behaviours
    {UA UD Y1 Y2 : Type}
    (b1 : @Behaviour (UA*(UD*Y2)) Y1)
    (b2 : @Behaviour ((UA*Y1)*UD) Y2)
    (y_default : Y1)
      : @Behaviour (UA*UD) (Y1*Y2) :=
  fun (uad : nat -> UA*UD) =>
    let ua := fun n => fst (uad n) in
    let ud := fun n => snd (uad n) in
    let b1' := fun (y2 : nat -> Y2) => b1 (fun n => (ua n, (ud n, y2 n))) in
    let b2' := fun (y1 : nat -> Y1) => b2 (fun n => ((ua n, y1 n), ud n)) in
      compose_behaviours_noinputs b1' b2' y_default.




Theorem mixed_causal_composed {UA UD Y1 Y2 : Type} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1)
         (b2 : @Behaviour ((UA*Y1)*UD) Y2)
         (y_default : Y1),
         (mixed_causal b1) -> (mixed_causal b2) ->
           is_composed_behaviour b1 b2
             (compose_behaviours b1 b2 y_default).
Proof.
  intros b1 b2 y_default.
  intros Hb1 Hb2.
  intros uad.
  intro n.
  intros ua ud.
  remember (fun (y2 : nat -> Y2) => b1 (fun n => (ua n, (ud n, y2 n)))) as b1'.
  remember (fun (y1 : nat -> Y1) => b2 (fun n => ((ua n, y1 n), ud n))) as b2'.
  intros py1 py2 gy1 gy2.
  assert (strictly_causal b1') as Hb1'. {
    unfold strictly_causal. unfold mixed_causal in Hb1.
    intros y2 y2' n' Hsc. rewrite -> Heqb1'. apply Hb1. trivial.
    intros m' Hm'. f_equal. f_equal. f_equal. apply Hsc. exact Hm'.
  }
  assert (causal b2') as Hb2'. {
    unfold causal. unfold mixed_causal in Hb2.
    intros y1 y1' n' Hc. rewrite -> Heqb2'. apply Hb2.
    intros m' Hm'. f_equal. f_equal. f_equal. apply Hc. exact Hm'. trivial.
  }
  assert (extensional b1') as Heb1'. {
    apply strictly_causal_behaviour_extensional. exact Hb1'.
  }
  assert (is_composed_behaviour_noinputs b1' b2' (compose_behaviours_noinputs b1' b2' y_default)). {
    pose (@causal_composed_noinputs Y1 Y2) as Hni.
    unfold mixed_causal in *.
    apply Hni.
    apply Hb1'.
    apply Hb2'.
  }
  assert (forall k, compose_behaviours b1 b2 y_default uad k
            = compose_behaviours_noinputs b1' b2' y_default k) as Hcni. {
    intros k. unfold compose_behaviours. rewrite -> Heqb1', Heqb2'. trivial.
  }
  assert (forall k, py1 k = fst (compose_behaviours_noinputs b1' b2' y_default k)) as Hpy1.  {
    intro k. unfold py1. rewrite <- Hcni. reflexivity. }
  assert (forall k, py2 k = snd (compose_behaviours_noinputs b1' b2' y_default k)) as Hpy2. {
    intro k. unfold py2. rewrite <- Hcni. reflexivity. }
  assert (forall k, gy1 k = b1' (fun n => py2 n) k) as Hgy1. {
    intro k. unfold gy1. rewrite -> Heqb1'. reflexivity. }
  assert (forall k, gy2 k = b2' (fun n => py1 n) k) as Hgy2. {
    intro k. unfold gy2. rewrite -> Heqb2'. reflexivity. }
  unfold is_composed_behaviour_noinputs in H.
  destruct (H n) as [H1 H2].
  rewrite <- Hpy1 in H1.
  rewrite <- Hpy2 in H2.
  rewrite -> Hgy1, -> Hgy2.
  split.
  - rewrite <- H1.
    apply Heb1'.
    intros n'.
    rewrite <- Hpy2.
    reflexivity.
  - rewrite <- Hgy2.
    reflexivity.
Qed.


Definition preprocess1 {UA UD Y1 Y2 Y3} ( b1 : @Behaviour (UA * (UD*(Y2*Y3))) Y1 ) :=
  fun (v : nat->UA*((UD*Y3)*Y2)) => b1 (fun k => let vk:=v k in (fst vk,(fst (fst (snd vk)),(snd (snd vk),snd (fst (snd vk)))))).
Definition preprocess3 {UA UD Y1 Y2 Y3} ( b3 : @Behaviour ((UA*(Y1*Y2)) * UD) Y3 ) :=
  fun (v : nat->((UA*Y1)*Y2)*UD) => b3 (fun k => let vk:=v k in ((fst (fst (fst vk)),(snd (fst (fst vk)),snd (fst vk))),snd vk)).
Definition postprocess {UA UD Y1 Y2 Y3} ( b123 : @Behaviour (UA * UD) (Y1*(Y2*Y3)) ) :=
  fun (u : nat->UA*UD) => (fun k => let wk := b123 u k in ((fst wk,fst (snd wk)),snd (snd wk))).
Definition unpostprocess {UA UD Y1 Y2 Y3} ( b123 : @Behaviour (UA * UD) ((Y1*Y2)*Y3) ) :=
  fun (u : nat->UA*UD) => (fun k => let wk := b123 u k in (fst (fst wk),(snd (fst wk),snd wk))).


Lemma mixed_causal_preprocess1  {UA UD Y1 Y2 Y3} :
  forall (b1 : @Behaviour(UA*(UD*(Y2*Y3))) Y1),
    mixed_causal b1 -> mixed_causal (preprocess1 b1).
Proof.
  intros b1 Hc1.
  unfold mixed_causal, preprocess1.
  unfold mixed_causal in Hc1.
  intros u u' n.
  intros Hua1 Hud1.
  set (ua:=fun n=>fst (u n)); set (ud:=fun n=>(fst (fst (snd (u n)))));
  set (y2:=fun n=>snd (snd (u n))); set (y3:=fun n=>snd (fst (snd (u n)))).
  set (ua':=fun n=>fst (u' n)); set (ud':=fun n=>(fst (fst (snd (u' n)))));
  set (y2':=fun n=>snd (snd (u' n))); set (y3':=fun n=>snd (fst (snd (u' n)))).
  assert (forall n, ua n = fst (u n)) as Huan; [unfold ua; reflexivity|].
  assert (forall n, ua' n = fst (u' n)) as Huan'; [unfold ua'; reflexivity|].
  assert (forall n, snd (u n) = ((ud n,y3 n),y2 n)) as Hudn; [unfold ud, y2, y3; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity|].
  assert (forall n, snd (u' n) = ((ud' n,y3' n),y2' n)) as Hudn'. { unfold ud', y2', y3'; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity. }
  apply Hc1.
  - unfold ua, ua'. exact Hua1.
  - intros m Hmltn.
    simpl.
    specialize (Hud1 m Hmltn).
    rewrite -> Hudn, -> Hudn' in Hud1.
    unfold ud, y2, y3, ud', y2', y3' in Hud1.
    rewrite -> pair_equal_spec, -> pair_equal_spec in Hud1.
    f_equal; [|f_equal].
    apply Hud1. apply Hud1. apply Hud1.
Qed.

Lemma mixed_causal_preprocess3  {UA UD Y1 Y2 Y3} :
  forall (b3 : @Behaviour ((UA*(Y1*Y2))*UD) Y3),
    mixed_causal b3 -> mixed_causal (preprocess3 b3).
Proof.
  intros b3 Hc3.
  unfold mixed_causal, preprocess3.
  unfold mixed_causal in Hc3.
  intros u u' n.
  intros Hua3 Hud3.
  set (ua:=fun n=>fst (fst (fst (u n)))); set (ud:=fun n=>(snd (u n)));
  set (y1:=fun n=>snd (fst (fst (u n)))); set (y2:=fun n=>snd (fst (u n))).
  set (ua':=fun n=>fst (fst (fst (u' n)))); set (ud':=fun n=>(snd (u' n)));
  set (y1':=fun n=>snd (fst (fst (u' n)))); set (y2':=fun n=>snd (fst (u' n))).
  assert (forall n, fst (u n) = ((ua n,y1 n),y2 n)) as Huan; [unfold ua, y1, y2; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity|].
  assert (forall n, fst (u' n) = ((ua' n,y1' n),y2' n)) as Huan'; [unfold ua', y1', y2'; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity|].
  assert (forall n, ud n = snd (u n)) as Hudn; [unfold ud; reflexivity|].
  assert (forall n, ud' n = snd (u' n)) as Hudn'; [unfold ud'; reflexivity|].
  apply Hc3.
  - intros m Hmlen.
    simpl.
    specialize (Hua3 m Hmlen).
    rewrite -> Huan, -> Huan' in Hua3.
    unfold ua, y1, y2, ua', y1', y2' in Hua3.
    rewrite -> pair_equal_spec, -> pair_equal_spec in Hua3.
    f_equal; [|f_equal].
    apply Hua3. apply Hua3. apply Hua3.
  - unfold ud, ud'. exact Hud3.
Qed.


Theorem compose_behaviours_associative {UA UD Y1 Y2 Y3} :
  forall (b1 : @Behaviour (UA*(UD*(Y2*Y3))) Y1)
         (b2 : @Behaviour ((UA*Y1)*(UD*Y3)) Y2)
         (b3 : @Behaviour ((UA*(Y1*Y2))*UD) Y3)
         (y1_default : Y1) (y2_default : Y2),
    let pb1 := (preprocess1 b1) in
    let pb3 := (preprocess3 b3) in
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
      forall u n,
        (compose_behaviours (compose_behaviours pb1 b2 y1_default) b3 (y1_default,y2_default)) u n
          = (postprocess (compose_behaviours b1 (compose_behaviours b2 pb3 y2_default) y1_default)) u n.
Proof.
  intros b1 b2 b3 y1_default y2_default pb1 pb3 Hcb1 Hcb2 Hcb3.
  assert (mixed_causal pb1) as Hcpb1. { apply mixed_causal_preprocess1. exact Hcb1. }
  assert (mixed_causal pb3) as Hcpb3. { apply mixed_causal_preprocess3. exact Hcb3. }
  set (b12 := compose_behaviours pb1 b2 y1_default).
  set (b12_3 := compose_behaviours b12 b3 (y1_default, y2_default)).
  set (b23 := compose_behaviours b2 pb3 y2_default).
  set (b1_23 := compose_behaviours b1 b23 y1_default).
  assert (is_composed_behaviour pb1 b2 b12) as Hb12. {
    apply mixed_causal_composed. exact Hcpb1. exact Hcb2. }
  assert (mixed_causal b12) as Hcb12. {
    exact (behaviour_composition_mixed_causal pb1 b2 b12 Hcpb1 Hcb2 Hb12). }
  assert (is_composed_behaviour b12 b3 b12_3) as Hb12_3. {
    apply mixed_causal_composed. exact Hcb12. exact Hcb3. }
  assert (is_composed_behaviour b2 pb3 b23) as Hb23. {
    apply mixed_causal_composed. exact Hcb2. exact Hcpb3. }
  assert (mixed_causal b23) as Hcb23. {
    exact (behaviour_composition_mixed_causal b2 pb3 b23 Hcb2 Hcpb3 Hb23). }
  assert (is_composed_behaviour b1 b23 b1_23) as Hb1_23. {
    apply mixed_causal_composed. exact Hcb1. exact Hcb23. }
  intro u.
  intro n; revert n.
  set (ua := fun n => fst (u n)).
  set (ud := fun n => snd (u n)).
  set (y12_3 := b12_3 u).
  set (y3 := fun n => (snd (y12_3 n))).
  set (y12' := b12 (fun n => (ua n, (ud n, y3 n)))).
  set (y12 := fun n => fst (y12_3 n)).
  set (y1 := fun n => (fst (y12 n))).
  set (y2 := fun n => (snd (y12 n))).

  assert (forall n, b3 (fun n=>((ua n,(y1 n,y2 n)),ud n)) n = y3 n ) as Hy3. {
    unfold ua, ud, y1, y2, y12, y12_3.
    unfold y3, y12_3.
    intro n.
    rewrite -> (proj2 (Hb12_3 u n)).
    f_equal.
  }

  assert (forall n, b12 (fun n=>(ua n,(ud n, y3 n))) n = y12 n ) as Hy12. {
    unfold ua, ud, y1, y2, y12, y12_3.
    unfold y3, y12_3.
    intro n.
    rewrite -> (proj1 (Hb12_3 u n)).
    f_equal.
  }

  assert ( forall n, b12 (fun n=>(ua n,(ud n, y3 n))) n = y12' n ) as Hy12'. {
    unfold ua, ud, y1, y2, y12', y12_3.
    unfold y3, y12_3.
    intro n.
    f_equal.
  }

  assert (forall n, y12 n = y12' n) as Hy12e. {
    intro n. rewrite <- Hy12, -> Hy12'. reflexivity. }

  assert ( forall n, b1 (fun n=>(ua n,(ud n, (y2 n,y3 n)))) n = y1 n ) as Hy1. {
    unfold y1.
    unfold ua, ud, y1, y2, y12, y12_3.
    unfold y3, y12_3.

    intro n.
    rewrite -> (proj1 (Hb12_3 u n)).
    rewrite -> (proj1 (Hb12 (fun k=>(fst (u k), (snd (u k), snd (b12_3 u k)))) n)).
    unfold pb1, preprocess1.
    apply (mixed_causal_behaviour_extensional b1 Hcb1).
    intro m.
    f_equal. f_equal. f_equal.
    replace (b12_3 u) with y12_3; [|reflexivity].
    replace (b12 (fun k => (fst (u k), (snd (u k), snd (y12_3 k)))) m) with (b12 (fun k=>(ua k, (ud k, y3 k))) m).
    rewrite -> Hy12.
    reflexivity.
    f_equal.
  }

  assert ( forall n, b2 (fun n=>((ua n,y1 n),(ud n,y3 n))) n = y2 n ) as Hy2. {
    unfold y1.
    unfold ua, ud, y1, y2, y12, y12_3.
    unfold y3, y12_3.

    intro n.
    rewrite -> (proj1 (Hb12_3 u n)).
    rewrite -> (proj2 (Hb12 (fun k=>(fst (u k), (snd (u k), snd (b12_3 u k)))) n)).
    apply (mixed_causal_behaviour_extensional b2 Hcb2).
    intro m.
    f_equal. f_equal. f_equal.
    replace (b12_3 u) with y12_3; [|reflexivity].
    replace (b12 (fun k => (fst (u k), (snd (u k), snd (y12_3 k)))) m) with (b12 (fun k=>(ua k, (ud k, y3 k))) m).
    rewrite -> Hy12.
    reflexivity.
    f_equal.
  }

  (* Cleanup. *)
  unfold y12 in y1, y2.
  clear Hy12' Hy12e y12' Hy12 Hb12 Hb12_3 y12.
  set (y23 := fun n => (y2 n, y3 n)).
  set (y1_23 := fun n => (y1 n, y23 n)).

  (* Now show that y1, y2, y3 satisfy conditions for b1_23. *)
  assert (forall n, b23 (fun k => ((ua k,y1 k),ud k)) n = y23 n) as Hy23'. {
    set (uy1 := fun k => ((ua k,y1 k),ud k)).
    set (y23' := b23 uy1).
    intro n.
    replace (y23' n) with (fst (y23' n), snd (y23' n)).
    revert n.
    unfold y23.
    unfold is_composed_behaviour in Hb23.
    apply (composed_mixed_causal_outputs_unique b2 pb3 Hcb2 Hcpb3 uy1).
    - intro n. apply eq_sym. apply (proj1 (Hb23 uy1 n)).
    - intro n. rewrite <- Hy2. f_equal.
    - intro n. apply eq_sym. apply (proj2 (Hb23 uy1 n)).
    - intro n. unfold pb3, preprocess3. rewrite <- Hy3. reflexivity.
    - apply surjective_pairing.
  }

  assert (forall n, b1_23 (fun k => (ua k, ud k)) n = y1_23 n) as Hy1_23'. {
    unfold y1_23.
    set (y1_23' := b1_23 (fun k => (ua k, ud k))).
    intro n. replace (y1_23' n) with (fst (y1_23' n), snd (y1_23' n)). revert n.
    apply (composed_mixed_causal_outputs_unique b1 b23 Hcb1 Hcb23 (fun k => (ua k, ud k))).
    - intro n. apply eq_sym. apply (proj1 (Hb1_23 u n)).
    - intro n. rewrite <- Hy1. f_equal.
    - intro n. apply eq_sym. apply (proj2 (Hb1_23 u n)).
    - intro n. unfold pb3, preprocess3. rewrite <- Hy23'. reflexivity.
    - apply surjective_pairing.
  }
  assert (forall n, b1_23 u n = y1_23 n) as Hy1_23. {
    intro n. rewrite <- Hy1_23'. reflexivity.
  }
  unfold postprocess.
  intro n.
  rewrite -> Hy1_23.
  reflexivity.
Qed.


Theorem behaviour_composition_associative {UA UD Y1 Y2 Y3 : Type} :
  forall (b1 : @Behaviour (UA * (UD*(Y2*Y3))) Y1)
         (b2 : @Behaviour ((UA*Y1) * (UD*Y3)) Y2)
         (b3 : @Behaviour ((UA*(Y1*Y2)) * UD) Y3)
         (b123 : @Behaviour (UA * UD) ((Y1*Y2)*Y3)),
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
    (inhabited (UA * UD)) ->
    ( exists b12 : @Behaviour (UA * (UD*Y3)) (Y1*Y2),
        (is_composed_behaviour (preprocess1 b1) b2 b12) /\ (is_composed_behaviour b12 b3 b123) )
    <->
    ( exists b23 : @Behaviour ((UA*Y1) * UD) (Y2*Y3),
        (is_composed_behaviour b2 (preprocess3 b3) b23) /\ (is_composed_behaviour b1 b23 (unpostprocess b123)) )
.
Proof.
  intros b1 b2 b3 b123 Hcb1 Hcb2 Hcb3.
  intro Hu; destruct Hu as [u_default].
  set (y123_default := b123 (fun n => u_default) 0).
  destruct y123_default as [[y1_default y2_default] _].
  set (pb1 := preprocess1 b1). set (pb3 := preprocess3 b3).
  assert (mixed_causal pb1) as Hcpb1. { apply mixed_causal_preprocess1. exact Hcb1. }
  assert (mixed_causal pb3) as Hcpb3. { apply mixed_causal_preprocess3. exact Hcb3. }
  set (b23 := compose_behaviours b2 pb3 y2_default).
  assert (is_composed_behaviour b2 pb3 b23) as Hb23. {
    apply mixed_causal_composed. exact Hcb2. exact Hcpb3. }
  assert (mixed_causal b23) as Hcb23. {
    apply (behaviour_composition_mixed_causal b2 pb3). exact Hcb2. exact Hcpb3. exact Hb23. }
  set (b1_23 := compose_behaviours b1 b23 y1_default).
  assert (is_composed_behaviour b1 b23 b1_23) as Hb1_23. {
    apply mixed_causal_composed. exact Hcb1. exact Hcb23. }
  set (b12 := compose_behaviours pb1 b2 y1_default).
  assert (is_composed_behaviour pb1 b2 b12) as Hb12. {
    apply mixed_causal_composed. exact Hcpb1. exact Hcb2. }
  assert (mixed_causal b12) as Hcb12. {
    apply (behaviour_composition_mixed_causal pb1 b2). exact Hcpb1. exact Hcb2. exact Hb12. }
  set (b12_3 := compose_behaviours b12 b3 (y1_default,y2_default)).
  assert (is_composed_behaviour b12 b3 b12_3) as Hb12_3. {
    apply mixed_causal_composed. exact Hcb12. exact Hcb3. }
  assert (forall u n, b12_3 u n = postprocess b1_23 u n) as Hb123p. {
    apply compose_behaviours_associative.
    exact Hcb1. exact Hcb2. exact Hcb3.
  }
  assert (forall u n, unpostprocess b12_3 u n = b1_23 u n) as Hb123up. {
    intros u n.
    unfold unpostprocess.
    rewrite -> Hb123p.
    unfold postprocess.
    reflexivity.
  }
  split.
  - intros H.
    exists b23.
    split.
    -- apply mixed_causal_composed. exact Hcb2. exact Hcpb3.
    -- destruct H as [b12' [Hb12' Hb123']].
       assert (forall u n, b12 u n = b12' u n) as Hb12e. {
         exact (composed_mixed_causal_behaviour_unique pb1 b2 b12 b12' Hcpb1 Hcb2 Hb12 Hb12'). }
       assert (mixed_causal b12') as Hcb12'. {
         exact (mixed_causal_equivalent_behaviours b12 b12' Hb12e Hcb12). }
       assert (is_composed_behaviour b12 b3 b123) as Hb123. {
         apply (is_composed_behaviour_input_extensional b12' b12 b3 b3 b123 Hcb12' Hcb12 Hcb3 Hcb3).
         intros uy2 n. apply eq_sym. apply Hb12e.
         reflexivity. exact Hb123'.
       }
       assert (forall u n, b123 u n = b12_3 u n) as Hb123e. {
         exact (composed_mixed_causal_behaviour_unique b12 b3 b123 b12_3 Hcb12 Hcb3 Hb123 Hb12_3). }
       assert (is_composed_behaviour b1 b23 (unpostprocess b12_3)) as Hb12_3'. {
         apply (is_composed_behaviour_output_extensional b1 b23 b1_23 (unpostprocess b12_3) Hcb1 Hcb23).
         intros u n; apply eq_sym; exact (Hb123up u n). exact Hb1_23.
       }
       apply (is_composed_behaviour_output_extensional b1 b23 b1_23 (unpostprocess b123) Hcb1 Hcb23).
       intros u n. rewrite <- Hb123up. unfold unpostprocess. rewrite -> Hb123e. reflexivity.
       exact Hb1_23.
  - intros H.
    exists b12.
    split.
    -- apply mixed_causal_composed. exact Hcpb1. exact Hcb2.
    -- destruct H as [b23' [Hb23' Hb123']].
       assert (forall u n, b23 u n = b23' u n) as Hb23e. {
         exact (composed_mixed_causal_behaviour_unique b2 pb3 _ _ Hcb2 Hcpb3 Hb23 Hb23'). }
       assert (mixed_causal b23') as Hcb23'. {
         exact (mixed_causal_equivalent_behaviours b23 b23' Hb23e Hcb23). }
       assert (is_composed_behaviour b1 b23 (unpostprocess b123)) as Hb123. {
         apply (is_composed_behaviour_input_extensional b1 b1 b23' b23 (unpostprocess b123) Hcb1 Hcb1 Hcb23' Hcb23).
         reflexivity.
         apply (composed_mixed_causal_behaviour_unique b2 pb3 b23' b23 Hcb2 Hcpb3 Hb23' Hb23).
         exact Hb123'.
       }
       assert (forall u n, unpostprocess b123 u n = b1_23 u n) as Hb123e'. {
         exact (composed_mixed_causal_behaviour_unique b1 b23 (unpostprocess b123) b1_23 Hcb1 Hcb23 Hb123 Hb1_23). }
       assert (forall u n, b12_3 u n = b123 u n) as Hb123e. {
         intros u n. rewrite -> Hb123p.
         unfold postprocess.
         rewrite <- Hb123e'.
         unfold unpostprocess.
         simpl.
         rewrite <- surjective_pairing, <- surjective_pairing.
         reflexivity.
       }
       exact (is_composed_behaviour_output_extensional b12 b3 b12_3 b123 Hcb12 Hcb3 Hb123e Hb12_3).
Qed.

