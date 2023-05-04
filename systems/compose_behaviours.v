(* ---------------------------------------------------------------- *)
(* Author:       SINDORF, S.L. & COLLINS, P.
   Date:         20221231
   Supervisor:   COLLINS, P.
   Description:  Coq, Gallina-code

                 Proof that behavior of composed system is composed
                 behavior of components.
                 Composition at behavioral level.

                 Master's Thesis Artificial Intelligence
                 Maastricht University
*)

(* Definition and correctness proof of composition of mixed causal behaviours: *)
(************************************************************************)
(* Copyright 2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Import Coq.Arith.PeanoNat.

Require Export definitions.
Require Export system_problems.

Notation causal := definitions.causal.
Notation causal' := definitions.causal'.
Notation strictly_causal := definitions.strictly_causal.
Notation strictly_causal' := definitions.strictly_causal'.
Notation strictly_causal_equivalent := definitions.strictly_causal_equivalent.
Notation mixed_causal := definitions.mixed_causal.
Notation is_composed_behaviour := system_problems.is_composed_behaviour.

(* Think of a better name than 'combine', maybe 'function_compose' *)
Definition combine_behaviours_noinputs
  {Y1 Y2 : Type}
  (b1 : (nat->Y2)->(nat->Y1))
  (b2 : (nat->Y1)->(nat->Y2))
  : (nat->Y1) -> (nat->Y1) := fun y1s => b1 (b2 y1s) .


Fixpoint iterated_behaviours_noinputs
  {Y : Type}
  (b : (nat->Y)->(nat->Y))
  (y_default : Y)
  (n : nat)
  : (nat->Y) :=
    match n with
    | O => b (fun _ => y_default)
    | S n' => b (iterated_behaviours_noinputs b y_default n')
    end.

Definition fixed_behaviour_noinputs
  {Y : Type}
  (b : (nat->Y)->(nat->Y))
  (y_default : Y)
  : (nat->Y) := fun n => (iterated_behaviours_noinputs b y_default (S n)) n.

Definition zip {Y1 Y2 : Type} (y1s : nat->Y1) (y2s : nat->Y2) : nat->(Y1*Y2)
  := fun n => (y1s n, y2s n).

Definition extend_behaviour_noinputs
  {Y1 Y2 : Type}
  (y1s : (nat->Y1))
  (b2 : (nat->Y1)->(nat->Y2))
  : (nat->(Y1*Y2)) := zip y1s (b2 y1s).
(*  let y2s := b2 y1s in (y1s n, y2s n). *)

(* Maybe call 'parallel_compose_behaviours_noinputs' *)
Definition compose_behaviours_noinputs
  {Y1 Y2 : Type}
  (b1 : (nat->Y2)->(nat->Y1))
  (b2 : (nat->Y1)->(nat->Y2))
  (y_default : Y1)
  : (nat->Y1*Y2) :=
    let b := combine_behaviours_noinputs b1 b2 in
    let y1s := fixed_behaviour_noinputs b y_default in
    extend_behaviour_noinputs y1s b2
.

Definition is_composed_behaviour_noinputs {Y1 Y2 : Type}
  (b1 : (nat->Y2) -> (nat->Y1))
  (b2 : (nat->Y1) -> (nat->Y2))
  (b12 : (nat->Y1*Y2))
  : Prop :=
  forall (n:nat),
     ( b1 (fun k => snd (b12 k)) n = fst (b12 n) ) /\
     ( b2 (fun k => fst (b12 k)) n = snd (b12 n) )
.

Definition is_fixed_behaviour_noinputs {Y : Type} (b : (nat->Y)->(nat->Y)) (ys : nat->Y) : Prop
  := forall (n:nat), (b ys) n = ys n.

(* Show that the fixed behaviour of the combined behaviour extends to the composed behaviour. *)
Lemma combined_behaviour_causal_noinputs {Y1 Y2 : Type} :
  forall (b1 : (nat->Y2) -> (nat->Y1))
         (b2 : (nat->Y1) -> (nat->Y2)),
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
    - (* Search (_ < 0). *)
      intros m1 H3.
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
  forall (b : (nat->Y) -> (nat->Y))
         (u u' : nat -> Y),
         (strictly_causal b) -> b u 0 = b u' 0.
Proof.
  intros b u u'.
  unfold strictly_causal.
  intros Hscb.
  apply Hscb with (n:=0).
  - intros m H0.
    (* Search (_ < 0). *)
    apply Nat.nlt_0_r in H0.
    exfalso. apply H0.
  - reflexivity.
Qed.

Lemma causal_fixed_noinputs_succ {Y : Type} :
  forall (b : (nat->Y) -> (nat->Y))
         (u u' : nat -> Y) (n : nat),
         (strictly_causal b) -> (forall m:nat, m<=n -> u m = u' m) -> b u (S n) = b u' (S n).
Proof.
  intros b u u' n.
  unfold strictly_causal.
  intros Hscb H0.
  apply Hscb with (n:= S n).
  - intros m H1.
    (* Search (_ < S _). *)
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
         (* Search (_ < _ + _). *)
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
        (* Search (_+_). *)
        symmetry.
        (* Check Nat.sub_add.
              : ∀ n m : nat, n ≤ m → m - n + n = m
        *)
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
    - (* Search (_ < S _). *)
      apply Nat.lt_succ_diag_r.
    - (* Search (_ <= S _). *)
      rewrite <- Nat.succ_le_mono.
      apply H4.
  }

  intros n m H4.
  induction n as [|n' IHn'].
  - (* Search (_<0). *)
    apply Nat.nlt_0_r in H4.
    exfalso. exact H4.
  - apply H3.
    (* Search (_ < S _). *)
    apply (Nat.lt_succ_r m n') in H4.
    exact H4.
Qed.


(*
Lemma table {Y : Type} (B:nat->nat->Y) :
  (forall n m, m<n -> B (S n) m = B n m) ->
   forall n m, m<n -> B n m = B (S m) m.
*)

Lemma causal_iterated_behaviours_noinputs {Y : Type} (b:(nat->Y)->(nat->Y)) (y_default:Y) :
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

(* Check strong_induction. *)

(* Show that the fixed behaviour is indeed a fixed-point. *)
Proposition causal_fixed_noinputs {Y : Type} :
  forall (b : (nat->Y) -> (nat->Y))
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
      * (* Search (_ < S _ <-> _ ≤ _). *)
        rewrite Nat.lt_succ_r.
        exact H0.
Qed.


(* Show that the fixed behaviour of the combined behaviour extends to the composed behaviour. *)
Lemma causal_fixed_is_composed_noinputs {Y1 Y2 : Type} :
  forall (b1 : (nat->Y2) -> (nat->Y1))
         (b2 : (nat->Y1) -> (nat->Y2))
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
  forall (b1 : (nat->Y2) -> (nat->Y1))
         (b2 : (nat->Y1)->(nat->Y2))
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
  forall (b1 : (nat->Y2) -> (nat->Y1))
         (b2 : (nat->Y1)->(nat->Y2))
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
    (b1 : (nat -> UA*(UD*Y2)) -> (nat -> Y1))
    (b2 : (nat -> (UA*Y1)*UD) -> (nat -> Y2))
    (y_default : Y1)
      : (nat -> (UA*UD)) -> (nat -> (Y1*Y2)) :=
  fun (uad : nat -> UA*UD) =>
    let ua := fun n => fst (uad n) in
    let ud := fun n => snd (uad n) in
    let b1' := fun (y2 : nat -> Y2) => b1 (fun n => (ua n, (ud n, y2 n))) in
    let b2' := fun (y1 : nat -> Y1) => b2 (fun n => ((ua n, y1 n), ud n)) in
      compose_behaviours_noinputs b1' b2' y_default.


Definition extensional {U Y : Type} (b : (nat -> U) -> (nat -> Y)) :=
  forall u u', (forall n, u n = u' n) -> (forall n, (b u) n = (b u') n).

Lemma strictly_causal_extensional {U Y} : forall (b:(nat->U)->(nat->Y)),
  strictly_causal b -> extensional b.
Proof.
  unfold strictly_causal, extensional.
  intros b Hc. intros u u' Hu n. apply (Hc u u' n).
  intros m Hm. apply Hu. apply Nat.le_refl.
Qed.



Theorem mixed_causal_composed {UA UD Y1 Y2 : Type} :
  forall (b1 : (nat->UA*(UD*Y2)) -> (nat->Y1))
         (b2 : (nat->(UA*Y1)*UD) -> (nat->Y2))
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
    intros u u' n' Hsc. rewrite -> Heqb1'. apply Hb1. trivial.
    intros m' Hm'. f_equal. apply Hsc. exact Hm'. 
  }
  assert (causal b2') as Hb2'. {
    unfold causal. unfold mixed_causal in Hb2.
    intros u u' n' Hc. rewrite -> Heqb2'. apply Hb2. 
    intros m' Hm'. f_equal. apply Hc. exact Hm'. trivial. 
  }
  assert (extensional b1') as Heb1'. { 
    apply strictly_causal_extensional. exact Hb1'. 
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
