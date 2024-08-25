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
Require Import Coq.Classes.RelationClasses.

Module causality.

Notation "n1 ≤ n2" := (n1 <= n2) (at level 70).

Definition Tr (X : Type) : Type := nat -> X.
Definition trace_equivalent {X : Type} (x1 x2 : Tr X) : Prop :=
  forall n, x1 n = x2 n.
Notation "x1 ≡ x2" := (trace_equivalent x1 x2) (at level 70).
Notation "x1 '|<' n '|≡' x2" := (forall m, m<n -> x1 m = x2 m) (at level 40).
Notation "x1 |≤ n |≡ x2" := (forall m, m <= n -> x1 m = x2 m) (at level 40).

#[export]
#[refine]
Instance trace_equivalence {X} : Equivalence (@trace_equivalent X) := { }.
Proof.
  - intros u n. reflexivity.
  - intros u1 u2 H n. symmetry. exact (H n).
  - intros u1 u2 u3 H12 H23 n.
    transitivity (u2 n). exact (H12 n). exact (H23 n).
Qed.


Definition zip {T1 T2} (s1 : Tr T1) (s2 : Tr T2) := fun n => (s1 n, s2 n).
Definition unzip {T1 T2} (s : Tr (T1*T2)) := (fun n => fst (s n), fun n => snd (s n)).
Notation "( u1 ; u2 )" := (zip u1 u2) (at level 0).

Lemma zip_unzip {UA UD} : 
  forall (u : Tr (UA*UD)),
    zip (fst (unzip u)) (snd (unzip u)) ≡ u.
Proof.
  intros u n. unfold zip,unzip. simpl. 
  now rewrite <- surjective_pairing.
Qed.

Lemma unzip_zip {UA UD} : 
  forall (ua : Tr UA) (ud : Tr UD),
    unzip (zip ua ud) = (ua,ud).
Proof.
  intros ua ud. now unfold zip,unzip.
Qed.

Lemma equal_projections : forall (A B : Type) (p1 p2 : A * B),
  forall (e : p1=p2), (fst p1 = fst p2) /\ (snd p1 = snd p2).
Proof. intros A B p1 p2 e. now rewrite <- e. Qed.
  
Lemma zip_prod {UA UD} : 
  forall (ua ua' : Tr UA) (ud ud' : Tr UD),
    ua ≡ ua' /\ ud ≡ ud' <-> (ua;ud) ≡ (ua';ud').
Proof.
  intros ua ua' ud ud'. 
  split.
  - intro Huad. destruct Huad as [Hua Hud].
    unfold zip. intro n. f_equal. apply Hua. apply Hud.
  - intro Huad. unfold zip in Huad. split.
    -- intro n. specialize (Huad n). 
       apply (f_equal fst) in Huad. simpl in Huad. exact Huad.
    -- intro n. specialize (Huad n). 
       apply (f_equal snd) in Huad. simpl in Huad. exact Huad.
Qed.
Lemma zip_prod_l {UA UD} : 
  forall (ua : Tr UA) (ud ud' : Tr UD),
    ud ≡ ud' -> (ua;ud) ≡ (ua;ud').
Proof. 
  intros ua ud ud' Hud. apply zip_prod. split.
  reflexivity. assumption.
Qed.
Lemma zip_prod_r {UA UD} : 
  forall (ua ua' : Tr UA) (ud : Tr UD),
    ua ≡ ua' -> (ua;ud) ≡ (ua';ud).
Proof. 
  intros ua ua' ud Hua. apply zip_prod. split.
  assumption. reflexivity.
Qed.

Lemma zip_prod_lt {U1 U2} : 
  forall (u1 u1' : Tr U1) (u2 u2' : Tr U2) (n:nat),
    u1 |< n |≡ u1' -> u2 |< n |≡ u2' -> (u1;u2) |< n |≡ (u1';u2').
Proof.
  intros u1 u1' u2 u2' n Hu1 Hu2 m Hmltn.
  unfold zip, unzip. f_equal.
  - exact (Hu1 m Hmltn).
  - exact (Hu2 m Hmltn).
Qed.

Lemma unzip_prod {UA UD} :
  forall (ua : Tr UA) (ud : Tr UD) (u : Tr (UA*UD)),
    (ua,ud) = unzip u -> (ua;ud) ≡ u.
Proof.
  unfold zip, unzip. intros ua ud u H n.
  apply injective_projections. 
  - apply (f_equal fst) in H. simpl in H. now rewrite -> H.
  - apply (f_equal snd) in H. simpl in H. now rewrite -> H. Qed.
Lemma fst_unzip_proj {UA UD} 
  {u : Tr (UA*UD)} {ua : Tr UA} {ud : Tr UD} : 
    forall (e : (ua,ud) = unzip u), 
      ua = fst (unzip u).
Proof. intro H. now apply (f_equal fst) in H. Qed.
Lemma unzip_proj {UA UD} 
  {u : Tr (UA*UD)} {ua : Tr UA} {ud : Tr UD} : 
    forall (e : (ua,ud) = unzip u), 
      ua = fst (unzip u) /\ ud = snd (unzip u).
Proof.
  intro H. split.
  now apply (f_equal fst) in H. 
  now apply (f_equal snd) in H.
Qed.
Lemma fst_unzip_prod {UA UD} :
  forall (u u' : Tr (UA*UD)),
    u ≡ u' -> fst (unzip u) ≡ fst (unzip u').
Proof.
  intros u u' H n. unfold unzip. simpl. now rewrite <- (H n).
Qed.
Lemma snd_unzip_prod {UA UD} :
  forall (u u' : Tr (UA*UD)),
    u ≡ u' -> snd (unzip u) ≡ snd (unzip u').
Proof.
  intros u u' H n. unfold unzip. simpl. now rewrite <- (H n).
Qed.

Lemma eqv_le_lt_succ {U} : 
  forall (u u' : Tr U) (n : nat),
    u |≤ n |≡ u' -> u |< (S n) |≡ u'.
Proof.
  intros u u' n Hu m HmltSn.
  set (Hmlen := (proj1 (Nat.lt_succ_r _ _)) HmltSn).
  exact (Hu m Hmlen).
Qed.

Lemma all_eqv_lt {U} :
  forall (u u' : Tr U),
    (forall n, u |< n |≡ u') -> u ≡ u'.
Proof.
  intros u u' H n. exact (H (S n) n (Nat.lt_succ_diag_r n)).
Qed.

(* A behaviour is a function from input sequences to output sequences. *)
Definition Behaviour (U:Type) (Y:Type) : Type := 
  Tr U -> Tr Y.

Definition behaviour_equivalent {U Y} (b1 b2 : Behaviour U Y) : Prop :=
  forall u n, b1 u n = b2 u n.
Notation "b1 ≣ b2" := (behaviour_equivalent b1 b2) (at level 70).

#[export]
#[refine]
Instance behaviour_equivalence {U Y} : Equivalence (@behaviour_equivalent U Y) := { }.
Proof.
  - intros b u n. reflexivity.
  - intros b1 b2 H u n. symmetry. exact (H u n).
  - intros b1 b2 b3 H12 H23 u n.
    transitivity (b2 u n). exact (H12 u n). exact (H23 u n).
Qed.


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
Definition strictly_causal {U Y : Type} 
    (b : Behaviour U Y) : Prop :=
  forall u u' : Tr U, forall n:nat, 
    u |<n |≡ u' -> b u |≤n |≡ b u'
.

(* A weaker definition of strict causality which turns out to be equivalent. *)
(* A behaviour is struct causal if the output at time n depends only on the input up to time n. *)
Definition strictly_causal' {U Y : Type}
    (b : Behaviour U Y) : Prop :=
  forall u u' : Tr U, forall n:nat, 
      u |<n |≡ u' -> b u n = b u' n
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

Definition mixed_causal {UA UD Y}
   (b : Behaviour (UA*UD) Y) : Prop :=
  forall (u u':Tr (UA*UD)) (n:nat),
    let (ua,ud):=unzip u in let (ua',ud'):=unzip u' in
      ua |≤n |≡ ua' -> ud |<n |≡ ud' -> b u |≤n |≡ b u'.

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


Definition extensional {U Y : Type} (b : Behaviour U Y) :=
  forall u u', u ≡ u' -> b u ≡ b u'.

Lemma strictly_causal_behaviour_extensional {U Y} : forall (b : Behaviour U Y),
  strictly_causal b -> extensional b.
Proof.
  unfold strictly_causal, extensional.
  intros b Hc. intros u u' Hu n. apply (Hc u u' n).
  intros m Hm. apply Hu. apply Nat.le_refl.
Qed.


Lemma mixed_causal_behaviour_extensional {UA UD Y} : forall (b : Behaviour (UA*UD) Y),
  mixed_causal b -> extensional b.
Proof.
  unfold mixed_causal, extensional.
  intros b Hc. intros u u' Hu n. apply (Hc u u' n).
  intros m Hm. rewrite <- Hu. reflexivity.
  intros m Hm. rewrite <- Hu. reflexivity.
  apply Nat.le_refl.
Qed.

Lemma mixed_causal_equivalent_behaviours {UA UD Y} : forall (b b' : @Behaviour (UA*UD) Y),
  b ≣ b' -> mixed_causal b -> mixed_causal b'.
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
