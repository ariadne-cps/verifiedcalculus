(******************************************************************************
 *  systems/cauality.v
 *
 *  Copyright 2023 Sacha L. Sindorf
 *                 Master's Thesis Artificial Intelligence
 *                 Maastricht University
 *
 *  Copyright 2023-24 Pieter Collins
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
  - intros x12 n. reflexivity.
  - intros x1 x2 H n. symmetry. exact (H n).
  - intros x1 x2 u3 H12 H23 n.
    transitivity (x2 n). exact (H12 n). exact (H23 n).
Qed.


Definition zip {X1 X2} (x1 : Tr X1) (x2 : Tr X2) := fun n => (x1 n, x2 n).
Definition unzip {X1 X2} (x12 : Tr (X1*X2)) := (fun n => fst (x12 n), fun n => snd (x12 n)).
Notation "( x1 ; x2 )" := (zip x1 x2) (at level 0).

Lemma zip_unzip {X1 X2} : 
  forall (x12 : Tr (X1*X2)),
    zip (fst (unzip x12)) (snd (unzip x12)) ≡ x12.
Proof.
  intros x12 n. unfold zip,unzip. simpl. 
  now rewrite <- surjective_pairing.
Qed.

Lemma unzip_zip {X1 X2} : 
  forall (x1 : Tr X1) (x2 : Tr X2),
    unzip (zip x1 x2) = (x1,x2).
Proof.
  intros x1 ud. now unfold zip,unzip.
Qed.

(* Definition unzip_eqv {X1 X2} (x12 : Tr (X1*X2)) : { x12 : (Tr X1) * (Tr X2) | ( (fst x12;snd x12) ≡ x12 ) }
  := exist _ (unzip x12) (zip_unzip x12). 
*)

Inductive sig_pair {A B : Type} (P : A -> B -> Prop) : Type :=
  exist_pair : forall (x : A) (y : B), P x y -> sig_pair P.

Definition unzip_eqv {X1 X2} (x12 : Tr (X1*X2)) : @sig_pair (Tr X1) (Tr X2) (fun x1 x2 => (x1;x2) ≡ x12 )
  := exist_pair _ (fst (unzip x12)) (snd (unzip x12)) (zip_unzip x12). 

Definition unzip_eq {X1 X2} (x12 : Tr (X1*X2))
    : @sig_pair (Tr X1) (Tr X2) (fun x1 x2 => ((x1 = fst (unzip x12)) /\ x2 = snd (unzip x12)) /\ (x1;x2) ≡ x12 ).
Proof.
  set (x1 := fst (unzip x12)).
  set (x2 := snd (unzip x12)).
  assert ((x1 = fst (unzip x12) /\ x2 = snd (unzip x12)) /\ (x1;x2)≡x12) as p. {
    split. split. reflexivity. reflexivity. now apply (zip_unzip x12). }
  exact (exist_pair _ x1 x2 p).
Qed.


Definition unzip3_l {X1 X2 X3} (x123 : Tr ((X1*X2)*X3))
  := ( ( fun n => fst (fst (x123 n)), fun n => snd (fst (x123 n)) ), fun n => snd (x123 n) ) .
Lemma zip_unzip3_l {X1 X2 X3} :
  forall (x123 : Tr ((X1*X2)*X3)),
    x123 ≡ ((fst (unzip (fst (unzip x123))); 
             snd (unzip (fst (unzip x123)))); 
            snd (unzip x123)).
Proof.
  intros x n. unfold zip,unzip. simpl.
  rewrite <- surjective_pairing. now rewrite <- surjective_pairing.
Qed.
Lemma zip_unzip3_l' {X1 X2 X3} : 
  forall (x : Tr ((X1*X2)*X3)),
    zip (zip (fst (unzip (fst (unzip x)))) (snd (unzip (fst (unzip x))))) (snd (unzip x)) ≡ x.
Proof.
  intros x n. unfold zip,unzip. simpl.
  rewrite <- surjective_pairing. now rewrite <- surjective_pairing.
Qed.
Definition unzip3_l_eqv {X1 X2 X3} (x123 : Tr ((X1*X2)*X3))
  : { x1x2x3 : ((Tr X1) * (Tr X2)) * (Tr X3) | ( ((fst (fst x1x2x3);snd (fst x1x2x3));snd x1x2x3) ≡ x123) }
    := exist _ (unzip3_l x123) (zip_unzip3_l' x123). 

Definition unzip3_r {X1 X2 X3} (x123 : Tr (X1*(X2*X3)))
  := ( fun n => fst (x123 n), ( fun n => fst (snd (x123 n)), fun n => snd (snd (x123 n))) ) .
Lemma zip_unzip3_r {X1 X2 X3} :
  forall (x123 : Tr (X1*(X2*X3))),
    x123 ≡ (fst (unzip x123);
            (fst (unzip (snd (unzip x123))); 
             snd (unzip (snd (unzip x123))))).
Proof.
  intros x n. unfold zip,unzip. simpl.
  rewrite <- surjective_pairing. now rewrite <- surjective_pairing.
Qed.
Lemma zip_unzip3_r' {X1 X2 X3} : 
  forall (x : Tr (X1*(X2*X3))),
    zip (fst (unzip x)) (zip (fst (unzip (snd (unzip x)))) (snd (unzip (snd (unzip x))))) ≡ x.
Proof.
  intros x n. unfold zip,unzip. simpl.
  rewrite <- surjective_pairing. now rewrite <- surjective_pairing.
Qed.
Definition unzip3_r_eqv {X1 X2 X3} (x123 : Tr (X1*(X2*X3)))
  : { x1x2x3 : (Tr X1) * ((Tr X2) * (Tr X3)) | 
      ( (fst x1x2x3;(fst (snd (x1x2x3));snd (snd x1x2x3))) ≡ x123) }
    := exist _ (unzip3_r x123) (zip_unzip3_r' x123). 


Lemma equal_projections : forall (A B : Type) (p1 p2 : A * B),
  forall (e : p1=p2), (fst p1 = fst p2) /\ (snd p1 = snd p2).
Proof. intros A B p1 p2 e. now rewrite <- e. Qed.
  
Lemma zip_prod {X1 X2} : 
  forall (x1 x1' : Tr X1) (x2 x2' : Tr X2),
    x1 ≡ x1' /\ x2 ≡ x2' <-> (x1;x2) ≡ (x1';x2').
Proof.
  intros x1 x1' x2 x2'. 
  split.
  - intro Huad. destruct Huad as [Hua Hud].
    unfold zip. intro n. f_equal. apply Hua. apply Hud.
  - intro Huad. unfold zip in Huad. split.
    -- intro n. specialize (Huad n). 
       apply (f_equal fst) in Huad. simpl in Huad. exact Huad.
    -- intro n. specialize (Huad n). 
       apply (f_equal snd) in Huad. simpl in Huad. exact Huad.
Qed.
Lemma zip_prod_l {X1 X2} : 
  forall (x1 : Tr X1) (x2 x2' : Tr X2),
    x2 ≡ x2' -> (x1;x2) ≡ (x1;x2').
Proof. 
  intros x1 x2 x2' Hud. apply zip_prod. split.
  reflexivity. assumption.
Qed.
Lemma zip_prod_r {X1 X2} : 
  forall (x1 x1' : Tr X1) (x2 : Tr X2),
    x1 ≡ x1' -> (x1;x2) ≡ (x1';x2).
Proof. 
  intros x1 x1' x2 Hua. apply zip_prod. split.
  assumption. reflexivity.
Qed.

Lemma zip_prod_lt {X1 X2} : 
  forall (x1 x1' : Tr X1) (x2 x2' : Tr X2) (n:nat),
    x1 |< n |≡ x1' -> x2 |< n |≡ x2' -> (x1;x2) |< n |≡ (x1';x2').
Proof.
  intros x1 x1' x2 x2' n Hx1 Hx2 m Hmltn.
  unfold zip, unzip. f_equal.
  - exact (Hx1 m Hmltn).
  - exact (Hx2 m Hmltn).
Qed.

Lemma unzip_prod {X1 X2} :
  forall (x1 : Tr X1) (x2 : Tr X2) (x12 : Tr (X1*X2)),
    (x1,x2) = unzip x12 -> (x1;x2) ≡ x12.
Proof.
  unfold zip, unzip. intros x1 x2 x12 H n.
  apply injective_projections. 
  - apply (f_equal fst) in H. simpl in H. now rewrite -> H.
  - apply (f_equal snd) in H. simpl in H. now rewrite -> H. Qed.
Lemma fst_unzip_proj {X1 X2} 
  {x12 : Tr (X1*X2)} {x1 : Tr X1} {x2 : Tr X2} : 
    forall (e : (x1,x2) = unzip x12), 
      x1 = fst (unzip x12).
Proof. intro H. now apply (f_equal fst) in H. Qed.
Lemma unzip_proj {X1 X2} 
  {x12 : Tr (X1*X2)} {x1 : Tr X1} {x2 : Tr X2} : 
    forall (e : (x1,x2) = unzip x12), 
      x1 = fst (unzip x12) /\ x2 = snd (unzip x12).
Proof.
  intro H. split.
  now apply (f_equal fst) in H. 
  now apply (f_equal snd) in H.
Qed.
Lemma fst_unzip_prod {X1 X2} :
  forall (x12 x12' : Tr (X1*X2)),
    x12 ≡ x12' -> fst (unzip x12) ≡ fst (unzip x12').
Proof.
  intros x12 x12' H n. unfold unzip. simpl. now rewrite <- (H n).
Qed.
Lemma snd_unzip_prod {X1 X2} :
  forall (x12 x12' : Tr (X1*X2)),
    x12 ≡ x12' -> snd (unzip x12) ≡ snd (unzip x12').
Proof.
  intros x12 x12' H n. unfold unzip. simpl. now rewrite <- (H n).
Qed.

Definition commute {X1 X2} (x12 : X1*X2) : (X2*X1) :=
  let (x1,x2) := x12 in (x2,x1).
Lemma commute_commute_id {X1 X2} : 
  forall x12 : X1*X2, commute (commute x12) = x12. 
Proof. 
  intro x12. 
  replace x12 with (fst x12, snd x12).
  unfold commute. reflexivity.
  now rewrite <- surjective_pairing.
Qed.
Definition commute_traces {X1 X2} (x12 : Tr (X1*X2)) : (Tr (X2*X1)) :=
  fun n => commute (x12 n).
Lemma commute_zip {X1 X2} : forall (x1 : Tr X1) (x2 : Tr X2),
  commute_traces (x1;x2) = (x2;x1).
Proof.
  intros x1 x2. unfold zip, commute_traces, commute. reflexivity. Qed.
Lemma commute_commute_eqv {X1 X2} : 
  forall x12 : Tr (X1*X2), commute_traces (commute_traces x12) ≡ x12. 
Proof. intros x12 n. unfold commute_traces. apply commute_commute_id. Qed.

Definition associate {Y1 Y2 Y3}
  (y12_3 : Tr ((Y1*Y2)*Y3)) : Tr (Y1*(Y2*Y3)) :=
    let (y12,y3) := unzip y12_3 in
      let (y1,y2) := unzip y12 in
        (y1;(y2;y3)).
Definition unassociate {Y1 Y2 Y3}
  (y1_23 : Tr (Y1*(Y2*Y3))) : Tr ((Y1*Y2)*Y3) :=
    let (y1,y23) := unzip y1_23 in
      let (y2,y3) := unzip y23 in
        ((y1;y2);y3).
Lemma associate_zip {Y1 Y2 Y3} :
  forall (y1 : Tr Y1) (y2 : Tr Y2) (y3 : Tr Y3),
    associate ((y1;y2);y3) = (y1;(y2;y3)).
Proof. intros; reflexivity. Qed.
Lemma unassociate_zip {Y1 Y2 Y3} :
  forall (y1 : Tr Y1) (y2 : Tr Y2) (y3 : Tr Y3),
    unassociate (y1;(y2;y3)) = ((y1;y2);y3).
Proof. intros; reflexivity. Qed.
Lemma associate_extensional {Y1 Y2 Y3} :
  forall (y123 y123' : Tr ((Y1*Y2)*Y3)),
    y123 ≡ y123' -> associate y123 ≡ associate y123'.
Proof.
  intros y123 y123' H123 n.
  unfold associate, zip, unzip.
  now rewrite <- (H123 n). 
Qed.
Lemma unassociate_extensional {Y1 Y2 Y3} :
  forall (y123 y123' : Tr (Y1*(Y2*Y3))),
    y123 ≡ y123' -> unassociate y123 ≡ unassociate y123'.
Proof.
  intros y123 y123' H123 n.
  unfold unassociate, zip, unzip.
  now rewrite <- (H123 n). 
Qed.
Lemma unassociate_associate_id {Y1 Y2 Y3} :
  forall (y1 : Tr Y1) (y2 : Tr Y2) (y3 : Tr Y3),
    unassociate (associate ((y1;y2);y3)) = ((y1;y2);y3).
Proof.
  intros y1 y2 y3. reflexivity.
Qed.
Lemma associate_unassociate_id {Y1 Y2 Y3} :
  forall (y1 : Tr Y1) (y2 : Tr Y2) (y3 : Tr Y3),
    associate (unassociate (y1;(y2;y3))) = (y1;(y2;y3)).
Proof.
  intros y1 y2 y3. reflexivity.
Qed.
Lemma unassociate_associate_eqv {Y1 Y2 Y3} :
  forall (y123 : Tr ((Y1*Y2)*Y3)),
    unassociate (associate y123) ≡ y123.
Proof.
  intros y123.
  set (y12 := fst (unzip y123)).
  set (y1 := fst (unzip y12)).
  set (y2 := snd (unzip y12)).
  set (y3 := snd (unzip y123)).
  assert (y123 ≡ ((y1;y2);y3)) as E123 by apply zip_unzip3_l.
  transitivity ((y1; y2); y3).
  transitivity (unassociate (associate ((y1; y2); y3))).
  - apply unassociate_extensional.
    apply associate_extensional.
    exact E123.
  - now rewrite -> (unassociate_associate_id y1 y2 y3).
  - symmetry.
    exact E123.
Qed.
Lemma associate_unassociate_eqv {Y1 Y2 Y3} :
  forall (y123 : Tr (Y1*(Y2*Y3))),
    associate (unassociate y123) ≡ y123.
Proof.
  intros y123.
  set (y23 := snd (unzip y123)).
  set (y1 := fst (unzip y123)).
  set (y2 := fst (unzip y23)).
  set (y3 := snd (unzip y23)).
  assert (y123 ≡ (y1;(y2;y3))) as E123 by apply zip_unzip3_r.
  transitivity (y1; (y2; y3)).
  transitivity (associate (unassociate (y1; (y2; y3)))).
  - apply associate_extensional.
    apply unassociate_extensional.
    exact E123.
  - rewrite -> (associate_unassociate_id y1 y2 y3).
    reflexivity.
  - symmetry.
    exact E123.
Qed.


Lemma eqv_le_lt_succ {X} : 
  forall (x x' : Tr X) (n : nat),
    x |≤ n |≡ x' -> x |< (S n) |≡ x'.
Proof.
  intros x x' n Hu m HmltSn.
  set (Hmlen := (proj1 (Nat.lt_succ_r _ _)) HmltSn).
  exact (Hu m Hmlen).
Qed.

Lemma all_eqv_lt {X} :
  forall (x x' : Tr X),
    (forall n, x |< n |≡ x') -> x ≡ x'.
Proof.
  intros x x' H n. exact (H (S n) n (Nat.lt_succ_diag_r n)).
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
