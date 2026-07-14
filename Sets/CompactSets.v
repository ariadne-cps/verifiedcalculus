(******************************************************************************
 *  Sets/CompactSets.v
 *
 *  Copyright 2026 Pieter Collins
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

From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Logic.FunctionalExtensionality.

Require Sierpinskian.
Require Import OpenSets.

Require Import DependentChoice.

(*
Require Export Monads.
Require Export SubMonads.
Require Export LimitMonads.
*)
Require Export Monads.
Require Export ContinuationMonads.

Module CompactSets.

Notation Continuation := ContinuationMonads.Continuation.
Notation Continuation_Monad := ContinuationMonads.Continuation_Monad.
Notation Cbind := ContinuationMonads.bind.
Notation Cpure := ContinuationMonads.pure.

Import OpenSets.

Definition compact_respectful {X} (c : OpenSet X -> S) : Prop := 
  forall U1 U2, (forall x, U1 x == U2 x) -> c U1 == c U2.

Definition compact_proper {X} (c : OpenSet X -> S) : Prop := 
  forall U1 U2, Sierpinskian.eqv (c (intersection U1 U2)) (Sand (c U1) (c U2)).

Definition CompactSet (X : Set) : Set :=
  { c : OpenSet X -> S | compact_respectful c /\ compact_proper c }.

Definition mkCompactSet {X : Set} (c : OpenSet X -> S) 
    (r : compact_respectful c) (p : compact_proper c) : CompactSet X :=
  @exist _ _ c (conj r p).

Definition subset {X} (C : CompactSet X) (U : OpenSet X) := (proj1_sig C) U.

Lemma compact_eq {X} : forall C1 C2 : CompactSet X, (forall U, subset C1 U == subset C2 U) -> C1 = C2.
Proof. admit. Admitted.

Notation Ounion := OpenSets.union.
Notation Ointersection := OpenSets.intersection.


Definition union_op {X} (c1 c2 : OpenSet X -> S) : OpenSet X -> S :=
  fun U => Sierpinskian.and (c1 U) (c2 U).

Lemma union_respectful {X} (c1 c2 : OpenSet X -> S) : 
  compact_respectful c1 -> compact_respectful c2 -> compact_respectful (union_op c1 c2).
Proof.
  unfold compact_respectful, union_op.
  intros HR1 HR2 U1 U2 HU.
  apply Sierpinskian.and_respectful.
  - apply HR1. exact HU.
  - apply HR2. exact HU.
Qed.

Lemma Sinner_and_comm : forall p11 p12 p21 p22 : S, 
  Sand (Sand p11 p12) (Sand p21 p22) == Sand (Sand p11 p21) (Sand p12 p22).
Proof.
  intros p11 p12 p21 p22;
  apply (Sierpinskian.eqv_trans _ (Sand (Sand (Sand p11 p12) p21) p22) _).
    apply Sierpinskian.eqv_sym. apply Sierpinskian.and_assoc.
  apply (Sierpinskian.eqv_trans _ (Sand (Sand p11 (Sand p12 p21)) p22) _).
    apply Sierpinskian.and_respectful. apply Sierpinskian.and_assoc. apply Sierpinskian.eqv_refl. 
  apply (Sierpinskian.eqv_trans _ (Sand (Sand p11 (Sand p21 p12)) p22) _).
    apply Sierpinskian.and_respectful. apply Sierpinskian.and_respectful. apply Sierpinskian.eqv_refl. apply Sierpinskian.and_comm. apply Sierpinskian.eqv_refl. 
  apply (Sierpinskian.eqv_trans _ (Sand (Sand (Sand p11 p21) p12) p22) _).
    apply Sierpinskian.and_respectful. apply Sierpinskian.eqv_sym. apply Sierpinskian.and_assoc. apply Sierpinskian.eqv_refl.
  now apply Sierpinskian.and_assoc. 
Qed.

Lemma union_proper {X} (c1 c2 : OpenSet X -> S) : 
  compact_proper c1 -> compact_proper c2 -> compact_proper (union_op c1 c2).
Proof.
  intros HP1 HP2 U1 U2.
  unfold compact_proper in *.
  specialize HP1 with U1 U2.
  specialize HP2 with U1 U2.
  unfold union_op.
  apply (Sierpinskian.eqv_trans _ (Sand (Sand (c1 U1) (c1 U2)) (Sand (c2 U1) (c2 U2))) _).
  - apply Sierpinskian.and_respectful. exact HP1. exact HP2.
  - now apply Sinner_and_comm.
Qed.


Definition union {X} (C1 C2 : CompactSet X) : CompactSet X :=
  let c1 := proj1_sig C1 in let c2 := proj1_sig C2 in
  let r1 := proj1 (proj2_sig C1) in let r2 := proj1 (proj2_sig C2) in
  let p1 := proj2 (proj2_sig C1) in let p2 := proj2 (proj2_sig C2) in
    mkCompactSet (union_op c1 c2) (union_respectful c1 c2 r1 r2) (union_proper c1 c2 p1 p2).


Definition difference_op {X} (c : OpenSet X -> S) (W : OpenSet X) : OpenSet X -> S :=
  fun U => c (OpenSets.union W U).

Lemma difference_respectful {X} (c : OpenSet X -> S) (W : OpenSet X) : 
  compact_respectful c -> compact_respectful (difference_op c W).
Proof.
  unfold compact_respectful.
  intros HR U1 U2 HU.
  unfold difference_op.
  apply HR.
  apply OpenSets.union_respectful.
  - now apply OpenSets.equivalent_refl.
  - exact HU.
Qed.

Lemma difference_proper {X} (c : OpenSet X -> S) (W : OpenSet X) : 
  compact_respectful c -> compact_proper c -> compact_proper (difference_op c W).
Proof.
  unfold compact_proper.
  intros HR HP U1 U2.
  unfold difference_op.
  apply (Sierpinskian.eqv_trans _ (c (Ointersection (Ounion W U1) (Ounion W U2))) _).
  2: now apply (HP (Ounion W U1) (Ounion W U2)).
  apply HR.
  intro x.
  unfold Ointersection, Ounion.
  now apply Sierpinskian.or_and_distrib_r.
Qed.

Definition difference {X} (C : CompactSet X) (W : OpenSet X) : CompactSet X :=
  let c := proj1_sig C in let r := proj1 (proj2_sig C) in let p := proj2 (proj2_sig C) in
    mkCompactSet (fun U => c (OpenSets.union W U)) (difference_respectful c W r) (difference_proper c W r p).

Definition complement {X} (H : effective_hausdorff X) (C : CompactSet X) : OpenSet X :=
  fun x => (proj1_sig C) (fun x' => (proj1_sig H) x x').

Definition hausdorff_intersection {X} (H : effective_hausdorff X) (C1 C2 : CompactSet X) : CompactSet X :=
  difference C1 (complement H C2).


Definition is_filter {A} (q : (A -> Sierpinskian) -> Sierpinskian) : Prop :=
  forall U1 U2 : A -> Sierpinskian,
    q (fun a => Sor (U1 a) (U2 a)) == Sor (q U1) (q U2).

Definition is_cofilter {A} (q : @OpenSet A -> Sierpinskian) : Prop :=
  forall U1 U2 : @OpenSet A,
    q (fun a => Sand (U1 a) (U2 a)) == Sand (q U1) (q U2).


Definition singleton_op {A : Set} (a : A) : OpenSet A -> Sierpinskian := 
  fun U => U a.

Lemma singleton_is_respectful : forall {A : Set} (a : A),
  compact_respectful (singleton_op a).
Proof.
  unfold compact_respectful, singleton_op.
  intros A a U1 U2 H. exact (H a).
Qed.

Lemma singleton_is_proper : forall {A : Set} (a : A),
  compact_proper (singleton_op a).
Proof.
  unfold compact_proper, singleton_op, Ointersection.
  intros A a U1 U2.
  unfold Sierpinskian.eqv.
  exists 0; reflexivity.
Qed.

Definition singleton {A : Set} (a : A) : @CompactSet A
  := mkCompactSet (fun U => U a) (singleton_is_respectful  a) (singleton_is_proper a).


Definition image_op {A B : Set}
   (C : OpenSet A -> Sierpinskian) (F : A -> OpenSet B -> Sierpinskian) : OpenSet B -> Sierpinskian
 := fun V => C (fun a => F a V).

Lemma image_is_respectful {A B : Set} : forall {C : OpenSet A -> Sierpinskian} {F : A -> OpenSet B -> Sierpinskian},
  compact_respectful C -> (forall a, compact_respectful (F a)) -> compact_respectful (image_op C F).
Proof.
  unfold Cbind, compact_respectful.
  intros C F HC HF U1 U2 HU.
  apply HC.
  intros x.
  apply HF.
  intro y.
  exact (HU y).
Qed.

Lemma image_is_proper {A B : Set} : forall {C : OpenSet A -> Sierpinskian} {F : A -> OpenSet B -> Sierpinskian},
   compact_respectful C -> compact_proper C -> (forall a, compact_proper (F a))-> compact_proper (image_op C F).
Proof.
  unfold compact_proper, image_op.
  intros C F HR HC HF.
  intros V1 V2.
  rewrite <- HC.
  apply HR.
  intro a.
  now apply HF.
Qed.

Definition image {A B : Set} (C : CompactSet A) (F : A -> CompactSet B) : CompactSet B
  := mkCompactSet (image_op (proj1_sig C) (fun a => proj1_sig (F a)))
       (image_is_respectful (proj1 (proj2_sig C)) (fun a => proj1 (proj2_sig (F a))))
       (image_is_proper (proj1 (proj2_sig C)) (proj2 (proj2_sig C)) (fun a => proj2 (proj2_sig (F a)))).


Lemma compose_image_image {X Y Z : Set} :
  forall (C : CompactSet X) (F : X -> CompactSet Y) (G : Y -> CompactSet Z), 
    image (image C F) G = image C (fun x => image (F x) G).
Proof.
  intros C F G. apply compact_eq. intro U; reflexivity.
Qed.


Definition singleton_image_op {A B : Set}
   (C : OpenSet A -> Sierpinskian) (f : A -> B) : OpenSet B -> Sierpinskian
 := fun V => C (fun a => V (f a)).

Lemma singleton_image_is_respectful {A B : Set} : forall {C : OpenSet A -> Sierpinskian} (f : A -> B),
  compact_respectful C -> compact_respectful (singleton_image_op C f).
Proof.
  unfold Cbind, compact_respectful.
  intros C f HC V1 V2 HV.
  apply HC.
  intros x.
  exact (HV (f x)).
Qed.

Lemma singleton_image_is_proper {A B : Set} : forall {C : OpenSet A -> Sierpinskian} (f : A -> B),
   compact_respectful C -> compact_proper C -> compact_proper (singleton_image_op C f).
Proof.
  unfold compact_proper, singleton_image_op, Ointersection.
  intros C f HR HC.
  intros V1 V2.
  rewrite <- HC.
  apply HR.
  intro a.
  reflexivity.
Qed.


Definition singleton_image {A B : Set} (C : CompactSet A) (f : A -> B) : CompactSet B
  := mkCompactSet (singleton_image_op (proj1_sig C) f)
       (singleton_image_is_respectful f (proj1 (proj2_sig C)))
       (singleton_image_is_proper f (proj1 (proj2_sig C)) (proj2 (proj2_sig C))).


Lemma singleton_image_spec {X Y : Set} : forall (C : CompactSet X) (f : X -> Y), 
  singleton_image C f = image C (fun (x : X) => singleton (f x)).
Proof.
  intros C f. apply compact_eq.
  unfold singleton_image, singleton_image_op, image, image_op, singleton, singleton_op. simpl.
  intro U. reflexivity.
Qed.

Lemma compose_image_singleton_image {X Y Z : Set} :
  forall (C : CompactSet X) (f : X -> Y) (G : Y -> CompactSet Z), 
    image (singleton_image C f) G = image C (fun x => G (f x)).
Proof.
  intros C f G. apply compact_eq. intro U; reflexivity.
Qed.


Definition image_save {X Y : Set} (A : CompactSet X) (F : X -> CompactSet Y) : CompactSet (X*Y) :=
  image A (fun x => singleton_image (F x) (fun y => (x,y))).




Definition element := Ensembles.In.

Definition  as_ensemble {X} (C : CompactSet X) : Ensemble X :=
  fun x => forall (U : OpenSet X), subset C U == Strue -> U x == Strue.

Notation Oas_ensemble := OpenSets.as_ensemble.


Definition Ocontains {X} (U : OpenSet X) (x : X) := U x == Strue.

Definition is_subset {X} (C : CompactSet X) U := subset C U == Strue.

Definition contains {X} (C : CompactSet X) (x : X) :=
  forall U, is_subset C U -> Ocontains U x.


Lemma compact_singleton_contains_point {X : Set} : forall (x : X), (as_ensemble (singleton x)) x.
Proof. intro x. unfold singleton, as_ensemble, subset. simpl. tauto. Qed.

Lemma compact_singleton_is_compactification {X : Set} : forall (x y : X), 
  (as_ensemble (singleton x)) y <-> forall (U : OpenSet X),  (Oas_ensemble U) x -> (Oas_ensemble U) y.
Proof. intros x y. unfold singleton, as_ensemble, Oas_ensemble, subset. simpl. tauto. Qed.


Lemma image_of_point {X Y} : forall (C : CompactSet X) (F : X -> CompactSet Y) x, 
  contains C x -> forall V, is_subset (image C F) V -> is_subset (F x) V.
Proof. 
  intros C F x H.
  unfold contains in H.
  unfold is_subset.
  intros V HV.
  set (U := fun x => subset (F x) V).
  specialize (H U).
  unfold U in H.
  pose proof (H HV) as HF.
  unfold Ocontains in HF.
  exact HF.
Qed.



Axiom compact_subset_entire : forall {X : Set} (C : CompactSet X) (U : OpenSet X), 
  (forall x, U x == Strue) -> subset C U == Strue.

Axiom compact_subset_monotone : forall {X : Set} (C : CompactSet X) (U V : OpenSet X), 
  (forall x, U x == Strue -> V x == Strue)  ->
    subset C U == Strue -> subset C V == Strue.

(*
Axiom classical_exists_negation_implication :
  forall (X : Type) (p q : X -> Prop), ~ (forall x, p x -> q x) -> (exists x, p x /\ ~ q x).
*)

Definition classical_exists_negation_implication (X : Type) :=
  forall (p q : X -> Prop), ~ (forall x, p x -> q x) -> (exists x, p x /\ ~ q x).

Definition discernable_equality (X : Set) := forall (x1 x2 : X), x1=x2 \/ x1<>x2.


Lemma singleton_contains {X : Set} : 
  (discernable_equality X) -> (effective_hausdorff X) -> 
    forall (C : CompactSet X) (x : X) (y : X),
      (contains (singleton x) y) <-> x = y.
Proof.
  unfold singleton, contains, is_subset, subset, Ocontains; simpl.
  intros He [ap Hap] C x y.
  split; intro H; simpl.
  - set (V := (fun w => ap w y) : OpenSet X).
    specialize (H V). unfold V in H.
    rewrite -> Hap, Hap in H.
    destruct (He x y) as [Heq|Ha]. assumption. 
    now contradiction (H Ha).
  - rewrite <- H. tauto.
Qed.


Lemma complement_contains_fwd {X} : forall (HX : effective_hausdorff X),
  forall (A : CompactSet X) (x : X),
    Ocontains (complement HX A) x -> ~ contains A x.
Proof.
  intros HX A x H HAx.
  unfold complement in H.
  destruct HX as [ap Hap].
  unfold Ocontains in H; simpl in H.
  set (V := (fun x' => ap x x') : OpenSet X).
  unfold contains in HAx.
  specialize (HAx V).
  pose proof (HAx H) as HVx.
  unfold V, Ocontains in HVx.
  apply Hap in HVx.
  contradiction.
Qed.

Lemma complement_contains_bwd {X} :
  Sierpinskian.LPO -> forall (HX : effective_hausdorff X),
    forall (C : CompactSet X) (x : X),
      ~ Ocontains (complement HX C) x -> contains C x.
Proof.
  intros lpo HX C x H.
  unfold Ocontains, complement in H. 
  unfold contains; simpl.
  destruct HX as [ap Hap]; simpl in H.
  intros U HCU.
  set (Unx := (fun (x' : X) => ap x x') : OpenSet X).
  replace (fun x' => ap x x') with Unx in H by reflexivity.
  pose proof (compact_subset_monotone C) as HmC.
  unfold Ocontains.
  destruct (Sierpinskian.true_or_not_true lpo (U x)) as [Ht|Hi]; [assumption|].
  assert (forall y, Ocontains U y -> Ocontains Unx y) as HUmono. {
    intros y HUy. apply Hap. intro Hxy. rewrite <- Hxy in HUy. contradiction. }
  apply (compact_subset_monotone C U Unx HUmono) in HCU.
  contradiction.
Qed.

Lemma complement_contains_bwd' {X : Set} : 
  (classical_exists_negation_implication (OpenSet X)) -> forall (HX : effective_hausdorff X),
    forall (C : CompactSet X) (x : X), 
       ~ (contains C x) -> Ocontains (complement HX C) x.
Proof.
  intros HE HX C x H.
  unfold Ocontains, complement.
  destruct HX as [ap Hap]; simpl in H; simpl.
  unfold contains in H.
  apply HE in H.
  destruct H as [U [HCU HnUx]].
  set (Unx := (fun x' => ap x x') : OpenSet X).
  apply (compact_subset_monotone C U).
  2: exact HCU.
  intros y HU. unfold Unx. rewrite -> Hap. intro Hxy. rewrite <- Hxy in HU. 
  contradiction HnUx.
Qed.



Lemma difference_contains_fwd {X} : 
  (discernable_equality X) -> (effective_hausdorff X) -> 
    forall (A : CompactSet X) (U : OpenSet X) (x : X), 
      contains (difference A U) x -> (contains A x /\ ~Ocontains U x).
Proof.
  intros He [ap Hap] A U x H. split.
  - unfold difference, contains, is_subset, subset in *; simpl in *.
    unfold contains. intros W HAW.
    specialize (H W). apply H.
    apply (compact_subset_monotone _ W).
    intros w Hw; unfold Ounion. apply Sierpinskian.or_up. right. exact Hw.
    exact HAW.
  - unfold difference, contains, is_subset, subset in *; simpl in *.
    set (V := (fun y => ap x y) : OpenSet X).
    intro Hu.
    specialize (H V).
    assert (is_subset A (Ounion U V)) as HAUV. { 
      apply (compact_subset_entire A). intro y. unfold Ounion.
      apply Sierpinskian.or_up. 
      assert (x=y \/ x<>y) as HXeq_dec. now apply He.
      destruct HXeq_dec. left. now rewrite <- H0. right. now apply Hap.
    }
    apply H in HAUV as HV.
    unfold Ocontains, V in HV. rewrite -> Hap in HV. contradiction.
Qed.


Lemma difference_contains_bwd {X} : 
  forall (A : CompactSet X) (U : OpenSet X) (x : X), 
    contains A x /\ ~ Ocontains U x -> contains (difference A U) x.
Proof.
  intros A U x [HA HU]. 
  unfold difference, contains, is_subset, subset; simpl.
  intros W HW.
  unfold contains in HA; simpl in HA.
  specialize (HA (Ounion U W) HW).
  unfold Ounion, Ocontains in HA.
  apply Sierpinskian.or_up in HA.
  destruct HA. 
  -- contradiction.
  -- assumption.
Qed.


Lemma image_contains_bwd {X Y} : 
  forall (C : CompactSet X) (F : X -> CompactSet Y) (y : Y),
    (exists x, contains C x /\ contains (F x) y) -> contains (image C F) y.
Proof.
  intros C F y H.
  destruct H as [x [Hx Hy]].
  intros V HV. apply (Hy V).
  apply (image_of_point C).
  exact Hx.
  exact HV.
Qed.

Lemma image_contains_fwd {X Y} : 
  forall (C : CompactSet X) (F : X -> CompactSet Y) (y : Y),
    contains (image C F) y -> exists x, contains C x /\ contains (F x) y.
Proof.
Admitted.


Lemma singleton_image_contains_fwd {X Y : Set} : 
  (discernable_equality Y) -> (effective_hausdorff Y) -> 
    forall (C : CompactSet X) (f : X -> Y) (y : Y),
      (contains (singleton_image C f) y) -> (exists x, contains C x /\ f x = y).
Proof.
  intros He Hh C f y H.
  rewrite -> singleton_image_spec in H.
  set (F := fun x => singleton (f x)).
  pose proof (image_contains_fwd C F y H) as [x [Hx Hy]].
  exists x; split. 
  - exact Hx.
   - apply (singleton_contains He Hh (F x) (f x) y). exact Hy.
Qed.

Lemma singleton_image_contains_bwd {X Y : Set} : 
  forall (A : CompactSet X) (f : X -> Y) (y : Y),
    (exists x, contains A x /\ f x = y) -> contains (singleton_image A f) y.
Proof.
  intros C f y H.
  rewrite -> singleton_image_spec.
  apply image_contains_bwd.
  destruct H as [x [Hx Hy]].
  exists x. split. exact Hx. unfold singleton, contains, is_subset; simpl. 
  rewrite -> Hy; tauto.
Qed.


Lemma image_save_contains_fwd {X Y} : forall (A : CompactSet X) (F : X -> CompactSet Y) (xy : X*Y),
  discernable_equality (X * Y) -> effective_hausdorff (X * Y) ->
    contains (image_save A F) xy -> contains A (fst xy) /\ contains (F (fst xy)) (snd xy).
Proof.
  intros A F xy He Hf. destruct xy as [x y]; simpl.
  intro H; unfold image_save in H.
  apply image_contains_fwd in H.
  destruct H as [x' [HAx' HFx']].
  apply singleton_image_contains_fwd in HFx'.
  2,3: assumption.
  destruct HFx' as [y' [HFx' Hxy]].
  apply pair_equal_spec in Hxy. destruct Hxy as [Hx Hy].
  rewrite -> Hx in HAx'; rewrite -> Hx, Hy in HFx'.
  tauto.
Qed.

Lemma image_save_contains_bwd {X Y} : forall (A : CompactSet X) (F : X -> CompactSet Y) (xy : X*Y),
  (contains A (fst xy) /\ contains (F (fst xy)) (snd xy)) -> contains (image_save A F) xy.
Proof.
  intros A F xy [Hx Hy]. destruct xy as (x,y). simpl in *.
  unfold image_save. apply image_contains_bwd.
  exists x. split. exact Hx.
  apply singleton_image_contains_bwd. 
  exists y. split. exact Hy. reflexivity.
Qed.


Lemma as_ensemble_iff_contains {X} : forall (C : CompactSet X) (x : X), as_ensemble C x = contains C x.
Proof. intros C x; unfold contains, as_ensemble. tauto. Qed.


Lemma discernable_equality_product_fwd : forall X Y, 
  inhabited X -> inhabited Y ->
    discernable_equality (X*Y) -> discernable_equality X /\ discernable_equality Y.
Proof.
  unfold discernable_equality.
  intros X Y HX HY H.
  destruct HX as [x0]; destruct HY as [y0]. 
  split.
  - intros x1 x2. specialize (H (x1,y0) (x2,y0)). destruct H. 
    left. apply pair_equal_spec in H. tauto. right. intro Hx. apply H. now rewrite -> Hx. 
  - intros y1 y2. specialize (H (x0,y1) (x0,y2)). destruct H. 
    left. apply pair_equal_spec in H. tauto. right. intro Hy. apply H. now rewrite -> Hy. 
Qed.

Lemma discernable_equality_product_bwd : forall X Y, 
    discernable_equality X /\ discernable_equality Y -> discernable_equality (X*Y).
Proof.
  unfold discernable_equality.
  intros X Y [HX HY].
  intros xy1 xy2.
  destruct xy1 as [x1 y1]; destruct xy2 as [x2 y2].
  specialize (HX x1 x2).
  specialize (HY y1 y2).
  destruct HX as [Hx|Hx].
  destruct HY as [Hy|Hy].
  - left. now rewrite -> Hx, Hy.
  - right. intro Hf. apply pair_equal_spec in Hf. contradiction (Hy (proj2 Hf)).
  - right. intro Hf. apply pair_equal_spec in Hf. contradiction (Hx (proj1 Hf)).
Qed.


Definition system_composition_helper {X Y Z : Set} 
  (EXYZ : discernable_equality (X*Y*Z))
  (HXY : effective_hausdorff (X*Y)) 
  (F : Y -> CompactSet (X * Z)) (G : X -> CompactSet Y)
    (lpo : Sierpinskian.LPO) ( HF : { A : CompactSet X | forall y, singleton_image (F y) (fst) = A } ) : 
      { C : CompactSet (X*Y*Z) | forall x y z, as_ensemble C (x,y,z) <-> ( as_ensemble (F y) (x,z) /\ as_ensemble (G x) y) }.
Proof.
  set (p := fun (y_xz : Y*(X*Z)) => (fst (snd y_xz), fst (y_xz), snd (snd y_xz))).
  destruct HF as [A HA].
  set (AB := image_save A G).
  set (B := image A G).
  set (opAB' := complement HXY AB). 
  set (opABZ' := (fun (xy_z : X*Y*Z) => opAB' (fst xy_z)) : OpenSet (X*Y*Z)).
  set (FB := singleton_image (image_save B F) p).
  set (ABC := difference FB opABZ').

  (* Shouldn't be needed; due to definition of ABC only need Hausdorff on X*Y *)
  assert (discernable_equality (X*Y)) as EXY. admit.
  assert (effective_hausdorff (X*Y*Z)) as HXYZ. admit.
  assert (discernable_equality (Y*(X*Z))) as EYXZ. admit.
  assert (effective_hausdorff (Y*(X*Z))) as HYXZ. admit.

  exists ABC.
  intros x y z.
  rewrite -> (as_ensemble_iff_contains ABC), (as_ensemble_iff_contains (F y)), (as_ensemble_iff_contains (G x)).

  assert (forall yxz, p yxz = (x,y,z) -> yxz = (y, (x,z))) as Hyxz. {
    intros yxz Hp. unfold p in Hp.
    destruct yxz as [y' [x' z']]; simpl in Hp; simpl.
    apply pair_equal_spec in Hp as [Hxy Hz].
    apply pair_equal_spec in Hxy as [Hx Hy].
    apply pair_equal_spec; split. 
    2: apply pair_equal_spec; split.
    all: assumption.
  }
 
  split; intro H.
  - unfold ABC in H.
    apply difference_contains_fwd in H. 2,3: assumption.
    destruct H as [HFB HABZ].
    unfold FB in HFB.
    apply singleton_image_contains_fwd in HFB.
    destruct HFB as [yxz [HFB Hp]]. 
    apply image_save_contains_fwd in HFB.
    rewrite (Hyxz yxz Hp) in HFB; simpl in HFB.
    unfold opABZ', Ocontains in HABZ. simpl in HABZ.
    unfold opAB' in HABZ.
    pose proof (complement_contains_bwd lpo HXY AB (x,y) HABZ) as HAB.
    unfold AB in HAB. apply image_save_contains_fwd in HAB; simpl in HAB.
    tauto.
    all: assumption.
  - destruct H as [HF HG].
    unfold ABC.
    apply difference_contains_bwd.
    split.
    -- unfold FB.
       apply singleton_image_contains_bwd.
       exists (y,(x,z)). split. 2: { tauto. }
       apply image_save_contains_bwd; simpl. 
       split.
       --- unfold B. apply image_contains_bwd.
           exists x. split. 2: exact HG.
           rewrite <- (HA y).
           apply singleton_image_contains_bwd.
           exists (x,z).
           split. exact HF. reflexivity.
       --- exact HF.
    -- unfold opABZ', opAB'.
       unfold Ocontains.
       replace (fst (x,y,z)) with (x,y) by reflexivity.
       intro HAB; apply (complement_contains_fwd HXY AB (x,y)) in HAB; apply HAB; clear HAB.
       unfold AB.
       apply image_save_contains_bwd; simpl.
       split.
       --- rewrite <- (HA y).
           apply singleton_image_contains_bwd.
           exists (x,z). 
           split. exact HF. reflexivity.
       --- exact HG.
Qed.




Lemma cpure_is_respectful {A : Set} (a : A) : compact_respectful (Cpure a).
Proof.
  unfold compact_respectful, Cpure.
  intros U1 U2 H. exact (H a).
Qed.

Lemma cpure_is_filter {A : Set} (a : A) : is_filter (Cpure A).
Proof.
  unfold is_filter, Cpure.
  intros U1 U2.
  reflexivity.
Qed.

Lemma cbind_is_respectful : forall {A B : Set} (F : A -> Continuation Sierpinskian B) (C : Continuation Sierpinskian A),
  (forall a, compact_respectful (F a)) -> compact_respectful C -> compact_respectful (Cbind F C).
Proof.
  unfold Cbind, compact_respectful.
  intros A B F C HF HC U1 U2 HU.
  apply HC.
  intros x.
  apply HF.
  intro y.
  now apply HU.
Qed.

Lemma cbind_is_filter : forall {A B : Set} (F : A -> Continuation Sierpinskian B) (C : Continuation Sierpinskian A),
  (compact_respectful C) -> (forall a, is_filter (F a)) -> is_filter C -> is_filter (Cbind F C).
Proof.
  unfold compact_respectful, is_filter, Cbind.
  intros A B F C HR HF HC.
  intros V1 V2.
   rewrite <- HC.
  apply HR. 
  intro a.
  now apply HF.
Qed.


Class SetMonad (M : Set -> Set) :=
{
    (* monad has pure and bind *)
    SMpure : forall {A : Set}, A -> M A;
    SMbind : forall {A B : Set}, (A -> M B) -> M A -> M B;

    (* coherence conditions *)
    SMleft_identity : forall {A B : Set} (f:A->M B) (a:A), SMbind f (SMpure a) = f a;
    SMright_identity : forall {A} (x : M A), SMbind (@SMpure A) x = x;
    SMassociativity : forall {A B C} (x : M A) (f : A -> M B) (g : B -> M C),
        SMbind g (SMbind f x) = SMbind (fun a => SMbind g (f a)) x;

    (* Mfunctor_map : forall {A B : Set}, (A -> B) -> M A -> M B; *)
    SMfunctor_map {A B : Set} : (A -> B) -> M A -> M B
      := fun (f : A -> B) (x : M A) => SMbind (fun x' => SMpure (f x')) x;
    SMlift {A B : Set} (f : A -> B) (a : M A) : M B
      := SMbind (fun a' => SMpure (f a')) a;

   SMleft_product {X Y} : M X -> M Y -> (M (prod X Y)) :=
      fun (mu : M X) (nu : M Y) => SMbind ( fun y => ( SMbind (fun x => SMpure (pair x y)) mu ) ) nu;
   SMright_product {A B} : M A -> M B -> M (prod A B)
      := fun mu nu => SMbind ( fun x => ( SMbind (fun y => SMpure (pair x y)) nu ) ) mu;
}.

Definition bind {A B : Set} (F : A -> CompactSet B) (C : CompactSet A) : CompactSet B :=
  @image A B C F.


Lemma compact_set_equal {A} : forall C1 C2 : CompactSet A, proj1_sig C1 = proj1_sig C2 -> C1 = C2.
Proof.
  unfold CompactSet.
  intros C1 C2 H. destruct C1; destruct C2.
  simpl in H.
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  exact H.
Qed.



#[global]
Instance CompactSetMonad : SetMonad (CompactSet).
Proof.
  apply (Build_SetMonad CompactSet (@singleton) (@bind)).
  - intros A B F a; unfold bind, singleton, image, mkCompactSet; simpl.
    apply compact_set_equal; simpl.
    unfold image_op, singleton_op; simpl.
    apply FunctionalExtensionality.functional_extensionality.
    intro V.
    reflexivity.
  - intros A C; unfold bind, singleton, mkCompactSet; simpl.
    apply compact_set_equal; simpl.
    unfold image_op, singleton_op; simpl.
    apply FunctionalExtensionality.functional_extensionality.
    intro U.
    f_equal.
  - admit.
Admitted.


(*
Definition image {A B : Type}
   (C : @CompactSet A) (F : A -> @CompactSet B) : @CompactSet B
 := mkCompactSet (Cbind (fun a => (F a).(intersects)) C.(intersects);
 := {| intersects := Cbind (fun a => (F a).(intersects)) C.(intersects);
       intersects_is_filter :=
         Cbind_is_filter
           (fun a => (F a).(intersects)) C.(intersects)
           (fun a => (F a).(intersects_is_filter)) C.(intersects_is_filter);
         |}.
*)


Fail Instance CompactSetMonad {A : Set} : Monad (@CompactSet)
  := @Subtype (Continuation Sierpinskian A) (is_filter).


Fail Definition CompactSetSubtype {A:Type} : Type
  := @Subtype (Continuation Sierpinskian A) (is_filter).

Fail Instance CompactSetSubtypeMonad : Monad (@CompactSetSubtype) :=
  @Subtype_Monad
    (@Continuation Sierpinskian)
    (@is_filter)
    (@Continuation_Monad Sierpinskian)
    (@cpure_is_filter)
    (@cbind_is_filter)
.



End CompactSets.
