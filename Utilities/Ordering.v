(******************************************************************************
 *  Utilities/Ordering.v
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


From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Classes.RelationClasses.

Declare Scope WSO_scope.
Delimit Scope WSO_scope with WSO.

(* RelationClasses are missing, so define ourselves *)

Print Reflexive.
Print Antisymmetric.

Print eq.

Class PartialOrder {A : Type} (R : A -> A -> Prop) := {
  refl : Reflexive R;
  antisymm : Antisymmetric A (@eq A) R;
  trans : Transitive R;
}.

Class StrictPartialOrder { A : Type } ( R : A -> A -> Prop ) := {
  irrefl : Irreflexive R;
  asymm : Asymmetric R;
  strict_trans : Transitive R;
}.


Section Ordering.

Print PartialOrder.
Print StrictOrder.

Lemma asymmetric_is_irreflexive {A} (R : A -> A -> Prop) :
  (Asymmetric R) -> (Irreflexive R).
Proof.
  intros H x Rx.
  specialize (H x x).
  exact (H Rx Rx).
Qed.

Lemma irreflexive_and_transitive_is_asymmetric {A} (R : A -> A -> Prop) :
  (Irreflexive R) -> (Transitive R) -> (Asymmetric R).
Proof.
  intros HIr HTr x y Rxy Ryx.
  pose proof (HTr _ _ _ Rxy Ryx) as Hrf.
  exact (HIr _ Hrf).
Qed.


Definition Incomparible {A : Type} (R : A -> A -> Prop) :=
  fun x y => (R x y -> False) /\ (R y x -> False).


Class MyStrictOrder { A : Type } ( R : A -> A -> Prop ) := {
  SO_Irreflexive : Irreflexive R;
  SO_Transitive : Transitive R;
  SO_Asymmetric : Asymmetric R := 
    (irreflexive_and_transitive_is_asymmetric R SO_Irreflexive SO_Transitive);
}.

Print Build_MyStrictOrder.
Check Build_MyStrictOrder.

Definition Build_MyStrictOrder' (A : Type) ( R : A -> A -> Prop )
    (asymmetric : Asymmetric R) (transitive : Transitive R) :=
  Build_MyStrictOrder A R (asymmetric_is_irreflexive R asymmetric) transitive.

Print StrictOrder.
Search StrictOrder.

Class WeakStrictOrder { A : Type} ( R : A -> A -> Prop ) := {
  WSO_StrictOrder : StrictOrder R;
  WSO_Irreflexive : Irreflexive R := @StrictOrder_Irreflexive A R WSO_StrictOrder;
  WSO_Asymmetric : Asymmetric R := StrictOrder_Asymmetric WSO_StrictOrder;
  WSO_Transitive : Transitive R := WSO_StrictOrder.(StrictOrder_Transitive);
  WSO_Incomparible : Transitive (Incomparible R);
  WSO_Decidable : forall x y, { R x y } + { Incomparible R x y } + { R y x };
}.

Context `{X:Type} `{R : X -> X -> Prop} `{WSO : WeakStrictOrder X R}.

Definition WSOlt a1 a2 := R a1 a2.
Definition WSOeqv a1 a2 := (Incomparible R) a1 a2.
Definition WSOle a1 a2 := R a1 a2 \/ (Incomparible R) a1 a2.

Infix "<" := WSOlt : WSO_scope.
Infix "==" := WSOeqv (at level 70, no associativity) : WSO_scope.
Infix "<=" := WSOle (at level 70, no associativity) : WSO_scope.


Global Open Scope WSO_scope.

Lemma WSOeqv_refl : forall a, a==a.
Proof.
  intros a. unfold Incomparible. split. apply WSO_Irreflexive. apply WSO_Irreflexive.
Qed.

Lemma WSOeqv_symm : forall a1 a2, (a1==a2) -> (a2==a1).
Proof.
  intros a1 a2. unfold WSOeqv, Incomparible. tauto.
Qed.

Lemma WSOeqv_trans : forall a1 a2 a3, (a1==a2) -> (a2==a3) -> (a1==a3).
Proof.
  intros a1 a2 a3. apply (WSO_Incomparible a1 a2 a3).
Qed.


Lemma WSOlt_neq : forall a1 a2, a1 < a2 -> a1==a2 -> False.
Proof.
  unfold Incomparible.
  intros a1 a2 Hlt Hneq .
  destruct Hneq as [Hnlt Hngt].
  contradiction.
Qed.

Lemma WSOgt_neq : forall a1 a2, a2 < a1 -> a1==a2 -> False.
Proof.
  unfold Incomparible; intros a1 a2 Hlt Heq; destruct Heq; contradiction.
Qed.

Lemma WSOle_lt_trans : forall a1 a2 a3, a1 <= a2 -> a2<a3 -> a1<a3.
Proof.
  intros a1 a2 a3.
  simpl.
  intros Hle12 Hlt23.
  destruct Hle12 as [Hlt12|Heq12].
  - exact (WSO_Transitive a1 a2 a3 Hlt12 Hlt23).
  - destruct (WSO_Decidable a1 a3) as [[Hlt13|Heq13]|Hlt31].
    -- assumption.
    -- apply WSOeqv_symm in Heq12 as Heq21.
       assert (a2==a3) as Heq23 by (apply WSOeqv_trans with a1; [exact Heq21|exact Heq13]).
       destruct Heq23 as [Hnlt23 Hnlt32]. contradiction.
    -- assert (a2<a1) as Hlt21 by (apply (WSO_Transitive a2 a3 a1 Hlt23 Hlt31)).
       apply (WSOgt_neq a1 a2 Hlt21) in Heq12. contradiction.
Qed.

Lemma WSOlt_le_trans : forall a1 a2 a3, a1 < a2 -> a2<=a3 -> a1<a3.
Proof.
  intros a1 a2 a3.
  simpl.
  intros Hlt12 Hle23.
  destruct Hle23 as [Hlt23|Heq23].
  - exact (WSO_Transitive a1 a2 a3 Hlt12 Hlt23).
  - destruct (WSO_Decidable a1 a3) as [[Hlt13|Heq13]|Hlt31].
    -- assumption.
    -- apply WSOeqv_symm in Heq23 as Heq32.
       assert (a1==a2) as Heq12 by (apply WSOeqv_trans with a3; [exact Heq13|exact Heq32]).
       destruct Heq12 as [Hnlt12 Hnlt21]. contradiction.
    -- assert (a3<a2) as Hlt32 by (apply (WSO_Transitive a3 a1 a2 Hlt31 Hlt12)).
       apply (WSOgt_neq a2 a3 Hlt32) in Heq23. contradiction.
Qed.

(*
Definition cmb_equiv cmb :=
  forall x1 x2, x1==x2 -> cmb x1 x2 == x1 /\ cmb x1 x2 == x2.

Definition cmb_min cmb a1 a2 :=
  match WSO_Decidable a1 a2 with
  | inleft (left _) => a1
  | inleft (right _) => (cmb a1 a2)
  | inright _ => a2
  end.

Lemma WSOcmb_min_le_l cmb (Hcmb : cmb_equiv cmb) :
  forall a1 a2, cmb_min cmb a1 a2 <= a1.
Proof.
  intros. unfold cmb_min.
  destruct (WSO_Decidable a1 a2) as [[Hlt|Heq]|Hgt].
  - right. apply WSOeqv_refl.
  - right. apply Hcmb. exact Heq.
  - left. exact Hgt.
Qed.

Lemma WSOcmb_min_le_r cmb (Hcmb : cmb_equiv cmb) :
  forall a1 a2, cmb_min cmb a1 a2 <= a2.
Proof.
  intros. unfold cmb_min.
  destruct (WSO_Decidable a1 a2) as [[Hlt|Heq]|Hgt].
  - left. exact Hlt.
  - right. apply Hcmb. exact Heq.
  - right. apply WSOeqv_refl.
Qed.

Lemma WSOmin_glb_lt cmb (Hcmb : cmb_equiv cmb) :
  forall a1 a2 a3, a1<a2 -> a1<a3 -> a1 < (cmb_min cmb a2 a3).
Proof.
  intros a1 a2 a3 H12 H13. unfold cmb_min.
  destruct (WSO_Decidable a2 a3) as [[Hlt|Heq]|Hgt].
  - exact H12.
  - apply WSOlt_le_trans with a2; [exact H12|].
    right. apply WSOeqv_symm. apply (Hcmb a2 a3). exact Heq.
  - exact H13.
Qed.
*)

Close Scope WSO_scope.

End Ordering.




Section NatOrdering.

Open Scope nat_scope.

Definition ic (x y : nat) :=
  (x < y -> False) /\ (y < x -> False).

Lemma ic_eq : forall (m1 m2 : nat),
  ic m1 m2 -> eq m1 m2.
Proof.
  intros m1 m2.
  set (H:=lt_eq_lt_dec m1 m2).
  intros Hneq; destruct Hneq as [Hnlt Hngt].
  destruct H as [[Hlt|Heq]|Hgt];
    [contradiction|assumption|contradiction].
Qed.

Lemma eq_ic : forall (m1 m2 : nat),
  eq m1 m2 -> ic m1 m2.
Proof.
  intros m1 m2 Heq. unfold ic.
  split.
  intros Hlt; revert Heq; apply Nat.lt_neq; exact Hlt.
  intros Hlt. apply eq_sym in Heq. revert Heq. apply Nat.lt_neq. exact Hlt.
Qed.

Lemma ic_refl : forall (m : nat),
  ic m m.
Proof.
  intros m. unfold ic. assert (m=m) as Heq; [trivial|].
  split.
  - intro Hlt. revert Heq. apply Nat.lt_neq. exact Hlt.
  - intro Hlt. revert Heq. apply Nat.lt_neq. exact Hlt.
Qed.

Lemma ic_symm : forall (m1 m2 : nat),
  ic m1 m2 -> ic m2 m1.
Proof.
  intros m1 m2 H. unfold ic in *.
  split. apply H. apply H.
Qed.

Lemma ic_trans : forall (m1 m2 m3 : nat),
  ic m1 m2 -> ic m2 m3 -> ic m1 m3.
Proof.
  intros m1 m2 m3 H12 H23.
  apply eq_ic.
  apply eq_trans with m2.
  - apply ic_eq; exact H12.
  - apply ic_eq; exact H23.
Qed.

Lemma lt_ic_lt_dec : forall m1 m2, { lt m1 m2 } + { ic m1 m2 } + { lt m2 m1}.
Proof.
  intros m1 m2.
  assert ({m1<m2}+{~(m1<m2)}) as H1 by (apply lt_dec).
  assert ({m2<m1}+{~(m2<m1)}) as H2 by (apply lt_dec).
  destruct H1 as [Hl1|Hn1].
  - left; left. exact Hl1.
  - destruct H2 as [Hl2|Hn2].
    -- right. exact Hl2.
    -- left; right. unfold ic. exact (conj Hn1 Hn2).
Qed.

Definition fst_eq {X} (a1 a2 : nat * X) := (fst a1) = (fst a2).
Definition fst_lt {X} (a1 a2 : nat * X) := (fst a1) < (fst a2).
Definition fst_ic {X} (a1 a2 : nat * X) := ic (fst a1) (fst a2).

Lemma fst_lt_irrefl {X} : forall (a : nat * X),
  (fst_lt a a) -> False.
Proof. unfold fst_lt. intros a. apply Nat.lt_irrefl. Qed.

Lemma fst_lt_trans {X} : forall (a1 a2 a3 : nat * X),
  (fst_lt a1 a2) -> (fst_lt a2 a3) -> (fst_lt a1 a3).
Proof. unfold fst_lt. intros a1 a2 a3. apply Nat.lt_trans. Qed.

Lemma fst_lt_ic_lt_dec {X} : forall (a1 a2 : nat * X),
  { fst_lt a1 a2 } + { fst_ic a1 a2 } + { fst_lt a2 a1}.
Proof. intros a1 a2. unfold fst_lt, fst_ic. apply lt_ic_lt_dec. Qed.

Lemma fst_lt_eq_lt_dec {X} : forall (a1 a2 : nat * X),
  { fst_lt a1 a2 } + { fst_eq a1 a2 } + { fst_lt a2 a1}.
Proof. intros a1 a2. unfold fst_lt, fst_eq. apply lt_eq_lt_dec. Qed.

Lemma fst_ic_eq {X} : forall (a1 a2 : nat * X),
  fst_ic a1 a2 -> fst_eq a1 a2.
Proof. intros a1 a2. apply ic_eq. Qed.

Lemma fst_ic_trans {X} : forall (a1 a2 a3 : nat * X),
  fst_ic a1 a2 -> fst_ic a2 a3 -> fst_ic a1 a3.
Proof. unfold fst_lt. intros a1 a2 a3. apply ic_trans. Qed.

Instance WSOfst_lt {A:Type} : WeakStrictOrder (@fst_lt A) :=
{
  WSO_StrictOrder := Build_StrictOrder _ fst_lt_irrefl fst_lt_trans;
  WSO_Incomparible := fst_ic_trans;
  WSO_Decidable := fst_lt_ic_lt_dec;
}.


Close Scope nat_scope.


End NatOrdering.


Section OrderTopology.

Class CompatibleOrders {A : Type} (le : A -> A -> Prop) (lt : A -> A -> Prop) := {
  le_order : PartialOrder le;
  le_refl := le_order.(refl);
  le_antisymm := le_order.(antisymm);
  le_trans := le_order.(trans);
  lt_strict_order : StrictPartialOrder lt;
  lt_irrefl := asymmetric_is_irreflexive lt (lt_strict_order.(asymm));
  lt_antisymm := lt_strict_order.(asymm);
  lt_trans := lt_strict_order.(strict_trans);
  lt_le : forall {a b}, lt a b -> le a b;
  le_lt_trans : forall {a b c}, le a b -> lt b c -> lt a c;
  lt_le_trans : forall {a b c}, lt a b -> le b c -> lt a c;
}.

Class CanonicalOrders {A : Type} (le : A -> A -> Prop) := {
  lt : A -> A -> Prop := (fun a b : A => le a b /\ ~ (le b a));
  lt_le_compatible_orders : CompatibleOrders le lt;
  lt_iff_le_and_not_ge : forall a b : A, lt a b <-> le a b  /\ ~ (le b a);
}.
 

Definition shift {X : Type} (seq : nat -> X) (n : nat) := fun m => seq (m+n).

Notation Nat := nat.

Section Bounds.

Context `{X:Type} `{le : X -> X -> Prop} `{PO : PartialOrder X le}.
(* 
Context  `{lt : X -> X -> Prop}`{compat : CompatibleOrders X le lt}.
*)

Infix "<=" := le.

Definition is_increasing (s : Nat -> X) : Prop := 
  forall {m n : Nat}, (m <= n)%nat -> s m <= s n.
Definition is_decreasing (s : Nat -> X) : Prop := 
  forall {m n : Nat}, (m <= n)%nat -> s n <= s m.
 
Definition is_upper_bound (s : Nat -> X) (ub : X) : Prop := 
  forall n, s n <= ub.
Definition is_set_upper_bound (s : X -> Prop) (ub : X) : Prop := 
  forall x, s x -> x <= ub.
Definition is_sup (s : Nat -> X) (sup : X) : Prop := 
  forall ub, is_upper_bound s ub -> sup <= ub.
Definition is_set_sup (s : X -> Prop) (lub : X) : Prop := 
  is_set_upper_bound s lub /\ forall ub, is_set_upper_bound s ub -> lub <= ub.

Definition is_lower_bound (s : Nat -> X) (lb : X) : Prop := 
  forall n, lb <= s n.
Definition is_set_lower_bound (s : X -> Prop) (lb : X) : Prop := 
  forall x, s x -> lb <= x.
Definition is_inf (s : Nat -> X) (inf : X) : Prop := 
  forall lb, is_lower_bound s lb -> lb <= inf.
Definition is_set_inf (s : X -> Prop) (glb : X) : Prop := 
  is_set_lower_bound s glb /\ forall lb, is_set_lower_bound s lb -> lb <= glb.

Definition is_limsup (s : Nat -> X) (x : X) : Prop := 
  is_set_inf (fun ub => exists n, is_upper_bound (shift s n) ub) x.
Definition is_liminf (s : Nat -> X) (x : X) : Prop := 
  is_set_sup (fun lb => exists n, is_lower_bound (shift s n) lb) x.

End Bounds.

Print is_upper_bound.

Definition countable (X : Type) : Type :=
  { numbering : Nat -> X | forall x, exists n, numbering n = x }.

Context `{Q:Type} `{le : Q -> Q -> Prop} `{PO : PartialOrder Q le}
  `{lt : Q -> Q -> Prop} `{SPO : StrictPartialOrder Q lt} `{CPO : CompatibleOrders Q le lt}.

Infix "<=" := le.
Infix "<" := lt.

Check is_increasing.

Record IncreasingSequence : Type := 
  { is :> Nat -> Q; incr : @is_increasing Q le is }.
Record DecreasingSequence : Type := 
  { ds :> Nat -> Q; decr : @is_decreasing Q le ds }.

Definition lower_equivalent (p q : IncreasingSequence) : Prop :=
  forall r : Q, @is_upper_bound Q le p r <-> (forall n, q.(is) n <= r).

Definition upper_equivalent (p q : Nat -> Q) : Prop :=
  forall r : Q, (forall n, r <= p n) <-> (forall n, r <= q n).

Definition all_le (p : IncreasingSequence) (q : DecreasingSequence) : Prop :=
  forall m n, p m <= q n.

Check Nat.le_max_r.

Lemma all_le_weak : forall  (p : IncreasingSequence) (q : DecreasingSequence),
  (forall n, p n <= q n) -> all_le p q.
Proof.
  intros [p Hp] [q Hq] Hw. intros m n.
  set (k := max m n : Nat).
  simpl; simpl in Hw.
  apply (PO.(trans) _ (q k) _).
  apply (PO.(trans) _ (p k) _).
  - exact (Hp m k (Nat.le_max_l m n)).
  - exact (Hw k).
  - exact (Hq n k (Nat.le_max_r m n)).
Qed.

Axiom DNE : forall (p : Prop), not (not p) -> p. 
Axiom NAEX : forall p : Nat -> Nat -> Prop, 
  not (forall m n, p m n) -> exists m n, not (p m n).

Lemma all_le_proper : forall (p1 p2 : IncreasingSequence) (q1 q2 : DecreasingSequence),
  lower_equivalent p1 p2 -> upper_equivalent q1 q2 -> all_le p1 q1 -> all_le p2 q2.
Proof.
  unfold all_le, lower_equivalent, upper_equivalent, is_upper_bound.
  intros [p1 Hp1] [p2 Hp2] [q1 Hq1] [q2 Hq2] Hp Hq H1.
  simpl; simpl in H1.
  intros m.
  specialize (Hq (p2 m)); simpl in Hq.
  apply (proj1 Hq); clear Hq.
  intro n; revert m.
  specialize (Hp (q1 n)); simpl in Hp.
  apply (proj1 Hp); clear Hp.
  exact (fun m => H1 m n).
Qed.


Lemma set_inf_unique :
  forall (S : Q -> Prop) (x1 x2 : Q), 
    @is_set_inf Q le S x1 -> @is_set_inf Q le S x2 -> x1 = x2.
Proof.
  unfold is_set_inf.
  intros S x1 x2 [Hlb1 Hu1] [Hlb2 Hu2].
  specialize (Hu1 x2 Hlb2).
  specialize (Hu2 x1 Hlb1).
  exact (PO.(antisymm) x1 x2 Hu2 Hu1).
Qed.

Lemma limsup_unique :
  forall (p : IncreasingSequence) (x1 x2 : Q), 
    @is_limsup Q le p x1 -> @is_limsup Q le p x2 -> x1 = x2.
Proof.
  unfold is_limsup; simpl.
  intros p x1 x2 Hx1 Hx2.
  remember (fun ub : Q => ex (fun n : nat => @is_upper_bound Q le (shift p n) ub)) as S.
  exact (set_inf_unique S x1 x2 Hx1 Hx2).
Qed.

Definition is_below_relation (lt : Q -> Q -> Prop) : Prop :=
  forall p x q y, 
    @is_increasing Q lt p -> @is_sup Q lt p x -> 
      @is_decreasing Q lt q -> @is_inf Q lt q y ->
        lt y x <-> exists m n, lt (q n) (p m).

Definition is_far_below_relation (le : Q -> Q -> Prop) (lt : Q -> Q -> Prop) : Prop :=
  forall p x q y, 
    @is_increasing Q le p -> @is_sup Q le p x -> 
      @is_decreasing Q le q -> @is_inf Q le q y ->
        lt y x <-> exists m n, lt (q n) (p m).

Definition is_way_below_relation (le : Q -> Q -> Prop) (lt : Q -> Q -> Prop) : Prop :=
  forall x y, (lt y x) <-> forall p q, 
    @is_increasing Q le p -> @is_sup Q le p x -> 
      @is_decreasing Q le q -> @is_inf Q le q y ->
        exists m n, le (q n) (p m).

Lemma is_far_below_relation_proper :
  is_far_below_relation le lt -> forall p1 p2 x q1 q2 y,
    @is_increasing Q le p1 -> @is_sup Q le p1 x -> 
    @is_increasing Q le p2 -> @is_sup Q le p2 x -> 
      @is_decreasing Q le q1 -> @is_inf Q le q1 y -> 
      @is_decreasing Q le q2 -> @is_inf Q le q2 y -> 
        (exists m1 n1, lt (q1 n1) (p1 m1)) <-> (exists m2 n2, lt (q2 n2) (p2 m2)).
Proof.
  intros FB p1 p2 x q1 q2 y Hp1 Hx1 Hp2 Hx2 Hq1 Hy1 Hq2 Hy2.
  pose proof (FB p1 x q1 y Hp1 Hx1 Hq1 Hy1) as Hlty1.
  pose proof (FB p2 x q2 y Hp2 Hx2 Hq2 Hy2) as Hlty2.
  apply (@iff_trans _ (lt y x) _).
  exact (iff_sym Hlty1).
  exact Hlty2.
Qed.

End OrderTopology.