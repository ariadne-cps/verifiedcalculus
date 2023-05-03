(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Import PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Classes.RelationClasses.


Declare Scope WSO_scope.
Delimit Scope WSO_scope with WSO.


Section Ordering.

Lemma asymmetric_irreflexive {A} (R : A -> A -> Prop) : 
  (Asymmetric R) -> (Irreflexive R).
Proof.
  intros H x Rx.
  specialize (H x x).
  exact (H Rx Rx).
Qed.


Definition Incomparible {A : Type} (R : A -> A -> Prop) := 
  fun x y => (R x y -> False) /\ (R y x -> False).


Class WeakStrictOrder { A : Type} ( R : A -> A -> Prop ) := {
  WSO_Asymmetric : Asymmetric R;
  WSO_Transitive : Transitive R;
  WSO_Irreflexive : Irreflexive R := (asymmetric_irreflexive R WSO_Asymmetric);
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

Lemma fst_lt_asymm {X} : forall (a1 a2 : nat * X), 
  (fst_lt a1 a2) -> (fst_lt a2 a1) -> False.
Proof. unfold fst_lt. intros a1 a2. apply Nat.lt_asymm. Qed.

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
  WSO_Asymmetric := fst_lt_asymm;
  WSO_Transitive := fst_lt_trans;
  WSO_Incomparible := fst_ic_trans;
  WSO_Decidable := fst_lt_ic_lt_dec;
}.


Close Scope nat_scope.


End NatOrdering.

