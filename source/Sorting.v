(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Import Coq.Arith.Compare_dec.
Require Import PeanoNat.

Require Import Recdef.
Require Import List.


Require Import Classes.RelationClasses.

Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.


Section OrderSorting.

Lemma asymmetric_irreflexive {A} (R : A -> A -> Prop) : 
  (Asymmetric R) -> (Irreflexive R).
Proof.
  intros H x Rx.
  specialize (H x x).
  exact (H Rx Rx).
Qed.

  

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

Definition Incomparible {A : Type} (R : A -> A -> Prop) := 
  fun x y => (R x y -> False) /\ (R y x -> False).


Class WeakStrictOrder { A : Type} ( R : A -> A -> Prop ) := {
  WSO_Asymmetric : Asymmetric R;
  WSO_Transitive : Transitive R;
  WSO_Irreflexive : Irreflexive R := (asymmetric_irreflexive R WSO_Asymmetric);
  WSO_Incomparible : Transitive (Incomparible R);
  WSO_Decidable : forall x y, { R x y } + { Incomparible R x y } + { R y x }; 
}.

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

Context `{X:Type} `{R : X -> X -> Prop} `{WSO : WeakStrictOrder X R}.


Definition WSOlt a1 a2 := R a1 a2.
Infix "<" := R. 

Definition WSOeqv a1 a2 := (Incomparible R) a1 a2.
Infix "==" := (Incomparible R) (at level 70, no associativity). 

Definition WSOle a1 a2 := a1 < a2 \/ a1 == a2.
Infix "<=" := WSOle (at level 70, no associativity). 

Lemma WSOeqv_refl : forall a, a==a.
Proof.
  intros a. unfold Incomparible. split. apply WSO_Irreflexive. apply WSO_Irreflexive.
Qed.

Lemma WSOeqv_symm : forall a1 a2, (a1==a2) -> (a2==a1).
Proof.
  intros a1 a2. unfold Incomparible. tauto.
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



Inductive is_sorted : list X -> Prop :=
   | is_sorted_nil : is_sorted nil
   | is_sorted_one : forall n0, is_sorted (cons n0 nil)
   | is_sorted_cons : forall (n0:X) (ns1:list X) n1, head ns1 = Some n1 -> n0 < n1 -> is_sorted ns1 -> is_sorted (n0::ns1).
  
Lemma is_sorted_cons_cons : forall n0 n1 ns2, n0 < n1 -> is_sorted (n1::ns2) -> is_sorted (n0::n1::ns2).
Proof.
  intros n0 n1 ns2 H01 H12.
  assert (head (n1::ns2) = Some n1) as Hn1; [trivial|].
  exact (is_sorted_cons _ _ _  Hn1 H01 H12). 
Qed.

Lemma is_sorted_cons_inv : forall n0 ns1, is_sorted (n0::ns1) -> is_sorted ns1.
Proof.
  intros n0 ns Hn; inversion Hn; trivial; apply is_sorted_nil.
Qed.

Lemma is_sorted_cons_lt: forall n0 n1 (ns2 : list X), 
  is_sorted (n0 :: n1 :: ns2) -> n0 < n1.
Proof.
  intros n0 n1 n2s Hns. inversion Hns. simpl in H1. injection H1. intros Hn1. subst n1. exact H2.
Qed.


Fixpoint filter (r : X -> bool) (ns : list X) : (list X) :=
  match ns with
  | nil => nil
  | n0 :: ns1 => if (r n0) 
                  then (filter r ns1)
                  else (n0::filter r ns1)
  end.

Lemma filter_cons : forall r n0 ns1, 
  filter r (n0::ns1) = if (r n0) then (filter r ns1) else (n0::filter r ns1).
Proof. intros. simpl. reflexivity. Qed.

Lemma filter_head : forall r n0 ns1 nf, 
  is_sorted (n0::ns1) -> head (filter r (n0::ns1)) = Some nf -> (n0 < nf \/ n0 = nf).
Proof.
  intros r n0 ns1. revert n0.
  induction ns1 as [|n1 ns2].
  - intros n0 nf Hs. simpl. destruct (r n0).
    -- discriminate. 
    -- simpl. intros H. inversion H. right. reflexivity. 
  - intros n0 nf Hs. 
    specialize (IHns2 n1).
    rewrite -> filter_cons.
    remember (r n0) as rn0.
    destruct (rn0).
    -- intros Hnf.
       left. 
       apply is_sorted_cons_lt with n0 n1 ns2 in Hs as H01.
       specialize (IHns2 nf (is_sorted_cons_inv _ _ Hs) Hnf).
       destruct IHns2 as [Hlt|Heq].
       --- apply (WSO_Transitive _ n1 _). exact H01. exact Hlt.
       --- rewrite <- Heq. exact H01.
    -- intros Hnf. right. inversion Hnf. reflexivity.
Qed.
 
Theorem filter_sorted : forall (r : X -> bool) (ns : list X), 
  is_sorted ns -> is_sorted (filter r ns).
Proof.
  intros r ns.
  induction ns as [|n0 ns1].
  - (* ns = nil *)
    simpl. tauto.
  - (* ns = n0::ns1 *)
    intros H.
    assert (is_sorted ns1) as Hns1 by (apply (is_sorted_cons_inv n0 _ H)).
    specialize (IHns1 Hns1).
    rewrite -> filter_cons.
    remember (r n0) as rn0.
    destruct (rn0).
    -- (* true = r n0 *)
       exact IHns1.
    -- (* false = r n0 *)
       destruct ns1 as [|n1 ns2].
       --- simpl. apply is_sorted_one.
       --- remember (filter r (n1::ns2)) as ns1f.
           destruct ns1f as [|n1f ns2f].
           ---- (* filter r ns1 = nil *)
                apply is_sorted_one.
           ---- apply is_sorted_cons with n1f; [trivial| |exact IHns1].
                assert (n1 < n1f \/ n1 = n1f) as H1f. {
                  apply filter_head with r ns2. exact Hns1. rewrite <- Heqns1f. trivial.                
                }
                apply is_sorted_cons_lt with n0 n1 ns2 in H as H01.
                destruct H1f as [H1lt|H1eq].
                apply (WSO_Transitive _ n1 _).
                exact H01. exact H1lt.
                subst n1f. exact H01.
Qed.




Lemma map_cons : forall {X} (r : X -> X) n0 ns1, 
  map r (n0::ns1) = r n0 :: map r ns1.
Proof. intros. simpl. reflexivity. Qed.

Definition increasing (r : X -> X) : Prop :=
  forall (x1 x2 : X), x1 < x2 -> r x1 < r x2.

Theorem map_sorted : forall (r : X -> X) (p : increasing r) (ns : list X), 
  is_sorted ns -> is_sorted (map r ns).
Proof.
  intros r p ns.
  induction ns as [|n0 ns1].
  - (* ns = nil *)
    simpl. tauto.
  - (* ns = n0::ns1 *)
    intros H.
    assert (is_sorted ns1) as Hns1 by (apply (is_sorted_cons_inv n0 _ H)).
    specialize (IHns1 Hns1).
    destruct ns1 as [|n1 ns2].
    -- (* ns1 = nil *)
       apply is_sorted_one.
    -- (* ns1 = n1 :: ns2 *)
       rewrite -> map_cons.
       apply is_sorted_cons with (r n1).
       --- simpl; reflexivity.
       --- apply p.
           exact (is_sorted_cons_lt n0 n1 ns2 H).
       --- exact IHns1.
Qed.



Function merge'
  (cmb : X -> X -> X)
    (msns : list X * list X)
      {measure (fun msns' => (length (fst msns') + length (snd msns'))) msns } 
  : list X :=
  match (msns) with
  | ( nil , nil ) => nil
  | ( nil , _ ) => snd msns
  | ( _ , nil ) => fst msns
  | ( m0::ms1 , n0::ns1 ) =>
      match WSO_Decidable m0 n0 with
      | inleft (left _) => m0 :: merge' cmb (ms1,n0::ns1)
      | inleft (right _) => (cmb m0 n0) :: merge' cmb (ms1,ns1)
      | inright _ => n0 :: merge' cmb (m0::ms1,ns1)
      end
  end.
Proof. (* Show that the measure is decreasing. *)
  - intros. simpl.
    apply Nat.lt_succ_diag_r.
  - intros. simpl. 
    apply Nat.lt_trans with ((length ms1 + S (length ns1))%nat). 
    apply Nat.add_lt_mono_l. apply Nat.lt_succ_diag_r.  
    apply Nat.lt_succ_diag_r.
  - intros. simpl. 
    apply (Nat.succ_lt_mono (length ms1 + length ns1)).
    apply Nat.add_lt_mono_l. apply Nat.lt_succ_diag_r.
Qed.

Function merge (cmb : X -> X -> X) (ms ns : list X) : list X := 
  merge' cmb (ms,ns).

Lemma merge_eq_nil_nil : forall cmb, 
  merge cmb nil nil = nil.
Proof. intros. unfold merge. rewrite merge'_equation. reflexivity. Qed.
Lemma merge_eq_cons_nil : forall cmb m0 ms1, 
  merge cmb (m0::ms1) nil = m0::ms1.
Proof. intros. unfold merge. rewrite merge'_equation. reflexivity. Qed.
Lemma merge_eq_nil_cons : forall cmb n0 ns1, 
  merge cmb nil (n0::ns1) = n0::ns1.
Proof. intros. unfold merge. rewrite merge'_equation. reflexivity. Qed.
Lemma merge_eq_cons_cons : forall cmb m0 ms1 n0 ns1, 
  merge cmb (m0::ms1) (n0::ns1) = 
    match WSO_Decidable m0 n0 with
    | inleft (left _) => m0 :: merge cmb ms1 (n0::ns1)
    | inleft (right _) => (cmb m0 n0) :: merge cmb ms1 ns1
    | inright _ => n0 :: merge cmb (m0::ms1) ns1
    end.
Proof. intros. unfold merge. rewrite merge'_equation. reflexivity. Qed.


Lemma merge_head : forall cmb m0 ms1 n0 ns1, 
  head (merge cmb (m0::ms1) (n0::ns1)) = Some (cmb_min cmb m0 n0).
Proof. 
  intros.
  rewrite -> merge_eq_cons_cons.
  unfold cmb_min.
  destruct (WSO_Decidable m0 n0) as [[Hlt0 | Heq0] | Hgt0].
  - simpl. reflexivity. 
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem merge_sorted : forall (cmb : X -> X -> X) (Hcmb : cmb_equiv cmb) (ms ns : list X),
  is_sorted ms -> is_sorted ns -> is_sorted (merge cmb ms ns).
Proof.
  intros cmb Hcmb.
  intro ms. 
  induction ms as [|m0 ms1].
  - (* ms=nil *)
    intro ns.
    induction ns as [|n0 ns1].
    -- (* ms=nil, ns=nil *)
       intros Hms Hns. rewrite -> merge_eq_nil_nil. exact Hms.
    -- (* ms=nil, ns=n0::ns1 *)
       intros Hms Hns. rewrite -> merge_eq_nil_cons. exact Hns.
  - (* ms=m0::ms1 *)
    intro ns. 
    induction ns as [|n0 ns1].
    -- (* ms=m0::ms1, ns=nil *)
       intros Hms Hns. rewrite -> merge_eq_cons_nil. exact Hms.
    -- (* ms=m0::ms1, ns=n0::ns1 *)
       intros Hms Hns.
       assert (is_sorted ms1) as Hms1 by (apply (is_sorted_cons_inv m0 ms1 Hms)).
       assert (is_sorted ns1) as Hns1 by (apply (is_sorted_cons_inv n0 ns1 Hns)).
       rewrite -> merge_eq_cons_cons.
       destruct (WSO_Decidable m0 n0) as [[Hlt0 | Heq0] | Hgt0].
       --- (* ms=m0::ms1, ns=n0::ns1; m0<n0 *)
           destruct ms1 as [|m1 ms2].
           (* m0 :: merge (nil, n0 :: ns1) *)
           rewrite -> merge_eq_nil_cons. 
           apply (is_sorted_cons_cons _ _ _ Hlt0 Hns).
           (* m0 :: merge (m1 :: ms2, n0 :: ns1) *)
           assert (m0<m1) as Hm0. apply (is_sorted_cons_lt _ _ _ Hms).
           apply is_sorted_cons with (cmb_min cmb m1 n0).
           apply merge_head.
           apply (WSOmin_glb_lt cmb Hcmb).
           exact Hm0.
           exact Hlt0.
           exact (IHms1 (n0::ns1) Hms1 Hns).
       --- (* ms=m0::ms1, ns=n0::ns1; m0=n0 *)
           destruct ms1 as [|m1 ms2]; destruct ns1 as [|n1 ns2].
           (* m0 :: merge (nil, nil) *)
           rewrite -> merge_eq_nil_nil. apply is_sorted_one.
           (* m0 :: merge (nil, n1 :: ns2) *)
           rewrite -> merge_eq_nil_cons. 
           apply is_sorted_cons_cons.
           apply WSOle_lt_trans with n0.
           right. apply Hcmb. exact Heq0.
           apply is_sorted_cons_lt with ns2. exact Hns.
           exact Hns1.
           (* (cmb m0 n0) :: merge (m1 :: ms2, nil) *)
           rewrite -> merge_eq_cons_nil. 
           apply is_sorted_cons_cons.
           apply WSOle_lt_trans with m0.
           right. apply Hcmb. exact Heq0.
           apply is_sorted_cons_lt with ms2. exact Hms.
           exact Hms1.
           (* (cmb m0 n0) :: merge (m1 :: ms2, n1 :: ns2) *)
           assert (m0<m1) as Hm0. apply (is_sorted_cons_lt _ _ _ Hms).
           assert (n0<n1) as Hn0. apply (is_sorted_cons_lt _ _ _ Hns).
           apply is_sorted_cons with (cmb_min cmb m1 n1). 
           apply merge_head.
           apply WSOmin_glb_lt. exact Hcmb. 
           apply WSOle_lt_trans with m0.
           right. apply Hcmb. exact Heq0.
           exact Hm0. 
           apply WSOle_lt_trans with n0.
           right. apply Hcmb. exact Heq0.
           exact Hn0.
           exact (IHms1 (n1::ns2) Hms1 Hns1).           
       --- (* ms=m0::ms1, ns=n0::ns1; m0>n0 *)
           destruct ns1 as [|n1 ns2].
           (* n0 :: merge (m0 :: ms1, nil) *)
           rewrite -> merge_eq_cons_nil. 
           apply (is_sorted_cons_cons _ _ _ Hgt0 Hms).
           (* n0 :: merge (m0 :: ms1, n1 :: ns2) *)
           assert (n0<n1) as Hn0. apply (is_sorted_cons_lt _ _ _ Hns).
           apply is_sorted_cons with (cmb_min cmb m0 n1). 
           apply merge_head.
           apply WSOmin_glb_lt. exact Hcmb. exact Hgt0. exact Hn0.
           apply (IHns1 Hms Hns1).
Qed.


End OrderSorting.
