(******************************************************************************
 *  utilities/Sorting.v
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


Require Import List.
Require Import PeanoNat.
Require Import Recdef.

Require Export Ordering.



Section Sorting.

Open Scope WSO_scope.

Context `{X:Type} `{R : X -> X -> Prop} `{WSO : WeakStrictOrder X R}.

Infix "<" := (@WSOlt X R) : WSO_scope.
Infix "==" := (@WSOeqv X R) (at level 70, no associativity) : WSO_scope.
Infix "<=" := (@WSOle X R) (at level 70, no associativity) : WSO_scope.

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

Close Scope WSO_scope.

End Sorting.
