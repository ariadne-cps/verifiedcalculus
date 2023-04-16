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


Section Sorting.

Open Scope nat_scope.

Inductive is_sorted : list nat -> Prop :=
   | is_sorted_nil : is_sorted nil
   | is_sorted_one : forall n0, is_sorted (cons n0 nil)
   | is_sorted_cons : forall n0 ns1 n1, head ns1 = Some n1 -> n0<n1 -> is_sorted ns1 -> is_sorted (n0::ns1).

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

Lemma is_sorted_cons_lt: forall n0 n1 (ns2 : list nat), 
  is_sorted (n0 :: n1 :: ns2) -> n0 < n1.
Proof.
  intros n0 n1 n2s Hns. inversion Hns. simpl in H1. injection H1. intros Hn1. subst n1. exact H2.
Qed.


Function merge 
  (msns : list nat * list nat)
    {measure (fun msns' => (length (fst msns') + length (snd msns'))) msns } 
  : list nat :=
  match (msns) with
  | ( nil , nil ) => nil
  | ( nil , _ ) => snd msns
  | ( _ , nil ) => fst msns
  | ( m0::ms1 , n0::ns1 ) =>
      match lt_eq_lt_dec m0 n0 with
      | inleft (left _) => m0 :: merge (ms1,n0::ns1)
      | inleft (right _) => m0 :: merge (ms1,ns1)
      | inright _ => n0 :: merge (m0::ms1,ns1)
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

Lemma merge_eq_nil_nil : merge (nil,nil) = nil.
Proof. intros. rewrite merge_equation. reflexivity. Qed.
Lemma merge_eq_cons_nil : forall m0 ms1, merge (m0::ms1,nil) = m0::ms1.
Proof. intros. rewrite merge_equation. reflexivity. Qed.
Lemma merge_eq_nil_cons : forall n0 ns1, merge (nil,n0::ns1) = n0::ns1.
Proof. intros. rewrite merge_equation. reflexivity. Qed.
Lemma merge_eq_cons_cons : forall m0 ms1 n0 ns1, 
  merge (m0::ms1,n0::ns1) = 
    match lt_eq_lt_dec m0 n0 with
    | inleft (left _) => (m0 :: merge (ms1,n0::ns1))
    | inleft (right _) => m0 :: merge (ms1,ns1)
    | inright _ => n0 :: merge (m0::ms1,ns1)
    end.
Proof. intros. rewrite merge_equation. reflexivity. Qed.
  
(*
Lemma merge_nil_r : forall ms, merge (ms,nil) = ms.
Proof. intros [|m0 ms1]; rewrite merge_equation; reflexivity. Qed.
Lemma merge_nil_l : forall ns, merge (nil,ns) = ns.
Proof. intros [|n0 ns1]; rewrite merge_equation; reflexivity. Qed.
*)  

Lemma merge_head : forall m0 ms1 n0 ns1, 
  head (merge (m0::ms1,n0::ns1)) = Some (min m0 n0).
Proof.
  intros.
  rewrite -> merge_eq_cons_cons.
  destruct (lt_eq_lt_dec m0 n0) as [[Hlt0 | Heq0] | Hgt0].
  - simpl. rewrite -> min_l. reflexivity. apply (PeanoNat.Nat.lt_le_incl m0 n0  Hlt0). 
  - simpl. rewrite -> min_l. reflexivity. apply (PeanoNat.Nat.eq_le_incl m0 n0  Heq0). 
  - simpl. rewrite -> min_r. reflexivity. apply (PeanoNat.Nat.lt_le_incl n0 m0  Hgt0). 
Qed.

Proposition merge_sorted : forall (ms ns : list nat),
  is_sorted ms -> is_sorted ns -> is_sorted (merge (ms,ns)).
Proof.
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
       destruct (lt_eq_lt_dec m0 n0) as [[Hlt0 | Heq0] | Hgt0].
       --- (* ms=m0::ms1, ns=n0::ns1; m0<n0 *)
           destruct ms1 as [|m1 ms2].
           (* m0 :: merge (nil, n0 :: ns1) *)
           rewrite -> merge_eq_nil_cons. 
           apply (is_sorted_cons_cons _ _ _ Hlt0 Hns).
           (* m0 :: merge (m1 :: ms2, n0 :: ns1) *)
           assert (m0<m1) as Hm0. apply (is_sorted_cons_lt _ _ _ Hms).
           apply is_sorted_cons with (min m1 n0).
           apply merge_head.
           apply PeanoNat.Nat.min_glb_lt; [exact Hm0|exact Hlt0].
           apply (IHms1 _ Hms1 Hns).
       --- (* ms=m0::ms1, ns=n0::ns1; m0=n0 *)
           destruct ms1 as [|m1 ms2]; destruct ns1 as [|n1 ns2].
           (* m0 :: merge (nil, nil) *)
           rewrite -> merge_eq_nil_nil. apply is_sorted_one.
           (* m0 :: merge (nil, n1 :: ns2) *)
           rewrite -> merge_eq_nil_cons. subst m0. exact Hns. 
           (* m0 :: merge (m1 :: ms2, nil) *)
           rewrite -> merge_eq_cons_nil. exact Hms. 
           (* m0 :: merge (m1 :: ms2, n1 :: ns2) *)
           assert (m0<m1) as Hm0. apply (is_sorted_cons_lt _ _ _ Hms).
           assert (n0<n1) as Hn0. apply (is_sorted_cons_lt _ _ _ Hns).
           apply is_sorted_cons with (min m1 n1). 
           apply merge_head.
           apply PeanoNat.Nat.min_glb_lt. exact Hm0. subst m0. apply Hn0.
           apply (IHms1 _ Hms1 Hns1).
       --- (* ms=m0::ms1, ns=n0::ns1; m0>n0 *)
           destruct ns1 as [|n1 ns2].
           (* n0 :: merge (m0 :: ms1, nil) *)
           rewrite -> merge_eq_cons_nil. 
           apply (is_sorted_cons_cons _ _ _ Hgt0 Hms).
           (* n0 :: merge (m0 :: ms1, n1 :: ns2) *)
           assert (n0<n1) as Hn0. apply (is_sorted_cons_lt _ _ _ Hns).
           apply is_sorted_cons with (min m0 n1). 
           apply merge_head.
           apply PeanoNat.Nat.min_glb_lt. exact Hgt0. exact Hn0.
           apply (IHns1 Hms Hns1).
Qed.
 
Fixpoint filter (r : nat -> bool) (ns : list nat) : (list nat) :=
  match ns with
  | nil => nil
  | n0 :: ns1 => if (r n0) 
                  then (filter r ns1)
                  else (n0::filter r ns1)
  end.

Lemma filter_cons : forall r n0 ns1, 
  filter r (n0::ns1) = if (r n0) then (filter r ns1) else (n0::filter r ns1).
Proof. intros. simpl. reflexivity. Qed.
(*
Lemma filter_true : forall r n0 ns1, 
  (true = r n0) -> filter r (n0::ns1) = filter r ns1.
Proof. intros. simpl. rewrite <- H. simpl. reflexivity. Qed.
Lemma filter_false : forall r n0 ns1,
  (false = r n0) -> filter r (n0::ns1) = n0::filter r ns1.
Proof. intros. simpl. rewrite <- H. simpl. reflexivity. Qed.
*)


Lemma filter_head : forall r n0 ns1 nf, 
  is_sorted (n0::ns1) -> head (filter r (n0::ns1)) = Some nf -> n0 <= nf.
Proof.
  intros r n0 ns1. revert n0.
  induction ns1 as [|n1 ns2].
  - intros n0 nf Hs. simpl. destruct (r n0).
    -- discriminate. 
    -- simpl. intros H. inversion H. apply PeanoNat.Nat.eq_le_incl. reflexivity. 
  - intros n0 nf Hs. 
    specialize (IHns2 n1).
    rewrite -> filter_cons.
    remember (r n0) as rn0.
    destruct (rn0).
    -- intros Hnf.
       apply PeanoNat.Nat.le_trans with n1.
       --- apply PeanoNat.Nat.lt_le_incl. apply is_sorted_cons_lt in Hs as Hlt01. exact Hlt01.
       --- apply IHns2. apply (is_sorted_cons_inv n0). exact Hs. exact Hnf.
    -- intros Hnf. inversion Hnf. apply PeanoNat.Nat.eq_le_incl. reflexivity.
Qed.

 
Theorem filter_sorted : forall r ns, is_sorted ns -> is_sorted (filter r ns).
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
                apply PeanoNat.Nat.lt_le_trans with n1.
                apply is_sorted_cons_lt with ns2. exact H.
                apply filter_head with r ns2. exact Hns1. rewrite <- Heqns1f. trivial.
Qed.
 
End Sorting.
