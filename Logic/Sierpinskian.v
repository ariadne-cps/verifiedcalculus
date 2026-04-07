(******************************************************************************
 *  logic/Sierpinskian.v
 *
 *  Copyright 2023 Pieter Collins
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
From Stdlib Require RelationClasses.

(* The Limited Principle of Omniscence for propositions *)
Definition LPO := forall p : nat -> Prop, (forall n : nat, (p n) \/ (~ p n)) ->
  ( exists n : nat, p n ) \/ (forall n : nat, ~ p n).

Notation B := bool.
Notation N := nat.

Notation succ := S.

Inductive BasicSierpinskian := | tru | indt.
Notation SB := BasicSierpinskian.

Definition SBand (sb1 sb2 : SB) := 
  match sb1,sb2 with | tru, tru => tru | _, _ => indt end.

Lemma SBand_tru : forall sb1 sb2 : SB, SBand sb1 sb2 = tru <-> sb1 = tru /\ sb2 = tru.
Proof. 
  unfold SBand. split.
  - destruct sb1, sb2. all: auto.
  - destruct sb1, sb2. 1: reflexivity. all: intros [H1 H2]; discriminate.
Qed.

Definition SBor (sb1 sb2 : SB) := 
  match sb1,sb2 with | indt, indt => indt | _, _ => tru end.
 
Lemma SBor_tru : forall sb1 sb2 : SB, SBor sb1 sb2 = tru <-> sb1 = tru \/ sb2 = tru.
Proof. 
  unfold SBor. split.
  - destruct sb1, sb2. all: auto.
  - destruct sb1, sb2. 1,2,3: reflexivity. all: intros [H1|H2]; discriminate.
Qed.


Definition next_after (s : N -> SB) : Prop := 
  forall n, s n = tru -> s (succ n) = tru.

Definition all_after (s : N -> SB) : Prop := 
  forall n, s n = tru -> forall m, n <= m -> s m = tru.


Record Sierpinskian := mkSierpinskian {
  seq :> N -> SB;
  proper : next_after seq
}.

Declare Scope Sierpinskian_scope.
Notation S := Sierpinskian.
Close Scope  Sierpinskian_scope.

Lemma all_ge : forall (p : N -> Prop) (i : N), 
  (p i) -> (forall j, p j -> p (succ j)) -> (forall j, i <= j -> p j).
Proof. 
  intros p i Hpi Hps.
  assert (forall k, p (i + k)) as Hk. {
    induction k.
    - rewrite -> Nat.add_0_r. exact Hpi.
    - rewrite -> Nat.add_succ_r. apply Hps. exact IHk. 
  }
  intros j Hj.
  pose proof (Nat.le_exists_sub i j Hj) as He.
  destruct He as [k [He _]].
  rewrite He. rewrite -> Nat.add_comm. now apply Hk.
Qed.

Lemma next_implies_all_after : forall seq : N -> SB, 
  next_after seq -> all_after seq.
Proof.
  intros seq H. unfold next_after, all_after in *. 
  intros i Hi. apply all_ge. exact Hi. exact H.
Qed.

Lemma all_after_sier : forall s : S, all_after s.
Proof.
  intros s. apply (next_implies_all_after s). exact (proper s).
Qed.


Delimit Scope Sierpinskian_scope with Sierpinskian.

Bind Scope Sierpinskian_scope with Sierpinskian.

Local Open Scope Sierpinskian_scope.


Definition eqv (s1 s2 : S) : Prop := exists i, forall j, i <= j -> s1 j = s2 j.
Infix "==" := eqv (at level 70, no associativity) : Sierpinskian_scope.

Lemma eqv_refl : forall s : S, s == s.
Proof. unfold eqv. intro s. exists 0. intros j Hilej. reflexivity. Qed.

Lemma eqv_sym : forall s1 s2 : S, s1 == s2 -> s2 == s1.
Proof. unfold eqv. intros s1 s2 [i He]. exists i. intros j Hilej. specialize He with j. symmetry. exact (He Hilej). Qed.

Lemma eqv_trans : forall s1 s2 s3 : S, s1 == s2 -> s2 == s3 -> s1 == s3.
Proof. 
  unfold eqv. intros s1 s2 s3 [i12 He12] [i23 He23].
  set (i13 := max i12 i23); exists i13.
  intro j; specialize He12 with j; specialize He23 with j.
  intro Hi13lej. rewrite -> He12. rewrite <- He23. reflexivity.
  - assert (i23 <= i13) as Hi23lei13 by (apply Nat.le_max_r). apply (Nat.le_trans _ i13); assumption.
  - assert (i12 <= i13) as Hi12lei13 by (apply Nat.le_max_l). apply (Nat.le_trans _ i13); assumption.
Qed.

#[global]
Instance eqvR : RelationClasses.Equivalence eqv.
Proof.
  split. exact eqv_refl. exact eqv_sym. exact eqv_trans.
Qed.

Lemma seq_eq_eqv : forall s1 s2 : S, (forall i, s1 i = s2 i) -> s1 == s2.
Proof. unfold eqv. intros s1 s2 H. exists 0. intros j _. exact (H j). Qed.


Definition definitely (s : Sierpinskian) : Prop := exists n, s n = tru.

Lemma definitely_respectful : 
  forall (s1 s2 : S) , eqv s1 s2 -> (definitely s1 -> definitely s2).
Proof.
  intros s1 s2 Heqv Ht.
  unfold definitely, eqv in *.
  destruct Heqv as [ie Heqv].
  destruct Ht as [it Ht].
  set (i := max ie it).
  pose proof (Heqv i (Nat.le_max_l ie it)) as H12i.
  pose proof (all_after_sier s1 it Ht i (Nat.le_max_r ie it)) as H1i.
  exists i. rewrite <- H12i. exact H1i.
Qed.



Lemma next_after_cnst : forall b : SB, next_after (fun _ : N => b).
Proof. intro b. unfold next_after. intros n H. exact H. Qed.

Definition tru_from (n : nat) : nat -> BasicSierpinskian := 
  fun k => if Nat.leb n k then tru else indt.
Lemma tru_from_next (n : nat) : forall k, 
  tru_from n k = tru -> tru_from n (succ k) = tru.
Proof.
  intros k H.
  unfold tru_from in *. 
  remember (Nat.leb n k) as p.
  destruct p.
  - assert (Nat.leb n (succ k) = (true : bool)) as HnSk. {
      apply PeanoNat.Nat.leb_le.
      transitivity k.
      - now apply PeanoNat.Nat.leb_le.
      - now apply PeanoNat.Nat.le_succ_diag_r.
    }
    now rewrite -> HnSk.
  - discriminate H.
Qed.

Definition true_from (n : nat) : Sierpinskian := 
  mkSierpinskian (tru_from n) (tru_from_next n).

Definition true := mkSierpinskian (fun _ : N => tru) (next_after_cnst tru).
Definition indeterminate := mkSierpinskian (fun _ : N => indt) (next_after_cnst indt).

Lemma true_iff_exists : forall s : Sierpinskian, 
  s == true <-> exists i, s i = tru.
Proof. 
  intro s; unfold eqv; simpl; split.
  - intros [i Hi]. exists i. apply Hi. exact (Nat.le_refl i).
  - intros [i Hi]. exists i. exact ( (all_after_sier s) i Hi ).
Qed.

Lemma indeterminate_iff_forall : forall s : Sierpinskian, 
  s == indeterminate <-> (forall i, s i = indt).
Proof. 
  intro s; unfold eqv; simpl; split.
  - pose proof (all_after_sier s) as Ht; unfold all_after in Ht.
    intros [k Hk] i. specialize (Ht i).
    destruct (s i).
    -- set (j := max i k).
       specialize (Ht (eq_refl tru) j (Nat.le_max_l i k)).
       specialize (Hk j (Nat.le_max_r i k)).
       now rewrite <- Ht, <- Hk.
    -- reflexivity.
  - intro Hi. exists 0. intros j Hj. exact (Hi j).
Qed.

Lemma not_true_and_indeterminate : forall s : Sierpinskian, s == true -> s == indeterminate -> False.
Proof.
  intros s HT HI.
  apply true_iff_exists in HT as HTe.
  pose proof (proj1 (indeterminate_iff_forall s) HI) as HIa.
  destruct HTe as [i HTe]; specialize (HIa i). rewrite -> HTe in HIa. discriminate HIa.
Qed.

Lemma true_or_indeterminate : LPO -> forall s : Sierpinskian, s == true \/ s == indeterminate. 
Proof.
  intros lpo s.
  assert (forall n, s n = tru \/ ~ (s n = tru)) as HD. {
    intro n; destruct (s n). left; reflexivity. right; intro HF; discriminate HF. }
  pose proof (lpo (fun n => s n = tru) HD) as H.
  destruct H as [HT|HI].
  - left; now apply true_iff_exists.
  - right. apply indeterminate_iff_forall. intro i; specialize (HI i).
    destruct (s i). contradiction. reflexivity.
Qed.



Definition and_seq (s1 s2 : N -> SB) := fun n => SBand (s1 n) (s2 n).

Lemma next_after_and : forall (s1 s2 : N -> SB), 
  next_after s1 -> next_after s2 -> next_after (and_seq s1 s2).
Proof.
  intros s1 s2 Hs1 Hs2 n Hs12.
  unfold and_seq, next_after in *.
  assert ((s1 n = tru) /\ (s2 n = tru)) as Hs1and2. {
    destruct (s1 n), (s2 n); simpl in Hs12. 
    1: split; reflexivity. all: discriminate Hs12.
  }
  rewrite -> Hs1, -> Hs2; tauto.
Qed.

Definition and (s1 s2 : S) :=
  mkSierpinskian (and_seq s1 s2) (next_after_and s1 s2 (proper s1) (proper s2)).

Lemma and_respectful : forall (s1 s1' s2 s2' : S), 
  eqv s1 s1' -> eqv s2 s2' -> eqv (and s1 s2) (and s1' s2').
Proof.
  intros s1 s1' s2 s2' [i1 He1] [i2 He2].
  unfold eqv in *.
  set (i := max i1 i2).
  exists i. intros j Hilej.
  unfold and, and_seq; simpl.
  rewrite <- He1, <- He2.
  reflexivity.
  transitivity i. exact (Nat.le_max_r i1 i2). exact Hilej.
  transitivity i. exact (Nat.le_max_l i1 i2). exact Hilej.
Qed.

Lemma and_up : forall (s1 s2 : S), and s1 s2 == true <-> s1 == true /\ s2 == true.
Proof.
  intros s1 s2.
  split.
  - unfold eqv, true. simpl. unfold and_seq. 
    intros [i Hi].
    split; exists i; intros j Hij; pose proof (Hi j Hij) as Hj;
    apply SBand_tru in Hj; destruct Hj; assumption.
  - intros [H1 H2].
    apply (eqv_trans _ (and true true)). 
    now apply and_respectful.
    unfold and, and_seq, SBand, true, eqv; simpl. 
    exists 0. reflexivity.
Qed.

Lemma and_comm : forall s1 s2 : Sierpinskian, and s1 s2 == and s2 s1.
Proof.
  intros s1 s2; unfold and, and_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); reflexivity.
Qed.

Lemma and_assoc : forall s1 s2 s3 : Sierpinskian, and (and s1 s2) s3 == and s1 (and s2 s3).
Proof.
  intros s1 s2 s3; unfold and, and_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); destruct (s3 j); reflexivity.
Qed.
  
Definition or_seq (s1 s2 : N -> SB) := fun n => SBor (s1 n) (s2 n).

Lemma next_after_or : forall (s1 s2 : N -> SB), 
  next_after s1 -> next_after s2 -> next_after (or_seq s1 s2).
Proof.
  intros s1 s2 Hs1 Hs2 n Hs12.
  unfold or_seq, next_after in *.
  apply SBor_tru in Hs12.
  apply SBor_tru.
  destruct Hs12 as [Hs1n|Hs2n].
  - left. apply Hs1. exact Hs1n.
  - right. apply Hs2. exact Hs2n.
Qed.

Definition or (s1 s2 : S) :=
  mkSierpinskian (or_seq s1 s2) (next_after_or s1 s2 (proper s1) (proper s2)).

Lemma or_respectful : forall (s1 s1' s2 s2' : S), 
  s1 == s1' -> s2 == s2' -> (or s1 s2) == (or s1' s2').
Proof.
  intros s1 s1' s2 s2' [i1 He1] [i2 He2].
  unfold eqv in *.
  set (i := max i1 i2).
  exists i. intros j Hilej.
  unfold or, or_seq; simpl.
  rewrite <- He1, <- He2.
  reflexivity.
  transitivity i. exact (Nat.le_max_r i1 i2). exact Hilej.
  transitivity i. exact (Nat.le_max_l i1 i2). exact Hilej.
Qed.

Lemma or_up : forall (s1 s2 : S), or s1 s2 == true <-> s1 == true \/ s2 == true.
Proof.
  intros s1 s2.
  split.
  - unfold eqv, true. simpl. unfold or_seq. 
    intros [i Hi].
    pose proof (Hi i (Nat.le_refl i)) as H12i. 
    apply SBor_tru in H12i.
    destruct H12i as [H1i|H2i].
    -- left. exists i. exact (all_after_sier s1 _ H1i).
    -- right. exists i. exact (all_after_sier s2 _ H2i).
  - unfold eqv, true in *; simpl.
    intros [H1|H2].
    -- destruct H1 as [i1 H1]. exists i1. intros j Hij. specialize H1 with j.
       unfold or_seq. rewrite -> H1. simpl. reflexivity. exact Hij.
    -- destruct H2 as [i2 H2]. exists i2. intros j Hij. specialize H2 with j.
       unfold or_seq. rewrite -> H2. rewrite -> SBor_tru. right. reflexivity. exact Hij.
Qed.

Lemma or_comm : forall s1 s2 : Sierpinskian, or s1 s2 == or s2 s1.
Proof.
  intros s1 s2; unfold or, or_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); reflexivity.
Qed.

Lemma or_assoc : forall s1 s2 s3 : Sierpinskian, or (or s1 s2) s3 == or s1 (or s2 s3).
Proof.
  intros s1 s2 s3; unfold or, or_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); destruct (s3 j); reflexivity.
Qed.


Lemma and_or_distrib_r : forall s1 s2 s3 : Sierpinskian, and s1 (or s2 s3) == or (and s1 s2) (and s1 s3).
Proof. 
  intros s1 s2 s3; unfold and, and_seq, or, or_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); destruct (s3 j); reflexivity.
Qed.
Lemma and_or_distrib_l : forall s1 s2 s3 : Sierpinskian, and (or s1 s2) s3 == or (and s1 s3) (and s2 s3).
Proof. 
  intros s1 s2 s3; unfold and, and_seq, or, or_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); destruct (s3 j); reflexivity.
Qed.
Lemma or_and_distrib_r : forall s1 s2 s3 : Sierpinskian, or s1 (and s2 s3) == and (or s1 s2) (or s1 s3).
Proof. 
  intros s1 s2 s3; unfold and, and_seq, or, or_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); destruct (s3 j); reflexivity.
Qed.
Lemma or_and_distrib_l : forall s1 s2 s3 : Sierpinskian, or (and s1 s2) s3 == and (or s1 s3) (or s2 s3).
Proof. 
  intros s1 s2 s3; unfold and, and_seq, or, or_seq, eqv. exists 0; intros j H0j. simpl.
  destruct (s1 j); destruct (s2 j); destruct (s3 j); reflexivity.
Qed.


(*
Bool.orb_andb_distrib_l : forall b1 b2 b3 : B, ((b1 && b2) || b3) = ((b1 || b3) && (b2 || b3))
Bool.andb_orb_distrib_r : forall b1 b2 b3 : B, (b1 && (b2 || b3)) = ((b1 && b2) || (b1 && b3))
Bool.andb_orb_distrib_l : forall b1 b2 b3 : B, ((b1 || b2) && b3) = ((b1 && b3) || (b2 && b3))
Bool.orb_andb_distrib_r : forall b1 b2 b3 : B, (b1 || (b2 && b3)) = ((b1 || b2) && (b1 || b3))
*)

Fixpoint one_of_le (seq : N -> SB) (n : N) : SB :=
  match n with
  | 0 => seq 0
  | succ m => SBor (one_of_le seq m) (seq (succ m))
  end. 
 
Lemma one_of_le_succ : forall seq n, 
  one_of_le seq (succ n) = SBor (one_of_le seq n) (seq (succ n)).
Proof. intros; auto. Qed.

Import PeanoNat.

Lemma one_of_le_iff_exists : forall seq n, (one_of_le seq n = tru) <-> exists i, (i <= n /\ seq i = tru).
Proof.
  intro seq. intro m; revert m. 
  split.
  - induction m.
    -- unfold one_of_le. intro H0. exists 0. split. exact (Nat.le_refl 0). exact H0.
    -- rewrite -> one_of_le_succ.
      intro H. 
      remember (seq (succ m)) as sn.
      destruct sn.
      --- exists (succ m). split. now apply Nat.le_refl. now rewrite Heqsn.
      --- assert (one_of_le seq m = tru) as H'. {
          destruct (one_of_le seq m). reflexivity. simpl in H. discriminate H. }
          destruct (IHm H') as [i [Him Hit]].
          exists i. split. apply le_S. exact Him. exact Hit.  
  - induction m.
    -- unfold one_of_le. intro H. destruct H as [i [Hi Ht]]. apply Nat.le_0_r in Hi. rewrite -> Hi in Ht. exact Ht.
    -- intro Hi. destruct Hi as [i [Hi Ht]]. rewrite -> one_of_le_succ.
      pose proof (proj1 (Nat.le_lteq i (succ m)) Hi) as Him.
      destruct Him.
      --- rewrite -> Nat.lt_succ_r in H. rewrite -> IHm. now simpl.
         exists i. split. exact H. exact Ht.
      --- rewrite -> H in Ht. rewrite -> Ht. 
          unfold SBor. destruct (one_of_le seq m); reflexivity.
Qed.

Fixpoint disj_seq (ss : N -> (N -> SB)) (n : N) : SB := 
  match n with
  | 0 => one_of_le (fun k => ss k 0) 0
  | succ m => 
      match disj_seq ss m with 
      | tru => tru 
      | indt => one_of_le (fun k => ss k n) n
      end
  end
.

Lemma disj_seq_succ : forall ss m,
  disj_seq ss (succ m) = 
    match disj_seq ss m with | tru => tru | indt => one_of_le (fun k => ss k (succ m)) (succ m) end.
Proof. intros; auto.  Qed.

Lemma one_of_le_implies_disj : forall ss n, 
  one_of_le (fun k => ss k n) n = tru -> disj_seq ss n = tru.
Proof. 
  intro ss. destruct n. 
  - intro H. unfold one_of_le in H. unfold disj_seq. simpl. exact H.
  - intro H.
    rewrite -> disj_seq_succ.  
    remember (disj_seq ss n) as djsn.
    destruct djsn. reflexivity. exact H.
Qed.

Lemma disj_implies_one_of_le : forall ss n, 
  (forall n, next_after (ss n)) -> disj_seq ss n = tru -> one_of_le (fun k => ss k n) n = tru.
Proof. 
  intros ss m Hna. revert m. induction m.
  - intro H. unfold one_of_le in H. unfold disj_seq. simpl. exact H.
  - intro H. rewrite -> disj_seq_succ in H.  
    remember (disj_seq ss m) as djsn.
    destruct djsn. 
    -- pose proof (IHm (eq_refl tru)) as IH. clear IHm H.
       apply one_of_le_iff_exists in IH.
       apply one_of_le_iff_exists.
       destruct IH as [i [Hilem Hssim]].    
       exists i. split. apply Nat.le_le_succ_r. exact Hilem. apply (Hna i). exact Hssim.
    -- exact H.
Qed. 

Lemma next_after_disj : forall seqs : N -> (N -> SB), 
  (forall n, next_after (seqs n)) -> next_after (disj_seq seqs).
Proof.
  intros ses H.
  unfold next_after in *.
  intros n Hd.
  rewrite -> disj_seq_succ.
  now rewrite -> Hd.
Qed.

Definition disj (ss : N -> S) : S :=
  mkSierpinskian (disj_seq ss) (next_after_disj ss (fun n => proper (ss n))).


Lemma disj_correct : forall ss : N -> S,
  eqv (disj ss) true <-> exists n, eqv (ss n) true.
  intros ss.
  split.
  - intro H. 
    unfold eqv in H.
    destruct H as [i Hi].
    pose proof (Hi i (Nat.le_refl i)) as Hit.
    pose proof (fun n => proper (ss n)) as Hna.
    pose proof (disj_implies_one_of_le ss i Hna Hit) as H.
    apply one_of_le_iff_exists in H.
    destruct H as [k [Hklei Hsski]].
    exists k.
    unfold eqv.
    exists i.
    pose proof (proper (ss k)) as Hnak.
    apply next_implies_all_after in Hnak.
    apply Hnak.
    exact Hsski.
  - intros [k Hk].
    unfold eqv in Hk.
    destruct Hk as [i Hki].
    set (j := max k i).
    pose proof (Hki j (Nat.le_max_r k i)) as Hkij.
    pose proof (fun n => proper (ss n)) as Hm.
    pose proof (next_after_disj ss Hm) as Hd.
    unfold eqv.
    exists j.
    apply next_implies_all_after in Hd.
    simpl.
    intros l Hjlel.
    unfold all_after in Hd.
    specialize Hd with j l.
    apply Hd.
    apply one_of_le_implies_disj.
    apply one_of_le_iff_exists.
    exists k. split. exact (Nat.le_max_l k i). now rewrite -> Hkij. exact Hjlel.
Qed.


Lemma disj_respectful : LPO -> forall (ss ss' : N -> S), 
  (forall n, ss n == ss' n) -> (disj ss) == (disj ss').
Proof.
  intros lpo.
  assert (forall s, ~ (s == true) <-> s == indeterminate) as HNT. {
    intros s. split.
    - intro HNT. destruct (true_or_indeterminate lpo s). contradiction. assumption.
    - intros HI HT. exact (not_true_and_indeterminate s HT HI). }
  assert (forall ss ss', (forall n, ss n == ss' n) -> disj ss == true -> disj ss' == true) as HT. {
    intros ss ss' HE H. apply disj_correct in H as [n Hn]. apply disj_correct; exists n.
    apply (eqv_trans _ (ss n) _). apply eqv_sym; exact (HE n). exact Hn. }
  intros ss ss' He.
  destruct (true_or_indeterminate lpo (disj ss)).
  - apply (eqv_trans _ true _). exact H. apply eqv_sym; exact (HT ss ss' He H).
  - apply (eqv_trans _ indeterminate _). assumption. apply eqv_sym.
    apply HNT in H; apply HNT. intro H'. apply H. 
    refine (HT ss' ss _ H'); intro n; exact (eqv_sym _ _ (He n)).
Qed.
