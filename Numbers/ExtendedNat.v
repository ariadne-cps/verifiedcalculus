(******************************************************************************
 *  Numbers/ExtendedNat.v
 *
 *  Copyright 2023-26 Pieter Collins
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



(*
 * Natural numbers with a point at infinity.
 * Implemented as a sequence of booleans consisting of n trues followed by all false.
 *)



From Stdlib Require Import Logic.ProofIrrelevance.

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Notation zero := PeanoNat.Nat.zero.
Notation succ := PeanoNat.Nat.succ.
Notation B := bool.
Notation N := nat.


Definition Cantor := N -> B.
Definition Baire := N -> N.


Module Nat.
Lemma le_succ_le_l : forall n m : N, S n <= m -> n <= m.
Proof. intros m n H. apply Nat.lt_le_incl. apply Nat.le_succ_l. exact H. Qed.
Lemma ltb_lt : forall n m : N, (n <? m) = true <-> n < m.
Proof. 
  intros n m. split.
  - intro Hnbltm. apply Nat.leb_le in Hnbltm. now apply Nat.le_succ_l.
  - intro Hnltm. apply Nat.leb_le. now apply Nat.le_succ_l.
Qed.
Lemma nltb_ge : forall n m : N, (n <? m) = false <-> m <= n.
Proof. intros n m; split; intro H; now apply Nat.ltb_ge. Qed.
End Nat.

(* Extended induction principle for propositions true from p n. *)
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


Definition next_after (s : N -> B) : Prop := 
  forall n, s n = false -> s (succ n) = false.

Definition all_after (s : N -> B) : Prop := 
  forall n, s n = false-> forall m, n <= m -> s m = false.

Definition next_before (s : N -> B) : Prop := 
  forall n, s (succ n) = true -> s n = true.

Definition all_before (s : N -> B) : Prop := 
  forall n, s n = true -> forall m, m <= n -> s m = true.

Lemma next_after_iff_all_after : forall s : N -> B, 
  next_after s <-> all_after s.
Proof.
  unfold next_after, all_after. intros s. split.
  - intros Hs i Hi. apply all_ge. exact Hi. exact Hs.
  - intros Hs i Hi. apply (Hs i Hi). exact (Nat.le_succ_diag_r i).
Qed.

Lemma next_after_iff_next_before : forall s, next_after s <-> next_before s.
Proof.
  unfold next_before, next_after. intro s; split.
  - intros H n Ht. apply not_false_is_true. intro Hf. specialize (H n Hf) as HSf.
    now apply (eq_true_false_abs (s (succ n))).
  - intros H n Hf. apply not_true_is_false. intro HSt. specialize (H n HSt) as Ht.
    now apply (eq_true_false_abs (s n)).
Qed.

Lemma all_after_iff_all_before : forall s, all_after s <-> all_before s.
Proof.
  unfold all_before, all_after. intro s; split.
  - intros H n Hsnt m Hmlen. apply not_false_is_true. intro Hsmf. 
    specialize (H m Hsmf n Hmlen) as Hsnf.
    now apply (eq_true_false_abs (s n)).
  - intros H m Hsm n Hmlen. apply not_true_is_false. intro Hsnt.
    specialize (H n Hsnt m Hmlen) as Hsmt.
    now apply (eq_true_false_abs (s m)).
Qed.

Lemma next_after_iff_all_before : forall s : N -> B, 
  next_after s <-> all_before s.
Proof.
  intros s. split.
  - intro Hs. now apply all_after_iff_all_before, next_after_iff_all_after.
  - intro Hs. now apply next_after_iff_all_after, all_after_iff_all_before.
Qed.


Record ExtendedNat := mkExtendedNat {
  seq :> N -> B;
  proper : next_after seq
}.

Notation Ninf := ExtendedNat.

Axiom Ninf_extensionality : 
  forall u1 u2 : Ninf, (forall n, seq u1 n = seq u2 n) -> u1 = u2.

Lemma Ninf_eq : forall n1 n2 : ExtendedNat, n1 = n2 <-> seq n1 = seq n2.
Proof. 
  intros n1 n2. split. 
  - intro He. now rewrite -> He. 
  - destruct n1 as [n1 p1]. destruct n2 as [n2 p2]. simpl.
    intro Hse. revert p1 p2. rewrite -> Hse. intros p1 p2.
    f_equal. now apply proof_irrelevance.
Qed.

Definition Ninf_eqv (u1 u2 : ExtendedNat) : Prop := forall k, u1 k = u2 k.
Infix "==" := Ninf_eqv (at level 70, no associativity).

Lemma Ninf_eqv_eq : 
  forall (u1 u2 : Ninf), u1 == u2 -> u1 = u2.
Proof. 
  exact Ninf_extensionality.
Qed. 

Lemma Ninf_after : forall (u : Ninf) (m : N), u m = false -> forall n, m <= n -> u n = false.
Proof. intros u m. apply next_after_iff_all_after. exact (proper u). Qed.

Lemma Ninf_before : forall (u : Ninf) n, u n = true -> forall m, m <= n -> u m = true.
Proof. intros u n. apply next_after_iff_all_before. exact (proper u). Qed.


Definition false_from (n : N) (k : N) : B := k <? n.

Lemma false_from_lt_is_true : forall n k, k < n -> false_from n k = true.
Proof. intros n k Hkltn. unfold false_from. now apply Nat.ltb_lt. Qed.

Lemma false_from_ge_is_false : forall n k, n <= k -> false_from n k = false.
Proof. intros n k Hnlek. unfold false_from. now apply Nat.nltb_ge. Qed.

Lemma next_after_false_from (n : N) : next_after (fun k => k <? n).
Proof. intros k Hkltn. now apply Nat.nltb_ge, Nat.le_le_succ_r, Nat.nltb_ge. Qed.

Lemma next_after_eqv : forall s, next_after s ->
  forall n, (forall k, s k = false_from n k) <-> (forall k, k < n -> s k = true) /\ (forall k, n <= k -> s k = false).
Proof.
  unfold false_from. 
  intros s Hs n. split.
  - intro H. split. 
    -- intro k. rewrite -> H. exact (false_from_lt_is_true n k). 
    -- intro k. rewrite -> H. exact (false_from_ge_is_false n k).
  - intros [Ht Hf].
    intro k. apply eq_sym. simpl.
    destruct (Nat.lt_ge_cases k n) as [Hkltn|Hnlek]. 
    -- rewrite -> (Ht k Hkltn). now apply Nat.ltb_lt.
    -- rewrite -> (Hf k Hnlek). now apply Nat.nltb_ge.
Qed.


Definition all_true : N -> B := fun _ => true.

Lemma next_after_all_true : next_after (fun _ => true).
Proof. unfold next_after, all_true. intros n Hy. exact Hy. Qed.

Definition Ninf_finite (n : N) : ExtendedNat :=
  mkExtendedNat _ (next_after_false_from n).

Definition Ninf_infinite : ExtendedNat :=
  mkExtendedNat _ next_after_all_true.

Coercion Ninf_finite : N >-> ExtendedNat.
Notation fin := Ninf_finite.
Notation inf := Ninf_infinite.

Lemma Ninf_finite_lt : forall n k, k < n -> Ninf_finite n k = true.
Proof. intros n k Hkltn. unfold Ninf_finite. now apply Nat.ltb_lt. Qed.

Lemma Ninf_finite_ge : forall n k, n <= k -> Ninf_finite n k = false.
Proof. intros n k Hnlek. unfold Ninf_finite. now apply Nat.nltb_ge. Qed.

Lemma Ninf_finite_eq : forall u n, 
  u = Ninf_finite n <-> (forall k, k < n -> u k = true) /\ (forall k, n <= k -> u k = false).
Proof.
  intros u n. unfold Ninf_finite. split.
  - intro H. rewrite -> H. clear H.
    split. exact (Ninf_finite_lt n). exact (Ninf_finite_ge n).
  - intros [Hf Ht].
    apply Ninf_extensionality. intro k. apply eq_sym. simpl.
    destruct (Nat.lt_ge_cases k n) as [Hkltn|Hnlek]. 
    -- rewrite -> (Hf k Hkltn). now apply Nat.ltb_lt.
    -- rewrite -> (Ht k Hnlek). now apply Nat.nltb_ge.
Qed.

Lemma Ninf_finite_inj : forall m n, Ninf_finite m = Ninf_finite n -> m = n.
Proof.
  intros m n Hemn.
  assert (forall k, (Ninf_finite m k) = (Ninf_finite n k)) as Hk. intro k. rewrite -> Hemn. reflexivity.
  pose proof (Nat.lt_trichotomy m n) as Hmn. destruct Hmn. 2: destruct H.
  - specialize (Hk m). unfold Ninf_finite in Hk; simpl in Hk. 
    rewrite -> Nat.ltb_irrefl in Hk. rewrite -> (proj2 (Nat.ltb_lt m n) H) in Hk. discriminate Hk.
  - exact H.
  - specialize (Hk n). unfold Ninf_finite in Hk; simpl in Hk. 
    rewrite -> Nat.ltb_irrefl in Hk. rewrite -> (proj2 (Nat.ltb_lt n m) H) in Hk. discriminate Hk.
Qed.

Lemma Ninf_finite_eq_zero : forall (u : Ninf), 
  u 0 = false -> u = Ninf_finite 0.
Proof.
  intros u Hu0. apply Ninf_finite_eq. split.
  - intros k Hklt0. contradiction (Nat.nlt_0_r _ Hklt0).
  - exact (Ninf_after u 0 Hu0).
Qed.

Lemma Ninf_finite_eq_succ : forall (u : Ninf) (n : N), 
  u n = true -> u (S n) = false -> u = Ninf_finite (S n).
Proof.
  intros u n Hun HuSn. apply Ninf_finite_eq. split.
  - intros k HkltSn. apply (Nat.lt_succ_r k n) in HkltSn. 
    exact (Ninf_before u n Hun k HkltSn).
  - intros k HSnlek. exact (Ninf_after u (S n) HuSn k HSnlek).
Qed.



Lemma Ninf_eq_fin_dec : forall m : N, forall u : Ninf, { u = fin m } + { u <> fin m }. 
Proof.
  intros m u.
  remember (u m) as um; apply eq_sym in Hequm. destruct um.
  - right. intro Hum. rewrite -> Hum in Hequm. simpl in Hequm. rewrite -> Nat.ltb_irrefl in Hequm. discriminate.
  - destruct m. 
    -- left. apply Ninf_finite_eq. split. 
       intros k Hk. now apply Nat.nlt_0_r in Hk. 
       intro k. apply next_after_iff_all_after. exact (proper u). exact Hequm.
    -- rename Hequm into HequSm. remember (u m) as um; apply eq_sym in Hequm. destruct um.
       --- left. apply Ninf_finite_eq. split. 
           intros k Hk. apply (Nat.lt_succ_r k m) in Hk. revert Hk. 
           apply all_after_iff_all_before. apply next_after_iff_all_after. exact (proper u). exact Hequm.
           apply next_after_iff_all_after. exact (proper u). exact HequSm.
       --- right. intros Hu. rewrite -> Hu in Hequm. simpl in Hequm. apply Nat.nltb_ge in Hequm. 
           apply (proj1 (Nat.le_succ_l m m)) in Hequm. now apply Nat.lt_irrefl in Hequm. 
Qed.


Lemma Ninf_finite_not_inf : forall n : N, fin n <> inf.
Proof. intros n Hnt. assert (Ninf_finite n n <> Ninf_infinite n) as Hntn. 
  intros Hf. unfold Ninf_finite, Ninf_infinite in Hf. simpl in Hf. 
  rewrite -> Nat.ltb_irrefl in Hf. discriminate Hf. rewrite -> Hnt in Hntn. contradiction.
Qed.





Definition prepend_true : (N -> B) -> (N -> B) := fun s n => match n with | O => true | S m => s m end. 
Lemma prepend_true_proper : forall s, next_after s -> next_after (fun n => match n with | O => true | S m => s m end).  
Proof. unfold next_after. intros s Hs n. destruct n as [|m].
  - intro Hsi0. discriminate Hsi0.
  - intro HsiSm. now apply Hs.
Qed.
Definition Ninf_succ : Ninf -> Ninf := 
  fun u => mkExtendedNat _ (prepend_true_proper _ (proper u)).

Lemma Ninf_succ_all_true : Ninf_succ Ninf_infinite = Ninf_infinite.
Proof. unfold Ninf_succ, Ninf_infinite.
  apply Ninf_extensionality; simpl. intro m. destruct m; reflexivity.
Qed.
Lemma Ninf_succ_fin : forall n : N, Ninf_succ (Ninf_finite n) = Ninf_finite (succ n).
Proof. intro n. unfold Ninf_succ, Ninf_finite.
  apply Ninf_extensionality; simpl. intro m. destruct m; intuition. Qed.
Lemma Ninf_succ_inj : forall x y, Ninf_succ x = Ninf_succ y -> x = y.
Proof. 
  intros x y HSxy. apply Ninf_extensionality; simpl. intro n.
  assert (Ninf_succ x (S n) = Ninf_succ y (S n)) as HSxyn by now rewrite -> HSxy. 
  unfold Ninf_succ in HSxyn; simpl in HSxyn. exact HSxyn.
Qed.
Lemma Ninf_succ_true : forall x, x = Ninf_infinite <-> Ninf_succ x = Ninf_infinite.
Proof.
  intro x. split.
  - intro Hx. rewrite -> Hx. exact Ninf_succ_all_true.
  - intro HSx. apply Ninf_succ_inj. rewrite -> Ninf_succ_all_true. exact HSx.
Qed.



Definition Ninf_le (u v : Ninf) : Prop := forall n, u n = true -> v n = true.

Lemma Ninf_le_spec_false : forall (u v : Ninf),
  Ninf_le u v <-> forall n, v n = false -> u n = false.
Proof.
  intros u v; unfold Ninf_le; split. 
  - intros H n Hvn. 
    apply not_true_iff_false; intro Hun.
    exact (eq_true_false_abs _ (H n Hun) Hvn). 
  - intros H n Hun. 
    apply not_false_iff_true; intro Hvn.
    exact (eq_true_false_abs _ Hun (H n Hvn)). 
Qed.     

Lemma Ninf_le_refl : forall u, Ninf_le u u.
Proof. unfold Ninf_le. intros us n Hn. exact Hn. Qed.

Lemma Ninf_le_trans : forall u v w, Ninf_le u v -> Ninf_le v w -> Ninf_le u w.
Proof. 
  unfold Ninf_le. intros u v w Huv Hvw.
  intros n Hun. apply Hvw. apply Huv. exact Hun.
Qed.

Lemma Ninf_le_nat : forall m n, Ninf_le (fin m) (fin n) <-> m <= n.
Proof. 
  intros m n; split.
  - unfold Ninf_le, fin; simpl.
    intro Himn. specialize (Himn n).
    apply Nat.nlt_ge; intro Hnltm. apply Nat.ltb_lt in Hnltm. specialize (Himn Hnltm).
    rewrite -> (Nat.ltb_irrefl n) in Himn. discriminate Himn.
  - intros Hmlen. unfold Ninf_le, fin; simpl.
    intros k Hkltm. apply Nat.ltb_lt. apply Nat.ltb_lt in Hkltm. 
    now apply (Nat.lt_le_trans k m n).
Qed.

Lemma Ninf_not_le_inf_finite : forall m, ~ (Ninf_le inf (fin m)).
Proof. unfold Ninf_le, inf, fin. intros n Hn.
  specialize (Hn n). simpl in Hn. 
  rewrite -> Nat.ltb_irrefl in Hn. now apply diff_false_true, Hn.
Qed.

Lemma Ninf_le_0_l : forall (u : Ninf), Ninf_le (fin 0) u.
Proof. 
  unfold fin, Ninf_le; simpl. intros u n H. rewrite -> Nat.ltb_lt in H. contradiction (Nat.nlt_0_r n H). Qed.

Lemma Ninf_le_inf : forall u, Ninf_le u inf.
Proof. unfold Ninf_le, inf, Ninf_infinite. intros _ n _. reflexivity. Qed.

Lemma Ninf_le_fin_r : forall (u : Ninf) (m : N), u m = false <-> Ninf_le u (fin m).
Proof. intros u m; unfold fin, Ninf_le; simpl; split.
  - intros Hum n Hun. apply Nat.ltb_lt. apply Nat.lt_nge; intro Hmlen. 
    pose proof (Ninf_after u m Hum n Hmlen) as Hu. now apply (eq_true_false_abs (seq u n)).
  - intros H. apply not_true_iff_false; intro Hum. specialize (H m Hum). rewrite -> Nat.ltb_irrefl in H. discriminate. 
Qed.

Lemma Ninf_gt_fin_l : forall (u : Ninf) (m : N), u m = true <-> Ninf_le (fin (S m)) u.
Proof. intros u m; unfold fin, Ninf_le; simpl; split.
  - intros Hum n Hnlem. apply Nat.ltb_lt, (Nat.lt_succ_r n m) in Hnlem.
    exact (Ninf_before u m Hum n Hnlem).
  - intros H. apply (H m). apply Nat.ltb_lt, (Nat.lt_succ_r m m). now apply Nat.le_refl.
Qed.

Lemma Ninf_ge_fin_l : forall (u : Ninf) (m : N), u m = true -> Ninf_le (fin m) u.
Proof. 
  intros u m Hum. apply Ninf_gt_fin_l in Hum.
  apply (Ninf_le_trans _ (fin (S m)) _).
  - apply Ninf_le_nat. now apply Nat.le_succ_diag_r.
  - exact Hum.
Qed.


(* Lemma 3.2 *)
Lemma Ninf_false_implies_is_finite : forall u : Ninf,
  (exists n, seq u n = false) -> (exists m, u = Ninf_finite m).
Proof.
  intros [s Hs] [n Hn].
  pose proof (proj1 (next_after_iff_all_after s) Hs) as Has.
  unfold all_after in Has.
  revert Hn.
  induction n.
  - intro Hs0. exists 0. apply Ninf_extensionality; simpl.
    intro n. exact (Has 0 Hs0 n (Nat.le_0_l n)).
  - remember (s n) as sn eqn:Hsn.
    destruct sn.
    -- clear IHn. intro HsSn. exists (S n).
       apply Ninf_extensionality; simpl.
       intro m.
       simpl. 
       remember (m <? S n) as mltSn.
       apply eq_sym in HeqmltSn.
       destruct  mltSn.
       --- assert (m <= n) as Hmlen. { 
             apply Nat.lt_succ_r. now apply Nat.ltb_lt. }
           apply not_false_iff_true. intro Hsm.
           specialize (Has m Hsm n Hmlen).
           exact (eq_true_false_abs _ (eq_sym Hsn) Has).
       --- apply (Has (S n) HsSn m). now apply Nat.nltb_ge.
    -- intro Hsm. now apply IHn.
Qed.

(* Lemma 3.3 *)
Lemma Ninf_not_finite_implies_infinite : forall u : Ninf,
  (forall n, u <> Ninf_finite n) -> u = Ninf_infinite.
Proof.
  intros u Hu.
  apply Ninf_extensionality.
  intro n; simpl.
  apply not_false_iff_true; intro Hsn.
  assert (exists n, u n = false) as Hexsn. { exists n; exact Hsn. }
    pose proof (Ninf_false_implies_is_finite u Hexsn) as [m Htfm].
    exact (Hu m Htfm).
Qed.

Corollary not_infinite_implies_classically_finite : forall u : Ninf,
  (u <> inf) -> ~ (forall n, u <> fin n).
Proof.
  intros u Huinf Huan. apply Huinf. now apply (Ninf_not_finite_implies_infinite u).
Qed.

Lemma Ninf_succ_fix : forall x, Ninf_succ x = x <-> x = Ninf_infinite.
Proof. 
  intro x. split. 
  - intros Hfx. assert ( (forall k, x <> Ninf_finite k)) as Hnk. {
      intros k Hk. rewrite -> Hk in Hfx. rewrite -> Ninf_succ_fin in Hfx. 
      apply Ninf_finite_inj in Hfx.
      now apply Nat.neq_succ_diag_l in Hfx. }
    exact (Ninf_not_finite_implies_infinite _ Hnk).
  - intro Hx. rewrite -> Hx. exact Ninf_succ_all_true.
Qed.

Lemma Ninf_le_finite_ex : forall u n, Ninf_le u (fin n) -> exists m, u = fin m.
Proof. 
  intros u n Hulen.
  assert (exists n, seq u n = false) as Hu. {
    exists n.
    apply not_true_iff_false; intro Hun.
    unfold Ninf_le, fin in Hulen. specialize (Hulen n Hun). simpl in Hulen.
    now rewrite -> Nat.ltb_irrefl in Hulen.
  }
  pose proof (Ninf_false_implies_is_finite u Hu) as H.
  destruct H as [m Hm]. exists m. exact Hm.
Qed.

Lemma Ninf_le_succ_iff : forall u v, Ninf_le (Ninf_succ u) (Ninf_succ v) <-> Ninf_le u v.
Proof. intros u v. unfold Ninf_le, Ninf_succ. simpl. split.
  - intros H n. specialize (H (S n)); simpl in H. exact H.
  - destruct n. 1: tauto. exact (H n).
Qed.

Lemma Ninf_false_le : forall (u : Ninf) (m : N), u m = false -> Ninf_le u (fin m).
Proof. 
  intros u m Hum. unfold Ninf_le, fin; simpl.
  intros n Hun.
  rewrite -> Nat.ltb_lt.
  apply Nat.nle_gt; intros Hmlen. 
  pose proof ( proj1 (next_after_iff_all_after (seq u)) (proper u) m Hum n Hmlen) as Hu.
  exfalso; now apply (eq_true_false_abs (u n)).
Qed.


Lemma Ninf_le_succ_diag_r : forall u, Ninf_le u (Ninf_succ u).
Proof. intros u. unfold Ninf_le, Ninf_succ. intros n Hn.
  destruct n. reflexivity. simpl. exact (Ninf_before u (S n) Hn n (Nat.le_succ_diag_r n)).
Qed.

Lemma Ninf_le_succ_l_le : forall u v, Ninf_le (Ninf_succ u) v -> Ninf_le u v.
Proof. intros u v H. apply (Ninf_le_trans _ (Ninf_succ u) _). now apply Ninf_le_succ_diag_r. exact H. Qed.  

Lemma Ninf_succ_le_fin_l : forall (u : Ninf) (m : N), (Ninf_succ u) m = true <-> Ninf_le (fin m) u.
Proof. 
  intros u m. rewrite -> Ninf_gt_fin_l. rewrite <- Ninf_succ_fin. now apply (Ninf_le_succ_iff (fin m)).
Qed.

Lemma Ninf_nle_ge : forall (u v : Ninf), ~ (Ninf_le u v) -> Ninf_le v u.
Proof. 
  unfold Ninf_le. intros u v Hvltu.
  intros n Hvn. apply not_false_iff_true. intro Hun.
  apply Hvltu; clear Hvltu. intros m Hum.
  apply (Ninf_before v n). 1: exact Hvn. 
  apply Nat.le_ngt. intro Hnlem. apply Nat.lt_le_incl in Hnlem. 
  apply not_false_iff_true in Hum; apply Hum.
  now apply (Ninf_after u n).
Qed.

Lemma Ninf_not_le_iff_gt : forall u m, ~ (Ninf_le u (fin m)) <-> Ninf_le (Ninf_succ (fin m)) u.
Proof. intros u m; split.
  - intro Hnle. rewrite -> Ninf_succ_fin. apply Ninf_succ_le_fin_l. 
    simpl. apply not_false_iff_true. intro Hum. apply Hnle. apply Ninf_le_fin_r. exact Hum.
  - intros HSmleu Hulem. apply Ninf_le_fin_r in Hulem. rewrite -> Ninf_succ_fin in HSmleu. 
    apply Ninf_succ_le_fin_l in HSmleu. simpl in HSmleu. exact (eq_true_false_abs _ HSmleu Hulem).
Qed.
 
Lemma Ninf_le_fin_dec : forall u m, { Ninf_le u (fin m) } + { ~ (Ninf_le u (fin m)) }.
Proof. 
  intros u m. remember (u m) as um; apply eq_sym in Hequm. destruct um.
  - right. intros Hum. apply Ninf_le_fin_r in Hum. now apply (eq_true_false_abs (seq u m)).
  - left. now apply Ninf_le_fin_r.
Qed.

Lemma Ninf_ge_fin_dec : forall m u, { Ninf_le (fin m) u} + { ~ (Ninf_le (fin m) u) }.
Proof. 
  intros m u. destruct m.
  - left. now apply Ninf_le_0_l.
  - remember (u m) as um; apply eq_sym in Hequm. destruct um.
    -- left. now apply Ninf_gt_fin_l.
    -- right. intros Hmu. apply Ninf_gt_fin_l in Hmu. now apply (eq_true_false_abs (seq u m)).
Qed.

Lemma Ninf_le_fin_cases : forall u m, { Ninf_le u (fin m) } + { Ninf_le (fin m) u }.
Proof. intros u m. destruct (Ninf_le_fin_dec u m) as [Hulem|Hugtm].
  - left. exact Hulem.
  - right. unfold Ninf_le. intros n Hmn.
    apply not_false_iff_true. intro Hun. apply Hugtm.
    destruct (Nat.le_gt_cases m n).
    -- unfold fin in Hmn; simpl in Hmn. apply Nat.ltb_lt in Hmn. contradiction (proj1 (Nat.le_ngt m n) H Hmn).
    -- apply Ninf_false_le. 
       apply (Ninf_after u n Hun m). now apply Nat.lt_le_incl.
Qed.


Lemma max_seq_proper : forall (u v : Ninf), next_after (fun n => orb (u n) (v n)). 
Proof. 
  intros [u Hu] [v Hv]. unfold next_after in *. 
  intro n. simpl. specialize (Hu n); specialize (Hv n). intro Huv.
  apply orb_false_iff in Huv.
  now rewrite -> (Hu (proj1 Huv)), -> (Hv (proj2 Huv)). 
Qed.

Definition Ninf_max (u v : Ninf) : Ninf := mkExtendedNat _ (max_seq_proper u v).

Lemma Ninf_max_of_le : forall m n, m <= n -> Ninf_max (fin m) (fin n) = (fin n).
Proof.
  intros m n Hmlen.
  unfold Ninf_max. apply Ninf_extensionality; simpl.
  intro k.
  remember (k <? n) as kltbn eqn:Hkltbn. apply eq_sym in Hkltbn. destruct kltbn.
  - now apply orb_true_r.
  - rewrite -> Nat.nltb_ge in Hkltbn. 
    assert (m <= k) as Hmlek by apply (Nat.le_trans _ _ _ Hmlen Hkltbn). 
    rewrite -> (proj2 (Nat.nltb_ge k m) Hmlek). reflexivity.
Qed.

Lemma Ninf_max_symm : forall u v : Ninf, Ninf_max u v = Ninf_max v u.
Proof. 
  intros u v. unfold Ninf_max.
  apply Ninf_extensionality; simpl. intro n.
  destruct (seq  u n); destruct (seq v n); reflexivity.
Qed.

Lemma Ninf_max_of_nat : forall m n, Ninf_max (fin m) (fin n) = fin (Nat.max m n).
Proof.
  intros m n. pose proof (Nat.le_ge_cases m n) as H. destruct H.
  - now rewrite -> (Ninf_max_of_le _ _ H), -> (Nat.max_r _ _ H).
  - rewrite -> Ninf_max_symm. now rewrite -> (Ninf_max_of_le _ _ H), -> (Nat.max_l _ _ H).
Qed.

Lemma Ninf_le_max : forall u v, Ninf_le u v <-> Ninf_max u v = v.
Proof. 
  intros u v. split.
  - unfold Ninf_le, Ninf_max. 
    intros Hle. apply Ninf_extensionality; simpl.
    intro n.
    remember (u n) as un; apply eq_sym in Hequn. destruct un.
    -- specialize (Hle n Hequn). rewrite -> Hle. reflexivity.
    -- simpl. reflexivity.     
  - intros Hmax. rewrite <- Hmax.
    unfold Ninf_max, Ninf_le; simpl.
    intros n Hun. rewrite -> Hun. reflexivity. 
Qed.



Declare Scope Ninf_scope.

Notation max := Ninf_max.
Notation le := Ninf_le.
Infix "<=" := Ninf_le.


Lemma Ninf_le_max_r : forall u v, v <= max u v.
Proof. unfold le, max. intros u v n Hvn.
  simpl. rewrite -> Hvn. destruct (u n); reflexivity.
Qed.

Lemma Ninf_max_r : forall u v, u <= v <-> max u v = v.
Proof. 
  unfold max, le. intros u v; split.
  - intro Hl. apply Ninf_extensionality; simpl. 
    intro n; specialize (Hl n). destruct (u n); simpl.
    apply eq_sym; now apply Hl. reflexivity.
  - intro Hm. rewrite <- Hm; simpl. 
    intros n Hun. rewrite -> Hun. reflexivity.
Qed.

Lemma Ninf_le_max_l : forall u v, u <= max u v.
Proof. unfold le, max. intros u v n Hvn.
  simpl. rewrite -> Hvn. destruct (u n); reflexivity.
Qed.

Lemma Ninf_max_l : forall u v, v <= u <-> max u v = u.
Proof. 
  intros u v. rewrite -> Ninf_max_symm. exact (Ninf_max_r v u). 
Qed.

Lemma Ninf_max_inf_r : forall u, max u inf = inf.
Proof. intro u. apply (proj1 (Ninf_max_r u inf)). now apply Ninf_le_inf. Qed.

Lemma Ninf_max_impl_ge : forall (P : Ninf -> Prop) (u : Ninf),
  (forall v, P (Ninf_max u v)) -> (forall v : Ninf, Ninf_le u v -> P v).
Proof. 
  intros P u.
  intro Hm. intros v Hulev. specialize (Hm v).
  now replace (Ninf_max u v) with v in Hm by exact (eq_sym (proj1 (Ninf_max_r u v) Hulev)). 
Qed.


















Open Scope nat_scope.

Fixpoint conj_seq (s : N -> B) (n : N) : B :=
  match n with 
  | O => s O
  | S m => andb (conj_seq s m) (s (S m)) 
  end.

Lemma conj_seq_zero : forall s, 
  conj_seq s zero = s zero.
Proof. intros s. unfold conj_seq. reflexivity. Qed.

Lemma conj_seq_succ : forall s n, 
  conj_seq s (succ n) = andb (conj_seq s n) (s (succ n)).
Proof. intros s n. unfold conj_seq. reflexivity. Qed.

Lemma conj_seq_next_after : forall s n, 
  conj_seq s n = false -> conj_seq s (succ n) = false.
Proof. intros s n Hrsn. rewrite -> conj_seq_succ. rewrite -> Hrsn. simpl. reflexivity. Qed.

Lemma conj_seq_all_after : forall s n, 
  conj_seq s n = false -> forall m, n <= m -> conj_seq s m = false.
Proof. intros s n Hsn. apply all_ge. exact Hsn. now apply conj_seq_next_after. Qed.

Lemma conj_seq_next_before : forall s n, 
  conj_seq s (succ n) = true -> conj_seq s n = true.
Proof. intros s n Hrsn. rewrite -> conj_seq_succ, andb_true_iff in Hrsn. exact (proj1 Hrsn). Qed.

Lemma conj_seq_all_before : forall s n, 
  conj_seq s n = true -> forall m, m <= n -> conj_seq s m = true.
Proof. intros s n Hsn. intros m Hmlen. apply not_false_is_true. intro Hrsm.
  pose proof (conj_seq_all_after s m Hrsm n Hmlen) as Hrsn. exact (eq_true_false_abs _ Hsn Hrsn). Qed.

Lemma conj_seq_at_false : forall s n, 
  s n = false -> conj_seq s n = false.
Proof. intros s n Hsn. destruct n. rewrite -> conj_seq_zero. exact Hsn.
  rewrite -> conj_seq_succ. apply andb_false_iff. right. exact Hsn. Qed.

Lemma conj_seq_at_true : forall s n, 
  conj_seq s n = true -> s n = true.
Proof. intros s n Hrsn. apply not_false_iff_true. intros Hsn. 
  exact (eq_true_false_abs _ Hrsn (conj_seq_at_false s n Hsn)). Qed.

Lemma conj_seq_is_false : forall s n, 
  conj_seq s n = false <-> exists k, k <= n /\ s k = false.
Proof. intros s n. split. 
  - induction n. 
    -- simpl. intro H0. exists 0. split. exact (Nat.le_0_l 0). exact H0.
    -- intro HrsSn. rewrite -> conj_seq_succ in HrsSn. apply andb_false_iff in HrsSn. destruct HrsSn as [Hrsn|HsSn].
       apply IHn in Hrsn. destruct Hrsn as [k [Hklen Hsk]]. exists k. split. 
       apply Nat.le_le_succ_r. exact Hklen. exact Hsk.
       exists (S n). split. exact (Nat.le_refl (S n)). exact HsSn.
  - intros [k [Hklen Hsk]].
    apply (conj_seq_all_after s k).
    now apply conj_seq_at_false.
    exact Hklen.
Qed.

Lemma conj_seq_is_true : forall s n, 
  conj_seq s n = true <-> forall k, k <= n -> s k = true.
Proof. intros s n. split.
  - intros Hrsn k Hklen. apply not_false_iff_true. intro Hsk.
    pose proof (conj_seq_at_false s k Hsk) as Hrsk.
    exact (eq_true_false_abs _ Hrsn (conj_seq_all_after s k Hrsk n Hklen)).
  - intros Hs. apply not_false_iff_true. intros Hrsn.
    apply conj_seq_is_false in Hrsn.
    destruct Hrsn as [k [Hklen Hsk]].
    specialize (Hs k Hklen).
    exact (eq_true_false_abs _ Hs Hsk).
Qed.

Lemma conj_seq_eqv_false_from : forall (s : N -> B) (n : N), 
  (forall k, conj_seq s k = false_from n k) <-> s n = false /\ forall k, k < n -> s k = true.
Proof.
  intros s n. split.
  - intro H.
    assert (forall k, k < n -> s k = true) as Ht. {
      intros k Hkltn. apply not_false_iff_true; intro Hsk.
      pose proof (false_from_lt_is_true n k Hkltn) as Htfnk.
      pose proof (conj_seq_at_false s k Hsk) as Hfdsk.
      rewrite -> H in Hfdsk; contradiction (eq_true_false_abs (false_from n k)). 
    }
    split.
    -- assert (conj_seq s n = false) as Hrsn by now rewrite -> H, -> (false_from_ge_is_false _ _ (Nat.le_refl n)).
       pose proof (proj1 (conj_seq_is_false s n) Hrsn) as [k [Hklen Hsk]].
       destruct (proj1 (Nat.lt_eq_cases k n) Hklen) as [Hkltn|Hkeqn].
       --- specialize (Ht k Hkltn). contradiction (eq_true_false_abs _ Ht Hsk).
       --- rewrite -> Hkeqn in Hsk. exact Hsk.
    -- exact Ht.
  - intros [Hsn Hsk] k.
    unfold Ninf_finite; simpl.
    unfold false_from.
    destruct (Nat.lt_ge_cases k n) as [Hkltn|Hnlek].
    -- rewrite -> (proj2 (Nat.ltb_lt k n) Hkltn).
       apply conj_seq_is_true.
       intros j Hjlek.
       assert (j < n) as Hjltn by exact (Nat.le_lt_trans _ k _ Hjlek Hkltn).
       exact (Hsk j Hjltn).
    -- rewrite -> (proj2 (Nat.nltb_ge k n) Hnlek).
       assert (conj_seq s n = false) as Hrsn by now apply conj_seq_at_false.
       exact (conj_seq_all_after s n Hrsn k Hnlek).
Qed.

Lemma conj_seq_eqv_all_true : forall (s : N -> B), 
  (forall k, conj_seq s k = Ninf_infinite k) <-> (forall n, s n = true).
Proof.
  intros s. split. 
  - intros Hrs n. apply conj_seq_at_true. now rewrite -> Hrs.  
  - intros Hs. induction k. 
    -- rewrite -> conj_seq_zero. exact (Hs zero).
    -- rewrite -> conj_seq_succ. apply andb_true_iff. split. now rewrite -> IHk. now apply Hs. 
Qed.

(* Lemma 3.1 *)
Lemma conj_seq_eqv_fixed_iff : forall s : N -> B, 
  next_after s <-> (forall k, conj_seq s k = s k).
Proof.
  unfold next_after.
  intro s.
  split. 
  - intros Hs.
    induction k.
    -- reflexivity.
    -- remember (s k) as sk eqn:Hsk.
       destruct (sk).
       --- rewrite -> conj_seq_succ. rewrite -> IHk. simpl. reflexivity.
       --- rewrite -> Hs by exact (eq_sym Hsk). exact (conj_seq_next_after s k IHk). 
  - intros Hfix k Hsk.
    rewrite <- Hfix.
    apply conj_seq_next_after.
    rewrite -> Hfix.
    exact Hsk.
Qed.

Close Scope nat_scope.

Definition Ninf_retr (s : Cantor) : ExtendedNat :=
  mkExtendedNat _ (conj_seq_next_after s).

Lemma Ninf_retr_is_false : forall (s : N -> B) (n : N), 
  Ninf_retr s n = false <-> (exists k : N, (k <= n)%nat /\ s k = false).
Proof. exact conj_seq_is_false. Qed.

Lemma Ninf_retr_eq_fin : forall (s : N -> B) (n : N), 
  (Ninf_retr s = fin n) <-> (s n = false /\ forall (k : N), (k < n)%nat -> s k = true).
Proof.
  intro s. split. 
  - intro H. apply conj_seq_eqv_false_from. apply Ninf_eq in H. simpl in H. now rewrite -> H.
  - intro H. apply Ninf_extensionality. apply conj_seq_eqv_false_from. exact H.
Qed.

Lemma Ninf_retr_eq_inf : forall (s : N -> B), 
  (Ninf_retr s = inf) <-> (forall n, s n = true).
Proof.
  intro s. split.
  - intro H. apply conj_seq_eqv_all_true. now rewrite <- H.  
  - intro H. apply Ninf_extensionality. apply conj_seq_eqv_all_true. exact H.
Qed.

Lemma Ninf_retr_is_fixed_iff : forall s : N -> B, (forall k, seq (Ninf_retr s) k = s k) <-> next_after s.
Proof. intro s. unfold Ninf_retr; simpl. apply iff_sym. exact (conj_seq_eqv_fixed_iff s). Qed.

Lemma Ninf_retr_is_retract : forall x : ExtendedNat, Ninf_retr x = x.
Proof. intros [s Hs]. apply Ninf_extensionality. rewrite -> Ninf_retr_is_fixed_iff. exact Hs. Qed.
