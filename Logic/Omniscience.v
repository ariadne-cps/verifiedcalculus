(******************************************************************************
 *  Logic/Omniscience.v
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
 * Formulation of omniscience principles, and proof of omnicience of N_inf.
 *
 * Based on
 *   "Infinite sets that satisfy the principle of omniscience in any variety of constructive mathematics"
 *   Martín H. Escardó, J. Symbolic Logic 78 (2013)
 * and implementation of Chuangjie Xu
 *)


From Stdlib Require Import Logic.ProofIrrelevance.

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.


 
Require Import Numbers.ExtendedNat.

Axiom sequence_extensionality : forall s1 s2 : N -> B, (forall n, s1 n = s2 n) -> s1 = s2.

Definition Cantor := N -> B.
Definition Baire := N -> N.

(* The Limited Principle of Omniscence for propositions *)
Definition LPOProp (X : Type) := forall p : X -> Prop, (forall x : X, (p x) \/ (~ p x)) ->
   ( exists x : X, ~ p x ) \/ ( forall x : X, p x ).

(* The Limited Principle of Omniscence for set *)
Definition LPOSet (X : Type) := forall p : X -> Prop, (forall x : X, {p x} + {~ p x}) ->
  { x : X | ~ p x } + { forall x : X, p x }.

(* The Limited Principle of Omniscence for bool *)
Definition LPOBool (X : Type) := forall p : X -> B,
  { x : X | p x = false } + { forall x : X, p x = true }.


Definition WLPOProp (X : Type) : Prop := forall p : X -> Prop, (forall x : X, (p x) \/ (~ p x)) ->
  (forall x, p x) \/ ~ (forall x, p x).

Definition WLPOSet (X : Type) := forall p : X -> Prop, (forall x : X, {p x} + {~ p x}) ->
  { forall x, p x } + { ~ forall x, p x }.

Definition WLPOBool (X : Type) := forall p : X -> B,
  { forall x : X, p x = true } + { ~ forall x, p x = true }.


Definition boolean_proposition {p q : Prop} (H : {p} + {q}) : bool :=
  match H with | left _ => true | right _ => false end.

Definition negated_boolean_proposition {p q : Prop} (H : {p} + {q}) : bool :=
  match H with | left _ => false | right _ => true end.

Lemma sumbool_true {P Q : Prop} : forall (d : {P} + {Q}), (boolean_proposition d = true) -> P.
Proof. intros d Hd. destruct d. exact p. discriminate Hd. Qed. 
Lemma sumbool_false {P Q : Prop} : forall (d : {P} + {Q}), (boolean_proposition d = false) -> Q.
Proof. intros d Hd. destruct d. discriminate Hd. exact q. Qed. 

Lemma sumbool_is_true {P : Prop} : forall (d : {P} + {~P}), P -> (boolean_proposition d = true).
Proof. intros d p. destruct d. reflexivity. contradiction. Qed. 
Lemma sumbool_is_false {P : Prop} : forall (d : {P} + {~P}), (~P) -> (boolean_proposition d = false).
Proof. intros d np. destruct d. contradiction. reflexivity. Qed. 

Proposition lpo_set_implies_bool : forall (X : Set), LPOSet X -> LPOBool X.
Proof.
  unfold LPOSet, LPOBool. intros X HLPOX p.
  set (q := fun x => p x = true).
  assert ( forall x, {p x = true} + {~ (p x = true)} ) as Hq. {
    intro x. pose proof (sumbool_of_bool (p x)) as [Hqxt|Hqxf].
    left; exact Hqxt. right; now apply not_true_iff_false. }
  pose proof (HLPOX q Hq) as Hp; unfold q in Hp.
  destruct Hp as [Hpf|Hpt].
  - left. destruct Hpf as [x Hpxf]. exists x. now apply not_true_iff_false.
  - right. exact Hpt. 
Qed.

Proposition lpo_bool_implies_set : forall (X : Set), LPOBool X -> LPOSet X.
Proof.
  unfold LPOSet, LPOBool. intros X HLPOX p Hp.
  set (q := bool_choice Hp).
  destruct q as [q Hq].
  pose proof (HLPOX q) as [Hqf|Hqt].
  - left; destruct Hqf as [x Hx]; exists x. 
    destruct (Hq x) as [[Hqxt _]|[_ Hnpx]]. contradiction (eq_true_false_abs (q x)). exact (Hnpx). 
  - right. intro x. specialize (Hqt x). destruct (Hq x) as [[_ Hpx]|[Hqxf _]]. 
    exact Hpx. contradiction (eq_true_false_abs (q x)).
Qed.

Proposition lpo_set_iff_bool : forall (X : Set), 
  (LPOSet X -> LPOBool X) * (LPOBool X -> LPOSet X).
Proof.
  intro X. exact (lpo_set_implies_bool X, lpo_bool_implies_set X).
Qed.

Proposition lpo_implies_wlpo : forall (X : Set), (LPOSet X) -> (WLPOSet X).
Proof.
  unfold WLPOSet, LPOSet; intros X Hlpo.
  intros p Hp; specialize (Hlpo p Hp).
  destruct Hlpo as [Hef|Hat].
  - right. intro Hat; destruct Hef as [n Haf]; specialize (Hat n). contradiction.
  - left. exact Hat.
Qed.

Proposition nwlpo_implies_nlpo : forall (X : Set), (WLPOSet X -> False) -> (LPOSet X -> False).
Proof. intros X Hnwlpo Hlpo. apply Hnwlpo. exact (lpo_implies_wlpo X Hlpo). Qed.


Definition is_selection_function {X : Type} (eps : (X -> B) -> X) :=
  forall p : X -> B, ( p (eps p) = true -> forall x, p x = true ).

Definition is_searchable (X : Type) := 
  { eps : (X -> B) -> X | is_selection_function eps }.


Lemma searchable_implies_omnisicience (X : Type)
  : is_searchable X -> LPOSet X.
Proof.
  unfold is_selection_function, LPOSet.
  intros [eps Heps] p Hp.
  set (q := fun x : X => boolean_proposition (Hp x)).
  unfold boolean_proposition in q.
  remember (q (eps q)) as qepsq eqn:Hqepsq; apply eq_sym in Hqepsq.
  destruct qepsq.
  - right. intros u.
    exact (sumbool_true (Hp u) (Heps q Hqepsq u)).
  - left. exists (eps q).
    exact (sumbool_false (Hp (eps q)) Hqepsq).
Qed.


(* FIXME: Duplicate, remove *)
Lemma exists_iff_search {X : Type} (eps : (X -> B) -> X) (Heps : is_selection_function eps) : 
  forall (q : X -> B), (exists x, q x = false) <-> q (eps q) = false.
Proof.
  unfold is_selection_function in Heps.
  intro q.
  specialize (Heps q).
  split. 
  - intros [x Hqx]. 
    apply not_true_implies_false.
    intro Hf.
    specialize (Heps Hf x).
    exact (eq_true_false_abs (q x) Heps Hqx).
  - intros Hq. 
    exists (eps q). 
    exact Hq.
Qed.






Definition is_full {X : Type} (e : X -> Prop) := 
  forall x : X, ~ (forall y, (e y -> x <> y)).

(* Lemma 3.4 *)
Lemma is_full_extended_nat : 
  is_full ( fun (u : ExtendedNat) => (exists n, u = fin n) \/ u = inf ).
Proof.
  unfold is_full.
  intros x Hy.
  apply (Hy inf).
  - right.
    reflexivity.
  - apply not_finite_implies_inf.
    intros k Hk.
    apply (Hy x).
    -- left. exists k. exact Hk.
    -- reflexivity.
Qed.

#[local]
Lemma bool_eq_dne : forall (b1 b2 : B), ~ (b1 <> b2) -> b1 = b2.
Proof. 
  intros b1 b2. intro Hne. destruct b1, b2.
  1,4: reflexivity. 1,2: exfalso; apply Hne; intros Hf; discriminate Hf. 
Qed.

(* Lemma 3.5 *)
Lemma full_dense_constant {X : Type} : forall (e : X -> Prop), is_full e ->
  forall p : X -> B, forall b : B, (forall x, e x -> p x = b) -> (forall x, p x = b).
Proof.
  unfold is_full.
  intros e He p b Hp x.
  apply bool_eq_dne. intro Hpne.
  apply (He x). intros y Hy. intro Hxy. 
  rewrite <- Hxy in Hy. specialize (Hp x Hy). exact (Hpne Hp).
Qed.




Definition eps : (ExtendedNat->B) -> ExtendedNat :=
  fun p => Ninf_retr (fun (n : N) => p n).


(* Unused *)
#[local]
Lemma eps_at_false : forall (p : Ninf -> B) (n : N), 
  eps p n = false <-> exists k : N, k<=n /\ p (fin k) = false.
Proof.
  intros p n.
  remember (fun n => p (fin n)) as s.
  pose proof (Ninf_retr_is_false (fun n => p (fin n)) n) as Hs.
  unfold eps, Ninf_retr; simpl.
  split.
  - intro Hrs. pose proof (proj1 Hs Hrs) as [k [Hklen Hsk]].
    exists k. split. apply Ninf_le_nat; exact Hklen. exact Hsk.
  - intros [k [Hklen Hsk]]. apply Hs.
    exists k. split. apply Ninf_le_nat; exact Hklen. exact Hsk.
Qed.


Lemma eps_is_finite : forall (p : Ninf -> B) (n : N), 
  eps p = fin n <-> p (fin n) = false /\ (forall k, (k<n)%nat -> p (fin k) = true).
Proof. exact Ninf_retr_eq_fin. Qed.

Lemma eps_is_infinite : forall (p : Ninf -> B),
  eps p = inf <-> forall n, p (fin n) = true.
Proof. exact Ninf_retr_eq_inf. Qed.

Lemma p_eps_p_true : forall (p : Ninf -> B), 
  p (eps p) = true -> eps p = inf.
Proof.
  intros p Hp. 
  apply (not_finite_implies_inf (eps p)).
  intros n Hpn.
  rewrite -> Hpn in Hp.
  pose proof (proj1 (proj1 (eps_is_finite p n) Hpn)) as Hpf.
  now apply (eq_true_false_abs (p (fin n))).
Qed.

Lemma p_eps_p_false : forall (p : Ninf -> B), 
  p (eps p) = false -> exists u, p u = false.
Proof.
  intros p Hp. 
  exists (eps p).
  exact Hp.
Qed.

(* Theorem 3.6 *)
Theorem extended_nat_selection_function : is_selection_function eps.
Proof.
  intros p Hp.
  pose proof (p_eps_p_true p Hp) as Hepspinf.
  pose proof (eps_is_infinite p) as Hf.
  rewrite -> Hepspinf in Hp; rename Hp into Hpinf.
  pose proof (proj1 Hf Hepspinf) as Hpfin.
  set (e := fun u => (exists n, u = fin n) \/ (u = inf)).
  pose proof (is_full_extended_nat) as He.
  pose proof (@full_dense_constant ExtendedNat e He p true) as Hfull.
  apply Hfull.
  clear He Hfull.
  intros u Heu.
  destruct Heu as [[n Hun]|Huinf].
  - rewrite -> Hun. exact (Hpfin n).
  - rewrite -> Huinf. exact Hpinf.
Qed.


Theorem extended_nat_lpo_set : LPOSet ExtendedNat.
Proof. 
  apply searchable_implies_omnisicience.
  unfold is_searchable.
  exists eps.
  apply extended_nat_selection_function.
Qed.

Theorem extended_nat_lpo_bool : LPOBool ExtendedNat.
(* forall p : Ninf -> B,  {x : Ninf | p x = false} + {forall x : Ninf, p x = true} *)
Proof. 
  apply lpo_set_implies_bool. exact extended_nat_lpo_set.
Qed.


Lemma lpo_ninf_restr_nat : forall p : Ninf -> B, 
  {x : Ninf | x <> inf /\ p x = false} + {forall n : N, p (fin n) = true}.
Proof.
  intro p.
  set (q := fun y => eqb (p y) (p (Ninf_succ y))).
  pose proof (extended_nat_lpo_bool q) as Hq.
  destruct Hq as [Hqf|Hqt].
  - left. destruct Hqf as [y Hqyf]. unfold q in Hqyf.
    remember (p y) as py; apply eq_sym in Heqpy. destruct (py).
    -- exists (Ninf_succ y). split.
       --- intro HSyt. pose proof (proj2 (Ninf_succ_true y) HSyt) as Hyt. rewrite -> HSyt, <- Hyt, -> Heqpy in Hqyf.
           discriminate.
       --- destruct (p (Ninf_succ y)). discriminate. reflexivity. 
    -- exists y. split.
       --- intro Hyt. apply (Ninf_succ_fix y) in Hyt. rewrite -> Hyt, -> Heqpy in Hqyf. discriminate. 
       --- exact Heqpy.
  - remember (p (fin 0)) as p0; apply eq_sym in Heqp0. destruct p0.
    -- right. induction n. 
       --- exact Heqp0. 
       --- specialize (Hqt (fin n)). unfold q in Hqt. 
           apply eqb_prop in Hqt. rewrite <- IHn, Hqt. rewrite -> Ninf_succ_false_from. reflexivity.
    -- left. exists (fin 0). split.
       --- now apply Ninf_finite_not_inf.
       --- assumption.
Qed.

(* Theorem 8.2 from "Omniscient sets in constructive mathematics". *)
Lemma wlpo_ninf_restr_nat : forall p : Ninf -> B, 
  {forall n : N, p (fin n) = true} + {~ forall n : N, p (fin n) = true}.
Proof.
  intro p. destruct (lpo_ninf_restr_nat p) as [H|H].
  - right. 
    destruct H as [u [Hufin Hpuf]].
    intro Hp.
    apply Hufin.
    apply (not_finite_implies_inf u).
    intros k Hsk.
    specialize (Hp k).
    rewrite <- Hsk in Hp.
    now apply (eq_true_false_abs (p u)).
  - left; exact H.
Qed.

(* Theorem 9.4 from "Omniscient sets in constructive mathematics". *)
Theorem eps_is_infemum : forall p : Ninf -> B, 
  (forall x, p x = false -> eps p <= x)
    /\ (forall y, (forall x, p x = false -> y <= x) -> y <= eps p).
Proof.
  pose proof (extended_nat_selection_function) as Heps. unfold is_selection_function in Heps.
  intros p. split.
  - intros x Hpx.
    (* Since we need to consider the case x=inf, we can't handle this directly. *)
    unfold Ninf_le.
    induction n.
    -- simpl.
       intro Hp0. 
       apply not_false_iff_true; intro Hx0.
       pose proof (Ninf_finite_eq_zero x Hx0) as Hx.
       rewrite <- Hx in Hp0; now apply (eq_true_false_abs (p x)).
    -- simpl. 
       intro HpS; apply andb_true_iff in HpS; destruct HpS as [Hepsp HpS]. 
       apply IHn in Hepsp as Hxn; clear IHn Hepsp.
       apply not_false_iff_true; intro HxSn.
       pose proof (Ninf_finite_eq_succ x n Hxn HxSn) as Hx. 
       rewrite <- Hx in HpS; now apply (eq_true_false_abs (p x)).
  - intros y Hx. 
    remember (p (eps p)) as pep; apply eq_sym in Heqpep. destruct pep.
    -- apply p_eps_p_true in Heqpep.
       rewrite -> Heqpep. now apply Ninf_le_inf.
    -- exact (Hx (eps p) Heqpep).
Qed.

Conjecture cantor_lpo : LPOSet (N -> B).
Conjecture cantor_searchable : is_searchable (N -> B). 
