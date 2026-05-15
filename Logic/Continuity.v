(******************************************************************************
 *  Logic/Continuity.v
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
 * Formulation of continuity for functions on Ninf,
 * and proof that if the weak limited principle of omnicience (WLPO) is false,
 * then every function N_inf to Bool is continuous.
 *
 * Based on
 *   "Constructive decidability of classical continuity"
 *   Martín H. Escardó, Math. Struct. in Comp. Science 25 (2015)
 *)


From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.ConstructiveEpsilon.

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.


Require Import Words.
Require Import ExtendedNat.
Require Import Omniscience.

Notation "'clexists' x , P" := ( ~ (forall x, ~ (P )) ) (at level 78).
(*
Notation "'clexists' (x : T) , P" := ( ~ (forall (x : T), ~ (P )) ) (at level 78).
*)

Open Scope nat_scope.

Lemma exists_implies_classical_exists : forall {X : Type} (p : X -> Prop),
  (exists x, p x) -> (clexists x, p x).
Proof. intros X p He Hnpx. destruct He as [x Hpx]. exact (Hnpx x Hpx). Qed.

Lemma forall_impl {X : Type} {p q : X -> Prop} :
  (forall x, p x) -> (forall x, p x -> q x) -> (forall x, q x).
Proof. intros Hp Hpq. intro x; specialize (Hp x). exact (Hpq x Hp). Qed.

Lemma clexists_impl {X : Type} {p q : X -> Prop} :
  (clexists x, p x) -> (forall x, p x -> q x) -> (clexists x, q x).
Proof. intros Hp Hpq. intro Hq; apply Hp; clear Hp. intro x; specialize (Hq x). 
  intro Hp; apply Hq; clear Hq. exact (Hpq x Hp). Qed.

Lemma exists_impl {X : Type} {p q : X -> Prop} :
  (exists x, p x) -> (forall x, p x -> q x) -> (exists x, q x).
Proof. intros [x Hpx] Hpq. exists x. exact (Hpq x Hpx). Qed.

Lemma forall_implies_l {X : Type} {p q r : X -> Prop} :
  (forall x, p x -> r x) -> (forall x, q x -> p x) -> (forall x, q x -> r x).
Proof. intros Hpr Hqp. intros x Hqx; now apply Hpr, Hqp. Qed.
Lemma forall_implies_r {X : Type} {p q r : X -> Prop} :
  (forall x, p x -> q x) -> (forall x, q x -> r x) -> (forall x, p x -> r x).
Proof. intros Hpq Hqr. intros x Hpx; now apply Hqr, Hpq. Qed.

Lemma forall_clexists_impl {X  Y: Type} {p q : X -> Y -> Prop} :
  (forall x, clexists y, p x y) -> (forall x y, p x y -> q x y) -> (forall x, clexists y, q x y).
Proof. intros Hp Hpq. apply (forall_impl Hp); intros x Hpx. apply (clexists_impl Hpx); intro y. exact (Hpq x y). Qed.

Lemma clexists_forall_impl {X  Y: Type} {p q : X -> Y -> Prop} :
  (clexists x, forall y, p x y) -> (forall x y, p x y -> q x y) -> (clexists x, forall y, q x y).
Proof. intros Hp Hpq. apply (clexists_impl Hp); intros x Hpx. apply (forall_impl Hpx); intro y. exact (Hpq x y). Qed.

Lemma or_of_sumbool : forall p q : Prop, { p } + { q } -> p \/ q.
Proof. intros p q. tauto. Qed.

(* Markov's principle for a type X. 
 * Note that Markov's principle for N states that 
 * given an algorithm that does not terminate, 
 * we can find the number of steps at which it terminates.
 * This is valid in some constructive mathematics, but is unprovable in Rocq.
 *)
Definition MarkovsPrinciple (X : Type) := forall p : X -> Prop, 
  (forall x : X, p x \/ ~ p x) ->
    (~ forall x, ~ p x) -> exists x, p x.

(* Note that this is stronger than "constructive indefinite description",
 * which is a theorem for N.
 *
 * Stdlib.Logic.ClassicalEpsilon
 * Axiom constructive_indefinite_description :
 *   forall (A : Type) (P : A->Prop), (exists x, P x) -> { x : A | P x }.
 * 
 * Stdlib.Logic.ConstructiveEpsilon
 * Definition constructive_indefinite_ground_description_nat :
 *   (exists n, P n) -> {n:nat | P n} :=
 *)

Definition eq_up_to {X : Type} (n : N) (a b : N -> X) : Prop :=
  proj n a = proj n b.
Definition eqv_up_to {X : Type} (n : N) (a b : N -> X) : Prop :=
  forall k, (k < n) -> a k = b k.

(* forall boolean quantifier. Note this is "E" from "Constructive continuity". *)
Definition A (p : Ninf -> B) : B := p (eps p).
Lemma A_spec_false : forall p, A p = false <-> exists u, p u = false.
Proof.
  set (Heps := (extended_nat_selection_function)).
  pose proof (exists_iff_search eps Heps) as Hexists.
  intro p; specialize (Hexists p).
  unfold A; apply iff_sym.
  split. exact Hexists. intro Hp; exists (eps p); exact Hp.
Qed.
Lemma A_spec_true : forall p, A p = true <-> forall u, p u = true.
Proof.
  intro p; pose proof (A_spec_false p) as Hp; split.
  - intros Ha u. apply not_false_iff_true. intro Hnpu. apply not_false_iff_true in Ha.
    apply Ha; clear Ha. apply Hp. exists u; exact Hnpu.
  - intro Ha. apply not_false_iff_true. intro Hnap. apply Hp in Hnap. destruct Hnap as [u Hnpu].
    apply not_true_iff_false in Hnpu. apply Hnpu; clear Hnpu. exact (Ha u).
Qed.

Definition E (p : Ninf -> B) : B := negb (A (fun u => negb (p u))).
Lemma E_spec : forall p, E p = true <-> exists u, p u = true.
Proof.
  unfold E; intro p; split.
  - intros HnAp.
    apply negb_true_iff, A_spec_false in HnAp.
    destruct HnAp as [u Hu].
    apply negb_false_iff in Hu; exists u; exact Hu.
  - intro HEp. destruct HEp as [u Hu]. 
    apply negb_true_iff; apply A_spec_false.
    exists u; apply negb_false_iff; exact Hu.
Qed.

 
Definition classically_continuous_cantor (f : (N -> B) -> B) :=
  forall alpha : N -> B, clexists n, 
    forall beta : N -> B,
      eqv_up_to n alpha beta -> f alpha = f beta.

Definition classically_uniformly_continuous_cantor (f : (N -> B) -> B) :=
  clexists n, 
    forall alpha beta : N -> B,
      eqv_up_to n alpha beta -> f alpha = f beta.

Definition continuous_cantor (f : (N -> B) -> B) :=
  forall alpha : N -> B, exists n : N, 
    forall beta : N -> B,
      eqv_up_to n alpha beta -> f alpha = f beta.

Definition uniformly_continuous_cantor (f : (N -> B) -> B) :=
  exists n : N, 
    forall alpha beta : N -> B,
      eqv_up_to n alpha beta -> f alpha = f beta.

Definition effectively_continuous_cantor (f : (N -> B) -> B) :=
  forall (alpha : N -> B), @sig N 
    ( fun (n : N) => ( forall (beta : N -> B),
      (eqv_up_to n alpha beta) -> (f alpha = f beta) ) ).

Definition is_modulus_of_continuity_cantor (f : (N -> B) -> B) (M : (N -> B) -> N) :=
  forall alpha beta : N -> B,  
    eqv_up_to (M alpha) alpha beta -> f alpha = f beta.

Definition continuous_cantor_to_nat (f : (N -> B) -> N) := 
  forall alpha : N -> B, exists n : N, forall beta : N -> B, 
    eqv_up_to n alpha beta -> f alpha = f beta.

Definition continuous_modulus_of_continuity_cantor (f : (N -> B) -> B) :=
  { M : (N->B)->N | is_modulus_of_continuity_cantor f M /\ continuous_cantor_to_nat M }.

Definition effectively_uniformly_continuous_cantor (f : (N -> B) -> B) :=
  { n : N | forall (alpha beta : N -> B), (eqv_up_to n alpha beta) -> (f alpha = f beta) }.

Close Scope nat_scope.


Open Scope Ninf_scope.

Definition effectively_continuous_ninf (f : Ninf -> B) :=
  { m | forall n, (m <= n)%nat -> f (fin n) = f (inf) }.

Definition continuous_ninf (f : Ninf -> B) :=
  exists m, forall n, (m <= n)%nat -> f (fin n) = f (inf).

Definition classically_continuous_ninf (f : Ninf -> B) :=
  clexists m, forall n, (m <= n)%nat -> f (fin n) = f (inf).

Definition classically_discontinuous_ninf (f : Ninf -> B) :=
  forall m, clexists n, ((m <= n)%nat /\ f (fin n) <> f (inf)).

Definition classical_continuity_principle_ninf :=
  forall (f : Ninf -> B),
    exists (n : N), forall m, (n < m)%nat -> f (fin m) = f (inf).

Definition effective_continuity_principle_ninf :=
  forall (f : Ninf -> B), 
    { n : N | forall m, (n < m)%nat -> f (fin m) = f (inf) }.


Definition classically_continuous_ninf_to_ninf (f : Ninf -> Ninf) :=
  (forall l, fin l <= f inf -> clexists m, forall n, (m <= n)%nat -> fin l <= f (fin n))
    /\ (forall u, f inf <= fin u -> clexists m, forall n, (m <= n)%nat -> f (fin n) <= fin u).

Definition continuous_ninf_to_ninf (f : Ninf -> Ninf) :=
  (forall l, fin l <= f inf -> exists m, forall n, (m <= n)%nat -> fin l <= f (fin n))
    /\ (forall u, f inf <= fin u -> exists m, forall n, (m <= n)%nat -> f (fin n) <= fin u).

Close Scope Ninf_scope.

(*
Notation r := conj_seq.

Definition prepend (alpha : N -> B) (n : N) (beta : N -> B) : N -> B :=
  fun i => if i <? n then alpha i else beta (i - n).
 
Definition shift_along (alpha : N -> B) (n : N) (f : (N -> B) -> B) : (N -> B) -> B :=
  fun beta => f (prepend alpha n beta).

Definition are_all_true (f : (N -> B) -> B) : B :=
  match (lpo_set_implies_bool _ cantor_lpo f) with | inleft _ => false | inright _ => true end.

Lemma are_all_true_spec : forall f, are_all_true f = true <-> forall s, f s = true.
Proof. 
  intro f.
  unfold are_all_true. split.
  - destruct (lpo_set_implies_bool _ cantor_lpo f) as [Ht|Hf].
    -- intro Hft. discriminate Hft.
    -- intro Ht. exact Hf.
  - destruct (lpo_set_implies_bool _ cantor_lpo f) as [Ht|Hf].
    -- intro Hf. destruct Ht as [s Hs]. specialize (Hf s).
       now rewrite <- Hf, <- Hs.
    -- intro Hs. reflexivity.
Qed.
 (forall a, {b a} + {~ b a})
*)

Notation decidable := Decidable.decidable.
Definition decidableT (p : Prop) := {p} + {~ p}.

Definition DecidableConstants (X : Type) := forall (f : X -> B),
  decidable (forall alpha beta, f alpha = f beta).

Definition DecidableConstantsT (X : Type) := forall (f : X -> B),
  decidableT (forall alpha beta, f alpha = f beta).

Definition Extensional {X Y Z : Type} (f : (X -> Y) -> Z) := 
  forall s1 s2, (forall k, s1 k = s2 k) -> f s1 = f s2.


Open Scope nat_scope.

Definition injw {X : Type} {n : N} : Wrd n X -> Wrds X :=
  fun w => existT _ n w.
 
Definition is_bar (b : Wrds B -> Prop) : Prop :=
  forall alpha, exists (n : N), b (existT _ n (proj n alpha)).

Definition is_uniform_bar (b : Wrds B -> Prop) : Prop :=
  exists n : N, forall alpha, exists m : N, (m <= n) /\ b (injw (proj m alpha)).


Definition BrouwersFanPrinciple := 
  forall b : Wrds B -> Prop, (forall a : Wrds B, decidable (b a)) ->
    is_bar b -> is_uniform_bar b.

Definition cat' {X : Type} (w : Wrds X) (x : X) : Wrds X := injw (cat (projT2 w) x).

Definition BarInductionPrinciple := 
  forall b a : Wrds B -> Prop,
    (forall s : Seq B, exists n, b (injw (proj n s))) ->  
      (forall w : Wrds B, decidable (b w)) ->
         (forall w, b w -> a w) ->
            (forall w : Wrds B, a (cat' w false) /\ a (cat' w true) -> a w) ->
               a (injw (null_wrd)).

Definition len {X : Type} : Wrds X -> N := fun w => projT1 w.
 
Definition is_prefix {X : Type} : Wrds X -> Seq X -> Prop :=
  fun w s => forall k, forall (p : (k < len w)), (projT2 w) (ord k p) = s k.

Lemma words_up_to_decidableT_exists : forall (n : N), forall (p : Wrd n B -> Prop), 
  (forall w, decidableT (p w)) -> decidableT (exists w, p w).
Proof.
  intro n.
  induction n.
  - intros p0 Hpw0. set (w0 := null_wrd : Wrd 0 B). specialize (Hpw0 w0). destruct Hpw0 as [Hpw0|Hnpw0].
    left. exists w0. exact Hpw0.
    right. intros [w Hpw]. rewrite <- (wrd_0_eq w0) in Hpw. exact (Hnpw0 Hpw).
  - intro pS.
    set (p := fun w => pS (cat w false) \/ pS (cat w true)).
    intro HpwSdec.
    assert (forall w : Wrd n B, decidableT (p w)) as Hpwdec. {
       intro w. unfold p.
       destruct (HpwSdec (cat w false)); destruct (HpwSdec (cat w true)).
       4: right; tauto.
       all: left; tauto.
    }
    specialize (IHn p Hpwdec).
    clear Hpwdec HpwSdec.
    unfold p in IHn.
    destruct IHn as [Hpt|Hpf].
    -- left. destruct Hpt as [w [Hwf|Hwt]].
       --- exists (cat w false). assumption.
       --- exists (cat w true). assumption.
    -- right. intros [w HpSw].
       set (v := restr n (Nat.le_succ_diag_r n) w).
       apply Hpf.
       exists v.
       remember (w (ord n (Nat.lt_succ_diag_r n))) as wn; destruct wn.
       --- right. rewrite <- cat_head_tail in HpSw. unfold v; rewrite -> Heqwn. exact HpSw.
       --- left. rewrite <- cat_head_tail in HpSw. unfold v; rewrite -> Heqwn. exact HpSw.
Qed.

Lemma words_up_to_decidable_exists : forall (n : N), forall (p : Wrd n B -> Prop), 
  (forall w, decidable (p w)) -> decidable (exists w, p w).
Proof.
  intro n.
  induction n.
  - intros p0 Hpw0. set (w0 := null_wrd : Wrd 0 B). specialize (Hpw0 w0). destruct Hpw0 as [Hpw0|Hnpw0].
    left. exists w0. exact Hpw0.
    right. intros [w Hpw]. rewrite <- (wrd_0_eq w0) in Hpw. exact (Hnpw0 Hpw).
  - intro pS.
    set (p := fun w => pS (cat w false) \/ pS (cat w true)).
    intro HpwSdec.
    assert (forall w : Wrd n B, decidable (p w)) as Hpwdec. {
       intro w. unfold p.
       destruct (HpwSdec (cat w false)); destruct (HpwSdec (cat w true)).
       4: right; tauto.
       all: left; tauto.
    }
    specialize (IHn p Hpwdec).
    clear Hpwdec HpwSdec.
    unfold p in IHn.
    destruct IHn as [Hpt|Hpf].
    -- left. destruct Hpt as [w [Hwf|Hwt]].
       --- exists (cat w false). assumption.
       --- exists (cat w true). assumption.
    -- right. intros [w HpSw].
       set (v := restr n (Nat.le_succ_diag_r n) w).
       apply Hpf.
       exists v.
       remember (w (ord n (Nat.lt_succ_diag_r n))) as wn; destruct wn.
       --- right. rewrite <- cat_head_tail in HpSw. unfold v; rewrite -> Heqwn. exact HpSw.
       --- left. rewrite <- cat_head_tail in HpSw. unfold v; rewrite -> Heqwn. exact HpSw.
Qed.

Lemma words_up_to_decidableT_forall : forall (n : N), forall (p : Wrd n B -> Prop),
  (forall w, decidableT (p w)) -> decidableT (forall w, p w).
Proof.
  intros n p Hpdec.
  set (q := fun w => ~ p w).
  assert (forall w, decidableT (q w)) as Hqdec. {
    unfold q; intro w. destruct (Hpdec w) as [Hpwt|Hpwf]. right; tauto. left; tauto. }
  pose proof (words_up_to_decidableT_exists n q Hqdec) as Hq. unfold q in *.
  destruct Hq as [Heqt|Heqf].
  - right. destruct Heqt as [w Hqw]. intro Hap. exact (Hqw (Hap w)).
  - left. intro w. destruct (Hpdec w) as [Hpw|Hqw]. exact Hpw.
    exfalso. apply Heqf. exists w. exact Hqw.
Qed.

Lemma words_up_to_decidable_forall : forall (n : N), forall (p : Wrd n B -> Prop),
  (forall w, decidable (p w)) -> decidable (forall w, p w).
Proof.
  intros n p Hpdec.
  set (q := fun w => ~ p w).
  assert (forall w, decidable (q w)) as Hqdec. {
    unfold q; intro w. destruct (Hpdec w) as [Hpwt|Hpwf]. right; tauto. left; tauto. }
  pose proof (words_up_to_decidable_exists n q Hqdec) as Hq. unfold q in *.
  destruct Hq as [Heqt|Heqf].
  - right. destruct Heqt as [w Hqw]. intro Hap. exact (Hqw (Hap w)).
  - left. intro w. destruct (Hpdec w) as [Hpw|Hqw]. exact Hpw.
    exfalso. apply Heqf. exists w. exact Hqw.
Qed.

Lemma words_up_to_clexists_exists : forall (n : N), forall (p : Wrd n B -> Prop), 
  (forall w, decidable (p w)) -> (clexists w, p w) -> (exists w, p w).
Proof.
  intros n p Hpdec Hexpw.
  destruct (words_up_to_decidable_exists n p Hpdec).
  - assumption. 
  - exfalso. apply Hexpw. intros w Hpw. apply H. exists w. exact Hpw.
Qed.

Lemma up_to_dec : forall (p : N -> Prop), (forall n, decidable (p n)) ->
  forall n, decidable (forall m, (m < n) -> p m).
Proof.
  intros p Hpdec n.
  induction n.
  - left. intros m Hmlt0. contradiction (Nat.nlt_0_r m Hmlt0). 
  - destruct (Hpdec n) as [Hpn|Hpn]. destruct IHn as [IHn|IHn]. 
    -- left. intros m HmltSn. apply (Nat.lt_succ_r m) in HmltSn. apply (Nat.lt_eq_cases) in HmltSn.
       destruct HmltSn as [Hmltn|Hmeqn]. exact (IHn m Hmltn). rewrite -> Hmeqn; exact Hpn.  
    -- right. intro Hp. apply IHn. intros m Hmltn. exact (Hp m (Nat.lt_lt_succ_r _ _ Hmltn)).   
    -- right. intro Hp. apply Hpn. exact (Hp n (Nat.lt_succ_diag_r n)).
Qed.

Lemma prefix_proj_eqv_up_to {X} : forall m (alpha beta : Seq X), 
  is_prefix (injw (proj m alpha)) beta = eqv_up_to m alpha beta.
Proof. intros m alpha beta. reflexivity. Qed.

Lemma eqv_up_to_refl {X} : forall {m} (alpha : Seq X),
  eqv_up_to m alpha alpha.
Proof.
  unfold eqv_up_to. intros m alpha k Hkltm. apply eq_refl.
Qed.

Lemma eqv_up_to_symm {X} : forall {m} (alpha beta : Seq X),
  eqv_up_to m alpha beta -> eqv_up_to m beta alpha.
Proof.
  unfold eqv_up_to. intros m alpha beta Halphabeta k Hkltm. apply eq_sym; now apply Halphabeta.
Qed.

Lemma eqv_up_to_trans {X} : forall {m} (alpha beta gamma : Seq X),
  eqv_up_to m alpha beta -> eqv_up_to m beta gamma -> eqv_up_to m alpha gamma.
Proof.
  unfold eqv_up_to. intros m alpha beta gamma Halphabeta Hbetagamma k Hkltm.
  transitivity (beta k). now apply Halphabeta. now apply Hbetagamma.
Qed.

Local Definition z (_ : N) := false : B.

Lemma bar_from_modulus : forall f : (N -> B) -> N, 
  continuous_cantor_to_nat f ->
    is_bar (fun w => (f (splice (projT2 w) z) <= len w)).
Proof. 
  intros f Hctsf alpha. 
  destruct (Hctsf alpha) as [n Hn]. 
  set (m := Nat.max n (f alpha)).
  exists m. simpl.
  set (gamma := splice (proj m alpha) z).
  assert (f gamma = f alpha) as Hw. {
    apply eq_sym; apply Hn; unfold gamma, eqv_up_to; simpl.
    intros k Hkltn. 
    assert (n <= m) as Hnlem by exact (Nat.le_max_l n (f alpha)).
    assert (k < m) as Hkltm by now apply (Nat.lt_le_trans _ n _).
    rewrite -> (splice_word_element Hkltm).
    unfold proj; now simpl.
  }
  unfold m; rewrite -> Hw. now apply (Nat.le_max_r n (f alpha)). 
Qed.

Lemma eqv_up_to_le {X : Type} : 
  forall {alpha beta : Seq X} {m} n, (m <= n) -> eqv_up_to n alpha beta -> eqv_up_to m alpha beta.
Proof. intros alpha beta m n Hmlen Hn k Hkltn. apply Hn. now apply (Nat.lt_le_trans _ m _). Qed.

Lemma eqv_up_to_proj {X : Type} : forall (alpha gamma : Seq X) n, eqv_up_to n alpha (splice (proj n alpha) gamma).
Proof. intros *. unfold eqv_up_to. intros k Hkltn. rewrite -> (splice_word_element Hkltn). now unfold proj. Qed.

Lemma eqv_up_to_splice_word {X : Type} : forall {n} {w : Wrd n X} {a b},
  eqv_up_to n (splice w a) (splice w b).
Proof. 
  intros *. unfold eqv_up_to. intros k Hkltn. 
  now rewrite -> (splice_word_element Hkltn), -> (splice_word_element Hkltn).
Qed.

Lemma non_constant_wrd : forall (f : (N -> B) -> B), continuous_cantor f ->
  (exists alpha beta, f alpha <> f beta) -> 
       (exists n, exists u v : Wrd n B, f (splice u z) <> f (splice v z)).
Proof.
  intros f Hfcts [alpha [beta Hfab]].
  pose proof (Hfcts alpha) as [na Hna].
  pose proof (Hfcts beta) as [nb Hnb].
  set (n := Nat.max na nb).
  set (u := proj n alpha); set (v := proj n beta).
  exists n, u, v.
  intro Hfuv; apply Hfab; clear Hfab.
  transitivity (f (splice u z)). 2: transitivity (f (splice v z)).
  - apply Hna. apply (eqv_up_to_le n (Nat.le_max_l na nb)). now apply eqv_up_to_proj.
  - now apply Hfuv.
  - symmetry. apply Hnb. apply (eqv_up_to_le n (Nat.le_max_r na nb)). now apply eqv_up_to_proj.
Qed.


Lemma all_cantor_clexists_exists_constant : (MarkovsPrinciple N) -> 
  (forall f : (N->B) -> B, continuous_cantor f ->
    (clexists alpha, clexists beta, f alpha <> f beta) -> (exists alpha beta, f alpha <> f beta)).
Proof.
  intros Hmp.
  intros f Hfcts.
  unfold MarkovsPrinciple in Hmp.
  set (p := fun n => fun (u v : Wrd n B) => f (splice u z) <> f (splice v z)).
  assert (forall n (u v : Wrd n B), decidable (p n u v)) as Hpnuvdec. { 
    intros n u v; unfold p. destruct (bool_dec (f (splice u z)) (f (splice v z))).
    right; tauto. left; tauto. }
  assert (forall n (u : Wrd n B), decidable (exists v, (p n u v))) as Hpnudec. { 
    intros n u. now apply words_up_to_decidable_exists. }
  assert (forall n, decidable (exists u v, (p n u v))) as Hpndec. { 
    intros n. now apply words_up_to_decidable_exists. }
  pose proof (Hmp _ Hpndec) as Hp.
  assert (forall n, (clexists u, clexists v, p n u v) -> (exists u v, p n u v)) as Hpcl. {
    intros n H. apply words_up_to_clexists_exists. now apply Hpnudec.
    intro H'; apply H; clear H. intro u; specialize (H' u). intro H; apply H'; clear H'.
    now apply words_up_to_clexists_exists. }
  assert ((clexists n, clexists u, clexists v, p n u v) -> (exists n u v, p n u v)) as Hwrdp. {
    intros H. apply Hp. 
    intro H'; apply H; clear H. intro u; specialize (H' u). intro H; apply H'; clear H'.
    now apply Hpcl. }
  clear Hpnuvdec Hpnudec Hpndec Hp Hpcl.
  unfold p in Hwrdp.
  intros Hclab.
  assert (clexists n, clexists u, clexists v, f (@splice _ n u z) <> f (@splice _ n v z)) as Hcluv. {
    intro H; apply Hclab. 
    intro alpha. pose proof (Hfcts alpha) as [na Hna].
    intro H'; apply H'; clear H'.
    intros beta Hfab.
    pose proof (Hfcts beta) as [nb Hnb].
    set (n := Nat.max na nb).
    apply (H n); clear H.
    intro Huv; set (u := proj n alpha); specialize (Huv u); apply Huv; clear Huv.
    intro Huv; set (v := proj n beta); specialize (Huv v); apply Huv; clear Huv.
    intros Hfuv; apply Hfab; clear Hfab.
    transitivity (f (splice u z)). 2: transitivity (f (splice v z)).
    - apply Hna. apply (eqv_up_to_le n). exact (Nat.le_max_l na nb).
      now apply eqv_up_to_proj.
    - exact Hfuv.
    - symmetry. apply Hnb. apply (eqv_up_to_le n). exact (Nat.le_max_r na nb).
      now apply eqv_up_to_proj.
  }
  specialize (Hwrdp Hcluv); clear Hcluv.
  destruct Hwrdp as [n [u [v Hfnuv]]].
  exists (splice u z); exists (splice v z).
  exact Hfnuv.
Qed.


(* Can't be constructively valid?? *)
Conjecture all_cantor_decidable_constant : (MarkovsPrinciple N) -> 
    (forall f : (N->B) -> B, continuous_cantor f ->
      (clexists alpha, clexists beta, f alpha <> f beta) \/ (forall alpha beta, f alpha = f beta)).


Theorem continuous_modulus_of_continuity_implies_uniformly_continuous_cantor : (BrouwersFanPrinciple) ->
  forall f, continuous_modulus_of_continuity_cantor f -> uniformly_continuous_cantor f.
Proof.
  unfold BrouwersFanPrinciple, continuous_modulus_of_continuity_cantor, is_modulus_of_continuity_cantor, continuous_cantor_to_nat, uniformly_continuous_cantor.
  intros Hfan f [M [Hfcts HMcts]].
  set (falses := fun (_ : N) => (false : B)).
  set (B := fun w : Wrds B => (M (splice (projT2 w) z) <= len w)).
  assert (is_bar B) as HB. unfold B; exact (bar_from_modulus M HMcts).
  apply Hfan in HB.
  2: { unfold B. intro w.
       destruct (Nat.le_gt_cases (M (splice (projT2 w) z)) (len w)) as [H|H].
       left; assumption.
       right. now apply Nat.lt_nge. }
  unfold is_uniform_bar, B in HB; simpl in HB.
  destruct HB as [N HN].
  exists N.
  intros alpha.
  specialize (HN alpha).
  intros beta Hab.
  destruct HN as [n [HnleN HNn]].
  set (gamma := splice (proj n alpha) z).
  assert (M gamma <= n) as HMclen by now apply HNn.
  assert (M gamma <= N) as HMcleN by now apply (Nat.le_trans _ n _).
  assert (eqv_up_to n gamma alpha) as Hca.
    intros k Hk. unfold gamma. now rewrite -> (splice_word_element Hk).
  assert (forall beta, eqv_up_to (M gamma) gamma beta -> f gamma = f beta) as Hgamma
    by exact (Hfcts gamma).
  transitivity (f gamma).
  - symmetry. apply Hgamma. now apply (eqv_up_to_le _ HMclen).
  - apply Hgamma.
    apply (eqv_up_to_trans _ alpha).
    now apply (eqv_up_to_le n).
    now apply (eqv_up_to_le N).
Qed.


(*
Lemma eqv_up_to_dec : forall (f : (N -> B) -> B) (n : N) (alpha : N -> B),
  let p := (forall beta : N -> B, eqv_up_to n alpha beta -> f alpha = f beta) in
   { p } + {~ p}.
Proof. Admitted.

Lemma uni_eqv_up_to_dec : forall (f : (N -> B) -> B) (n : N),
  let p := (forall alpha beta : N -> B, eqv_up_to n alpha beta -> f alpha = f beta) in
   { p } + {~ p}.
Proof. Admitted.
*)

Definition shift {X : Type} n (s : Seq X) := fun k => s (n+k).
    
Lemma splice_eqv_front_back {X : Type} : forall (alpha : Seq X) n, 
  forall k, splice (proj n alpha) (shift n alpha) k = alpha k.
Proof.
  intros alpha n k; unfold shift. destruct (Nat.lt_ge_cases k n).
  rewrite -> (splice_word_element H). now apply proj_at.
  rewrite -> (splice_sequence_element H). f_equal. rewrite -> Nat.add_comm. now apply Nat.sub_add.
Qed.


Definition SequenceExtensionality (X : Type) := forall (a b : N -> X), 
  (forall k, a k = b k) -> a = b.

Lemma splice_eq_front_back {X : Type} : (SequenceExtensionality X) ->
  forall (alpha : Seq X) n, splice (proj n alpha) (shift n alpha) = alpha.
Proof.
  intros Hseq alpha n. apply Hseq. intro k. destruct (Nat.lt_ge_cases k n).
  rewrite -> (splice_word_element H). now apply proj_at.
  rewrite -> (splice_sequence_element H). f_equal. unfold shift. f_equal. rewrite -> Nat.add_comm. now apply Nat.sub_add.
Qed.

Lemma splice_eqv {X : Type} : forall {n} {u v : Wrd n X} {a b},
  (forall k p, u (ord k p) = v (ord k p)) -> (forall k, a k = b k) -> forall k, (splice u a) k = (splice v b) k.
Proof.
 intros n u v a b Huv Hab k. destruct (Nat.lt_ge_cases k n).
 now rewrite -> (splice_word_element H), -> (splice_word_element H).
 now rewrite -> (splice_sequence_element H), -> (splice_sequence_element H).
Qed.

Definition wrd_eqv {X : Type} {n} (u v : Wrd n X) := 
  forall k (p : k < n), u (ord k p) = v (ord k p).

Lemma extensional_decompose_eq  {X Y : Type} : forall (f : (N->X)->Y), (Extensional f) ->
  forall (n : N) alpha, f alpha = f (splice (proj n alpha) (shift n alpha)).
Proof. 
  intros f Hfext n alpha.
  apply Hfext. intros k. symmetry. now apply splice_eqv_front_back.
Qed.

Lemma extensional_word_eq  {X Y : Type} : forall (f : (N->X)->Y), (Extensional f) ->
  forall (n : N) (u v : Wrd n X) (gamma : Seq X), wrd_eqv u v -> f (splice u gamma) = f (splice v gamma).
Proof. 
  intros f Hfext n u v gamma Huv.
  apply Hfext. apply splice_eqv.
  - intros k p. now apply Huv.
  - reflexivity.
Qed.

Lemma extensional_splice_eq  {X Y : Type} : forall (f : (N->X)->Y), (Extensional f) ->
  forall (n : N) (w : Wrd n X), 
    (forall alpha beta, wrd_eqv (proj n alpha) w -> wrd_eqv (proj n beta) w -> f alpha = f beta) <-> 
      (forall gamma delta, f (splice w gamma) = f (splice w delta)).
Proof.
  intros f Hfext n w. split.
  - intro H. intros gamma delta. apply H. 
    unfold eqv_up_to, proj. intros k Hkltn; simpl. now rewrite -> (splice_word_element Hkltn).
    unfold eqv_up_to, proj. intros k Hkltn; simpl. now rewrite -> (splice_word_element Hkltn).
  - intro H. intros alpha beta Haw Hbw.
    set (u:=proj n alpha); set (gamma := shift n alpha).
    set (v:=proj n beta); set (delta := shift n beta).
    transitivity (f (splice v delta)).
    transitivity (f (splice w delta)).
    transitivity (f (splice w gamma)).
    transitivity (f (splice u gamma)).
    -- now apply extensional_decompose_eq. 
    -- now apply extensional_word_eq.
    -- now apply H.
    -- now apply extensional_word_eq.
    -- symmetry. now apply extensional_decompose_eq. 
Qed.

Lemma extensional_splice_all_eq  {X Y : Type} : forall (f : (N->X)->Y), (Extensional f) ->
  forall (n : N),
    (forall alpha beta, eqv_up_to n alpha beta -> f alpha = f beta) <-> 
      (forall (w : Wrd n X) gamma delta, f (splice w gamma) = f (splice w delta)).
Proof.
  intros f Hfext n. split.
  - intros H w. apply extensional_splice_eq. exact Hfext.
    intros alpha beta Ha Hb. apply H. 
    unfold eqv_up_to. intros k p. transitivity (w (ord k p)). 2: symmetry.
    now apply Ha. now apply Hb.
  - intro H. 
    assert (forall w, (forall alpha beta, 
        wrd_eqv (proj n alpha) w -> wrd_eqv (proj n beta) w -> f alpha = f beta)) as Hfab.
      intro w. now apply extensional_splice_eq.
    intros alpha beta Hab. apply (Hfab (proj n alpha)).
    unfold wrd_eqv; reflexivity. 
    unfold wrd_eqv; symmetry; now apply Hab.
Qed.

Lemma extensional_splice_first_eq  {X Y : Type} : forall (f : (N->X)->Y), (Extensional f) ->
  forall (n : N) alpha,
    (forall beta, eqv_up_to n alpha beta -> f alpha = f beta) <-> 
      (forall gamma delta, f (splice (proj n alpha) gamma) = f (splice (proj n alpha) delta)).
Proof.
  intros f Hfext n gamma. split.
  - intro H. apply extensional_splice_eq. exact Hfext.
    intros alpha beta Ha Hb. transitivity (f gamma).
    -- symmetry. apply H. unfold eqv_up_to, wrd_eqv, proj in *. symmetry in Ha. apply Ha. 
    -- apply H. unfold eqv_up_to, wrd_eqv, proj in *. symmetry in Hb. apply Hb. 
  - intro H. rename gamma into alpha.
    pose proof (proj2 (extensional_splice_eq f Hfext n (proj n alpha)) H) as Hfab.
    intro beta; specialize (Hfab alpha beta).
    intro Hab. apply Hfab.
    -- unfold wrd_eqv; reflexivity.
    -- unfold wrd_eqv; symmetry; now apply Hab.
Qed.


Lemma decidable_constants_implies_decidable_from : (DecidableConstants (N->B)) ->
  forall (f : (N -> B) -> B), Extensional f ->
    forall n alpha, decidable (forall beta, eqv_up_to n alpha beta -> f alpha = f beta).
Proof.
  intros Hdeco f Hfext n alpha. 
  set (u := proj n alpha).
  set (g := fun gamma => f (splice (proj n alpha) gamma)).
  destruct (Hdeco g) as [Hg|Hg]. all: unfold g in Hg.
  - left. now apply extensional_splice_first_eq.
  - right. intro Hf; apply Hg. now apply extensional_splice_first_eq.
Qed.

Lemma decidable_constants_implies_decidable_fromT : (DecidableConstantsT (N->B)) ->
  forall (f : (N -> B) -> B), Extensional f ->
    forall n alpha, decidableT (forall beta, eqv_up_to n alpha beta -> f alpha = f beta).
Proof.
  intros Hdeco f Hfext n alpha. 
  set (u := proj n alpha).
  set (g := fun gamma => f (splice (proj n alpha) gamma)).
  destruct (Hdeco g) as [Hg|Hg]. all: unfold g in Hg.
  - left. now apply extensional_splice_first_eq.
  - right. intro Hf; apply Hg. now apply extensional_splice_first_eq.
Qed.

Lemma decidable_constants_implies_uniformly_decidable_from : (DecidableConstants (N->B)) ->
  forall (f : (N -> B) -> B), Extensional f ->
    forall n, decidable (forall alpha beta, eqv_up_to n alpha beta -> f alpha = f beta).
Proof.
  unfold DecidableConstants.
  intros Hdeco f Hfext n. 
  set (g := fun (w : Wrd n B) => fun gamma => f (splice w gamma)).
  assert (forall (u : Wrd n B), decidable (forall gamma delta, f (splice u gamma) = f (splice u delta))) as Hgu.
    intro u. exact (Hdeco (g u)).
  assert (decidable (forall (u : Wrd n B), forall gamma delta, f (splice u gamma) = f (splice u delta))) as Hg.
    now apply words_up_to_decidable_forall. 
  destruct Hg as [Hg|Hg].
  - left. now apply extensional_splice_all_eq.
  - right. intro Hf; apply Hg. now apply extensional_splice_all_eq.
Qed.

Lemma decidable_constants_implies_uniformly_decidable_fromT : (DecidableConstantsT (N->B)) ->
  forall (f : (N -> B) -> B), Extensional f ->
    forall n, decidableT (forall alpha beta, eqv_up_to n alpha beta -> f alpha = f beta).
Proof.
  unfold DecidableConstantsT.
  intros Hdeco f Hfext n. 
  set (g := fun (w : Wrd n B) => fun gamma => f (splice w gamma)).
  assert (forall (u : Wrd n B), decidableT (forall gamma delta, f (splice u gamma) = f (splice u delta))) as Hgu.
    intro u. exact (Hdeco (g u)).
  assert (decidableT (forall (u : Wrd n B), forall gamma delta, f (splice u gamma) = f (splice u delta))) as Hg.
    now apply words_up_to_decidableT_forall.
  destruct Hg as [Hg|Hg].
  - left. now apply extensional_splice_all_eq.
  - right. intro Hf; apply Hg. now apply extensional_splice_all_eq.
Qed.



(* Not provable.
Lemma classically_continuous_implies_extensional_cantor : 
  forall f, classically_continuous_cantor f -> Extensional f.
*)

Lemma continuous_implies_extensional_cantor : forall f, continuous_cantor f -> Extensional f.
Proof. 
  unfold continuous_cantor, Extensional.
  intros f Hfcts alpha beta Haeqvb.
  pose proof (Hfcts alpha) as [na Hna].
  specialize (Hna beta).
  apply Hna.
  unfold eqv_up_to. intros k Hkltna. exact (Haeqvb k).
Qed.

Lemma classically_continuous_implies_continuous_cantor :
  (MarkovsPrinciple N) ->
    (DecidableConstants (N -> B)) -> 
      forall f, Extensional f -> classically_continuous_cantor f -> continuous_cantor f.
Proof.
  unfold MarkovsPrinciple, DecidableConstants, classically_continuous_cantor, continuous_cantor.
  intros Hmp Hdeco f Hfext Hfccts.
  intros alpha.
  apply Hmp. 2: exact (Hfccts alpha).
  intro n.
  set (u := proj n alpha).
  set (g := fun gamma => f (splice u gamma)).
  set (gamma := fun k : N => alpha (n+k)).
  destruct (Hdeco g) as [H|H].
  - left. intros beta Hab. 
    set (v := proj n beta).
    set (delta := fun k => beta (n+k)).
    transitivity (f (splice u gamma)).
    2: transitivity (f (splice u delta)).
    -- apply Hfext. 
       intro k. symmetry. apply splice_eqv_front_back.
    -- unfold g in H. now apply H.
    -- apply Hfext. 
       intro k. destruct (Nat.lt_ge_cases k n) as [Hkltn|Hnlek].
       rewrite -> (splice_word_element Hkltn). unfold u.
       unfold proj. simpl. now apply Hab.
       rewrite -> (splice_sequence_element Hnlek). unfold delta.
       f_equal. rewrite -> Nat.add_comm. now apply Nat.sub_add. 
  - right. intro Hb; apply H; clear H.
    intros beta delta. unfold g.
    transitivity (f alpha). 1: symmetry.
    all: apply Hb. all: now apply eqv_up_to_proj.
Qed.

(* Do we need DecidableConstants here? *)
Lemma continuous_implies_effectively_continuous_cantor :
  (DecidableConstantsT (N->B)) -> 
    forall f, continuous_cantor f -> effectively_continuous_cantor f.
Proof.
  unfold DecidableConstantsT.
  intros Hdeco f Hfcts alpha.
  pose proof (continuous_implies_extensional_cantor f Hfcts) as Hfext.
  apply constructive_indefinite_ground_description_nat.
  intro n.
  pose proof (decidable_constants_implies_decidable_fromT Hdeco f Hfext n alpha) as H.
  destruct H. left; tauto. right; tauto.
  now apply Hfcts.
Qed.

Lemma classically_uniformly_continuous_implies_classically_continuous_cantor : 
  forall f, classically_uniformly_continuous_cantor f -> classically_continuous_cantor f.
Proof.
  unfold classically_uniformly_continuous_cantor, classically_continuous_cantor.
  intros f Hfcucts. 
  intro alpha. intros H; apply Hfcucts. intro n; specialize (H n).
  intro H'; apply H; clear H. intro beta; specialize (H' alpha beta).
  tauto.
Qed.

Lemma uniformly_continuous_implies_continuous_cantor : 
  forall f, uniformly_continuous_cantor f -> continuous_cantor f.
Proof. 
  intros f [n Hfn] alpha. exists n. intro beta. now apply Hfn.
Qed.


Lemma classically_uniformly_continuous_implies_uniformly_continuous_cantor : 
  (MarkovsPrinciple N) -> (DecidableConstants (N->B)) ->
    forall f, Extensional f -> classically_uniformly_continuous_cantor f -> uniformly_continuous_cantor f.
Proof.
  unfold MarkovsPrinciple, DecidableConstants.
  unfold classically_uniformly_continuous_cantor, uniformly_continuous_cantor.
  intros Hmp Hdeco f Hfext Hfcucts.
  apply Hmp.
  - intro n.
    assert (classically_continuous_cantor f) as Hfccts by 
      now apply classically_uniformly_continuous_implies_classically_continuous_cantor.
    assert (continuous_cantor f) as Hfcts.
      now apply classically_continuous_implies_continuous_cantor.
    set (g := fun (w : Wrd n B) gamma => f (splice w gamma)).
    assert (forall w, continuous_cantor (g w)) as Hgcts. {
      intros w gamma. pose proof (Hfcts (splice w gamma)) as [na Hna].
      exists (na-n)%nat.
      intro delta.
      specialize (Hna (splice w delta)).
      unfold g. intro Hgd. apply Hna.
      destruct (Nat.le_ge_cases na n). 
      - apply (eqv_up_to_le n H). apply eqv_up_to_splice_word.
      - unfold eqv_up_to. intros k Hkltna. destruct (Nat.lt_ge_cases k n) as [Hkltn|Hnlek]. 
        -- now rewrite -> (splice_word_element Hkltn), -> (splice_word_element Hkltn).
        --rewrite -> (splice_sequence_element Hnlek), -> (splice_sequence_element Hnlek).
          apply Hgd.
          apply (Nat.add_lt_mono_r (k-n) (na-n) n).
          rewrite -> (Nat.sub_add n k), -> (Nat.sub_add n na).
          --- exact Hkltna.
          --- apply (Nat.le_trans _ k _ Hnlek). Search lt le. now apply Nat.lt_le_incl.
          --- exact Hnlek.
    }
    set (Hg := fun w => forall alpha beta, g w alpha = g w beta).
    assert (forall w, decidable (Hg w)) as Hgwdec. {
      intro w. 
      destruct (all_cantor_decidable_constant Hmp (g w) (Hgcts w)).
      - right. unfold Hg. intro Ha; apply H; clear H. intro alpha. intro He; apply He; clear He.
        intro beta. intro He; apply He. now apply Ha.
      - left. exact H.
    }
    pose proof (words_up_to_decidable_forall n Hg Hgwdec) as Hga.
    destruct Hga.
    -- left. now apply extensional_splice_all_eq.
    -- right. intros Hfab. apply H; clear H. unfold Hg.
       now apply (extensional_splice_all_eq f Hfext).
  - exact Hfcucts.
Qed.

Lemma uniformly_continuous_implies_effectively_uniformly_continuous_cantor : 
  (DecidableConstantsT (N->B)) -> 
    forall f, Extensional f -> uniformly_continuous_cantor f -> effectively_uniformly_continuous_cantor f.
Proof.
  intros Hdeco f Hfext Hfcts.
  apply constructive_indefinite_ground_description_nat.
  - intro n.
    exact (decidable_constants_implies_uniformly_decidable_fromT Hdeco f Hfext n).
  - now apply Hfcts.
Qed.

Theorem decidable_constants_continuous_implies_uniformly_continuous_cantor :
  (BrouwersFanPrinciple) -> (DecidableConstantsT (N -> B)) ->
    forall f, Extensional f -> continuous_cantor f -> uniformly_continuous_cantor f.
Proof.
  unfold BrouwersFanPrinciple, DecidableConstants.
  unfold continuous_cantor, uniformly_continuous_cantor.
  intros Hfan Hdeco f Hfext Hctsf.
  set (falses := fun (_ : N) => (false : B)).
  set (P := fun alpha n => forall beta, eqv_up_to n alpha beta -> f alpha = f beta).
  assert (forall alpha n, decidableT (P alpha n)) as HPndec. {
    intros alpha n. unfold P. now apply decidable_constants_implies_decidable_fromT.
  }
  set (M := fun alpha => constructive_indefinite_ground_description_nat (P alpha) (HPndec alpha) (Hctsf alpha)).
  pose proof (continuous_implies_effectively_continuous_cantor Hdeco f Hctsf) as Hectsf.
  unfold effectively_continuous_cantor in *.
Admitted.

From Stdlib Require Import Logic.ChoiceFacts.

Theorem cc : (forall f, effectively_continuous_ninf f) -> (forall f, classically_continuous_cantor f).
Proof.
  assert (DecidableConstants (N->B)) as Hdeco. admit.
  assert (MarkovsPrinciple N) as Hmp. admit.
  assert (ChoiceFacts.FunctionalCountableChoice_on (N->B)) as Hchoice. admit.
  assert (forall (p : (N -> B) -> Prop), (clexists alpha, p alpha) -> exists alpha, (p alpha)) as Hclex. admit.
  unfold MarkovsPrinciple in Hmp.
  unfold effectively_continuous_ninf, classically_continuous_cantor.
  intros Hcsf.
  intros f alpha. intro Hdcf.
  assert (Extensional f) as Hfext. admit.
  assert (forall n, clexists beta, (eqv_up_to n alpha beta /\ f alpha <> f beta)) as Hclbe. {
    intro n. specialize (Hdcf n). 
    intros Hax. apply Hdcf; clear Hdcf. intro beta; specialize (Hax beta).
    intro Hab. 
    destruct (bool_dec (f alpha) (f beta)). assumption.
    exfalso. apply Hax. split. assumption. assumption.
  }
  assert (forall n, exists beta, (eqv_up_to n alpha beta /\ f alpha <> f beta)) as Hbe. {
    intro n; now apply Hclex. 
  }
  apply Hchoice in Hbe as [be Hbe].
  assert (forall (u : Ninf) n, (u n = false) -> { m | u = Ninf_finite m }). {
    intros u n Hun. assert (exists m, u = Ninf_finite m). 
    apply (Ninf_false_implies_is_finite u). exists n. exact Hun.
    apply constructive_indefinite_ground_description_nat.
    intro m. apply Ninf_eq_fin_dec. exact H.
  }  
  set (bes := fun (u:Ninf) (n:N) => 
    match (bool_dec (u n) false) with | left p => be (proj1_sig (H u n p)) n | right _ => alpha n end).
  assert (forall (m n : N), bes (fin m) n = be m n) as Hbefin. {
    intros m n. unfold bes.
    destruct (bool_dec (fin m n) false) as [Hf|Ht].
    pose proof (proj1 (Ninf_finite_le_iff m n) Hf) as Hmlen.
    f_equal. destruct (H (fin m) n Hf) as [l Hl].
    simpl. now apply Ninf_finite_inj.
    rewrite -> not_false_iff_true in Ht.
    pose proof (proj1 (Ninf_finite_gt_iff m n) Ht) as Hnltm.
    pose proof (proj1 (Hbe m)) as Hbem.
    now apply Hbem. 
  }
  assert (forall n, bes inf n = alpha n) as Hbeinf. {
    unfold bes. intro n.
    destruct (bool_dec (inf n) false) as [Hf|Ht].
    unfold inf in Hf; simpl in Hf. contradiction (diff_true_false Hf).
    reflexivity.
  }
  set (g := fun u => f (bes u)).
  assert (forall m, g (fin m) = f (be m)) as Hgfin. intro m. unfold g. apply Hfext. apply Hbefin. 
  assert (g inf = f alpha) as Hginf. unfold g. apply Hfext. apply Hbeinf.
  assert (forall m, g (fin m) <> g inf) as Hminf. {
    intro m; rewrite -> Hgfin, -> Hginf. symmetry. apply (proj2 (Hbe m)).
  }
  destruct (Hcsf g) as [m Hm].
  apply (Hminf m). apply Hm. exact (Nat.le_refl m).
Admitted.


Open Scope Ninf_scope.


Lemma classically_discontinuous_iff_not_classically_continuous_ninf :
  forall f, classically_discontinuous_ninf f <-> ~ classically_continuous_ninf f.
Proof.
  unfold classically_continuous_ninf, classically_discontinuous_ninf.
  intro f; split.
  -intros Hdc Hc. apply Hc; clear Hc. 
   intro m; specialize (Hdc m).
   intro Hc; apply Hdc; clear Hdc.
   intro n; specialize (Hc n).
   intro Hdc; destruct Hdc as [Hmlen Hfn].
   exact (Hfn (Hc Hmlen)).
 - intro Hnc.
   intros m Hc.
   apply Hnc; clear Hnc.
   intro Hnc; specialize (Hnc m).
   apply Hnc; clear Hnc. intro n; specialize (Hc n).
   intro Hmlen.
   assert (~ (f n <> f inf)) as Hnnr.
   intro Hfn. apply Hc. split. exact Hmlen. exact Hfn.
   remember (f inf) as finf; destruct finf.
   destruct (f n). reflexivity. exfalso. apply Hnnr. auto.  
   destruct (f n). exfalso; apply Hnnr; intro Hf; discriminate. reflexivity.
Qed.

Lemma not_not_classically_continuous_implies_classically_continuous_ninf :
  forall f, ~ (~classically_continuous_ninf f) -> classically_continuous_ninf f.
Proof.
  intros f Hnncf Hdcf.
  apply Hnncf; clear Hnncf; intro Hcf; apply Hcf; clear Hcf. assumption.
Qed.

Lemma classically_continuous_iff_not_classically_discontinuous_ninf :
  forall f, classically_continuous_ninf f <-> ~ classically_discontinuous_ninf f.
Proof.
  intro f; split.
  - intros Hc Hdc. now apply classically_discontinuous_iff_not_classically_continuous_ninf in Hdc.
  - intro Hndc. apply not_not_classically_continuous_implies_classically_continuous_ninf.
    intro Hnc; apply Hndc; clear Hndc. now apply classically_discontinuous_iff_not_classically_continuous_ninf.
Qed.

Conjecture effective_continuity_principle_ninf_implies_cantor : 
  (forall f, effectively_continuous_ninf f) -> 
    (forall f, effectively_continuous_cantor f).

Theorem effective_continuity_principle_cantor_implies_ninf : 
  (forall f, effectively_continuous_cantor f) -> 
    (forall f, effectively_continuous_ninf f).
Proof.
  unfold effectively_continuous_cantor, effectively_continuous_ninf.
  intro Hncan.
  intros f.
  set (rf := fun (a : N -> B) => f (Ninf_retr a)).
  set (alpha := inf).
  specialize (Hncan rf alpha).
  destruct Hncan as [n Hn].
  exists n.
  intros m Hnlem.
  symmetry.
  set (beta := fin m).
  specialize (Hn beta).
  replace beta with (Ninf_retr beta) by now apply Ninf_retr_is_retract.
  replace alpha with (Ninf_retr alpha) by now apply Ninf_retr_is_retract.
  apply Hn.
  intros i Hiltn.
  unfold all_true, false_from; simpl.
  apply eq_sym; apply Nat.ltb_lt. 
  now apply (Nat.lt_le_trans _ n _).
Qed.

Theorem uniform_effective_continuity_principle_cantor_implies_ninf : 
  (forall f, effectively_uniformly_continuous_cantor f)-> 
    (forall f, effectively_continuous_ninf f).
Proof.
  unfold effectively_continuous_ninf, effectively_uniformly_continuous_cantor.
  intro Hncan.
  intros f.
  set (rf := fun (a : N -> B) => f (Ninf_retr a)).
  specialize (Hncan rf).
  destruct Hncan as [n Hn].
  exists n.
  intros m Hnlem.
  symmetry.
  set (alpha := (inf)).
  set (beta := (fin m)).
  specialize (Hn alpha beta).
  unfold rf, alpha, beta in Hn.
  replace beta with (Ninf_retr beta) by now apply Ninf_retr_is_retract.
  replace alpha with (Ninf_retr alpha) by now apply Ninf_retr_is_retract.
  apply Hn.
  intros i Hiltn.
  unfold all_true, false_from; simpl.
  apply eq_sym; apply Nat.ltb_lt.
  set (ralpha := Ninf_retr alpha).
  now apply (Nat.lt_le_trans _ n).
Qed.


Conjecture cantor_has_uniform_effective_continuity : 
  forall f, effectively_uniformly_continuous_cantor f.

Close Scope nat_scope.


Open Scope Ninf_scope.

#[local]
Lemma forall_ge_iff (r : N -> Prop) :
  forall m, (forall n, (m <= n)%nat -> r n) <-> (forall n, (fin m <= fin n) -> r n).
Proof. intro m; split. all: intros H n Hmn; apply H; now apply Ninf_le_nat. Qed.

#[local]
Lemma forall_ge_impl (r : Ninf -> Prop) :
  forall m : N, (forall v : Ninf, (fin m <= v) -> r v) -> (forall n : N, (m <= n)%nat -> r (fin n)).
Proof. intro m; intros H n Hmn; apply H; now apply Ninf_le_nat. Qed.



(* Eq1 from "Constructive continuity" *)
Lemma p_eps_p_true_iff : forall (p : Ninf -> B), 
  (p (eps p) = true) <-> (forall u, p u = true).
Proof.
  pose proof extended_nat_selection_function as Heps.
  unfold is_selection_function in Heps.
  intro p; split.
  - exact (Heps p).
  - intro H; exact (H (eps p)).
Qed.

(* Eq2 from "Constructive continuity" *)
Lemma p_eps_p_false_iff : forall (p : Ninf -> B), 
  (p (eps p) = false) <-> (exists u, p u = false).
Proof.
  pose proof extended_nat_selection_function as Heps.
  unfold is_selection_function in Heps.
  intro p; split.
  - intro Hpepsp; exists (eps p); exact Hpepsp.
  - intros [u Hpuf].
    apply not_true_iff_false; intro Hpepsp.
    revert Hpuf; apply not_false_iff_true.
    exact (Heps p Hpepsp u).
Qed.

(* Eq3 from "Constructive continuity" *)
Lemma clexists_implies_exists_ninf : forall (p : Ninf -> B),
  (clexists u, p u = false) -> (exists u, p u = false).
Proof.
  intros p Hcleu.
  pose proof (extended_nat_lpo_bool p) as Hlpo.
  destruct Hlpo as [Hepuf|Haput].
  - now apply ex_of_sig.
  - exfalso. apply Hcleu; clear Hcleu.
    intro u; specialize (Haput u).
    now apply not_false_iff_true.
Qed.

(* Theorem 8.2 from "Omniscient sets in constructive mathematics".
Lemma wlpo_ninf_restr_nat : forall p : Ninf -> B, 
  {forall n : N, p (fin n) = true} + {~ forall n : N, p (fin n) = true}.
*)

Definition bool_of_decidable {p : Prop} : {p} + {~p} -> B :=
  fun dp => match dp with | left _ => true | right _ => false end.



Lemma E3_1 : forall q : Ninf -> Ninf -> B,
  (forall m, clexists n, q (fin m) (fin n) = false)
              \/ (clexists m, forall n, q (fin m) (fin n) = true).
Proof.
  intro q.
  set ( p := fun u => negb (bool_of_decidable (wlpo_ninf_restr_nat (q u))) ).
  pose proof (wlpo_ninf_restr_nat p) as Hr. 
  destruct Hr as [Ht|Hf].
  - left.
    unfold p, bool_of_decidable in Ht; clear p; simpl in Ht.
    intro m; specialize (Ht m). 
    apply negb_true_iff, sumbool_is_false in Ht.
    intro Hf; apply Ht; clear Ht.
    intro n; specialize (Hf n).
    exact (proj1 (not_false_iff_true _) Hf).
  - right. 
    unfold p, bool_of_decidable in Hf; clear p; simpl in Hf.
    intro Ht; apply Hf; clear Hf. 
    intro m; specialize (Ht m).
    apply negb_true_iff, sumbool_of_false.
    exact Ht.
Qed.




Theorem E3_2 : forall f : Ninf -> B, 
  classically_continuous_ninf f \/ classically_discontinuous_ninf f.
Proof.
  unfold classically_continuous_ninf, classically_discontinuous_ninf.
  intro f.
  set ( q := fun (u v : Ninf) => eqb (f (max u v)) (f inf) ).
  pose proof (E3_1 q) as Hq.
  unfold q in Hq. destruct Hq as [Hq|Hq].
  - right. 
    intro m; specialize (Hq m).
    intros Hr; apply Hq; clear Hq.
    intro n; specialize (Hr (Nat.max m n)).
    intro Hf; apply Hr; clear Hr.
    rewrite -> eqb_false_iff, Ninf_max_of_nat in Hf.
    split. exact (Nat.le_max_l m n). exact Hf.
  - left.
    apply (clexists_forall_impl Hq). intros m n. 
    intros Hm Hmlen.
    rewrite -> eqb_true_iff, -> Ninf_max_of_nat in Hm.
    rewrite -> (Nat.max_r _ _ Hmlen) in Hm.
    exact Hm.
Qed.

Definition p (f : Ninf -> B) : Ninf -> B := 
  fun v => negb (A (fun u => eqb (f (max u v)) (f inf))).

Lemma p_spec : forall f v,
  p f v = false <-> forall u, f (max u v) = f inf.
Proof.
  intros f v. unfold p. rewrite -> negb_false_iff. rewrite -> A_spec_true.
  split. 
  - intros H u; specialize (H u). now rewrite -> eqb_true_iff in H.
  - intros H u; specialize (H u). now rewrite -> eqb_true_iff.
Qed.

Definition F : (Ninf -> B) -> Ninf :=
  fun f => eps (p f).


(* Lemma 3.3 *)
Lemma F_spec : 
  forall f : Ninf -> B, 
      (forall w, f (max (F f) w) = f inf) /\ 
        forall v, (forall w, f (max w v) = f inf) -> (F f) <= v.
Proof.
  intro f.
  unfold F.
  pose proof (eps_is_infemum (p f)) as [Hlb Hglb].
  split.
  - intro v; rewrite -> Ninf_max_symm; revert v.
    apply p_spec.
    apply p_eps_p_false_iff.
    exists inf.
    unfold p.
    apply negb_false_iff.
    apply A_spec_true.
    intro u.
    apply eqb_true_iff.
    now rewrite -> (Ninf_max_inf_r u).
  - intros v Hw. apply Hlb.
    apply p_spec.
    exact Hw.
Qed.



Lemma Ninf_ge_impl_max (f : Ninf -> B) (m : N) : 
  (forall n : N, (m <= n)%nat -> f (fin n) = f inf)
    -> (forall w : Ninf, f (max w (fin m)) = f inf).
Proof.
  intros Hl.
  set (p := fun w : Ninf => orb (negb ((Ninf_succ w) m)) (eqb (f w) (f inf))).
  pose proof (extended_nat_lpo_bool p) as Hlpo; unfold LPOBool in Hlpo.
  destruct Hlpo as [He|Ha].
  - destruct He as [x Hpx].
    unfold p in Hpx; clear p.
    rewrite -> orb_false_iff in Hpx.
    rewrite -> negb_false_iff in Hpx.
    rewrite -> eqb_false_iff in Hpx.
    destruct Hpx as [Hpmx Hfxnefinf].
    apply Ninf_succ_le_fin_l in Hpmx.
    exfalso; apply Hfxnefinf; f_equal.
    apply Ninf_not_finite_implies_infinite.
    intros n Hxn.
    rewrite -> Hxn in Hfxnefinf.
    apply Hfxnefinf; clear Hfxnefinf.
    apply Hl.
    rewrite -> Hxn in Hpmx.
    now apply Ninf_le_nat.
  - unfold p in Ha; clear p.
    intro w; specialize (Ha w).
    rewrite -> orb_true_iff in Ha.
    rewrite -> negb_true_iff in Ha.
    rewrite -> eqb_true_iff in Ha.
    destruct Ha as [Hwm|Hwinf].
    -- apply Ninf_le_fin_r, Ninf_le_succ_l_le in Hwm.
       specialize (Hl m (Nat.le_refl m)); rewrite <- Hl.
       f_equal. now apply Ninf_max_r.
    -- destruct (Ninf_le_fin_dec w m) as [Hwlem|Hmltw].
       --- rewrite -> (proj1 (Ninf_max_r w _) Hwlem).
           exact (Hl m (Nat.le_refl m)).
       --- apply Ninf_nle_ge in Hmltw.
           now rewrite -> (proj1 (Ninf_max_l w (fin m)) Hmltw).
Qed.

(* _classical_continuous *)
Corollary classically_continuous_ninf_iff :
  forall f : Ninf -> B, classically_continuous_ninf f <->
    exists u, (u <> inf /\ forall v, u <= v -> f v = f inf).
Proof.
  unfold classically_continuous_ninf.
  intro f.
  split.
  - pose proof (F_spec f) as Hf.
    intros Hm.
    exists (F f).
    split.
    -- intro Hvinf.
       destruct Hf as [_ Hf].
       rewrite -> Hvinf in Hf.
       apply Hm; clear Hm. intros m Hnm.
       specialize (Hf (fin m)).
       apply (Ninf_not_le_inf_finite m); apply Hf; clear Hf.
       now apply Ninf_ge_impl_max.
    -- apply Ninf_max_impl_ge. exact (proj1 Hf).
  - intros [u [Hui Hv]]; intro Hm.
    apply Hui; apply Ninf_not_finite_implies_infinite.
    intros m Hum; rewrite -> Hum in Hv; clear Hum Hui u.
    apply (Hm m); clear Hm.
    now apply (forall_ge_impl (fun v => f v = f inf)).
Qed.


Corollary classical_continuous_implies_continuous_ninf : 
  MarkovsPrinciple N -> forall f : Ninf -> B,
    classically_continuous_ninf f -> continuous_ninf f.
Proof.
  unfold continuous_ninf, MarkovsPrinciple.
  intros Hmp f Hccf.
  apply classically_continuous_ninf_iff in Hccf.
  destruct Hccf as [u [Hucfin Hv]].
  apply not_infinite_implies_classically_finite in Hucfin.
  assert { m | u = fin m} as Hufin. {
    apply constructive_indefinite_ground_description_nat.
    intro n; now apply Ninf_eq_fin_dec. 
    apply Hmp. intro m. apply or_of_sumbool; now apply Ninf_eq_fin_dec. exact Hucfin.
  }
  destruct Hufin as [m Hum]; exists m.
  rewrite -> Hum in Hv. now apply (forall_ge_impl (fun v => f v = f inf)).
Qed.



#[local]
Lemma p_dec : forall {f : Ninf -> Prop}, forall (f_dec : forall (u : Ninf), {f u} + {~ f u}), forall m : N,
  let p := (forall n, (m <= n)%nat -> f (fin n)) in {p} + {~p}. 
Proof. 
  intros f f_dec m. unfold p.
  pose proof (wlpo_ninf_restr_nat_dec (fun u => m <= u -> f u)) as Hq. destruct Hq as [Hq|Hq].
  - intro u. destruct (Ninf_ge_fin_dec m u); destruct (f_dec u).
    2: right; tauto. all: left; tauto.
  - left. now apply forall_ge_iff.
  - right. intro Hp; apply Hq. now apply forall_ge_iff.
Qed.


Corollary classically_continuous_implies_continuous_ninf : 
  MarkovsPrinciple N -> forall f : Ninf -> B,
    classically_continuous_ninf f -> continuous_ninf f.
Proof.
  unfold classically_continuous_ninf, continuous_ninf, MarkovsPrinciple.
  intros Hmp f Hccf.
  apply Hmp.
  - intro m. apply or_of_sumbool. 
    now apply (p_dec (fun u => bool_dec (f u) (f inf))).
  - exact Hccf.
Qed.

Corollary continuous_implies_effectively_continuous_ninf : 
  forall f : Ninf -> B,
    continuous_ninf f -> effectively_continuous_ninf f.
Proof.
  unfold continuous_ninf, effectively_continuous_ninf.
  intros f Hcf.
  apply constructive_indefinite_ground_description_nat.
  2: exact Hcf.
  intros m.
  set (p := fun u => (m <= u) -> f u = f inf).
  assert (forall u, {p u} + {~ p u}) as Hpdec. {
    intro u. unfold p. destruct (Ninf_ge_fin_dec m u) as [Hmleu|Hulem].
    - destruct (bool_dec (f u) (f inf)) as [He|Hn].
      -- left. auto.
      -- right. intro Hl; apply Hn. apply Hl. exact Hmleu.
    - left. intro Hmleu. contradiction.
  }
  pose proof (wlpo_ninf_restr_nat_dec _ Hpdec) as Hf. unfold p in Hf; destruct Hf as [Hf|Hf].
  - left. now apply forall_ge_iff. 
  - right. intros Hfn; apply Hf. now apply forall_ge_iff. 
Qed. 

Definition g (f : Ninf -> B) (v : Ninf) : Ninf :=
  eps (fun u => eqb (f (max u v)) (f inf)).

Definition G (f : Ninf -> B) (v : Ninf) : Ninf :=
  max (g f v) v.

(* Lemma 3_6 from "Constructive Continuity" *)
Lemma G_ge : forall f v, v <= G f v.
Proof. intros f v. unfold G. apply Ninf_le_max_r. Qed.
 
Lemma g_spec : forall (f :  Ninf -> B) (v : Ninf),
  (clexists u, (v <= u /\ f u <> f inf)) -> (f (max (g f v) v) <> f inf).
Proof. 
  intros f.
  assert (forall (v : Ninf), (exists u, f (max u v) <> f inf) -> (f (max (g f v) v) <> f inf)) as Eq10. {
    intros v Hv.
    destruct Hv as [u Hu].
    remember (fun u => eqb (f (max u v)) (f inf)) as p eqn:Hp.
    unfold g.
    rewrite <- Hp.
    assert (p u = false) as Hpu. {
      rewrite -> Hp; simpl.
      apply eqb_false_iff.
      exact Hu.
    }
    assert (p (eps p) = false) as Hpepsp. {
      apply p_eps_p_false_iff. exists u; exact Hpu.
    }
    remember (eps p) as epsp; clear Heqepsp.
    rewrite -> Hp in Hpepsp.
    apply eqb_false_iff in Hpepsp.
    exact Hpepsp.
  }
  intros v; specialize (Eq10 v).
  intro Hclu. apply Eq10; clear Eq10.
  (* Need a boolean function to use clexists_implies_exists *)
  assert (exists u, eqb (f (max u v)) (f inf) = false) as Heu. {
    apply clexists_implies_exists_ninf.
    apply (clexists_impl Hclu); intro u; intros [Hvu Huinf]. 
    apply eqb_false_iff.
    rewrite -> (proj1 (Ninf_max_l u v) Hvu).
    exact Huinf.
  }
  clear Hclu.
  apply (exists_impl Heu); intros u Hu. 
  apply eqb_false_iff in Hu. exact Hu.
Qed.


Lemma G_spec : forall (f :  Ninf -> B) (v : Ninf), 
  (clexists u, (v <= u /\ f u <> f inf)) -> (f (G f v) <> f inf).
Proof. unfold G; exact g_spec. Qed.

Lemma not_sig_of_false {X : Type} (p : X -> Prop) : (forall x, ~ p x) -> { x | p x } -> False.
Proof. intros Hna He. destruct He as [x px]. exact (Hna x px). Qed. 

Lemma not_all_of_not_sig {X : Type} (p : X -> Prop) : ({ x | p x } -> False) -> (forall x, ~ p x).
Proof. intros Hne x px. apply Hne. exists x. exact px. Qed.

Theorem exists_classically_discontinuous_implies_wlpo_ninf :
  { f : Ninf -> B | classically_discontinuous_ninf f} -> (WLPOBool N).
Proof.
  unfold classically_discontinuous_ninf, WLPOBool.
  intros [f Hf].
  (* Eq11 *)
  assert (forall n, f (G f (fin n)) <> f inf) as HfGn. {
    intro n. apply G_spec. specialize (Hf n).
    intro Hu; apply Hf; clear Hf. 
    intros m; specialize (Hu (fin m)).
    intro Hm; apply Hu; clear Hu.
    split. apply Ninf_le_nat; exact (proj1 Hm). exact (proj2 Hm).
  }
  clear Hf.
  (* Eq12 *)
  assert (forall u, u = inf <-> f (G f u) = f inf) as HfGu. {
    intro u. split.
    - intro Hu. rewrite -> Hu. unfold G.
      now rewrite -> (proj1 (Ninf_max_r _ inf) (Ninf_le_inf _)).
    - intros Hu. apply Ninf_not_finite_implies_infinite. 
      intros n Hn. apply (HfGn n). rewrite <- Hn. exact Hu.
  }
  clear HfGn.
  assert (forall u, { u <> inf } + { u = inf }) as Huinfdec. {
    intro u; specialize (HfGu u).
    destruct (Decidable_eq_bool (f (G f u)) (f inf)) as [b Hb].
    destruct b.
    - right; apply HfGu, Hb; reflexivity.
    - left. intro Hu. apply HfGu, Hb in Hu. discriminate Hu.
  }
  intro p.
  set (u := Ninf_retr p).
  assert (u = inf -> forall n, p n = true) as Hupinf. {
    intro Hu; unfold u in Hu.
    apply Ninf_retr_eq_inf; exact Hu.
  }
  assert ( { n | u = fin n } -> { m : N | p m = false }) as Hupfin. {
    intros [n Hu].
    unfold u in Hu.
    apply Ninf_retr_eq_fin in Hu. 
    exists n; exact (proj1 Hu).
  }
  destruct (Huinfdec u) as [Hufin|Huinf].
  - right.
    intros Hpinf; apply Hufin; clear Hufin. 
    apply Ninf_not_finite_implies_infinite.
    intros n Hun.
    pose proof (exist (fun n => u = fin n) n Hun) as sigu. 
    pose proof (Hupfin sigu) as Hpm.
    destruct Hpm as [m Hpm]; specialize (Hpinf m).
    now apply (eq_true_false_abs (p m)).
  - left. apply Hupinf. exact Huinf.
Qed.

Theorem wlpo_implies_exists_classically_discontinuous_ninf : (WLPOBool N) -> 
  {f : Ninf -> B | classically_discontinuous_ninf f}.
Proof.
  intros Hwlpo.
  assert (forall u, { u = inf} + { u <> inf })  as Hu. {
    intro u.
    pose proof (Hwlpo (seq u)) as Hu.
    destruct Hu as [Huinf|Hufin].
    - left. apply Ninf_extensionality. auto.
    - right. intro Hu. apply Hufin. now rewrite -> Hu.
  }
  set (f := fun u => negated_boolean_proposition (Hu u)).
  exists f. intro m.
  intro Hn. apply (Hn m); clear Hn.
  split. apply Nat.le_refl.
  unfold f, negated_boolean_proposition; simpl.
  destruct (Hu (fin m)) as [Hum|Hum]; destruct (Hu inf) as [Huinf|Huinf].
  - now apply Ninf_finite_not_inf in Hum.
  - now apply diff_false_true.
  - now apply diff_true_false.
  - tauto.
Qed.


Theorem not_wlpo_implies_classical_continuity_ninf : (WLPOBool N -> False) <->
  forall f : Ninf -> B, classically_continuous_ninf f.
Proof.
  split.
  - intros nwlpo f.
    pose proof exists_classically_discontinuous_implies_wlpo_ninf as H.
    apply classically_continuous_iff_not_classically_discontinuous_ninf.
    intro Hdcf. apply nwlpo. apply H.
    exists f; exact Hdcf.
  - intros Hc Hwlpo.
    apply wlpo_implies_exists_classically_discontinuous_ninf in Hwlpo.
    destruct Hwlpo as [f Hdcf].
    specialize (Hc f).
    apply classically_discontinuous_iff_not_classically_continuous_ninf in Hdcf; contradiction.
Qed.

Corollary not_wlpo_implies_continuity_ninf : (WLPOBool N -> False) -> MarkovsPrinciple N ->
  forall f : Ninf -> B, continuous_ninf f.
Proof.
  intros Hnwlpo Hmp f. apply classical_continuous_implies_continuous_ninf. 
  exact Hmp. apply not_wlpo_implies_classical_continuity_ninf. exact Hnwlpo.
Qed.


Theorem not_wlpo_implies_classical_continuity_ninf_to_ninf : (WLPOBool N -> False) ->
  forall f : Ninf -> Ninf, classically_continuous_ninf_to_ninf f.
Proof.
  unfold classically_continuous_ninf_to_ninf.
  intros Hnwlpo f. split.
  - intros l Hfinf; destruct l.
    -- (* Handle case l=0 separately *)
       intro Hf; specialize (Hf 0%nat); apply Hf; clear Hf. intros n _. now apply Ninf_le_0_l.
    -- (* Case l=succ l' *)
       set (fl := fun v => seq (f v) l).
       pose proof (proj1 not_wlpo_implies_classical_continuity_ninf Hnwlpo fl) as Hfel.
       unfold classically_continuous_ninf, fl in Hfel.
       apply (clexists_impl Hfel); intros m Hfelm.
       apply (forall_implies_r Hfelm); intros n Hfelmn.
       apply Ninf_gt_fin_l. rewrite -> Hfelmn. apply Ninf_gt_fin_l. exact Hfinf.
  - intros k Hfinf. 
    set (fk := fun v => f v k). 
    pose proof (proj1 not_wlpo_implies_classical_continuity_ninf Hnwlpo fk) as Hfek.
    unfold classically_continuous_ninf in Hfek.
    apply (clexists_impl Hfek); intros m Hfekm.
    apply (forall_implies_r Hfekm); intros n Hfkmn.
    apply Ninf_le_fin_r. unfold fk in Hfkmn. rewrite -> Hfkmn. apply Ninf_le_fin_r. exact Hfinf.
Qed.

Lemma classical_continuous_implies_continuous_ninf_to_ninf : 
  MarkovsPrinciple N -> forall f : Ninf -> Ninf,
    classically_continuous_ninf_to_ninf f -> continuous_ninf_to_ninf f.
Proof.
  unfold classically_continuous_ninf_to_ninf, continuous_ninf_to_ninf, MarkovsPrinciple.
  intros Hmp f Hccf.
  split.
  - intros l Hl. apply Hmp. set (p := fun u => Ninf_ge_fin_dec l (f u)).
    intro m; apply or_of_sumbool. now apply (p_dec p). now apply (proj1 Hccf).
  - intros k Hk. apply Hmp. set (p := fun u => Ninf_le_fin_dec (f u) k). 
    intro m; apply or_of_sumbool. now apply (p_dec p). now apply (proj2 Hccf).
Qed.

Corollary not_wlpo_implies_continuity_ninf_to_ninf : (WLPOBool N -> False) -> MarkovsPrinciple N ->
  forall f : Ninf -> Ninf, continuous_ninf_to_ninf f.
Proof.
  intros Hnwlpo Hmp f. apply classical_continuous_implies_continuous_ninf_to_ninf . 
  exact Hmp. apply not_wlpo_implies_classical_continuity_ninf_to_ninf . exact Hnwlpo.
Qed.



Proposition continuous_ninf_to_ninf_not_inf : forall f : Ninf -> Ninf, 
  continuous_ninf_to_ninf f -> MarkovsPrinciple N ->
    f inf <> inf -> exists m, forall n, (m <= n)%nat -> f n <> inf.
Proof.
  intros f Hcts Hmp. unfold continuous_ninf_to_ninf in Hcts.
  destruct Hcts as [_ Hcts].
  intros Hfinf.
  assert (exists k : N, f inf = k) as Hfinfk. {
    apply Hmp.
    intro m; apply or_of_sumbool; now apply Ninf_eq_fin_dec.
    intro Hffin; apply Hfinf; clear Hfinf.
    now apply Ninf_not_finite_implies_infinite.
  }
  destruct Hfinfk as [k Hfinfk].
  assert (f inf <= k) as Hfinflek. {
     rewrite -> Hfinfk; now apply Ninf_le_refl.
  }
  specialize (Hcts k Hfinflek).
  destruct Hcts as [m Hctsm]; exists m.
  apply (forall_implies_r Hctsm); intros n Hctsmn.
  intros Hfninf; rewrite -> Hfninf in Hctsmn. 
  exact (Ninf_not_le_inf_finite _ Hctsmn).
Qed.

Close Scope Ninf_scope.
