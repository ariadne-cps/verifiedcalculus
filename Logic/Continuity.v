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


Require Import ExtendedNat.
Require Import Omniscience.

Notation "'clexists' x , P" := ( ~ (forall x, ~ (P )) ) (at level 78).

Lemma exists_implies_classical_exists : forall {X : Type} (p : X -> Prop),
  (exists x, p x) -> (clexists x, p x).
Proof. intros X p He Hnpx. destruct He as [x Hpx]. exact (Hnpx x Hpx). Qed.

Lemma forall_impl {X : Type} (p q : X -> Prop) :
  (forall x, p x -> q x) -> (forall x, p x) -> (forall x, q x).
Proof. intros Hpq Hp. intro x; specialize (Hp x). exact (Hpq x Hp). Qed.

Lemma clexists_impl {X : Type} (p q : X -> Prop) :
  (forall x, p x -> q x) -> (clexists x, p x) -> (clexists x, q x).
Proof. intros Hpq Hp. intro Hq; apply Hp; clear Hp. intro x; specialize (Hq x). 
  intro Hp; apply Hq; clear Hq. exact (Hpq x Hp). Qed.

Lemma forall_clexists_impl {X  Y: Type} (p q : X -> Y -> Prop) :
  (forall x y, p x y -> q x y) -> (forall x, clexists y, p x y) -> (forall x, clexists y, q x y).
Proof. intros Hpq. apply forall_impl; intro x. apply clexists_impl; intro y. exact (Hpq x y). Qed.

Lemma clexists_forall_impl {X  Y: Type} (p q : X -> Y -> Prop) :
  (forall x y, p x y -> q x y) -> (clexists x, forall y, p x y) -> (clexists x, forall y, q x y).
Proof. intros Hpq. apply clexists_impl; intro x. apply forall_impl; intro y. exact (Hpq x y). Qed.

(* Markov's principle for a type X. 
 * Note that Markov's principle for N states that 
 * given an algorithm that does not terminate, 
 * we can find the number of steps at which it terminates.
 * This is valid in some constructive mathematics, but is unprovable in Rocq.
 *)
Definition MarkovsPrinciple (X : Type) := forall p : X -> Prop, (forall x : X, {p x} + {~ p x}) ->
  (~ forall x, ~ p x) -> { x | p x}.

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
  forall k, (k < n)%nat -> a k = b k.

(* forall boolean quantifier. Note this is "E" from "Constructive continuity". *)
Definition A (p : Ninf -> B) : B := p (eps p).
Lemma A_spec_false : forall p, A p = false <-> exists u, p u = false.
Proof.
  set (Heps := (extended_nat_selection_function)).
  pose proof (exists_iff_search eps Heps) as Hexists.
  intro p; specialize (Hexists p).
  unfold A; apply iff_sym; exact Hexists.
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

(* Continuity principles *)
Definition continuity_principle (W Y : Type) :=
  forall (f : (N -> W) -> Y), forall (alpha : N -> W), exists (n : N), forall (beta : N -> W),
    (eq_up_to n alpha beta) -> (f alpha = f beta).

Definition effective_continuity_principle (W Y : Type) : Type :=
  forall (f : (N -> W) -> Y), forall (alpha : N -> W), @sig N 
    ( fun (n : N) => ( forall (beta : N -> W),
      (eq_up_to n alpha beta) -> (f alpha = f beta) ) ).

Definition choice_continuity_principle (W Y : Type) :=
  fun (f : (N -> W) -> Y) (alpha : N -> W) => @sig N 
    ( fun (n : N) => ( forall (beta : N -> W),
      (eq_up_to n alpha beta) -> (f alpha = f beta) ) ).

(* Not sure what the relation between choice and effective versions is. *)


Definition uniform_continuity_principle (W Y : Type) :=
  forall (f : (N -> W) -> Y), exists (n : N), forall (alpha beta : N -> W),
    (eq_up_to n alpha beta) -> (f alpha = f beta).

Definition effective_uniform_continuity_principle (W Y : Type) :=
  forall (f : (N -> W) -> Y), @sig N 
    ( fun (n : N) => ( forall (alpha beta : N -> W), 
      (eq_up_to n alpha beta) -> (f alpha = f beta) ) ).


Definition effective_continuity_principle_cantor :=
  forall (f : (N -> B) -> B), forall (alpha : N -> B), @sig N 
    ( fun (n : N) => ( forall (beta : N -> B),
      (eq_up_to n alpha beta) -> (f alpha = f beta) ) ).

Definition uniform_effective_continuity_principle_cantor :=
  forall (f : (N -> B) -> B), @sig N 
    ( fun (n : N) => ( forall (alpha beta : N -> B),
      (eq_up_to n alpha beta) -> (f alpha = f beta) ) ).


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

Definition continuous_ninf_to_ninf (f : Ninf -> Ninf) :=
  (forall l, fin l <= f inf -> exists m, forall n, (m <= n)%nat -> fin l <= f (fin n))
    /\ (forall u, f inf <= fin u -> exists m, forall n, (m <= n)%nat -> f (fin n) <= fin u).

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
*)

Lemma discontinuous_iff_not_continuous_ninf :
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

Lemma not_not_continuous_implies_continuous_ninf :
  forall f, ~ (~classically_continuous_ninf f) -> classically_continuous_ninf f.
Proof.
  intros f Hnncf Hdcf.
  apply Hnncf; clear Hnncf; intro Hcf; apply Hcf; clear Hcf. assumption.
Qed.

Lemma continuous_iff_not_discontinuous_ninf :
  forall f, classically_continuous_ninf f <-> ~ classically_discontinuous_ninf f.
Proof.
  intro f; split.
  - intros Hc Hdc. now apply discontinuous_iff_not_continuous_ninf in Hdc.
  - intro Hndc. apply not_not_continuous_implies_continuous_ninf.
    intro Hnc; apply Hndc; clear Hndc. now apply discontinuous_iff_not_continuous_ninf.
Qed.

Conjecture effective_continuity_ninf_cantor : 
  effective_continuity_principle_ninf -> effective_continuity_principle_cantor.

Theorem effective_continuity_cantor_implies_ninf : 
  effective_continuity_principle_cantor -> effective_continuity_principle_ninf.
Proof.
  unfold effective_continuity_principle_ninf, effective_continuity_principle_cantor.
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
  replace beta with (Ninf_retr beta).
  replace alpha with (Ninf_retr alpha).
  apply Hn.
  intros i Hiltn.
  unfold all_true, false_from; simpl.
  apply eq_sym. apply Nat.ltb_lt. 
  set (ralpha := Ninf_retr alpha).
  now apply (Nat.lt_trans _ n).
  - now apply Ninf_retr_is_retract.
  - now apply Ninf_retr_is_retract.
Qed.

Theorem uniform_effective_continuity_cantor_ninf : 
  uniform_effective_continuity_principle_cantor -> effective_continuity_principle_ninf.
Proof.
  unfold effective_continuity_principle_ninf, uniform_effective_continuity_principle_cantor.
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
  replace beta with (Ninf_retr beta).
  replace alpha with (Ninf_retr alpha).
  apply Hn.
  intros i Hiltn.
  unfold all_true, false_from; simpl.
  apply eq_sym; apply Nat.ltb_lt.
  set (ralpha := Ninf_retr alpha).
  now apply (Nat.lt_trans _ n).
  - now apply Ninf_retr_is_retract.
  - now apply Ninf_retr_is_retract.
Qed.




Conjecture cantor_has_uniform_effective_continuity : 
  uniform_effective_continuity_principle_cantor.




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
    apply not_true_implies_false; intro Hpepsp.
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
    apply negb_true_iff, sumbool_false in Ht.
    intro Hf; apply Ht; clear Ht.
    intro n; specialize (Hf n).
    exact (not_false_implies_true _ Hf).
  - right. 
    unfold p, bool_of_decidable in Hf; clear p; simpl in Hf.
    intro Ht; apply Hf; clear Hf. 
    intro m; specialize (Ht m).
    apply negb_true_iff, sumbool_is_false.
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
    revert Hq. apply clexists_forall_impl. intros m n. 
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
    apply not_finite_implies_inf.
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
    apply Hui; apply not_finite_implies_inf.
    intros m Hum; rewrite -> Hum in Hv; clear Hum Hui u.
    apply (Hm m); clear Hm.
    intros n Hmlen.
    apply Hv. apply Ninf_le_nat. exact Hmlen.
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
    apply Hmp. intro m. now apply Ninf_eq_fin_dec. exact Hucfin.
  }
  destruct Hufin as [m Hum]; exists m.
  intros n Hmlen. apply Hv. 
  rewrite -> Hum. now apply Ninf_le_nat.
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
  - left. intros n Hmlen; apply Hf. now apply Ninf_le_nat.
  - right. intros Hfn; apply Hf. intros n Hmlen; apply Hfn. now apply Ninf_le_nat.
Qed. 

Definition g (f : Ninf -> B) (v : Ninf) : Ninf :=
  eps (fun u => eqb (f (max u v)) (f inf)).

Definition G (f : Ninf -> B) (v : Ninf) : Ninf :=
  max (g f v) v.

(* Lemma 3_6 from "Constructive Continuity" *)
Lemma G_ge : forall f v, v <= G f v.
Proof. intros f v. unfold G. apply Ninf_le_max_r. Qed.

Lemma exists_impl {X : Type} {p q : X -> Prop} :
  (forall x, p x -> q x) -> (exists x, p x) -> (exists x, q x).
Proof. intro Hpq. intros [x Hpx]; exists x. exact (Hpq x Hpx). Qed.
 
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
    revert Hclu; apply clexists_impl; intro u; intros [Hvu Huinf]. 
    apply eqb_false_iff.
    rewrite -> (proj1 (Ninf_max_l u v) Hvu).
    exact Huinf.
  }
  clear Hclu.
  revert Heu; apply exists_impl; intros u Hu. 
  apply eqb_false_iff in Hu. exact Hu.
Qed.


Lemma G_spec : forall (f :  Ninf -> B) (v : Ninf), 
  (clexists u, (v <= u /\ f u <> f inf)) -> (f (G f v) <> f inf).
Proof. unfold G; exact g_spec. Qed.

Lemma not_sig_of_false {X : Type} (p : X -> Prop) : (forall x, ~ p x) -> { x | p x } -> False.
Proof. intros Hna He. destruct He as [x px]. exact (Hna x px). Qed. 

Lemma not_all_of_not_sig {X : Type} (p : X -> Prop) : ({ x | p x } -> False) -> (forall x, ~ p x).
Proof. intros Hne x px. apply Hne. exists x. exact px. Qed.

Theorem exists_discontinuous_implies_wlpo_ninf :
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
    - intros Hu. apply not_finite_implies_inf. 
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
    apply not_finite_implies_inf.
    intros n Hun.
    pose proof (exist (fun n => u = fin n) n Hun) as sigu. 
    pose proof (Hupfin sigu) as Hpm.
    destruct Hpm as [m Hpm]; specialize (Hpinf m).
    now apply (eq_true_false_abs (p m)).
  - left. apply Hupinf. exact Huinf.
Qed.

Theorem wlpo_implies_exists_discontinuous_ninf : (WLPOBool N) -> {f : Ninf -> B | classically_discontinuous_ninf f}.
  intros Hwlpo.
  assert (forall u, { u = inf} + { u <> inf })  as Hu. {
    intro u.
    pose proof (Hwlpo (seq u)) as Hu. 
    destruct Hu as [Huinf|Hufin].
    - left. apply Ninf_eq, sequence_extensionality. auto.
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
  - intros nlpo f.
    pose proof exists_discontinuous_implies_wlpo_ninf as H.
    apply continuous_iff_not_discontinuous_ninf.
    intro Hdcf. apply nlpo. apply H.
    exists f; exact Hdcf.
  - intros Hc Hwlpo.
    apply wlpo_implies_exists_discontinuous_ninf in Hwlpo.
    destruct Hwlpo as [f Hdcf].
    specialize (Hc f).
    apply discontinuous_iff_not_continuous_ninf in Hdcf; contradiction.
Qed.

Theorem not_wlpo_implies_continuity_ninf : (WLPOBool N -> False) -> MarkovsPrinciple N ->
  forall f : Ninf -> B, continuous_ninf f.
Proof.
  intros Hnwlpo Hmp f. apply classical_continuous_implies_continuous_ninf. 
  exact Hmp. apply not_wlpo_implies_classical_continuity_ninf. exact Hnwlpo.
Qed.

Theorem not_wlpo_implies_continuity_ninf_to_ninf : (WLPOBool N -> False) -> MarkovsPrinciple N ->
  forall f : Ninf -> Ninf, continuous_ninf_to_ninf f.
Proof.
  unfold continuous_ninf_to_ninf.
  intros Hnwlpo Hmp f. split.
  - intro l; destruct l.
    -- (* Handle case l=0 separately *)
       intros _. exists 0%nat. intros n _. now apply Ninf_le_0_l.
    -- (* Case l=succ l' *)
       set (pl := fun v => seq (f v) l).
       pose proof (not_wlpo_implies_continuity_ninf Hnwlpo Hmp pl) as Hpl.
       unfold continuous_ninf in Hpl.
       destruct Hpl as [m Hplm]; intro HSl. exists m.
       intros n Hmlen. 
       specialize (Hplm n Hmlen).
       unfold pl in Hplm.
       apply Ninf_gt_fin_l. rewrite -> Hplm.
       apply Ninf_gt_fin_l. exact HSl.
  - set (p := fun k : N => f inf <= k -> exists m, forall n, (m <= n)%nat -> f n <= k).
    intros k Hfk. 
    set (fk := fun v => f v k). 
    pose proof (not_wlpo_implies_continuity_ninf Hnwlpo Hmp fk) as Hfek.
    unfold continuous_ninf in Hfek.
    destruct Hfek as [m Hfek]; exists m.
    intros n Hmlen; specialize (Hfek n Hmlen).
    apply Ninf_le_fin_r. unfold fk in Hfek. rewrite -> Hfek. apply Ninf_le_fin_r. exact Hfk.
Qed.


Proposition continuous_ninf_to_ninf_not_inf : forall f : Ninf -> Ninf, 
  continuous_ninf_to_ninf f -> MarkovsPrinciple N ->
    f inf <> inf -> exists m, forall n, (m <= n)%nat -> f n <> inf.
Proof.
  intros f Hcts Hmp. unfold continuous_ninf_to_ninf in Hcts.
  destruct Hcts as [_ Hcts].
  intros Hfinf.
  assert (exists k : N, f inf = k) as Hfinfk. {
    apply ex_of_sig; apply Hmp.
    intro m; now apply Ninf_eq_fin_dec.
    intro Hffin; apply Hfinf; clear Hfinf.
    now apply not_finite_implies_inf.
  }
  destruct Hfinfk as [k Hfinfk].
  assert (f inf <= k) as Hfinflek. {
     rewrite -> Hfinfk; now apply Ninf_le_refl.
  }
  specialize (Hcts k Hfinflek).
  destruct Hcts as [m Hctsm]; exists m.
  intros n Hmlen; specialize (Hctsm n Hmlen).
  intro Hfn. rewrite -> Hfn in Hctsm.
  exact (Ninf_not_le_inf_finite _ Hctsm).
Qed.

