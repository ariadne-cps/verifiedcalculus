(******************************************************************************
 * Copyright 2023 Pieter Collins
 *
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
 ******************************************************************************)


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Logic.ProofIrrelevance.

Require Import List.
Require Import Ensembles.

Require Import DependentChoice.

Require Export Monads.
Require Export SubMonads.
Require Export LimitMonads.

Require Export EnsembleMonad.



Section EnsembleMonads.

Record InhabitedEnsemble {A:Type} : Type :=
{
  subset : Ensemble A;
  subset_inhabited : inhabited subset;
}.

Lemma singleton_inhabited : forall {X : Type} (x : X), inhabited (singleton x).
Proof. intros X x. unfold inhabited, singleton. exists x. reflexivity. Qed.

Lemma image_inhabited : forall {X Y : Type} (fs : X -> Ensemble Y) (xs : Ensemble X),
  (forall x, inhabited (fs x)) -> (inhabited xs) -> inhabited (image fs xs).
Proof.
  intros X Y fs xs Hf Hx.
  unfold inhabited, image in *.
  destruct Hx as [x Hx].
  specialize (Hf x) as Hy.
  destruct Hy as [y Hy].
  exists y.
  exists x.
  split.
  - exact Hx.
  - exact Hy.
Qed.


Definition inhabited_singleton {X : Type} (x : X) : @InhabitedEnsemble X :=
  {| subset := singleton x;
     subset_inhabited := singleton_inhabited x; |}.
Definition inhabited_image {X Y : Type} (fs : X -> @InhabitedEnsemble Y) (xs : @InhabitedEnsemble X) : @InhabitedEnsemble Y :=
  {| subset := image (fun x => subset (fs x)) (subset xs);
     subset_inhabited := image_inhabited (fun x => subset (fs x)) (subset xs) (fun x => subset_inhabited (fs x)) (subset_inhabited xs); |}.


Lemma inhabited_subset_equality : forall {X : Type} (s1 s2 : @InhabitedEnsemble X),
  (subset s1) = (subset s2) -> s1 = s2.
Proof.
  intros X s1 s2.
  destruct s1 as [s1 s1ne].
  destruct s2 as [s2 s2ne].
  simpl.
  intros H.
  revert s1ne s2ne.
  rewrite <- H.
  intros s1ne s2ne.
  rewrite (proof_irrelevance _ s1ne s2ne).
  reflexivity.
Qed.

Lemma inhabited_subset_left_identity :
  forall {X Y : Type} (f : X -> @InhabitedEnsemble Y) (x : X),
    inhabited_image f (inhabited_singleton x) = f x.
Proof.
  intros A B f a.
  apply inhabited_subset_equality.
  simpl.
  rewrite -> ensemble_left_identity.
  reflexivity.
Qed.

Lemma inhabited_subset_right_identity :
  forall {X : Type} (xs : @InhabitedEnsemble X),
    inhabited_image (@inhabited_singleton X) xs = xs.
Proof.
  intros A a.
  apply inhabited_subset_equality.
  simpl.
  rewrite -> ensemble_right_identity.
  reflexivity.
Qed.

Lemma inhabited_subset_associativity :
  forall {X Y Z : Type} (xs : @InhabitedEnsemble X) (fs : X -> @InhabitedEnsemble Y) (gs : Y -> @InhabitedEnsemble Z),
    inhabited_image gs (inhabited_image fs xs) = inhabited_image (fun x => inhabited_image gs (fs x)) xs.
Proof.
  intros A B C x f g.
  apply inhabited_subset_equality.
  simpl.
  rewrite -> ensemble_associativity.
  reflexivity.
Qed.


#[export]
Instance InhabitedEnsemble_Monad : Monad (@InhabitedEnsemble) :=
{
   Mpure := @inhabited_singleton;
   Mbind := @inhabited_image;

   Mleft_identity := @inhabited_subset_left_identity;
   Mright_identity := @inhabited_subset_right_identity;
   Massociativity := @inhabited_subset_associativity;
}.

(* Define inhabited subsets as a general subtype. *)
Definition InhabitedSubtype {X : Type} := @Subtype (Ensemble X) (inhabited).

Instance InhabitedSubtype_Monad : Monad (@InhabitedSubtype) :=
  @Subtype_Monad (@Ensemble) (@inhabited) (@Ensemble_Monad)
    (@singleton_inhabited) (@image_inhabited).



Theorem inhabited_subset_monad_has_infinite_skew_product:
  has_infinite_skew_product (@InhabitedEnsemble) (InhabitedEnsemble_Monad).
Proof.
  unfold InhabitedEnsemble_Monad.
  unfold has_infinite_skew_product.
  intros X Finhabited.
  set ( F := fun xl => subset (Finhabited xl) ).
  assert (forall xl, inhabited (F xl)) as HF_inhabited. {
    intro xl. exact (Finhabited xl).(subset_inhabited). }
  set ( Finf := (fun (xs : nat -> X) => forall n, F (proj n xs) (xs n)) ).
  assert (inhabited Finf) as HFinf_inhabited. {
    apply list_dependent_choice. exact HF_inhabited. }
  exists ({|subset:=Finf; subset_inhabited:=HFinf_inhabited|}).
  unfold is_infinite_skew_product.
  split. {
    simpl.
    unfold inhabited_singleton, inhabited_image.
    apply inhabited_subset_equality.
    apply functional_extensionality.
    intro xl.
    apply propositional_extensionality.
    simpl.
    split.
    -- intros [xs [_ Hnil]].
       exact Hnil.
    -- intros Hnil.
       assert (forall {X} (p:X->Prop) (q:Prop), (exists x, p x) /\ q -> exists x, (p x /\ q)) as Hexists. {
         intros X' p q H.
         destruct H as [[x Hp] Hq].
         exists x.
         split. exact Hp. exact Hq.
       }
       unfold image.
       apply Hexists.
       split; [|exact Hnil].
       apply list_dependent_choice.
       unfold is_chosable.
       apply HF_inhabited.
  }
  intros n.
  simpl.
  unfold inhabited_singleton, inhabited_image.
  apply inhabited_subset_equality.
  apply functional_extensionality.
  intros xl.
  apply propositional_extensionality.
  simpl.
  split.
  - intros H.
    destruct H as [[xl' xn] H].
    destruct H as [Hp Hc].
    destruct Hp as [xl'' [Hp Hf]].
    destruct Hp as [xs [Hp Hp0]].
    destruct Hf as [xn' [Hf Ht]].
    unfold Mpure in Hp0, Ht, Hc.
    rewrite -> Hp0 in Hf, Ht.
    clear Hp0 xl''.
    injection Ht. intros Hxn' Hxl'.
    rewrite <- Hxn' in *; rewrite -> Hxl' in *.
    clear Hxl' Hxn' xl' xn'.
    clear Ht.
    rewrite -> Hc in *.
    clear Hc.
    clear xl.
    unfold lcons.
    simpl.
    set (xl := cons xn (proj n xs)).
    assert (exists xs' : nat -> X, proj (length xl) xs' = xl /\ forall n', F (proj n' xs') (xs' n')) as Hxs'. {
      apply list_dependent_choice_from.
      - unfold is_chosable.
        apply HF_inhabited.
      - unfold xl.
        apply is_choice_list_cons.
        split.
        -- exact Hf.
        -- apply is_choice_prefix_of_sequence.
           unfold is_choice_sequence.
           exact Hp.
    }
    destruct Hxs' as [xs' [Hpxs' Hcxs']].
    exists xs'.
    split.
    -- unfold Finf.
       unfold element.
       apply Hcxs'.
    -- replace (length xl) with (S n) in Hpxs'.
       rewrite <- proj_succ.
       apply eq_sym.
       exact Hpxs'.
       unfold xl.
       simpl.
       f_equal.
       rewrite -> length_proj.
       reflexivity.
  - unfold singleton, image.
    unfold lcons.
    unfold Finf.
    intros H.
    destruct H as [xs [Hc Hh]].
    exists (proj n xs, xs n).
    split.
    -- exists (proj n xs).
       split.
       --- exists xs.
           split.
           ---- apply Hc.
           ---- reflexivity.
       --- exists (xs n).
           split.
           ---- apply Hc.
           ---- reflexivity.
    -- simpl.
       exact Hh.
Qed.

End EnsembleMonads.
