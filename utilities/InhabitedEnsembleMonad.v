(******************************************************************************
 *  utilities/InhabitedEnsembleMonad.v
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


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Logic.ProofIrrelevance.

Require Import Bool.
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
  ensmbl : Ensemble A;
  ensmbl_inhabited : inhabited ensmbl;
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
  {| ensmbl := singleton x;
     ensmbl_inhabited := singleton_inhabited x; |}.
Definition inhabited_image {X Y : Type} (fs : X -> @InhabitedEnsemble Y) (xs : @InhabitedEnsemble X) : @InhabitedEnsemble Y :=
  {| ensmbl := image (fun x => ensmbl (fs x)) (ensmbl xs);
     ensmbl_inhabited := image_inhabited (fun x => ensmbl (fs x)) (ensmbl xs) (fun x => ensmbl_inhabited (fs x)) (ensmbl_inhabited xs); |}.


Lemma inhabited_subset_equality : forall {X : Type} (s1 s2 : @InhabitedEnsemble X),
  (ensmbl s1) = (ensmbl s2) -> s1 = s2.
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
  set ( F := fun xl => ensmbl (Finhabited xl) ).
  assert (forall xl, inhabited (F xl)) as HF_inhabited. {
    intro xl. exact (Finhabited xl).(ensmbl_inhabited). }
  set ( Finf := (fun (xs : nat -> X) => forall n, F (proj n xs) (xs n)) ).
  assert (inhabited Finf) as HFinf_inhabited. {
    apply list_dependent_choice. exact HF_inhabited. }
  exists ({|ensmbl:=Finf; ensmbl_inhabited:=HFinf_inhabited|}).
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





Require Import Words.

(*
Context {M : Type -> Type} {MonadM : Monad M}.
*)

Definition proj {X : Type} (n : nat) (xs : Seq X) : Wrd n X :=
  fun kp => xs kp.(val n).

Definition is_inverse_limit {M : Type -> Type} {MonadM : Monad M}{X} (A : forall (n: nat), M (ordinal n -> X)) (Alim : M (nat -> X)) :=
  forall n, Mlift (proj n) Alim = A n.

Definition is_inverse_sequence {M : Type -> Type} {MonadM : Monad M} {X} (A : forall n, M (ordinal n -> X)) : Prop :=
  forall (m n : nat) (p : m <= n), Mlift (restr m p) (A n) = A m.

Definition has_inverse_limits (M : Type -> Type) (MonadM : Monad M) := forall {X}
   (A : forall (n: nat), M (ordinal n -> X)), is_inverse_sequence A -> 
    sig (fun Ainf : M (nat -> X) => is_inverse_limit A Ainf).
      

Definition lt_succ_diag_r := PeanoNat.Nat.lt_succ_diag_r.
Definition le_succ_diag_r := PeanoNat.Nat.le_succ_diag_r.

Lemma limit_words_sequence : 
  forall X, forall (xw : forall n : nat, Wrd n X) (p : forall n, restr n (le_succ_diag_r n) (xw (S n)) = xw n),
    exists xs : nat -> X, forall n, proj n xs = xw n.
Proof.
  intros X xw p.
  set (xs := (fun n => xw (S n) (ord n (lt_succ_diag_r n)))).
  exists xs.
  induction n.
  - apply wrd_eq. intros kp. destruct kp as [k pk]. 
    apply (PeanoNat.Nat.nle_succ_0) in pk as pfls. contradiction.
  - apply wrd_eq. intros kp. destruct kp as [k pk].
    set (Hleg := PeanoNat.Nat.lt_trichotomy k n).
    destruct Hleg as [Hlt|[Heq|Hgt]].
    -- set (kp := {| val:=k; val_lt:=pk|}).
       assert (proj n xs = restr n (le_succ_diag_r n) (proj (S n) xs)) as Hpr.
         apply projw_restr.
       assert (xw (S n) kp = restr n (le_succ_diag_r n) (xw (S n)) (ord k Hlt) ) as HSr.
         rewrite -> restr_at. apply wrd_at_ordinal. simpl. reflexivity.
       rewrite -> HSr. rewrite -> p. rewrite <- IHn. 
       rewrite -> projw_at, projw_at.
       simpl.
       reflexivity.
    -- rewrite -> projw_at. simpl.
       replace (xs k) with (xs n); [|rewrite -> Heq; reflexivity].     
       unfold xs. f_equal. apply ord_eq. symmetry. exact Heq.
    -- apply Arith_prebase.lt_n_Sm_le_stt in pk as pk'.
       apply Arith_prebase.lt_le_S_stt in Hgt.
       apply (PeanoNat.Nat.le_trans _ k _ Hgt) in pk' as HSnlen. 
       contradiction (PeanoNat.Nat.nle_succ_diag_l n).
Qed.

Theorem inhabited_subset_monad_has_inverse_limits:
  has_inverse_limits (@InhabitedEnsemble) (InhabitedEnsemble_Monad).
Proof.
  unfold InhabitedEnsemble_Monad.
  unfold has_inverse_limits, is_inverse_sequence.
  intros X A' Hinvseq.
  set ( A := (fun n => ensmbl (A' n))).
  assert ( forall n, inhabited (A n)) as HA.
    exact (fun n => ensmbl_inhabited (A' n)).
  set ( Ainf := (fun (xs : nat -> X) => forall n, (A n) (proj n xs)) ).
  assert (inhabited Ainf) as HAinf. {
    admit. }
  exists ({|ensmbl:=Ainf; ensmbl_inhabited:=HAinf_inhabited|}).
  unfold is_inverse_limit.
  intro n.
  unfold Mlift, Mbind.
  unfold inhabited_image.
  apply inhabited_subset_equality. 
  unfold Ainf.
  unfold image.
  simpl.
  apply functional_extensionality.
  intro x.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct H as [xs [Hs Hu]].
    unfold singleton in Hu. 
    rewrite -> Hu.
    apply Hs.
  - unfold Mlift, Mbind, Mpure in Hinvseq. 
    intro HxinAn.
    set (le_s := PeanoNat.Nat.le_succ_diag_r).

    assert (forall m (w : Wrd m X), element w (ensmbl (A m)) -> exists w', 
             element w' (ensmbl (A (S m))) /\ restr m (le_s m) w' = w) as Hsu.
    {
       unfold element. intros m w Hw.  
       specialize (Hinvseq m (S m) (le_s m)).
       admit.
    }

    assert (exists xe : forall m, @Wrd (n+m) X,
      (forall m, element (xe m) (ensmbl (A (n+m)))) /\ 
      (forall l m (p:n+l<=n+m), restr (n+l) p (xe m) = xe l)) as Hxe.
    { admit. }

    exists (fun m => 
      let p := (PeanoNat.Nat.lt_decidable (m<n)) in xe 1 0).
      let p := Nat.ltb m n in 
                       if p then x (ord m ) else xe (S m) m).
inhabited_image.
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
