(******************************************************************************
 *  utilities/EnsembleMonad.v
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

Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.

Require Import DependentChoice.

Require Export Monads.
Require Export SubMonads.
Require Export LimitMonads.



Section EnsembleMonads.

Definition element {X : Type} (x : X) (xs : Ensemble X) : Prop := xs x.
Definition intersection {X : Type} (xs1 xs2 : Ensemble X) : Ensemble X :=
  fun x => (xs1 x) /\ (xs2 x).
Definition union {X : Type} (xs1 xs2 : Ensemble X) : Ensemble X :=
  fun x => (xs1 x) \/ (xs2 x).

Definition singleton {X : Type} (x : X) : Ensemble X :=
  fun x' => (x'=x).
Definition image {X Y : Type} (fs : X -> Ensemble Y) (xs : Ensemble X) : Ensemble Y :=
  fun y => exists x, (xs x) /\ ((fs x) y).
Definition apply {X Y : Type} (f : X -> Y) (xs : Ensemble X) : Ensemble Y
  := fun y => exists x, xs x /\ f x = y.

Definition subset {X} (s1 s2 : Ensemble X) : Prop :=
  forall x, element x s1 -> element x s2.

Proposition ensemble_equal : forall {X : Type} {s1 s2 : Ensemble X},
  (forall x : X, element x s1 <-> element x s2) -> s1 = s2.
Proof.
  intros X s1 s2 H.
  apply functional_extensionality.
  intro x.
  apply propositional_extensionality.
  exact (H x).
Qed.


Lemma ensemble_left_identity :
  forall {X Y : Type} (f : X -> Ensemble Y) (x : X), image f (singleton x) = f x.
Proof.
  intros X Y f x.
  unfold image, singleton.
  apply functional_extensionality. intro y.
  apply propositional_extensionality.
  split.
  - intros [xe Hxe].
    destruct Hxe as [Hxe Hfxe].
    rewrite -> Hxe in Hfxe.
    exact Hfxe.
  - intros Hfxy.
    exists x.
    split. reflexivity. assumption.
Qed.

Lemma ensemble_right_identity :
  forall {X : Type} (xs : Ensemble X), image (@singleton X) xs = xs.
Proof.
  intros X xs. unfold image, singleton.
  apply functional_extensionality. intro x.
  apply propositional_extensionality.
  split.
  - intros Hxe.
    destruct Hxe as [xe [Hxs Hxe]].
    rewrite <- Hxe in Hxs.
    assumption.
  - intros Hxs.
    exists x.
    split. assumption. reflexivity.
Qed.

Lemma ensemble_associativity :
  forall {X Y Z : Type} (xs : Ensemble X) (fs : X -> Ensemble Y) (gs : Y -> Ensemble Z),
    image gs (image fs xs) = image (fun x => image gs (fs x)) xs.
Proof.
  intros X Y Z xs fs gs.
  unfold image.
  apply functional_extensionality.
  intro z.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct H as [y [[x [Hx Hf]] Hg]].
    exists x.
    split.
    -- exact Hx.
    -- exists y.
       split.
       --- exact Hf.
       --- exact Hg.
  - intros H.
    destruct H as [x [Hx [y [Hf Hg]]]].
    exists y.
    split.
    -- exists x.
       split.
       exact Hx.
       exact Hf.
    -- exact Hg.
Qed.

#[export]
Instance Ensemble_Monad : Monad (Ensemble) :=
{
   Mpure := @singleton;
   Mbind := @image;

   Mleft_identity := @ensemble_left_identity;
   Mright_identity := @ensemble_right_identity;
   Massociativity := @ensemble_associativity;
}.


Definition ensemble_product {X Y : Type} (xs : Ensemble X) (ys : Ensemble Y) : Ensemble (X*Y) :=
  fun xy => xs (fst xy) /\ ys (snd xy).

Proposition ensemble_monad_right_product : forall {X Y : Type},
  @ensemble_product X Y = @Mright_product Ensemble Ensemble_Monad X Y.
Proof.
  intros X Y.
  unfold ensemble_product, Mright_product, Mleft_product.
  unfold Ensemble_Monad, Mpure, Mbind, image, singleton.
  apply functional_extensionality.
  intro xs.
  apply functional_extensionality.
  intro ys.
  apply functional_extensionality.
  intros xy.
  apply propositional_extensionality.
  split.
  - destruct xy as [x y].
    simpl.
    intros [Hx Hy].
    exists x.
    split.
    -- exact Hx.
    -- exists y.
       split.
       --- exact Hy.
       --- reflexivity.
  - intros [x [Hx [y [Hy Hxy]]]].
    rewrite -> Hxy.
    simpl.
    split.
    -- exact Hx.
    -- exact Hy.
Qed.

Proposition ensemble_monad_left_product : forall {X Y : Type},
  @ensemble_product X Y = @Mleft_product Ensemble Ensemble_Monad X Y.
Proof.
  intros X Y.
  unfold ensemble_product, Mright_product, Mleft_product.
  unfold Ensemble_Monad, Mpure, Mbind, image, singleton.
  apply functional_extensionality.
  intro xs.
  apply functional_extensionality.
  intro ys.
  apply functional_extensionality.
  intros xy.
  apply propositional_extensionality.
  split.
  - destruct xy as [x y].
    simpl.
    intros [Hx Hy].
    exists y.
    split.
    -- exact Hy.
    -- exists x.
       split.
       --- exact Hx.
       --- reflexivity.
  - intros [y [Hy [x [Hx Hxy]]]].
    rewrite -> Hxy.
    simpl.
    split.
    -- exact Hx.
    -- exact Hy.
Qed.

Proposition ensemble_monad_products : forall {X Y : Type},
  @ensemble_product X Y = @Mright_product Ensemble Ensemble_Monad X Y
    /\ @ensemble_product X Y = @Mleft_product Ensemble Ensemble_Monad X Y.
Proof.
  intros X Y.
  split.
  apply ensemble_monad_right_product.
  apply ensemble_monad_left_product.
Qed.


Definition ensemble_right_skew {X Y : Type} (xs : Ensemble X) (fs : X -> Ensemble Y) :=
  fun xy => xs (fst xy) /\ fs (fst xy) (snd xy).

Theorem ensemble_monad_right_skew : forall {X Y : Type},
  @ensemble_right_skew X Y = @Mright_skew Ensemble Ensemble_Monad X Y.
Proof.
  intros X Y.
  unfold Ensemble_Monad.
  unfold Mright_skew, Mlift, Mpure, Mbind.
  unfold ensemble_right_skew.
  unfold image, singleton.
  apply functional_extensionality; intro xs.
  apply functional_extensionality; intro fs.
  apply ensemble_equal; intro xy.
  split.
  - destruct xy as [x y].
    simpl.
    intros [Hx Hf].
    exists x.
    split.
    -- exact Hx.
    -- exists y.
       split.
       --- exact Hf.
       --- reflexivity.
  - intros [x [Hx [y [Hf Hxy]]]].
    rewrite -> Hxy.
    simpl.
    split.
    -- exact Hx.
    -- exact Hf.
Qed.


Definition ensemble_parallel {X Y : Type} (fs : Y -> Ensemble X) (gs : X -> Ensemble Y) : Ensemble (X*Y) :=
  fun xy => let x:=fst xy in let y:= snd xy in fs y x /\ gs x y.

Theorem ensemble_parallel_right_skew : forall {X Y : Type} (xs : Ensemble X) (fs : X -> Ensemble Y),
  ensemble_parallel (fun (y:Y) => xs) fs = Mright_skew xs fs.
Proof.
  intros xs fs.
  rewrite <- ensemble_monad_right_skew.
  unfold ensemble_parallel, ensemble_right_skew.
  reflexivity.
Qed.


Lemma apply_element : forall {X Y} (f : X -> Y) (A : Ensemble X) (x : X), (A x) -> (apply f A) (f x).
Proof. 
  intros X Y f A x HAx. unfold apply. 
  exists x. split. exact HAx. reflexivity. 
Qed.

Lemma image_singleton_apply : forall {X Y} (f : X -> Y) (A : Ensemble X), image (fun x => singleton (f x)) A = apply f A.
Proof.
  intros X Y f A.
  unfold image, singleton, apply.
  apply functional_extensionality. intro y.
  apply propositional_extensionality.
  split. 
  - intro H. destruct H as [x [HA Hf]]. exists x. split. exact HA. symmetry. exact Hf.
  - intro H. destruct H as [x [HA Hf]]. exists x. split. exact HA. exact (eq_sym Hf).
Qed.


Definition inhabited {X:Type} (s : Ensemble X) := exists x, s x.
Definition empty {X : Type} (s : Ensemble X) := forall x, not (s x).
Definition nonempty {X:Type} (s : Ensemble X) := not (empty s).

Lemma ensemble_empty_image : forall {X Y : Type} (fs : X -> Ensemble Y) (xs : Ensemble X),
  (empty xs) -> empty (image fs xs).
Proof.
  intros X Y fs xs.
  unfold empty.
  intros H.
  intro y.
  unfold image.
  intros [xe [Hxe Hy]].
  apply H in Hxe.
  contradiction.
Qed.

Lemma inhabited_set_constant_image : forall {X Y : Type} (ys : Ensemble Y) (xs : Ensemble X),
  inhabited xs -> image (fun X => ys) (xs) = ys.
Proof.
  intros X Y ys xs.
  intros [x Hx].
  unfold image, inhabited.
  apply functional_extensionality.
  intro y.
  apply propositional_extensionality.
  split.
  - intros [x' [Hx' Hy]]. exact Hy.
  - intros Hy.
    exists x.
    split.
    -- exact Hx.
    -- exact Hy.
Qed.




#[local]
Lemma proj1_eq {M} {Monad_M : Monad M} : 
  forall {X : Type} (F : forall n, Wrd n X -> M X) (Finf : M (Seq X)),
    (is_infinite_skew_product F Finf) -> 
      (Mlift (projw 1) Finf = Mlift (fun x => fun kp => x) (F 0 null_wrd)).
Proof.
  unfold is_infinite_skew_product.
  intros X F Finf.
  intros [Hnil *Hcons].
  rewrite <- Hcons.
  rewrite -> Hnil.
  unfold Mright_skew, Mlift.
  rewrite -> Massociativity.
  rewrite -> Mleft_identity.
  rewrite -> Massociativity.
  f_equal.
  apply functional_extensionality.
  intro x0.
  rewrite -> Mleft_identity.
  f_equal.
  apply wrd_1_eq.
  unfold wlcons, cat.
  reflexivity.
Qed.

#[local]
Lemma proj2_eq {M} {Monad_M : Monad M} : 
  forall {X : Type} (F : forall n, Wrd n X -> M X) (Finf : M (Seq X)),
    is_infinite_skew_product F Finf ->
      (Mlift (projw 2) Finf = 
        Mlift (wlcons 1) (Mright_skew (Mlift (fun x => fun kp => x) (F 0 null_wrd)) (F 1))).
Proof.
  intros X F Finf H.
  rewrite <- (proj1_eq F Finf H).
  apply eq_sym.
  unfold is_infinite_skew_product in H.
  destruct H as [HO HS].
  exact (HS 1).
Qed.


Theorem ensemble_monad_does_not_have_infinite_skew_product :
  not (exists_infinite_skew_product (Ensemble) (Ensemble_Monad)).
Proof.
  set (X := bool).
  unfold has_infinite_skew_product.
  set (F := fun n : nat =>
    match n as m return (Wrd m X -> Ensemble X) with
    | 0 => fun (_ : Wrd 0 X) (_ : X) => True
    | 1 => fun (w : Wrd 1 X) (x : X) => 
         let k := ord 0 (PeanoNat.Nat.lt_0_1) in 
           match w k with | true => True | false => False end
    | S m => (fun (m' : nat) (w : Wrd (S m') X) (x : X) => 
         let k := ord m' (PeanoNat.Nat.lt_succ_diag_r m') in 
           w k = x) m
    end).
  intros H.
  specialize (H X).
  specialize (H F).
  destruct H as [Finf H].
  assert ( forall {X} (xs : nat -> X), projw 1 xs = fun kp => xs 0) as Hpr1. {
    intros X' xs. apply wrd_1_eq. rewrite -> projw_at. reflexivity. }
  assert ( forall (xs : nat -> X), projw 2 xs = fun kp => xs (val 2 kp) ) as Hpr2. {
    intros xs. unfold projw. reflexivity. }
  set ( S1 := fun x0:X => True).
  set ( S2 := fun x01:X*X => (fst x01=true)).
  assert (Mlift (projw 1) Finf = Mlift (fun x0:X => fun kp => x0) S1 ) as Hs1. {
    rewrite -> (proj1_eq F Finf H).
    unfold F, S1.
    reflexivity.
  }
  assert (Mlift (projw 2) Finf = Mlift (fun x01:X*X => cat (cat null_wrd (fst x01)) (snd x01)) S2 ) as Hs2.  {
    rewrite -> (proj2_eq F Finf H).
    unfold Ensemble_Monad.
    unfold Mright_skew, Mlift, Mbind, Mpure.
    unfold singleton, image.
    apply functional_extensionality.
    intro xw.
    apply propositional_extensionality.
    split.
    - intro Hxw_x.
      destruct Hxw_x as [xw_x [[xw' [Hxw0' Hxw1']] Hc]].
      destruct Hxw0' as [x0 [Hx0F Hx0w]].
      destruct Hxw1' as [x1 [Hx1F Hx1w]].
      exists (x0,x1).
      split.
      -- unfold S2.
         simpl.
         rewrite -> Hx0w in Hx1F.
         unfold F in Hx1F.
         destruct x0.
         --- reflexivity.
         --- contradiction.
      -- rewrite -> Hc, -> Hx1w, -> Hx0w.
         unfold wlcons.
         simpl.
         f_equal.
         apply (wrd_1_eq).
         unfold cat. 
         reflexivity.
         
    - intro Hx01.
      destruct Hx01 as [[x0 x1] [Hs2 Hxw]].
      simpl in Hxw.
      exists (cat null_wrd x0, x1).
      split.
      -- exists (cat null_wrd x0).
         split.
         --- exists x0.
             split.
             ---- unfold F.
                  trivial.
             ----apply wrd_1_eq. unfold cat. reflexivity.
         --- exists x1.
             split.
             ---- unfold S2 in Hs2.
                  simpl in Hs2.
                  rewrite -> Hs2.
                  unfold F.
                  unfold element, In.
                  unfold cat, null_wrd. 
                  simpl.
                  trivial.
             ---- reflexivity.
      -- simpl.
         exact Hxw.
    }
    assert (Mlift (restr 1 (PeanoNat.Nat.le_succ_diag_r 1)) (Mlift (projw 2) Finf) = Mlift (projw 1) Finf) as Hx21. {
      apply Mlift_compose. }
    revert Hx21.
    rewrite -> Hs1.
    rewrite -> Hs2.
    rewrite -> Mlift_associative.
    unfold compose.
    assert (forall {X} (s1 s2 : Ensemble X), (exists c, ~ (s1 c) /\ s2 c) -> (s1=s2) -> False ) as Hsne. {
      intros X' s1 s2 Hc He.
      destruct Hc as [c [Hs1c Hs2c]].
      apply Hs1c.
      rewrite -> He.
      exact Hs2c.
    }
    apply Hsne.
    exists (cat null_wrd false).
    split.
    - unfold S2.
      simpl.
      unfold singleton, image.
      intros [x [Hxt Hxf]].
      rewrite -> Hxt in Hxf.
      rewrite -> restr_cat_id in Hxf.
      set (k0 := ord 0 PeanoNat.Nat.lt_0_1). 
      assert (forall {X Y} (x : X) (f1 f2 : X -> Y), f1 = f2 -> f1 x = f2 x) as Heqf. {
        intros X' Y' x' f1 f2 e. rewrite <- e. reflexivity. }
      set (c := Heqf _ _ k0 (cat null_wrd false) _ Hxf). 
      discriminate c.
    - unfold S1.
      simpl.
      unfold singleton, image.
      exists false.
      split.
      -- trivial.
      -- apply wrd_1_eq. reflexivity.
Qed.


End EnsembleMonads.
