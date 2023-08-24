Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Logic.ProofIrrelevance.

Require Import List.
Require Import Ensembles.

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
Lemma proj1_eq {M} {Monad_M : Monad M} : forall {X : Type} (F : list X -> M X) (Finf : M (nat -> X)),
  is_infinite_skew_product F Finf -> (Mlift (proj 1) Finf = Mlift (fun x => cons x nil) (F nil)).
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
  unfold lcons.
  simpl.
  reflexivity.
Qed.

#[local]
Lemma proj2_eq {M} {Monad_M : Monad M} : forall {X : Type} (F : list X -> M X) (Finf : M (nat -> X)),
  is_infinite_skew_product F Finf -> 
    (Mlift (proj 2) Finf = Mlift lcons (Mright_skew (Mlift (fun x => cons x nil) (F nil)) F)).
Proof.
  intros X F Finf H.
  rewrite <- (proj1_eq F Finf H).
  apply eq_sym.
  unfold is_infinite_skew_product in H.
  destruct H as [HO HS].
  exact (HS 1).
Qed.

Theorem ensemble_monad_does_not_have_infinite_skew_product :
  not (has_infinite_skew_product (Ensemble) (Ensemble_Monad)).
Proof.
  unfold has_infinite_skew_product.
  set (F := fun (xl : list bool) =>
    match xl with
    | nil => (fun (x:bool) => True) : Ensemble bool
    | cons true nil => fun (x:bool) => True
    | cons false nil => fun x => False
    | cons x _ => fun x' => x'=x
    end).
  intros H.
  specialize (H bool).
  specialize (H F).
  destruct H as [Finf H].
  assert ( forall {X} (xs : nat -> X), proj 1 xs = cons (xs 0) nil ) as Hpr1. {
    unfold proj. reflexivity. }
  assert ( forall {X} (xs : nat -> X), proj 2 xs = cons (xs 1) (cons (xs 0) nil) ) as Hpr2. {
    unfold proj. reflexivity. }
  set ( S1 := fun x0:bool => True).
  set ( S2 := fun x01:bool*bool => (fst x01=true)).
  assert (Mlift (proj 1) Finf = Mlift (fun x0:bool => cons x0 nil) S1 ) as Hs1. {
    rewrite -> (proj1_eq F Finf H).
    unfold F, S1.
    reflexivity.
  }
  assert (Mlift (proj 2) Finf = Mlift (fun x01:bool*bool => cons (snd x01) (cons (fst x01) nil)) S2 ) as Hs2.  {
    rewrite -> (proj2_eq F Finf H).
    unfold lcons.
    unfold Ensemble_Monad.
    unfold Mright_skew, Mlift, Mbind, Mpure.
    unfold singleton, image.
    apply functional_extensionality.
    intro xl.
    apply propositional_extensionality.
    split.
    - intro Hxl_x.
      destruct Hxl_x as [xl_x [[xl' [Hxl0' Hxl1']] Hc]].
      destruct Hxl0' as [x0 [Hx0F Hx0l]].
      destruct Hxl1' as [x1 [Hx1F Hx1l]].
      exists (x0,x1).
      split.
      -- unfold S2.
         simpl.
         rewrite -> Hx0l in Hx1F.
         unfold F in Hx1F.
         destruct x0.
         --- reflexivity.
         --- contradiction.
      -- rewrite -> Hc, -> Hx1l, -> Hx0l.
         simpl.
         reflexivity.
    - intro Hx01.
      destruct Hx01 as [[x0 x1] [Hs2 Hxl]].
      simpl in Hxl.
      exists (cons x0 nil, x1).
      split.
      -- exists (cons x0 nil).
         split.
         --- exists x0.
             split.
             ---- unfold F.
                  unfold element.
                  trivial.
             ---- reflexivity.
         --- exists x1.
             split.
             ---- unfold S2 in Hs2.
                  simpl in Hs2.
                  rewrite -> Hs2.
                  unfold F.
                  unfold element, In.
                  trivial.
             ---- reflexivity.
      -- simpl.
         exact Hxl.
    }
    assert (Mlift (@tl bool) (Mlift (proj 2) Finf) = Mlift (proj 1) Finf) as Hx21. { 
      apply Mlift_compose. }
    revert Hx21.
    rewrite -> Hs1.
    rewrite -> Hs2.
    rewrite -> Mlift_associative.
    unfold tail, compose.
    assert (forall {X} (s1 s2 : Ensemble X), (exists c, ~ (s1 c) /\ s2 c) -> (s1=s2) -> False ) as Hsne. {
      intros X s1 s2 Hc He.
      destruct Hc as [c [Hs1c Hs2c]].
      apply Hs1c.
      rewrite -> He.
      exact Hs2c.
    }
    apply Hsne.
    exists (cons false nil).
    split.
    - unfold S2.
      simpl.
      unfold singleton, image.
      intros [x [Hxt Hxf]].
      rewrite -> Hxt in Hxf.
      discriminate Hxf.
    - unfold S1.
      simpl.
      unfold singleton, image.
      exists false.
      split.
      -- unfold element.
         trivial.
      -- reflexivity.
Qed.


End EnsembleMonads.
