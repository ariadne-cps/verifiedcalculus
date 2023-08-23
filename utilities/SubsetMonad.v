Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.PropExtensionalityFacts.

Require Export Monads.

Section SubsetMonad.

Definition Subset (X:Type) : Type := (X -> Prop).
Definition element {X : Type} (x : X) (xs : Subset X) : Prop := xs x.
Definition intersection {X : Type} (xs1 xs2 : Subset X) : Subset X :=
  fun x => (xs1 x) /\ (xs2 x).
Definition union {X : Type} (xs1 xs2 : Subset X) : Subset X :=
  fun x => (xs1 x) \/ (xs2 x).
  
Definition singleton {X : Type} (x : X) : Subset X :=
  fun x' => (x'=x).
Definition image {X Y : Type} (fs : X -> Subset Y) (xs : Subset X) : Subset Y :=
  fun y => exists x, (xs x) /\ ((fs x) y).

Lemma set_left_identity :
  forall {X Y : Type} (f : X -> Subset Y) (x : X), image f (singleton x) = f x.
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

Lemma set_right_identity :
  forall {X : Type} (xs : Subset X), image (@singleton X) xs = xs.
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

Lemma set_associativity :
  forall {X Y Z : Type} (xs : Subset X) (fs : X -> Subset Y) (gs : Y -> Subset Z),
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
Instance Subset_Monad : Monad (Subset) :=
{
   Mpure := @singleton;
   Mbind := @image;
   
   Mleft_identity := @set_left_identity;
   Mright_identity := @set_right_identity;
   Massociativity := @set_associativity;
}.


Definition set_product {X Y : Type} (xs : Subset X) (ys : Subset Y) : Subset (X*Y) :=
  fun xy => xs (fst xy) /\ ys (snd xy).

Theorem set_product_elements : forall X Y,
  @set_product X Y = @Mright_product Subset Subset_Monad X Y
    /\ @set_product X Y = @Mleft_product Subset Subset_Monad X Y.
Proof.
  intros X Y.
  unfold set_product, Mright_product, Mleft_product.
  unfold Subset_Monad, Mpure, Mbind, image, singleton.
  split.
  * apply functional_extensionality.
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
  * apply functional_extensionality.
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
   
  
Definition set_right_skew {X Y : Type} := @Mright_skew Subset Subset_Monad X Y.

Theorem set_right_skew_elements :
  forall X Y (xs : Subset X) (fs : X -> Subset Y),
    set_right_skew xs fs = fun xy => xs (fst xy) /\ fs (fst xy) (snd xy).
Proof.
  intros X Y xs fs.
  unfold set_right_skew.
  unfold Subset_Monad.
  unfold Mright_skew, Mlift, Mpure, Mbind.
  unfold image, singleton.
  apply functional_extensionality. intro xy.
  apply propositional_extensionality.
  split.
  - intros [x [Hx [y [Hf Hxy]]]].
    rewrite -> Hxy.
    simpl.
    split.
    -- exact Hx.
    -- exact Hf.
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
Qed.


Definition set_parallel {X Y : Type} (fs : Y -> Subset X) (gs : X -> Subset Y) : Subset (X*Y) :=
  fun xy => let x:=fst xy in let y:= snd xy in fs y x /\ gs x y.
 
Theorem parallel_skew {X Y : Type} :
  forall (xs : Subset X) (fs : X -> Subset Y),
    set_parallel (fun (y:Y) => xs) fs = set_right_skew xs fs.
Proof.
  intros xs fs.
  unfold set_parallel, set_right_skew.
  unfold Subset_Monad.
  unfold Mright_skew, Mlift, Mpure, Mbind.
  unfold image, singleton.
  apply functional_extensionality. intro xy. 
  apply propositional_extensionality.
  split.
  - intros [Hx Hf].
    destruct xy as [x y]. simpl.
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



End SubsetMonad.
