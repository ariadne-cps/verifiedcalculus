Require Import Coq.Logic.PropExtensionality.

Require Import Monads.
Require Import DependentChoice.


Section LimitMonads.

Definition lcons {X : Type} : prod (list X) X -> list X := 
  fun xl_x => cons (snd xl_x) (fst xl_x).

Definition is_infinite_skew_product {M : Type -> Type} {_ : Monad M} {X : Type}
  (F : (list X) -> M X) (Finf : M (nat -> X)) :=
    (Mlift (proj 0) Finf = Mpure nil) /\
      forall (n:nat), 
        Mlift lcons (Mright_skew (Mlift (proj n) Finf) F) = 
        Mlift (proj (S n)) Finf.

Definition has_infinite_skew_product (M : Type -> Type) (_ : Monad M) :=
  forall (X : Type) (F : (list X) -> M X), 
    exists (Finf : M (nat -> X)),
      is_infinite_skew_product F Finf.

End LimitMonads.
