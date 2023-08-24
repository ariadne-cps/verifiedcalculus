Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Require Export Monads.

Section Monads.

Record Subtype {T : Type} {P : T -> Prop} : Type :=
{
  val : T;
  prop : (P val);
}.

Lemma subtype_equality : forall {T : Type} {P : T -> Prop} (st1 st2 : @Subtype T P),
  st1.(val) = st2.(val) -> st1 = st2.
Proof.
  intros T P st1 st2.
  destruct st1 as [st1v st1p].
  destruct st2 as [st2v st2p].
  simpl.
  intros H.
  revert st1p st2p.
  rewrite <- H.
  intros st1p st2p.
  rewrite (proof_irrelevance _ st1p st2p).
  reflexivity.
Qed.

Definition subtype_pure
  {M : Type -> Type} {P : forall {X:Type}, M X -> Prop} {_ : Monad M}
  (pp : forall {X:Type} (x:X), P (Mpure x))
  {X : Type} (x : X)
    : @Subtype (M X) (@P X)
      := {| val:=Mpure x; prop:=pp x; |}.

Definition subtype_bind
  {M : Type -> Type} {P : forall {X:Type}, M X -> Prop} {_ : Monad M}
  (pb : forall {X Y} (f:X->M Y) (x:M X), (forall x, P (f x)) -> P x -> P (Mbind f x))
  {X Y : Type} (f : X -> @Subtype (M Y) (@P Y)) (x : @Subtype (M X) (@P X))
    : @Subtype (M Y) (@P Y)
      := {| val:=Mbind (fun x' => val (f x')) (val x);
            prop:=pb (fun x' => val (f x')) (val x) (fun x' => prop (f x')) (prop x); |}.


#[export]
#[refine]
Instance Subtype_Monad
    {M : Type -> Type} {P : forall {X:Type}, M X -> Prop} {Monad_M : Monad M}
    (pp : forall {X:Type} (x:X), P (Mpure x))
    (pb : forall {X Y} (f:X->M Y) (x:M X), (forall x, P (f x)) -> P x -> P (Mbind f x))
  : Monad (fun T => @Subtype (M T) P) :=
{
  Mpure := @subtype_pure M P Monad_M pp;
  Mbind := @subtype_bind M P Monad_M pb;
}.
Proof.
- intros A B f a.
  apply subtype_equality.
  simpl.
  rewrite -> Mleft_identity.
  reflexivity.
- intros A a.
  apply subtype_equality.
  simpl.
  rewrite -> Mright_identity.
  reflexivity.
- intros A B C x f g.
  apply subtype_equality.
  simpl.
  rewrite -> Massociativity.
  reflexivity.
Qed.

End Monads.
