(******************************************************************************
 *  utilities/ContinuationMonads.v
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

Require Import Monads.

Section ContinuationMonads.

Definition Continuation (T : Type) (X : Type) := ( X-> T ) -> T.

Definition pure {T : Type} {X : Type} (x : X) : (Continuation T X) :=
  fun (phi : X -> T) => (phi x).

Definition bind {T : Type} {X : Type} {Y : Type}
    (F : X -> Continuation T Y) (xi : Continuation T X) : (Continuation T Y) :=
  fun (psi : Y -> T) => xi (fun (x:X) => F x psi).

Lemma bind_extensionality : forall {T} {X1 X2 Y}
    (F1 : X1 -> Continuation T Y) (F2 : X2 -> Continuation T Y)
    (xi1 : Continuation T X1) (xi2 : Continuation T X2),
  (forall (psi : Y -> T), bind F1 xi1 psi = bind F2 xi2 psi) -> bind F1 xi1 = bind F2 xi2.
Proof. intros T X1 X2 Y F1 F2 xi1 xi2. apply functional_extensionality. Qed.

Proposition left_identity' : forall {T} {X Y} (F : X -> Continuation T Y) (x : X) (psi : Y->T), (bind F (pure x)) psi = F x psi.
Proof.
  intros T X Y F x psi.
  unfold bind.
  unfold pure.
  reflexivity.
Qed.

Proposition right_identity' : forall {T} {X} (xi : Continuation T X) (phi : X -> T),
  (bind (pure) xi) phi = xi phi.
Proof.
  intros T X xi.
  intros phi.
  unfold bind.
  unfold pure.
  f_equal.
Qed.

Proposition associativity' : forall {T} {X Y Z} (xi : Continuation T X) (F : X -> Continuation T Y) (G : Y -> Continuation T Z) (theta : Z -> T),
  bind G (bind F xi) theta = bind (fun x => bind G (F x)) xi theta.
Proof.
  intros T X Y Z xi F G theta.
  unfold bind.
  reflexivity.
Qed.



Proposition left_identity : forall {T} {X Y} (F : X -> Continuation T Y) (x : X), bind F (pure x) = F x.
Proof. intros T X Y F x. unfold bind, pure. apply functional_extensionality. intro psi. reflexivity. Qed.

Proposition right_identity : forall {T} {X} (xi : Continuation T X),  bind pure xi = xi.
Proof. intros T X xi. unfold bind, pure. apply functional_extensionality. intro phi. f_equal. Qed.

Proposition associativity : forall {T} {X Y Z} (xi : Continuation T X) (F : X -> Continuation T Y) (G : Y -> Continuation T Z),
  bind G (bind F xi) = bind (fun x => bind G (F x)) xi.
Proof. intros T X Y Z xi F G. unfold bind. reflexivity. Qed.


Definition lift {T} {X Y} (f : X -> Y) (mu : Continuation T X) :=
  bind (fun x => pure (f x)) mu.

Definition right_product {T} {X Y} (mu : Continuation T X) (nu : Continuation T Y) :=
  bind ( fun x => ( bind (fun y => pure (pair x y)) nu ) ) mu.

Definition left_product {T} {X Y} (mu : Continuation T X) (nu : Continuation T Y) :=
  bind ( fun y => ( bind (fun x => pure (pair x y)) mu ) ) nu.


#[export]
Instance Continuation_Monad : forall T:Type, Monad (Continuation T) :=
{
  Mpure := @pure T;
  Mbind := @bind T;

  (* coherence conditions *)
  Mleft_identity := @left_identity T;
  Mright_identity := @right_identity T;
  Massociativity := @associativity T;
}.


Theorem lift_associativity : forall {T : Type} {X Y Z : Type} (xi : Continuation T X) (f : X -> Y) (g : Y -> Z),
  lift g (lift f xi) = lift (fun x => g (f x)) xi.
Proof.
  intros T X Y Z. intros xi f g.
  unfold lift.
  apply bind_extensionality.
  intros theta.
  unfold bind, pure.
  reflexivity.
Qed.

Theorem product_pure_pure : forall {T : Type} {X Y} (x : X) (y : Y),
  @left_product T X Y (pure x) (pure y) = right_product (pure x) (pure y).
Proof.
  intros T X Y. intros x y.
  unfold left_product. unfold right_product.
  apply bind_extensionality. intro psi.
  rewrite -> left_identity. rewrite -> left_identity.
  rewrite -> left_identity. rewrite -> left_identity.
  reflexivity.
Qed.

Theorem product_pure_monad : forall {T : Type} {X Y} (x : X) (eta : Continuation T Y), left_product (pure x) eta = right_product (pure x) eta.
Proof.
  intros T X Y. intros x eta.
  unfold left_product. unfold right_product.
  apply bind_extensionality. intro psi.
  rewrite -> left_identity.
  f_equal.
Qed.

Theorem product_monad_pure : forall {T : Type} {X Y} (xi : Continuation T X) (y : Y),
  left_product xi (pure y) = right_product xi (pure y).
Proof.
  intros T X Y. intros xi y.
  unfold left_product. unfold right_product.
  apply bind_extensionality. intro psi.
  rewrite -> left_identity.
  f_equal.
Qed.


Section Experimental.

(* An operator intended to be similar to logical disjunction. *)

Parameter T : Type.
Parameter ast : T -> T -> T.

(* An relation intended to be some kind of equivalence on X. *)
Parameter X : Type.
Parameter sim : X -> X -> T.

(* An operator similar to the intersection of compact and closed sets. *)
Definition oast : Continuation T X -> (X -> T) -> Continuation T X :=
  fun mu phi => fun psi : X -> T => mu (fun x : X => ast (phi x) (psi x)).

(* An operator similar to the embedding of compact sets into closed sets for a Hausdorff space. *)
Definition osim : Continuation T X -> (X -> T) :=
  fun mu => fun y => mu (fun x => sim x y).

(* An interpretation of the whole space in the monad. *)
Parameter sum : (X -> T) -> T.

Axiom sim_symmetric : forall x x', sim x x' = sim x' x.

Axiom delta : forall phi : X -> T, forall x x' : X,
  ast (sim x x') (phi x) = ast (sim x x') (phi x').

Axiom complete : forall phi : X -> T, forall mu : (X -> T) -> T,
  mu phi = sum ( fun x : X => mu (fun x' : X => ast (sim x x') (phi x')) ).

Lemma sum_total : forall phi : X -> T, forall x : X,
  phi x = sum ( fun x' : X => ast (sim x x') (phi x') ).
Proof.
  intros phi x.
  assert (Hpx : (pure x) phi = sum ( fun x'' : X => (pure x) (fun x' : X => ast (sim x'' x') (phi x')) )  ).
  apply complete.
  assert  (Hpure : pure x phi = phi x).
  auto.
  rewrite Hpure in Hpx.
  rewrite Hpx.
  f_equal.
  apply functional_extensionality.
  auto.
  intros x0.
  unfold pure.
  assert (ast (sim x x0) (phi x) = ast (sim x0 x) (phi x)).
  f_equal.
  apply sim_symmetric.
  rewrite <- H.
  apply delta.
Qed.

Conjecture conditioning : forall {Y:Type} (sigma : Continuation T (X * Y) -> (X -> Continuation T Y)) (C : Continuation T (X * Y)),
  (forall (x : X) (psi : Y -> T),
      ast ((lift fst C) (fun x'=>sim x x')) (sigma C x psi) = C ( fun (xy':X*Y) => ast (sim x (fst xy')) (psi (snd xy')) ) )
    -> Mright_skew (lift fst C) (sigma C) = C.

End Experimental.

End ContinuationMonads.
