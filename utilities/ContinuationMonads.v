Require Import Coq.Logic.FunctionalExtensionality.

Require Import Monads.

Module Type ContinuationMonads.

Parameter T : Type.

Definition M (X : Type) := ( X-> T ) -> T.
 
Definition pure {X : Type} (x : X) : (M X) :=
  fun (phi : X -> T) => (phi x).
 
Definition bind {X : Type} {Y : Type} (F : X -> M Y) (xi : M X) : (M Y) :=
  fun (psi : Y -> T) => xi (fun (x:X) => F x psi).

Lemma bind_extensionality: forall {X1 X2 Y} (F1 : X1 -> M Y) (F2 : X2 -> M Y) (xi1 : M X1) (xi2 : M X2),
  (forall (psi : Y -> T), bind F1 xi1 psi = bind F2 xi2 psi) -> bind F1 xi1 = bind F2 xi2.
Proof. intros X1 X2 Y F1 F2 xi1 xi2. apply functional_extensionality. Qed.

Proposition left_identity  : forall {X} {Y} (F : X -> M Y) (x : X) (psi : Y->T), (bind F (pure x)) psi = F x psi.
Proof.
  intros X Y F x psi.
  unfold bind.
  unfold pure.
  reflexivity.
Qed.

Proposition right_identity  : forall {X} (xi : M X) (phi : X -> T), 
  (bind (pure) xi) phi = xi phi.
Proof.
  intros X xi.
  intros phi.
  unfold bind.
  unfold pure.
  f_equal.
Qed.

Proposition associativity : forall {X} {Y} {Z} (xi:M X) (F:X->M Y) (G:Y->M Z) (theta : Z -> T),
  bind G (bind F xi) theta = bind (fun x => bind G (F x)) xi theta.
Proof.
  intros X Y Z xi F G theta.
  unfold bind.
  reflexivity.
Qed.



Proposition left_identity_extensional : forall {X} {Y} (F : X -> M Y) (x : X), bind F (pure x) = F x.
Proof. intros X Y F x. unfold bind, pure. apply functional_extensionality. intro psi. reflexivity. Qed.

Proposition right_identity_extensional : forall {X} (xi : M X),  bind pure xi = xi.
Proof. intros X xi. unfold bind, pure. apply functional_extensionality. intro phi. f_equal. Qed.

Proposition associativity_extensional : forall {X} {Y} {Z} (xi:M X) (F:X->M Y) (G:Y->M Z),
  bind G (bind F xi) = bind (fun x => bind G (F x)) xi.
Proof. intros X Y Z xi F G. unfold bind. reflexivity. Qed.


Definition lift {X:Type} {Y:Type} (f : X -> Y) (mu : M X) :=
  bind (fun x => pure (f x)) mu.

Definition right_product {X:Type} {Y:Type} (mu : M X) (nu : M Y) :=
  bind ( fun x => ( bind (fun y => pure (pair x y)) nu ) ) mu.

Definition left_product {X:Type} {Y:Type} (mu : M X) (nu : M Y) :=
  bind ( fun y => ( bind (fun x => pure (pair x y)) mu ) ) nu.


#[export]
Instance Continuation_Monad : Monad M :=
{
  Mpure := @pure;
  Mbind := @bind;

  (* coherence conditions *)
  Mleft_identity := @left_identity_extensional;
  Mright_identity := @right_identity_extensional;
  Massociativity := @associativity_extensional;
}.


(* Requires bind functional_extensionality *)
Theorem lift_associative : forall {A:Type} {B:Type} {C:Type} (a : M A) (f:A->B) (g:B->C),
  lift g (lift f a) = lift (fun x => g (f x)) a.
Proof.
  intros A B C. intros a f g.
  unfold lift.
  rewrite -> associativity_extensional.
  f_equal.
Qed.

Theorem product_pure_pure : forall {A:Type} {B:Type} (x : A) (y : B), left_product (pure x) (pure y) = right_product (pure x) (pure y).
Proof.
  intros A B. intros x b.
  unfold left_product. unfold right_product.
  apply bind_extensionality. intro psi. 
  rewrite -> left_identity. rewrite -> left_identity.
  rewrite -> left_identity. rewrite -> left_identity.
  reflexivity.
Qed.

(* Requires bind functional_extensionality *)
Theorem product_pure_monad : forall {A:Type} {B:Type} (x : A) (b : M B), left_product (pure x) b = right_product (pure x) b.
Proof.
  intros A B. intros x b.
  unfold left_product. unfold right_product.
  apply bind_extensionality. intro psi. 
  rewrite -> left_identity.
  f_equal.
Qed.

(* Requires bind functional_extensionality *)
Theorem product_monad_pure : forall {A:Type} {B:Type} (a : M A) (y : B), left_product a (pure y) = right_product a (pure y).
Proof.
  intros A B. intros a y.
  unfold left_product. unfold right_product.
  apply bind_extensionality. intro psi. 
  rewrite -> left_identity.
  f_equal.
Qed.



(* An operator intended to be similar to logical disjunction. *)
Parameter ast : T -> T -> T.

(* An relation intended to be some kind of equivalence on X. *)
Parameter X : Type.
Parameter sim : X -> X -> T.

(* An operator similar to the intersection of compact and closed sets. *)
Definition oast : M X -> (X -> T) -> M X := 
  fun mu phi => fun psi : X -> T => mu (fun x : X => ast (phi x) (psi x)).

(* An operator similar to the embedding of compact sets into closed sets for a Hausdorff space. *)
Definition osim : M X -> (X -> T) :=
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

Conjecture conditioning : forall {Y:Type} (sigma : M (X * Y) -> (X -> M Y)) (C : M (X * Y)),
  (forall (x : X) (psi : Y -> T),
      ast ((lift fst C) (fun x'=>sim x x')) (sigma C x psi) = C ( fun (xy':X*Y) => ast (sim x (fst xy')) (psi (snd xy')) ) ) 
    -> Mright_skew (lift fst C) (sigma C) = C.


End ContinuationMonads.
