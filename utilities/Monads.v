Section Monads.

Axiom extensionality : forall {A B} (f g : A -> B), (forall x, f x = g x) -> f = g.


Class Monad (M : Type -> Type) :=
{
    (* monad has pure and bind *)
    Mpure : forall {A : Type}, A -> M A;
    Mbind : forall {A B : Type}, (A -> M B) -> M A -> M B;
    
    (* coherence conditions *)
    Mleft_identity : forall {A B} (f:A->M B) (a:A), Mbind f (Mpure a) = f a;
    Mright_identity : forall {A} (x : M A), Mbind (@Mpure A) x = x;
    Massociativity : forall {A B C} (x : M A) (f : A -> M B) (g : B -> M C), 
        Mbind g (Mbind f x) = Mbind (fun a => Mbind g (f a)) x;

    (* Mfunctor_map : forall {A B : Type}, (A -> B) -> M A -> M B; *)
    Mfunctor_map {A B : Type} : (A -> B) -> M A -> M B 
      := fun (f : A -> B) (x : M A) => Mbind (fun x' => Mpure (f x')) x;
    Mlift {A B : Type} (f : A -> B) (a : M A) : M B
      := Mbind (fun a' => Mpure (f a')) a;

   Mleft_product {X Y : Type} : M X -> M Y -> (M (prod X Y)) :=
      fun (mu : M X) (nu : M Y) => Mbind ( fun y => ( Mbind (fun x => Mpure (pair x y)) mu ) ) nu;
   Mright_product {A B : Type} : M A -> M B -> M (prod A B)
      := fun mu nu => Mbind ( fun x => ( Mbind (fun y => Mpure (pair x y)) nu ) ) mu;
}.

(*
Axiom Mbind_extensionality : 
  forall {M : Type -> Type} {MonadM : Monad M} {A B : Type} (f1 f2 : A -> M B) (a : M A),
    (forall x, f1 x = f2 x) -> Mbind f2 a = Mbind f2 a.
*)

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C 
  := fun (a:A) => g (f a).

Theorem Mlift_associative : forall {M} {MonadM : Monad M} {A:Type} {B:Type} {C:Type} (a : M A) (f:A->B) (g:B->C),
  Mlift g (Mlift f a) = Mlift (compose g f) a.
Proof.
  intros M MonadM A B C. intros a f g.
  unfold Mlift.
  rewrite -> Massociativity.
  f_equal.
  apply extensionality.
  intro x.
  rewrite -> Mleft_identity.
  unfold compose.
  reflexivity.
Qed.

Lemma Mlift_identity {M} {_ : Monad M}: forall {A : Type}, 
  Mlift (fun (x : A) => x) = (fun (x : M A) => x).
Proof. 
  intros A.
  unfold Mlift.
  apply extensionality. intros al.
  rewrite -> Mright_identity.
  reflexivity.
Qed.

Lemma Mfunctorial_compose {M} {_ : Monad M}  : forall {A B C : Type} (f : A -> B) (g : B -> C),
  Mfunctor_map (fun x => g (f x))
    = fun x => (Mfunctor_map g) ((Mfunctor_map f) x).
Proof. 
  intros A B C f g.
  unfold Mfunctor_map.
  apply extensionality. intros al.
  rewrite -> Massociativity.
  f_equal.
  apply extensionality. intros a.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.

Lemma Mfunctorial_identity {M} {_ : Monad M}: forall {A : Type}, 
  (fun (x : M A) => x) = Mfunctor_map (fun (x : A) => x).
Proof. 
  intros A.
  unfold Mfunctor_map.
  apply extensionality. intros al.
  rewrite -> Mright_identity.
  reflexivity.
Qed.

Definition Mjoin {M} {_ : Monad M} {A : Type}
  := fun (mma : M (M A)) => Mbind (fun (ma : M A) => ma) mma.

(* Notation "unit" := pure; *)
Definition Munit {M} {MonadM} {A : Type} := @Mpure M MonadM A.
(* Notation "join" := mult; *)
Definition Mmult {M} {MonadM} {A : Type} := @Mjoin M MonadM A.

Definition Mcompose {M} {_ : Monad M} {A B C : Type} (g : B -> M C) (f : A -> M B) : A -> M C 
  := fun (a : A) => Mbind g (f a).

(* pure and join (unit and mult) are natural transformations.  *)
Lemma Mpure_natural_transformation {M} {_ : Monad M} : 
  forall {A B} (f : A -> B) (x : A), 
    (Mfunctor_map f) (Mpure x) = Mpure (f x).
Proof.  
  intros A B f x.
  unfold Mfunctor_map.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.

Lemma Mjoin_natural_transormation {M} {_ : Monad M} : forall {A B} (f : A -> B) (al : M A), 
  Mjoin (Mfunctor_map (Mfunctor_map f) (Mpure al))
    = (Mfunctor_map f) al. 
(*
  join ((Mfunctor_map (@Mfunctor_map M MonadM (M A) (M A) f)) x) = (Mfunctor_map f) (@mult A x);  
*)
Proof.
  intros A B f al.
  unfold Mjoin, Mfunctor_map.
  rewrite -> Mleft_identity.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.


Theorem Mproduct_pure_pure {M} {_ : Monad M} : forall {A:Type} {B:Type} (x : A) (y : B), 
  Mleft_product (Mpure x) (Mpure y) = Mright_product (Mpure x) (Mpure y).
Proof.
  intros A B. intros x b.
  unfold Mleft_product. unfold Mright_product.
  rewrite -> Mleft_identity. rewrite -> Mleft_identity.
  rewrite -> Mleft_identity. rewrite -> Mleft_identity.
  reflexivity.
Qed.

(* Requires extensionality *)
Theorem Mproduct_pure_monad {M} {MonadM  : Monad M} : forall {A:Type} {B:Type} (x : A) (b : M B),
  Mleft_product (Mpure x) b = Mright_product (Mpure x) b.
Proof.
  intros A B. intros x b.
  unfold Mleft_product. unfold Mright_product.
  rewrite -> Mleft_identity.
  f_equal.
  apply extensionality. intros b0.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.

(* Requires extensionality *)
Theorem Mproduct_monad_pure {M} {MonadM  : Monad M} : forall {A:Type} {B:Type} (a : M A) (y : B),
  Mleft_product a (Mpure y) = Mright_product a (Mpure y).
Proof.
  intros A B. intros a y.
  unfold Mleft_product. unfold Mright_product.
  rewrite -> Mleft_identity.
  f_equal.
  apply extensionality. intros al.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.

Definition Mright_skew {M} {MonadM : Monad M} {A B : Type} (mu : M A) (nu : A -> M B) : M (prod A B) :=
  Mbind( fun (a : A) => ( Mlift (fun (b : B) => (pair a b)) (nu a) ) ) mu.

(* A property of monads which holds if whenever bind is applied to a constant map, 
   the result is that constant. *)
Definition Mbind_const (M : Type -> Type) (MonadM : Monad M) : Prop
  := forall (A B : Type) (b: M B) (x : M A), 
       Mbind (fun (a:A) => b) x = b.

Lemma Mright_skew_first {M} {MonadM : Monad M} : 
  Mbind_const M MonadM -> forall {A B : Type} mu nu, 
                            Mfunctor_map (fst : A*B -> A) (Mright_skew mu nu) = mu.
Proof.
  intros Hbc.
  intros A B mu nu.
  unfold Mfunctor_map, Mright_skew, Mlift.
  rewrite -> Massociativity.
  assert (forall (a:A), 
    Mbind (fun (c : prod A B) => Mpure (fst c)) (Mbind (fun b => Mpure (a,b)) (nu a)) 
      = Mbind (fun (b:B) => Mpure a) (nu a)) as H1. {
    intro a.
    rewrite -> Massociativity.
    f_equal.
    apply extensionality. intro b.
    rewrite -> Mleft_identity.
    unfold fst.  
    reflexivity.
  }
  apply extensionality in H1.
  rewrite -> H1.
  assert (forall (a:A), 
      Mbind (fun (b : B) => Mpure (a)) (nu a) = Mpure a) as H2. {
   intro a.
   apply Hbc.
  }
  apply extensionality in H2.
  rewrite -> H2.
  rewrite -> Mright_identity.
  reflexivity.
Qed.

Lemma Mlift_compose {M} {MonadM : Monad M} : 
  forall {A B C} (f:A->B) (G:B->M C) (x:M A), 
    Mbind G (Mlift f x) = Mbind (compose G f) x.
Proof.
  intros A V C f G x.
  unfold Mlift, compose.
  rewrite -> Massociativity.
  f_equal.
  apply extensionality. intro a.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.

Definition tuple_associate {A B C : Type} (a_bc : prod A (prod B C)) : prod (prod A B) C
  := ((fst a_bc, fst (snd a_bc)), snd (snd a_bc)).

Definition tuple_unassociate {A B C : Type} (ab_c : prod (prod A B) C) : prod A (prod B C) 
  := (fst (fst ab_c), ( snd (fst ab_c), snd ab_c) ).
  
Proposition Mright_skew_associative {M} {MonadM : Monad M} : 
  forall {A B C : Type} (x : M A) (f : A -> M B) (g : (prod A B) -> M C),
    Mright_skew (Mright_skew x f) g = 
      Mlift tuple_associate (Mright_skew x (fun a => Mright_skew (f a) (fun b => g (a,b)))).
Proof.
  intros A B C x f g.
  unfold Mright_skew.
  unfold Mlift.
  rewrite -> Massociativity.
  rewrite -> Massociativity.
  f_equal.
  apply extensionality. intro a.
  rewrite -> Massociativity.
  rewrite -> Massociativity.
  rewrite -> Massociativity.
  f_equal.
  apply extensionality. intro b.
  rewrite -> Massociativity.
  rewrite -> Mleft_identity.
  f_equal.
  apply extensionality. intro c.
  rewrite -> Mleft_identity.
  rewrite -> Mleft_identity.
  unfold tuple_associate.
  simpl.
  reflexivity.
Qed.


End Monads.
