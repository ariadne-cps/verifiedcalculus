(******************************************************************************
 *  systems/monadic_system.v
 *
 *  Copyright 2023 Sacha L. Sindorf
 *  Copyright 2023-24 Pieter Collins
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


Require Import Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Words.
Require Import Monads.
Require Import LimitMonads.

Definition N := nat.

Lemma lt_succ_diag_r : forall n, n < S n.
Proof. exact Nat.lt_succ_diag_r. Qed.
Lemma lt_succ_succ_diag_r : forall n, n < S (S n).
Proof. intro n; transitivity (S n); now apply Nat.lt_succ_diag_r. Qed.


Definition Seq (X : Type) := N -> X.

Definition Tr (X : Type) : Type := N -> X.
Definition trace_equivalent {T X : Type} (x1 x2 : T -> X) : Prop :=
  forall t, x1 t = x2 t.
Notation "x1 ≡ x2" := (trace_equivalent x1 x2) (at level 70).

#[export]
#[refine]
Instance trace_equivalence {T X} : Equivalence (@trace_equivalent T X) := { }.
Proof.
  - intros x12 t. reflexivity.
  - intros x1 x2 H t. symmetry. exact (H t).
  - intros x1 x2 u3 H12 H23 t.
    transitivity (x2 t). exact (H12 t). exact (H23 t).
Qed.


Definition zip {T X1 X2} (s1 :T->X1) (s2 : T->X2) := fun t => (s1 t, s2 t).
Notation "( s1 ; s2 )" := (zip s1 s2) (at level 0).

Definition zip_pair {T X1 X2} (s1s2 : (T->X1) * (T->X2)) := zip (fst s1s2) (snd s1s2).
Definition unzip {T X1 X2} (s : T -> (X1*X2)) := (fun t=>fst (s t), fun t => snd (s t)).
Definition fst_unzip {T X1 X2} := fun x12 : T-> (X1*X2) => fst (unzip x12).
Definition snd_unzip {T X1 X2} := fun x12 : T -> (X1*X2) => snd (unzip x12).

Lemma zip_unzip {X1 X2} :
  forall (x12 : Tr (X1*X2)),
    zip (fst (unzip x12)) (snd (unzip x12)) ≡ x12.
Proof.
  intros x12 n. unfold zip,unzip. simpl.
  now rewrite <- surjective_pairing.
Qed.

Inductive sig_pair {A B : Type} (P : A -> B -> Prop) : Type :=
  exist_pair : forall (x : A) (y : B), P x y -> sig_pair P.

Definition unzip_eqv {X1 X2} (x12 : Tr (X1*X2)) : @sig_pair (Tr X1) (Tr X2) (fun x1 x2 => (x1;x2) ≡ x12 )
  := exist_pair _ (fst (unzip x12)) (snd (unzip x12)) (zip_unzip x12).

Lemma unzip_proj {X1 X2}
  {x12 : Tr (X1*X2)} {x1 : Tr X1} {x2 : Tr X2} :
    forall (e : (x1,x2) = unzip x12),
      x1 = fst (unzip x12) /\ x2 = snd (unzip x12).
Proof.
  intros H. split.
  - apply (f_equal fst) in H. simpl in H. now rewrite -> H.
  - apply (f_equal snd) in H. simpl in H. now rewrite -> H.
Qed.

Lemma unzip_proj_at {X1 X2}
  {x12 : Tr (X1*X2)} {x1 : Tr X1} {x2 : Tr X2} :
    forall (e : (x1,x2) = unzip x12), forall n,
      x1 n = fst (x12 n) /\ x2 n = snd (x12 n).
Proof.
  intros H n. split.
  - apply (f_equal fst) in H. simpl in H. now rewrite -> H.
  - apply (f_equal snd) in H. simpl in H. now rewrite -> H.
Qed.

Definition restr_prec {X n} : Wrd (S n) X -> Wrd n X :=
  fun (x : Wrd (S n) X) => restr n (Nat.le_succ_diag_r n) x.




Lemma unit_wrd_at {X} : forall (x:X) kp, (unit_wrd x) kp = x.
Proof. intros x kp. now unfold unit_wrd. Qed.

Context `{M : Type -> Type } `{Monad_M : Monad M}
  `{has_inverse_limits_M : @has_inverse_limits M Monad_M}
  `{unique_inverse_limits_M : @unique_inverse_limits M Monad_M}
  `{preserves_constants_M : @preserves_constants M Monad_M}.

Definition Mproduct {X1 X2} : M X1 -> M X2 -> M (X1*X2) := @Mright_product M Monad_M X1 X2.

Definition Behaviour (U Y : Type) : Type := (Tr U) -> M (Tr Y).

Definition causal {U Y : Type} (b : Tr U -> M (Tr Y)) :=
  forall u1 u2 : Tr U, forall n,
     (proj n u1 ≡ proj n u2) ->
       (Mlift (proj n) (b u1) = Mlift (proj n) (b u2)).

Definition strictly_causal {U Y : Type} (b : Tr U -> M (Tr Y)) :=
  forall u1 u2 : Tr U, forall n,
     (proj n u1 ≡ proj n u2) ->
       (Mlift (proj (S n)) (b u1) = Mlift (proj (S n)) (b u2)).

Definition mixed_causal {UA UD Y : Type} (b : Tr (UA*UD) -> M (Tr Y)) :=
  forall u1 u2 : Tr (UA*UD), forall n,
    let (ua1,ud1) := unzip u1 in
    let (ua2,ud2) := unzip u2 in
     (proj (S n) ua1 ≡ proj (S n) ua2) -> (proj n ud1 ≡ proj n ud2) ->
       (Mlift (proj (S n)) (b u1) = Mlift (proj (S n)) (b u2)).

Definition FiniteMixedBehaviour (UA UD Y : Type) : Type :=
  forall n, Wrd (S n) UA -> Wrd n UD -> M (Wrd (S n) Y).

Definition is_composed_behaviour {Y1 Y2 : Type}
  (b1 : Seq Y2 -> M (Seq Y1))
  (b2 : Seq Y1 -> M (Seq Y2))
  (b12 : M (Seq (Y1*Y2))) := 
        let my1y2 := Mlift unzip b12 : M (Seq Y1 * Seq Y2) in
        let my1 := (Mlift fst my1y2) : M (Seq Y1) in
        let my2 := (Mlift snd my1y2) : M (Seq Y2) in
          Mleft_skew b1 my2 = my1y2 /\ Mright_skew my1 b2 = my1y2.

Definition is_finite_composed_behaviour {Y1 Y2 : Type}
  (b1 : forall n, (Wrd n Y2) -> M (Wrd (S n) Y1))
  (b2 : forall n, (Wrd (S n) Y1) -> M (Wrd (S n) Y2))
  (b12 : forall n, M (Wrd (S n) (Y1*Y2))) : Prop :=
    forall (n : N),
        let y1y2 := Mlift unzip (b12 n) : M ((Wrd (S n) Y1) * (Wrd (S n) Y2)) in
        let y1 := Mlift fst y1y2 : M (Wrd (S n) Y1) in
        let y2 := Mlift snd y1y2 : M (Wrd (S n) Y2) in
          Mbind (b1 n) (Mlift restr_prec y2) = y1 /\ Mbind (b2 n) y1 = y2.



Inductive System (U X Y : Type) : Type :=
  | state_space_model (f:X->U->M X) (h:X->U->Y) (e:M X).
Arguments state_space_model {U X Y}.

Inductive StrictlyCausalSystem (U X Y : Type) : Type :=
  | strictly_causal_state_space_model (f:X->U->M X) (h:X->Y) (e:M X).
Arguments strictly_causal_state_space_model {U X Y}.

Inductive InputFreeSystem (X Y : Type) : Type :=
  | input_free_state_space_model (f:X->M X) (h:X->Y) (e:M X).
Arguments input_free_state_space_model {X Y}.



Definition last {X} {n} (xw : Wrd (S n) X) : X :=
  xw (ord n (Nat.lt_succ_diag_r n)).


Definition pair_cat {X} {n} (xlx: Wrd n X * X) : Wrd (S n) X :=
  cat (fst xlx) (snd xlx).

Fixpoint finite_trajectory {U X : Type} {n:N}
  (f:X->U->M X) (e:M X) : (Wrd n U) -> M (Wrd (S n) X) :=
    match n with
    | O => fun _ => Mlift (@unit_wrd X) e
    | S m => fun u =>
      let xm := finite_trajectory f e (restr_prec u) in
        Mlift pair_cat (Mright_skew xm (fun x => f (last x) (last u)))
    end.

Fixpoint finite_input_free_trajectory {X : Type} 
  (f:X->M X) (e:M X) (n:N) : M (Wrd (S n) X) :=
    match n with
    | O => Mlift (@unit_wrd X) e
    | S m => 
      let xm := finite_input_free_trajectory f e m in
        Mlift pair_cat (Mright_skew xm (fun x => f (last x)))
    end.

Definition finite_signal {X U Y : Type} {n : N}
  (h:X->U->Y) (u:Wrd n U) (x:Wrd n X) : Wrd n Y :=
    fun k => h (x k) (u k).

Definition finite_strictly_causal_signal {X Y : Type} {n : N}
  (h:X->Y) (x:Wrd n X) : Wrd n Y :=
    fun k => h (x k).

Definition finite_behaviour {U X Y}
  (s : System U X Y) : forall n, Wrd (S n) U -> M (Wrd (S n) Y) :=
    match s with | state_space_model f h e => fun n u => 
      Mlift (finite_signal h u) (finite_trajectory f e (restr_prec u))
    end.

Definition finite_strictly_causal_behaviour {U X Y}
  (s : StrictlyCausalSystem U X Y)
    : forall n, Wrd n U -> M (Wrd (S n) Y) :=
    match s with | strictly_causal_state_space_model f h e => fun n u => 
      Mlift (finite_strictly_causal_signal h) (finite_trajectory f e u)
    end.

Definition finite_input_free_behaviour {X Y}
  (s : InputFreeSystem X Y)
    : forall n, M (Wrd (S n) Y) :=
    match s with | input_free_state_space_model f h e => fun n => 
      Mlift (finite_strictly_causal_signal h) (finite_input_free_trajectory f e n)
    end.

Lemma finite_trajectory_null {U X : Type} :
 forall (f:X->U->M X) (e:M X) (u:Wrd O U),
   finite_trajectory f e u = Mlift unit_wrd e.
Proof. intros. trivial. Qed.

Lemma finite_trajectory_succ {U X : Type} {n:N} :
 forall (f:X->U->M X) (e:M X) (u:Wrd (S n) U),
   finite_trajectory f e u =
     Mlift pair_cat (Mright_skew (finite_trajectory f e (restr_prec u)) (fun x => f (last x) (last u))).
Proof. intros. trivial. Qed.

Lemma finite_input_free_trajectory_null {X : Type} :
 forall (f:X->M X) (e:M X),
   finite_input_free_trajectory f e 0 = Mlift unit_wrd e.
Proof. intros. trivial. Qed.

Lemma finite_input_free_trajectory_succ {X : Type} :
 forall (f:X->M X) (e:M X) (n:N),
   finite_input_free_trajectory f e (S n) =
     Mlift pair_cat (Mright_skew (finite_input_free_trajectory f e n) (fun x => f (last x))).
Proof. intros. trivial. Qed.

Lemma unit_wrd_at_id {X} : 
  forall (x : Wrd 1 X) (kp : Ordinal 1), unit_wrd (x kp) = x.
Proof. 
  intros x kp. unfold unit_wrd. apply wrd_1_eq. destruct kp as [k p].
  apply wrd_at. simpl. exact (proj1 (Nat.lt_1_r k) p).
Qed.

Lemma restr_prec_pair_cat {X} {n} : forall (xs_x : (Wrd n X) * X),
  restr_prec (pair_cat xs_x) = fst xs_x.
Proof. 
  intros xs_x. unfold restr_prec, pair_cat, cat, restr. simpl.
  apply wrd_eq. intros kp. destruct kp as [k p]. simpl.
  destruct (Compare_dec.le_lt_eq_dec k n) as [q|q].
  now apply wrd_at_eq. lia.
Qed.

Proposition finite_trajectory_spec {U X : Type} :
  forall (f:X->U->M X) (e:M X) (t : forall n, (Wrd n U) -> M (Wrd (S n) X)),
       (forall (u : Wrd O U), let x0 := t O u in x0 = Mlift unit_wrd e) ->
         (forall (n:N) (u : Wrd (S n) U), let u' := restr_prec u in
           let x := t (S n) u in let x' := t n u' in
             x = Mlift pair_cat (Mright_skew x' (fun (x' : Wrd (S n) X) => f (last x') (last u)))) -> 
               forall n (u : Wrd n U), t n u = finite_trajectory f e u.
Proof.
  intros f e t He Hf.
  assert (forall n (u : Wrd (S n) U), t n (restr_prec u) = Mlift restr_prec (t (S n) u)) as Ht. {
    intros n u.
    rewrite -> (Hf n u).
    rewrite -> Mlift_associative.
    rewrite <- Mlift_extensional with (f := @fst (Wrd (S n) X) X).
    rewrite -> ((preserves_constants_implies_fst_skew_product_is_id Monad_M) preserves_constants_M).
    reflexivity.
    - unfold compose. intros xs_x. now rewrite -> restr_prec_pair_cat.
  }
  induction n.
  - intro u. specialize (He u). simpl in He.
    rewrite -> finite_trajectory_null. 
    exact He.
  - intros u. specialize (Hf n u). simpl in Hf.
    rewrite -> finite_trajectory_succ.
    rewrite <- (IHn (restr_prec u)).
    exact Hf.
Qed.

Proposition input_free_finite_trajectory_spec {X : Type} :
  forall (f:X->M X) (e:M X) (t : forall n,M (Wrd (S n) X)),
       (let x0 := t O in x0 = Mlift unit_wrd e) ->
         (forall (n:N), let x := t (S n) in let x' := t n in
             x = Mlift pair_cat (Mright_skew x' (fun (x' : Wrd (S n) X) => f (last x')))) -> 
               forall n, t n = finite_input_free_trajectory f e n.
Proof.
  intros f e t He Hf.
  assert (forall n, t n = Mlift restr_prec (t (S n))) as Ht. {
    intros n.
    rewrite -> (Hf n).
    rewrite -> Mlift_associative.
    rewrite <- Mlift_extensional with (f := @fst (Wrd (S n) X) X).
    rewrite -> ((preserves_constants_implies_fst_skew_product_is_id Monad_M) preserves_constants_M).
    reflexivity.
    - unfold compose. intros xs_x. now rewrite -> restr_prec_pair_cat.
  }
  induction n.
  - simpl in He.
    rewrite -> finite_input_free_trajectory_null. simpl.
    exact He.
  - specialize (Hf n). simpl in Hf.
    rewrite -> finite_input_free_trajectory_succ. simpl.
    rewrite <- IHn.
    exact Hf.
Qed.

(*
Conjecture finite_trajectory_pair_spec {U X : Type} :
  forall (f:X->U->M X) (e:M X) (t : forall n, (Wrd n U) -> M (Wrd (S n) X)),
     Mlift frst (t 0 (@null_wrd U)) = e -> 
       (forall (n:N) (u : Wrd (S n) U), let x := t (S n) u in
         Mlift last_pair x = Mright_skew (Mlift last (Mlift restr_prec x)) (fun x => f x (last u))) ->
           forall n (u : Wrd n U), t n u = finite_trajectory f e u.
*)




(* Define the composition of state space models. *)
Definition compose_systems {X1 X2 Y1 Y2 : Type}
  (s1 : StrictlyCausalSystem Y2 X1 Y1)
  (s2 : System Y1 X2 Y2)
  : (InputFreeSystem (X1*X2) (Y1*Y2)) :=
    match s1 with | strictly_causal_state_space_model f1 h1 e1 =>
    match s2 with | state_space_model f2 h2 e2 =>
      let e12 : M (X1*X2) := Mproduct e1 e2 in

      let h_y1 : X1*X2->Y1 :=
        fun x12 => h1 (fst x12) in
      let h_y2 : X1*X2->Y2 :=
        fun x12 => h2 (snd x12) (h_y1 x12) in
      let h12 : X1*X2->Y1*Y2 :=
        fun x12 => (h_y1 x12, h_y2 x12) in

      let f_x1 : X1*X2->M X1 :=
        fun x12 => f1 (fst x12) (h_y2 x12) in
      let f_x2:  X1*X2->M X2 :=
        fun x12 => f2 (snd x12) (h_y1 x12) in
      let f12 := fun x => Mproduct (f_x1 x) (f_x2 x) in
        input_free_state_space_model f12 h12 e12
    end
    end
.

Lemma fst_Mproduct {X1 X2} :
  forall (e1 : M X1) (e2 : M X2),
    Mlift fst (Mproduct e1 e2) = e1.
Proof.
  intros e1 e2. unfold Mproduct, Mright_product.
  rewrite -> Mlift_bind_associative.
  transitivity (Mbind (fun (x1:X1) => Mpure x1) e1).
  apply Mbind_extensional; intro x1.
  rewrite -> Mlift_bind_associative.
  transitivity (Mbind (fun (x2:X2) => Mpure x1) e2).
  apply Mbind_extensional; intro x2.
  unfold Mlift. now rewrite -> Mleft_identity.
  - now apply preserves_constants_M.
  - now rewrite -> Mright_identity.
Qed.

Lemma snd_Mproduct {X1 X2} :
  forall (e1 : M X1) (e2 : M X2),
    Mlift snd (Mproduct e1 e2) = e2.
Proof.
  intros e1 e2. unfold Mproduct, Mright_product.
  rewrite -> Mlift_bind_associative.
  rewrite -> Mbind_extensional with (F':=fun x1:X1 =>e2).
  now apply preserves_constants_M.
  - intro x1. rewrite -> Mlift_bind_associative. 
    rewrite <- Mbind_extensional with (F:=fun x2:X2 =>Mpure x2). 
    now rewrite -> Mright_identity.
    intro x2. unfold Mlift. now rewrite -> Mleft_identity. 
Qed.

Lemma Mlift_left_identity {M} {Monad_M : Monad M} :
  forall A B (f : A -> B) (a : A), Mlift f (Mpure a) = Mpure (f a).
Proof. intros A B f a. unfold Mlift. now rewrite -> Mleft_identity. Qed.

Lemma Mlift_product {X1 X2 Y} :
  forall (f : X1 -> X2 -> Y) (a1 : M X1) (a2 : M X2),
    Mbind (fun x1 => Mlift (fun x2 => f x1 x2) a2) a1
      = Mlift (fun x12 => f (fst x12) (snd x12)) (Mproduct a1 a2).
Proof.
  intros f a1 a2. unfold Mproduct, Mright_product.
  rewrite -> Mlift_bind_associative.
  apply Mbind_extensional; intro x1.
  rewrite -> Mlift_bind_associative.
  apply Mbind_extensional; intro x2.
  rewrite -> Mlift_left_identity.
  simpl. reflexivity.
Qed.




Lemma product_function {X1 X2 Y} : forall (f : (X1 * X2) -> Y) (A1 : M X1) (A2 : M X2),
  Mlift f (Mproduct A1 A2) = Mbind (fun x1 => Mlift (fun x2 => f (x1,x2)) A2) A1.
Proof.
  intros f A1 A2.
  unfold Mproduct, Mright_product.
  rewrite -> Mlift_bind_associative.
  apply Mbind_extensional; intro x1.
  rewrite -> Mlift_bind_associative.
  unfold Mlift.
  apply Mbind_extensional; intro x2.
  rewrite -> Mleft_identity.
  reflexivity.
Qed.


Lemma unit_wrd_eq {X} : forall (x1 x2 : X), x1=x2 <-> unit_wrd x1 = unit_wrd x2.
Proof. 
  intros x1 x2. split.
  - intro Hx. now rewrite <- Hx.
  - intro Hw. set (k:=ord 0 (Nat.lt_succ_diag_r 0)).
    transitivity (unit_wrd x2 k).
    transitivity (unit_wrd x1 k).
    -- now rewrite -> unit_wrd_at.
    -- now rewrite <- Hw.
    -- now rewrite -> unit_wrd_at.
Qed.




Variable (X1 X2 Y1 Y2 : Type).
Variable (f1 : X1 -> Y2 -> M X1) (f2 : X2 -> Y1 -> M X2) (e1 : M X1) (e2 : M X2) (h1 : X1 -> Y1) (h2 : X2 -> Y1 -> Y2).
Definition s1 {n:N} : Wrd n X1 -> Wrd n Y1 := fun x1 => (fun kp => h1 (x1 kp)). 
Definition s2 {n:N} : Wrd n Y1 -> Wrd n X2 -> Wrd n Y2 := fun y1 x2 => (fun kp => h2 (x2 kp) (y1 kp)). 

Fixpoint t1 {n:N} : Wrd n Y2 -> M (Wrd (S n) X1) := match n with 
  | S m => fun y2 => Mbind (fun w1:Wrd (S m) X1 => Mlift (fun x1:X1=>cat w1 x1) (f1 (last w1) (last y2))) (t1 (restr_prec y2))
  | O => fun _ => Mlift unit_wrd e1 end.        
Fixpoint t2 {n:N} : Wrd n Y1 -> M (Wrd (S n) X2) := match n with 
  | S m => fun y1 => Mbind (fun w2:Wrd (S m) X2 => Mlift (fun x2:X2=>cat w2 x2) (f2 (last w2) (last y1))) (t2 (restr_prec y1))
  | O => fun _ => Mlift unit_wrd e2 end.        
Definition b1 {n:N} : (Wrd n Y2) -> M (Wrd (S n) Y1) := fun y2 => Mlift s1 (t1 y2).
Definition b2 {n:N} : Wrd (S n) Y1 -> M (Wrd (S n) Y2) := fun y1  => Mlift (s2 y1) (t2 (restr_prec y1)).

Definition f12 : (X1*X2) -> M (X1*X2) := fun x12 => Mproduct (f1 (fst x12) (h2 (snd x12) (h1 (fst x12)))) (f2 (snd x12) (h1 (fst x12))).
Definition e12 : M (X1*X2) := Mproduct e1 e2.
Definition h12 : X1*X2 -> Y1*Y2 := fun x12 => (h1 (fst x12), h2 (snd x12) (h1 (fst x12))).
Definition s12 {n:N} : Wrd n (X1*X2) -> Wrd n (Y1*Y2) := fun x12 => (fun kp => h12 (x12 kp)). 

Definition Mscat {X} {n:N} (F:X->M X) (x:Wrd (S n) X) : M (Wrd (S (S n)) X) :=
  Mlift (fun xf:X=>cat x xf) (F (last x)).

Definition Mscatu {U X} {n:N} (F:X->U->M X) (u:Wrd (S n) U) (x:Wrd (S n) X) : M (Wrd (S (S n)) X) :=
  Mlift (fun xf:X=>cat x xf) (F (last x) (last u)).


Fixpoint t12 (n:N) : M (Wrd (S n) (X1*X2)) := match n with 
  | S m => Mbind (Mscat f12) (t12 m)
  | O => Mlift unit_wrd e12 end.     

Lemma s12_unit_word : forall (x12 : X1*X2), s12 (unit_wrd x12) = unit_wrd (h12 x12).
Proof. intro x12. unfold s12. apply wrd_1_eq. now repeat rewrite -> unit_wrd_at. Qed.
Lemma s2_unit_word : forall (x2 : X2) (y1 : Y1), s2 (unit_wrd y1) (unit_wrd x2) = unit_wrd (h2 x2 y1).
Proof. intros x2 y1. unfold s2. apply wrd_1_eq. now repeat rewrite -> unit_wrd_at. Qed.
Lemma unzip_unit_word {X1 X2} : forall (x12 : X1*X2), unzip (unit_wrd x12) = (unit_wrd (fst x12), unit_wrd (snd x12)).
Proof. intro x12. apply pair_equal_spec. split. all: apply wrd_1_eq; now repeat rewrite -> unit_wrd_at. Qed.
Lemma fst_unzip_unit_word {X1 X2} : forall (x12 : X1*X2), fst (unzip (unit_wrd x12)) = unit_wrd (fst x12).
Proof. intro x12. now rewrite -> unzip_unit_word. Qed.
Lemma snd_unzip_unit_word {X1 X2} : forall (x12 : X1*X2), snd (unzip (unit_wrd x12)) = unit_wrd (snd x12).
Proof. intro x12. now rewrite -> unzip_unit_word. Qed.

Definition m0x12 := Mlift unit_wrd e12.
Definition m0y12 := Mlift s12 m0x12.
Definition m0y1y2 := Mlift unzip m0y12.
Definition m0y1 := Mlift fst m0y1y2.
Definition m0y2 := Mlift snd m0y1y2.


Lemma compose0 : Mbind b1 (Mlift restr_prec m0y2) = m0y1 /\  Mbind b2 m0y1 = m0y2.
Proof.
  split.
  - unfold m0y1, m0y2, m0y1y2, m0y12, m0x12, e12.
    replace (Mlift restr_prec m0y2) with (Mpure (@null_wrd Y2)).
    2: { unfold Mlift. rewrite <- Mbind_extensional with (F := fun _ : Wrd 1 Y2 => Mpure (@null_wrd Y2)).
         now rewrite -> preserves_constants_M . intros y2. f_equal. now apply wrd_0_eq. }
    rewrite -> Mleft_identity.
    unfold b1, t1.
    rewrite -> Mlift_associative; unfold compose.
    rewrite <- Mlift_extensional with (f := compose unit_wrd h1).
    2: { intro x1. unfold compose. apply wrd_1_eq. now repeat rewrite -> unit_word_at. }
    repeat rewrite -> Mlift_associative; unfold compose.
    rewrite <- Mlift_extensional with (f := fun x12 : X1*X2 => unit_wrd (fst (h12 x12))).
    2: { intro x12. unfold unzip. simpl. apply wrd_1_eq. now repeat rewrite -> unit_word_at. }
    rewrite <- Mlift_extensional with (f := fun x12 : X1*X2 => unit_wrd (h1 (fst x12))).
    2: { intro x12. apply unit_wrd_eq with (x1:=h1 (fst x12)). now unfold h12. }
    rewrite <- Mlift_extensional with (f := compose (fun x1 => unit_wrd (h1 x1)) (@fst X1 X2)).
    2: { intro x12. trivial. }
    rewrite <- Mlift_associative.
    replace (Mlift fst (Mproduct e1 e2)) with e1.
    2: now rewrite -> fst_Mproduct. 
    reflexivity.
  - unfold b2, t2, m0y1, m0y2, m0y1y2, m0y12, m0x12, e12.
    repeat rewrite -> Mlift_associative; rewrite -> Mbind_lift_associative; unfold compose.
    rewrite <- Mlift_extensional with (f:=compose unit_wrd (fun x12:X1*X2=>snd(h12 x12))).
    2: { intro x12; rewrite -> s12_unit_word; now rewrite -> unzip_unit_word. }
    rewrite <- Mbind_extensional with (F:=fun x12:X1*X2=>Mlift (compose unit_wrd (fun x2=>snd(h12 (fst x12,x2)))) e2).
    2: { intro x12. rewrite -> Mlift_associative; unfold compose. apply Mlift_extensional; intro x2.
         rewrite -> s12_unit_word, -> fst_unzip_unit_word, s2_unit_word. now unfold h12. }
    rewrite <- Mbind_extensional with (F:=compose (fun x1:X1=>Mlift (fun x2=>unit_wrd(snd(h12 (x1,x2)))) e2) fst).
    2: { intro x12; now unfold compose. }
    rewrite <- Mbind_lift_associative.
    rewrite -> fst_Mproduct.
    unfold Mproduct, Mright_product. unfold compose.
    rewrite -> Mlift_bind_associative.
    apply Mbind_extensional; intro x1.
    rewrite -> Mlift_bind_associative.
    unfold Mlift. apply Mbind_extensional; intro x2.
    rewrite -> Mleft_identity.
    reflexivity.
Qed.

Lemma compose : forall n, 
  let mx12 := t12 n in let my12 := Mlift s12 mx12 in 
  let my1 := Mlift fst_unzip my12 in let my2 := Mlift snd_unzip my12 in
    Mbind b1 (Mlift restr_prec my2) = my1 /\  Mbind b2 my1 = my2.
Proof.
  assert ( forall n, t12 (S n) = Mbind (Mscat f12) (t12 n) ) as Ht12. { trivial. } 
  assert ( forall n (y2 : Wrd (S n) Y2), t1 y2 = Mbind (Mscatu f1 y2) (t1 (restr_prec y2)) ) as Ht1. { trivial. } 
  assert ( forall n (y1 : Wrd (S n) Y1), t2 y1 = Mbind (Mscatu f2 y1) (t2 (restr_prec y1)) ) as Ht2. { trivial. } 
  induction n.
  admit.
  intros mx12 my12 my1 my2.
  destruct IHn as [IHn1 IHn2].
  remember (t12 n) as mx12' eqn:Emx12'. 
  remember (Mlift s12 mx12') as my12' eqn:Emy12'. 
  remember (Mlift fst_unzip my12') as my1' eqn:Emy1'. 
  remember (Mlift snd_unzip my12') as my2' eqn:Emy2'. 
  assert (Mlift restr_prec mx12 = mx12') as Hmx12'. admit.
  assert (Mlift restr_prec my12 = my12') as Hmy12'. admit.
  assert (Mlift restr_prec my1 = my1') as Hmy1'. admit.
  assert (Mlift restr_prec my2 = my2') as Hmy2'. admit.
  split.
  - rewrite -> Hmy2'. rewrite <- IHn2. 
    unfold my1, my12, mx12. rewrite -> Ht12. rewrite <- Emx12'.
    rewrite -> Mlift_associative.
    rewrite <- Mlift_extensional with (f := compose s1 (@fst_unzip (Ordinal (S (S n))) X1 X2)).
    2: admit.
    rewrite <- Mlift_associative.
    rewrite -> Mlift_bind_associative.
(***** This is looking good! ****)
    unfold b1. 
    rewrite <- Mlift_bind_associative.
    f_equal. (* Eliminate s1 *)
(***** Still looking good! ****)
    rewrite <- Mlift_bind_associative; 
    rewrite -> Emy1', Emy12'.
    
    repeat rewrite -> Mbind_lift_associative; unfold compose.
    rewrite -> Mbind_associative.

    remember (fun x12 => (x12,h12 x12)) as xh12 eqn:Exh12.

    remember (Mright_skew mx12' (fun x12 => Mpure (s12 x12))) as mxy12' eqn:Emxy12'.
    unfold b2.
    unfold f12.
    unfold Mproduct, Mright_product.

Check Ht1.
    rewrite <- Mbind_extensional with (F:=fun (y2 : Wrd (S n) Y2) => Mbind (Mscatu f1 y2) (t1 (restr_prec y2))).
    2: { intro y2; now rewrite -> Ht1. }

(* Probably CAN'T use extensionality here. *)
    apply Mbind_extensional; intro x12.


Check (Mlift (s2 (fst_unzip (s12 x12)))
     (t2 (restr_prec (fst_unzip (s12 x12))))).
    rewrite -> Ht1.
    rewrite -> Ht2.

    rewrite -> Mbind_lift_associative.

    rewrite -> Mlift_associative.

    rewrite <- Mlift_bind_associative.

unfold Mscat.
    unfold f12.
 simpl.
Admitted.

(*
Variable (UA UD X1 X2 Y1 Y2 : Type).
Variable (f1 : X1 -> UA * (UD * Y2) -> M X1) (h1 : X1 -> UA -> Y1) (e1 : M X1).
Variable (f2 : X2 -> (UA * Y1) * UD -> M X2) (h2 : X2 -> UA * Y1 -> Y2) (e2 : M X2).

Definition e12 := Mproduct e1 e2.

Definition h12 := fun (x12:X1*X2) (ua:UA) => 
  let (x1,x2):=x12 in let y1:=h1 x1 ua in let y2:=h2 x2 (ua,y1) in 
    (y1,y2).
Definition f1' := ( fun x1 x2 ua ud => 
  let y1 := h1 x1 ua in let y2 := h2 x2 (ua,y1) in
    f1 x1 (ua,(ud,y2)) ) : X1 -> X2 -> UA -> UD -> M X1.
Definition f2' := ( fun x1 x2 ua ud => 
  let y1 := h1 x1 ua in let y2 := h2 x2 (ua,y1) in
    f2 x2 ((ua,y1),ud) ) : X1 -> X2 -> UA -> UD -> M X2.
Definition f12 := fun (x12:X1*X2) (uad:UA*UD) => 
  let (x1,x2) := x12 in let (ua,ud) := uad in 
    Mproduct (f1' x1 x2 ua ud) (f2' x1 x2 ua ud) : M (X1*X2).
*)



(* Show that the behaviour of the composition of two systems
   is a composition of the behaviours of the components. *)
Theorem composed_system_behaviour {UA UD X1 X2 Y1 Y2 : Type} :
   forall (s1 : StrictlyCausalSystem Y2 X1 Y1)
          (s2 : System Y1 X2 Y2),
          is_finite_composed_behaviour
            (finite_strictly_causal_behaviour s1)
            (finite_behaviour s2)
            (finite_input_free_behaviour (compose_systems s1 s2)).
Proof.
   intros s1 s2.
   remember (compose_systems s1 s2) as s12 eqn:Es12.
   destruct s1 as (f1,h1,e1).
   destruct s2 as (f2,h2,e2).
   destruct s12 as (f12,h12,e12).

   unfold compose_systems in Es12.
   injection (Es12) as Ef12 Eh12 Ee12. clear Es12.
   revert Ef12 Eh12 Ee12; intros Ef12 Eh12 Ee12.

   unfold is_composed_behaviour.
   intro n. induction n.
   - clear Ef12.
     unfold finite_strictly_causal_behaviour, finite_behaviour, finite_input_free_behaviour.
     remember (finite_input_free_trajectory f12 e12 0) as mx12 eqn:Emx12.
     assert (mx12 = Mlift unit_wrd e12) as Hmx12. {
       rewrite -> Emx12. rewrite -> finite_input_free_trajectory_null. reflexivity. }
     rewrite -> Hmx12.
     repeat rewrite -> Mlift_associative; unfold compose.
     split.
     -- rewrite <- Mbind_extensional with (F := fun _ : Wrd 0 Y2 => Mlift (compose unit_wrd h1) e1).
        rewrite <- Mlift_extensional with (f := fun _ : X1*X2 => @null_wrd Y2).
        rewrite <- Mlift_extensional with (f := fun x12 : X1*X2 => (compose (compose unit_wrd h1) fst) x12).
        repeat rewrite -> preserves_constants_M.
        repeat rewrite <- Mlift_associative. 
        rewrite -> Ee12. now rewrite -> fst_Mproduct.
        --- intro x12. unfold compose. 
            unfold finite_strictly_causal_signal, unzip. simpl.
            apply wrd_1_eq. repeat rewrite -> unit_wrd_at.
            rewrite -> Eh12. simpl. reflexivity.
        --- intro x12. now apply wrd_0_eq.
        --- intro y2. rewrite -> finite_trajectory_null.
            rewrite -> Mlift_associative. unfold compose.
            apply Mlift_extensional. intro x1. 
            unfold finite_strictly_causal_signal.
            apply wrd_1_eq. repeat rewrite -> unit_wrd_at.
            reflexivity.
     -- rewrite <- Mbind_extensional with (F := fun y1 : Wrd 1 Y1 => Mlift (fun x2 => unit_wrd (h2 x2 (last y1))) e2).
        rewrite <- Mlift_extensional with (f := fun x12 : X1*X2 => unit_wrd (h1 (fst x12))).
        rewrite <- Mlift_extensional with (f := fun x12 : X1*X2 => unit_wrd (snd (h12 x12))).
        rewrite -> Mbind_lift_associative; unfold compose.
        replace (fun x12 => Mlift (fun x2 => unit_wrd (h2 x2 (last (unit_wrd (h1 (fst x12)))))) e2) 
          with (compose (fun x1 : X1 => Mlift (fun x2 => unit_wrd (h2 x2 (h1 x1))) e2) (@fst X1 X2)).
        rewrite <- Mbind_lift_associative.
        rewrite -> Ee12. rewrite -> fst_Mproduct.
        rewrite -> Eh12. simpl.
        rewrite -> product_function.
        apply Mbind_extensional; intro x1.
        apply Mlift_extensional; intro x2.
        simpl. reflexivity.
        --- unfold compose.
            apply functional_extensionality; intro x12.
            apply Mlift_extensional; intro x2.
            unfold last; rewrite -> unit_wrd_at.
            reflexivity.
        --- intro x12. unfold finite_strictly_causal_signal, unzip. simpl.
            apply wrd_1_eq. repeat rewrite -> unit_wrd_at. reflexivity.
        --- intro x12. unfold finite_strictly_causal_signal, unzip. simpl.
            apply wrd_1_eq. repeat rewrite -> unit_wrd_at. 
            rewrite -> Eh12. simpl. reflexivity.
        --- intro y1. 
            rewrite -> finite_trajectory_null.
            unfold last, finite_signal. 
            rewrite -> Mlift_associative; unfold compose.
            apply Mlift_extensional; intro x2.
            apply wrd_1_eq. repeat rewrite -> unit_wrd_at. 
            f_equal. now apply wrd_at_eq.
  - admit.
(*
Mbind (fun y2 : Tr Y2 => b1 (ua; (ud; y2))) my2 = my1 /\
Mbind (fun y1 : Tr Y1 => b2 ((ua; y1); ud)) my1 = my2
*)

Admitted.




