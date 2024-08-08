(******************************************************************************
 *  utilities/LimitMonads.v
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

Require Export Words.
Require Export Monads.

Require Import DependentChoice.


Section LimitMonads.


Definition is_inverse_limit {M : Type -> Type} {MonadM : Monad M}{X} (A : forall (n: nat), M (Wrd n X)) (Alim : M (Seq X)) :=
  forall n, Mlift (projw n) Alim = A n.

Definition is_inverse_sequence {M : Type -> Type} {MonadM : Monad M} {X} (A : forall n, M (Wrd n X)) : Prop :=
  forall (m n : nat) (p : m <= n), Mlift (restr m p) (A n) = A m.

Definition has_inverse_limits (M : Type -> Type) (MonadM : Monad M) := forall (X:Type)
   (A : forall (n: nat), M (Wrd n X)), is_inverse_sequence A -> 
    sig (fun Ainf : M (Seq X) => is_inverse_limit A Ainf).



Definition wlcons {X : Type} : forall n, (Wrd n X * X) -> Wrd (S n) X :=
  fun n wx => cat (fst wx) (snd wx).

Lemma restr_wlcons_id : forall {X : Type} n (p : n <= S n) w (x : X), restr n p (wlcons n (w,x)) = w.
Proof.
  intros X n q w x. 
  apply wrd_eq. intro kp. destruct kp as [k p].
  rewrite -> restr_at.
  unfold wlcons. simpl.
  apply cat_tail.
Qed.  


Definition is_infinite_skew_product {M : Type -> Type} {_ : Monad M} {X : Type}
  (F : forall n, Wrd n X -> M X) (Finf : M (Seq X)) :=
    (Mlift (projw 0) Finf = Mpure null_wrd) /\
      forall (n:nat),
        Mlift (wlcons n) (Mright_skew (Mlift (projw n) Finf) (F n)) =
        Mlift (projw (S n)) Finf.

Definition exists_infinite_skew_product (M : Type -> Type) (_ : Monad M) :=
  forall (X : Type) (F : forall n, Wrd n X -> M X), 
    exists (Finf : M (Seq X)),
      is_infinite_skew_product F Finf.
      
Definition has_infinite_skew_product (M : Type -> Type) (_ : Monad M) :=
  forall (X : Type) (F : forall n, Wrd n X -> M X), 
    sig (fun Finf : M (Seq X) => is_infinite_skew_product F Finf).


Definition skew_products {M} {MonadM : Monad M} {X} 
    (F : forall n, Wrd n X -> M X) : (forall n, M (Wrd n X)) :=
  fun (n : nat) =>
    nat_rect _ (Mpure null_wrd)
      (fun m A => Mlift (wlcons m) (Mright_skew A (F m))) n.

Definition fst_skew_product_is_id (M : Type -> Type) (MonadM : Monad M) :=
  forall (X : Type) (F : forall n, Wrd n X -> M X), forall n An, Mlift (fst) (Mright_skew An (F n)) = An.

Proposition inverse_limits_imply_skew_products (M : Type -> Type) (MonadM : Monad M) :
  fst_skew_product_is_id M MonadM -> has_inverse_limits M MonadM -> has_infinite_skew_product M MonadM.
Proof.
  intros Hs Hi. intros X F.
  set (A := skew_products F).
  assert (forall n, Mlift (restr n (PeanoNat.Nat.le_succ_diag_r n)) (A (S n)) = A n) as HSA. {
    intro n. 
    replace (A (S n)) with (skew_products F (S n)) by (reflexivity).
    unfold skew_products.
    simpl.
    rewrite -> Mlift_associative. 
    replace (compose (restr n (PeanoNat.Nat.le_succ_diag_r n)) (wlcons n)) with (@fst (Wrd n X) X).
    rewrite -> Hs.
    reflexivity.
    - apply functional_extensionality. intro wx. destruct wx as [w x]. simpl.
      unfold compose. unfold wlcons. simpl.
      symmetry.
      apply restr_wlcons_id.
  }
  assert (forall n k (p : n <= n + k), Mlift (restr n p) (A (n+k)) = A n) as HA''. {
    intro n. induction k.
    - replace (n+0) with n by (exact (eq_sym (PeanoNat.Nat.add_0_r n))).
      intro p.
      replace (restr n p) with (fun (w : Wrd n X) => w). rewrite -> Mlift_identity. reflexivity.
      apply functional_extensionality. intro w. symmetry. apply restr_id.
    - intro r.
      assert (n <= n + k) as p by (exact (PeanoNat.Nat.le_add_r n k)).
      rewrite <- (IHk p).
      rewrite <- (HSA (n+k)).
      assert (n + S k = S (n + k)) as e by (exact (PeanoNat.Nat.add_succ_r n k)).
      replace (A (S (n+k))) with (Mlift (cast_wrd e) (A (n + S k))).
      rewrite -> Mlift_associative. unfold compose.
      rewrite -> Mlift_associative. unfold compose.
      f_equal.
      apply functional_extensionality. intro w.
      rewrite -> restr_cast_wrd.
      rewrite -> restr_restr.
      apply restr_eq.
      -- rewrite <- e. rewrite -> Mlift_identity. reflexivity.
  }
  assert (forall m n (p : m <= n), Mlift (restr m p) (A n) = A m) as HA'. {
    intros m n p. 
    destruct (PeanoNat.Nat.le_exists_sub m n p) as [k [e _]].
    rewrite -> PeanoNat.Nat.add_comm in e.
    assert (m <= m + k) as p' by (exact (PeanoNat.Nat.le_add_r m k)).
    rewrite <- (HA'' m k p'). 
    replace (A (m+k)) with (Mlift (cast_wrd e) (A n)).
    rewrite -> Mlift_associative. unfold compose. f_equal.
    apply functional_extensionality. intro w.
    rewrite -> restr_cast_wrd. apply restr_eq.
    -- rewrite <- e. rewrite -> Mlift_identity. reflexivity.
  }
  assert (is_inverse_sequence A) as HA. { 
    unfold is_inverse_sequence. exact HA'. 
  }
  clear HSA. clear HA'. clear HA''.
  set (Ainf' := Hi X A HA).
  destruct Ainf' as [Ainf HAinf].
  set (Finf := Ainf).
  assert (is_infinite_skew_product F Finf) as HFinf. {
    unfold Finf.
    unfold is_infinite_skew_product.
    unfold is_inverse_limit in HAinf.
    split.
    - rewrite -> HAinf.
      unfold A, skew_products. simpl. reflexivity. 
    - intro n. rewrite -> HAinf. rewrite -> HAinf. unfold A.
      unfold skew_products. simpl. reflexivity. 
  }
  set (Finf' := exist (is_infinite_skew_product F) Finf HFinf).
  exact Finf'.
Qed.


End LimitMonads.
