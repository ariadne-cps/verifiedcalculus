(******************************************************************************
 *  systems/monadic_systems.v
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


Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Words.
Require Import Monads.
Require Import LimitMonads.

Require Import FunctionalExtensionality.

Definition N := nat.

Definition Seq (X : Type) := nat -> X.

Definition Tr (X : Type) : Type := nat -> X.
Definition trace_equivalent {T X : Type} (x1 x2 : T -> X) : Prop :=
  forall t, x1 t = x2 t.
Notation "x1 ≡ x2" := (trace_equivalent x1 x2) (at level 70).
Notation "x1 '|<' n '|≡' x2" := (forall m, m<n -> x1 m = x2 m) (at level 40).
Notation "x1 |≤ n |≡ x2" := (forall m, m <= n -> x1 m = x2 m) (at level 40).

#[export]
#[refine]
Instance trace_equivalence {T X} : Equivalence (@trace_equivalent T X) := { }.
Proof.
  - intros x12 t. reflexivity.
  - intros x1 x2 H t. symmetry. exact (H t).
  - intros x1 x2 u3 H12 H23 t.
    transitivity (x2 t). exact (H12 t). exact (H23 t).
Qed.


Definition zip {X1 X2} (x1 : Tr X1) (x2 : Tr X2) : Tr (X1*X2) := 
  fun n => (x1 n, x2 n).
Notation "( x1 ; x2 )" := (zip x1 x2) (at level 0).

Definition unzip {X1 X2} (x12 : Tr (X1*X2)) : (Tr X1) * (Tr X2) := 
  (fun n => fst (x12 n), fun n => snd (x12 n)).
Definition fst_unzip {X1 X2} := fun x12 : Tr (X1*X2) => fst (unzip x12).
Definition snd_unzip {X1 X2} := fun x12 : Tr (X1*X2) => snd (unzip x12).

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

(*
Fixpoint proj {X} (n : nat) (s : nat -> X) : list X :=
  match n with | 0 => nil | S m => cons (s m) (proj m s) end.
*)

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




Context `{M : Type -> Type } `{Monad_M : Monad M}
  `{has_inverse_limits_M : @has_inverse_limits M Monad_M}
  `{unique_inverse_limits_M : @unique_inverse_limits M Monad_M}
  `{preserves_constants_M : @preserves_constants M Monad_M}.

Definition Mproduct {X1 X2} : M X1 -> M X2 -> M (X1*X2) := @Mright_product M Monad_M X1 X2.


Definition Behaviour (U Y : Type) : Type := (Tr U) -> M (Tr Y).

Inductive System (UA UD X Y : Type) : Type :=
  | state_space_model (f:X->UA*UD->M X) (h:X->UA->Y) (e:M X)
.
Arguments state_space_model {UA UD X Y}.

Definition unit_wrd {X} (x : X) : Wrd 1 X := fun kp => x.

Definition restr_prec {X} {n} (x : Wrd (S n) X) : Wrd n X := restr n (Nat.le_succ_diag_r n) x.

Definition pair_cat {X} {n} (xw_x : (Wrd n X)*X) : Wrd (S n) X := cat (fst xw_x) (snd xw_x).


Definition last {X} {n} (x : Wrd (S n) X) : X := x (ord n (Nat.lt_succ_diag_r n)).

Fixpoint finite_trajectory' {U X : Type} {n : N}
    (f:X->U->M X) (e:M X) : Wrd n U -> M (Wrd (S n) X) :=
  match n return (Wrd n U -> M (Wrd (S n) X)) with
  | O => fun _ => Mlift unit_wrd e 
  | S m => fun (u : Wrd (S m) U) => let mx := finite_trajectory' f e (restr_prec u) : M (Wrd (S m) X) in 
      Mlift pair_cat ( Mright_skew mx (fun (x : Wrd (S m) X) => f (last x) (last u)) )
  end.

Proposition finite_trajectory_succ' {U  X} {n} (f:X->U->M X) (e:M X) : 
  forall (u : Wrd (S n) U), finite_trajectory' f e u =
    Mlift pair_cat ( Mright_skew (finite_trajectory' f e (restr_prec u)) (fun (x : Wrd (S n) X) => f (last x) (last u)) ).
Proof. intros u. trivial. Qed.

Lemma lt_succ_diag_r : forall n, n < S n.
Proof. exact Nat.lt_succ_diag_r. Qed.
Lemma lt_succ_succ_diag_r : forall n, n < S (S n).
Proof. intros n. transitivity (S n). exact (Nat.lt_succ_diag_r n). exact (Nat.lt_succ_diag_r (S n)). Qed.

Proposition finite_trajectory_pair' {U  X} {n} (f:X->U->M X) (e:M X) : 
  forall (u : Wrd (S n) U),
    let mxSn := finite_trajectory' f e u in let mxn := finite_trajectory' f e (restr_prec u) in
    let HnltSn := lt_succ_diag_r n : n < S n in
    let HnltSSn := lt_succ_succ_diag_r n : n < S (S n) in
    let HSnltSSn := lt_succ_diag_r (S n) : S n < S (S n) in
      Mlift (fun (x : Wrd (S (S n)) X) => (x (ord n HnltSSn),x (ord (S n) HSnltSSn))) mxSn 
        = Mright_skew (Mlift (fun (x : Wrd (S n) X) => x (ord n HnltSn)) mxn) (fun (x :X) => f x (last u)).
Proof.
  intros u. 
  rewrite -> finite_trajectory_succ'.
  remember (finite_trajectory' f e (restr_prec u)) as mx eqn:Emx.
  simpl.
  set (HnltSn := lt_succ_diag_r n : n < S n).
  rewrite -> Mlift_associative; unfold compose.
  setoid_rewrite <- Mlift_extensional 
    with (f := fun xs_x => ((fst xs_x) (ord n HnltSn), snd xs_x)).
  2: { intros xs_x. 
       destruct xs_x as [xs x]; simpl.
       unfold pair_cat, cat; simpl.
       apply pair_equal_spec; split.
       - destruct (Compare_dec.le_lt_eq_dec n (S n)) .
         now apply wrd_at_eq. contradiction (Nat.neq_succ_diag_r n).
       - destruct (Compare_dec.le_lt_eq_dec (S n) (S n)).
         contradiction (Nat.lt_irrefl (S n)). reflexivity.
  }
  unfold Mright_skew.
  rewrite -> Mlift_bind_associative.
  setoid_rewrite <- Mbind_extensional 
    with (F := fun (xs : Wrd (S n) X) => Mlift (fun (x : X) => (last xs, x)) (f (last xs) (last u))).
  2: { intro xs.
       rewrite -> Mlift_associative. 
       apply Mlift_extensional; intro x.
       unfold compose; simpl. 
       unfold last. apply pair_equal_spec. split.
       now apply wrd_at_eq. reflexivity. 
  }
  rewrite -> Mbind_lift_associative; unfold compose.
  apply Mbind_extensional; intros xs. 
  replace (xs (ord n HnltSn)) with (last xs). 2: { unfold last; now apply wrd_at_eq. }
  reflexivity.
Qed.


Definition list_next {X} (F : X -> M X) (e : M X) (xl : list X) : M X :=
  match xl with 
   | nil => e
   | cons x _ => F x
  end. 

Fixpoint trajectory_list {U X : Type}
  (f:X->U->M X) (e:M X) (u:nat->U) (n:nat) : M (list X) :=
    match n with
    | O => Mlift (fun x => cons x nil) e
    | S m => 
      let xwm := trajectory_list f e u m in
      let fu := fun xw => list_next (fun x => f x (u m)) e xw in
        Mlift (fun (xlx : (list X) * X) => cons (snd xlx) (fst xlx)) (Mright_skew xwm fu)
    end
.
Fixpoint signal_list {X U Y : Type }
  (h:X->U->Y)
  (xl:list X)
  (u:nat->U)
  : list Y :=
    match xl with
    | nil => nil
    | cons x xl' => cons (h x (u (length xl))) (signal_list h xl' u)
    end
.


Definition next {U X} {n} (F : X -> U -> M X) (e : M X) (u : Seq U) : Wrd n X -> M X :=
  match n with 
   | O => fun _ => e
   | S m => fun x => F (x (ord m (Nat.lt_succ_diag_r m))) (u m) 
  end. 



(* Trajectory x:ℕ→X is defined by x[n+1] = f(x[n], u[n]) *)
Fixpoint finite_trajectory {U X : Type}
  (f:X->U->M X) (e:M X) (u: Seq U) (n:nat) : M (Wrd n X) :=
(*
    let hf := fun u => fun xw => next (fun x => f x u) e xw in
*)
    match n with
    | 0 => Mlift (fun x => (fun k => x)) e
    | S m => 
      let xwm := finite_trajectory f e u m in
      let fu := fun xw => next f e u xw in
        Mlift pair_cat (Mright_skew xwm fu)
    end
.

Definition finite_signal {X U Y : Type} {n : nat}
  (h:X->U->Y) (x:Wrd n X) (u:Seq U) : Wrd n Y :=
    fun k => h (x k) (u k).


Lemma finite_trajectory_succ {U X : Type} {n:nat} :
 forall (f:X->U->M X) (e:M X) (u:Seq U),
   finite_trajectory f e u (S n) =
    let xwn := finite_trajectory f e u n in
    let fu := fun xw => next f e u xw in
      Mlift pair_cat (Mright_skew xwn fu).
Proof. intros. trivial. Qed.


Lemma finite_trajectory_last {U X : Type} {n:nat} :
 forall (f:X->U->M X) (e:M X) (u:Seq U),
   finite_trajectory f e u (S (S n)) =
    let xwSn := finite_trajectory f e u (S n) in
    let fxu := fun xw => f (last xw) (u n) in
      Mlift pair_cat (Mright_skew xwSn fxu).
Proof. intros. trivial. Qed.


Lemma restr_prec_finite_trajectory {U X : Type} :
  forall (f:X->U->M X) (e:M X) (u : nat -> U), 
  forall (n:nat), Mlift (restr_prec) (finite_trajectory f e u (S n)) = (finite_trajectory f e u n).
Proof.
  intros f e u n.
  set (Hpc := preserves_constants_M).
  rewrite -> finite_trajectory_succ. simpl.
  remember (finite_trajectory f e u n) as xwn eqn:Exwn.
  rewrite -> Mlift_associative.
  replace (compose restr_prec pair_cat) with (@fst (Wrd n X) X).
  - set (Hsk := preserves_constants_implies_fst_skew_product_is_id _ Hpc).
    now apply Hsk.
  - unfold compose, restr_prec, pair_cat.
    apply functional_extensionality. intro xnx.
    destruct xnx as [xn x]. simpl.
    symmetry; now apply restr_cat_id.
Qed.

Proposition restr_finite_trajectory {U X : Type} :
  forall (f:X->U->M X) (e:M X) (u : nat -> U), 
  forall (m n:nat) (p:m<=n), Mlift (restr m p) (finite_trajectory f e u n) = (finite_trajectory f e u m).
Proof.
  intros f e u.
  set (Hpc := preserves_constants_M).
  remember (finite_trajectory f e u) as ft eqn:Eft.
  intro m. 
  assert (forall k (p:m<=m+k),
    Mlift (restr m p) (ft (m+k)) = ft m) as H. {
    induction k.
    - replace (m+0) with m. intro p.
      replace (restr m p) with (fun (x:Wrd m X)=>x).
      unfold Mlift.
      now rewrite -> Mright_identity.
      apply functional_extensionality. intro xw.
      now rewrite -> restr_id.
      symmetry; now apply Nat.add_0_r.
    - replace (m+S k) with (S (m+k)) by lia. 
      intro p.
      assert (m <= m+k) as q. lia.
      transitivity (Mlift (restr m q) (Mlift restr_prec (ft (S (m+k))))).
      -- rewrite -> Mlift_associative.
         f_equal. unfold compose, restr_prec.
         apply functional_extensionality. intro x.
         rewrite -> restr_restr. f_equal. now apply proof_irrelevance.
      -- rewrite <- (IHk q).
         f_equal. rewrite -> Eft.
         now apply restr_prec_finite_trajectory.
   }
   intros n p. set (k := n - m). 
   assert (n = m+k) as Hn by lia.
   revert p. rewrite -> Hn. now apply H.
Qed.

Definition trajectory {U X : Type} (f:X->U->M X) (e:M X) (u:nat->U) : M (Seq X) :=
   let xw := finite_trajectory f e u in
     let Hxw := restr_finite_trajectory f e u in
       let xs := has_inverse_limits_M X xw Hxw in
         proj1_sig xs.


Definition sgnl {X U Y : Type}
  (h : X -> U -> Y) (u : Tr U) : Tr X -> Tr Y := 
    fun x n => h (x n) (u n).

(* Output signal y:ℕ→Y is defined by y[n] = h(x[n], u[n]) *)
Definition signal {X U Y : Type}
  (h:X->U->Y) (x:M (Tr X)) (u:Tr U) : M (Tr Y) := 
    Mlift (fun xs => fun n => h (xs n) (u n)) x.

Lemma lift_signal {X U Y} :
  forall (h : X -> U -> Y) (u : Tr U) (x : M (Tr X)), 
    signal h x u = Mlift (sgnl h u) x.
Proof. intros h u x. trivial. Qed.

Definition behaviour {UA UD Y X : Type}
  (s:System UA UD X Y) : Behaviour (UA*UD) Y := 
    fun (u:Tr (UA*UD)) =>
      match s with
      | state_space_model f h e =>
        signal h (trajectory f e u) (fun k => fst (u k))
      end.


Definition causal {U Y : Type} (b : Tr U -> M (Tr Y)) :=
  forall u1 u2 : Tr U, forall n,
     (proj n u1 ≡ proj n u2) ->
       (Mlift (proj n) (b u1) = Mlift (proj n) (b u2))
.

Definition strictly_causal {U Y : Type} (b : Tr U -> M (Tr Y)) :=
  forall u1 u2 : Tr U, forall n,
     (proj n u1 ≡ proj n u2) ->
       (Mlift (proj (S n)) (b u1) = Mlift (proj (S n)) (b u2))
.

Definition mixed_causal {UA UD Y : Type} (b : Tr (UA*UD) -> M (Tr Y)) :=
  forall u1 u2 : Tr (UA*UD), forall n,
    let (ua1,ud1) := unzip u1 in
    let (ua2,ud2) := unzip u2 in
     (proj (S n) ua1 ≡ proj (S n) ua2) -> (proj n ud1 ≡ proj n ud2) ->
       (Mlift (proj (S n)) (b u1) = Mlift (proj (S n)) (b u2))
.

Definition word_strictly_causal' {U Y} (b : Tr U -> M (Tr Y)) (Hscb : strictly_causal b)
   : {bw : forall n (p:0<n), Wrd n U -> M (Wrd (S n) Y)  
       | forall us n p, bw n p (proj n us) = Mlift (proj (S n)) (b us) }.
Proof.
  assert (forall n k, 0<n -> min k (pred n) < n) as q by lia.
  set (bw := fun n (p:0<n) (uw:Wrd n U) => Mlift (proj (S n)) (b (fun k => uw (ord (min k (pred n)) (q n k p))))).
  assert (forall us n p, bw n p (proj n us) = Mlift (proj (S n)) (b us)) as Hbw. {
    intros us n p.
    set (bwu := bw n p (proj n us)).
    unfold bw in bwu. unfold bwu. simpl. clear bw bwu.
    unfold strictly_causal in Hscb. revert Hscb; intro Hscb.
    apply Hscb.
    intro kp. rewrite -> proj_at, -> proj_at, -> proj_at. 
    destruct kp as [k pk]. simpl. f_equal. lia. 
  }
  exact (exist _ bw Hbw).
Qed.

Definition word_strictly_causal {U Y} (b : Tr U -> M (Tr Y)) (Hscb : strictly_causal b) (u_default : U)
   : {bw : forall n, Wrd n U -> M (Wrd (S n) Y)  
       | forall us n, bw n (proj n us) = Mlift (proj (S n)) (b us) }.
Proof.
  set (pad := fun {n:nat} (uw : Wrd n U) => (fun (k:nat) => 
    match Compare_dec.le_lt_dec n k with
    | left _ => u_default | right p => uw (ord k p) end) : Tr U).  
  set (bw := fun n (uw:Wrd n U) => Mlift (proj (S n)) (b (pad n uw))).
  assert (forall us n, bw n (proj n us) = Mlift (proj (S n)) (b us)) as Hbw. {
    intros us n.
    set (bwu := bw n (proj n us)).
    unfold bw in bwu. unfold bwu. simpl. clear bw bwu.
    unfold strictly_causal in Hscb. revert Hscb; intro Hscb.
    apply Hscb.
    intro kp. unfold pad. rewrite -> proj_at, -> proj_at. 
    destruct kp as [k pk]. simpl. 
    destruct (Compare_dec.le_lt_dec n k). lia.
    rewrite -> proj_at. f_equal.
  }
  exact (exist _ bw Hbw).
Qed.


Lemma proj_trajectory {U X} :
  forall f (e : M X) (u : Tr U) n, Mlift (proj n) (trajectory f e u) = finite_trajectory f e u n.
Proof.
  intros f e u n. unfold trajectory.
  unfold has_inverse_limits.
  destruct (has_inverse_limits_M X (finite_trajectory f e u) (restr_finite_trajectory f e u)) as [xs Hxs].
  unfold proj1_sig. 
  unfold is_inverse_limit in Hxs.
  exact (Hxs n).
Qed.

Lemma finite_trajectory_strictly_causal  {U X : Type} :
  forall (f : X->U->M X) (e:M X) (u u' : Seq U),
    forall (n:nat), 
      proj n u = proj n u' ->
        finite_trajectory f e u (S n) = finite_trajectory f e u' (S n).
Proof.
  induction n.
  - intro Hu.
    rewrite -> finite_trajectory_succ. simpl. reflexivity.
  - intro HuSn.
    assert (proj n u = proj n u') as Hun. {
      rewrite <- agree_proj in HuSn.
      rewrite <- agree_proj.
      intros k Hkltn. apply HuSn. lia.
    }
    specialize (IHn Hun).
    rewrite -> finite_trajectory_succ.
    rewrite -> IHn.
    unfold next.
    replace (u n) with (u' n).
    reflexivity.
    rewrite <- agree_proj in HuSn.
    symmetry; apply HuSn. lia.
Qed.
  
Lemma trajectory_strictly_causal  {U X : Type} :
  forall (f : X->U->M X) (e:M X),
      forall (u u' : Tr U), forall (n:nat), 
        (proj n u = proj n u') ->
          Mlift (proj (S n)) (trajectory f e u) = 
            Mlift (proj (S n)) (trajectory f e u').
Proof.
  intros f e u u' n Hun.
  rewrite -> proj_trajectory, -> proj_trajectory.
  now apply finite_trajectory_strictly_causal.
Qed.

Lemma trajectory_input_extensional {U X : Type} :
  forall (f : X->U->M X) (e:M X),
      forall (u u' : Tr U),
        (u ≡ u') -> trajectory f e u = trajectory f e u'.
Proof.
  intros f e u u' Hu.
  assert (forall n, Mlift (proj (S n)) (trajectory f e u) 
      = Mlift (proj (S n)) (trajectory f e u')) as HSfinite. {
    intro n. apply trajectory_strictly_causal.
    apply wrd_eq. intro kp. destruct kp as [k p].
    rewrite -> proj_at, proj_at. simpl. exact (Hu k).
  }
  assert (forall n, Mlift (proj n) (trajectory f e u) 
      = Mlift (proj n) (trajectory f e u')) as Hfinite. {
    intro n. destruct n.
    - set (restr01 := @restr X 1 0 (Nat.le_succ_diag_r 0)).
      replace (proj 0) with (compose restr01 (proj 1)).
      rewrite <- Mlift_associative, <- Mlift_associative.
      f_equal. exact (HSfinite 0). unfold compose.
      apply functional_extensionality. intro xs.
      unfold restr01. now rewrite <- proj_restr_eq.
    - exact (HSfinite n).
  }
  clear HSfinite.
  set (Huil := unique_inverse_limits_M).
  unfold unique_inverse_limits in Huil.
  set (A := fun n => Mlift (@proj X n) (trajectory f e u)).
  specialize (Huil X (fun n => Mlift (@proj X n) (trajectory f e u))).
  apply Huil. clear Huil.
  - unfold is_inverse_sequence. intros m n p.
    rewrite -> Mlift_associative. f_equal.
  - unfold is_inverse_limit. reflexivity.
  - unfold is_inverse_limit.
    intro n. symmetry. exact (Hfinite n).
Qed.

Lemma trajectory_succ {U X : Type} :
 forall (f:X->U->M X) (e:M X) (u:nat->U),
   let xs := trajectory f e u : M (Tr X) in
     forall (n:nat), 
       Mlift (fun xs' => (xs' n, xs' (S n))) xs = Mright_skew (Mlift (fun xs' => xs' n) xs) (fun x => f x (u n)).
Proof.
  intros f e u xs n. 
  assert (n < S (S n)) as p by lia.
  assert (S n < S (S n)) as q by lia.
  assert (n < S n) as r by lia.
  transitivity (Mlift (compose (fun xw' => (xw' (ord n p), xw' (ord (S n) q))) (proj (S (S n)))) xs).
  - f_equal.
  - rewrite <- Mlift_associative.
    unfold xs. 
    replace (Mlift (proj (S (S n))) (trajectory f e u))
      with (finite_trajectory f e u (S (S n))).
    2: now rewrite -> proj_trajectory.
    transitivity ( Mright_skew
  (Mlift (compose (fun xw' : Wrd (S n) X => xw' (ord n r)) (@proj X (S n))) (trajectory f e u)) (fun x => f x (u n)) ).
    rewrite  <- Mlift_associative.
    replace (Mlift (proj (S n)) (trajectory f e u))
      with (finite_trajectory f e u (S n)).
    rewrite -> finite_trajectory_succ.
    remember (finite_trajectory f e u (S n)) as xwn eqn: Exwn.
    unfold next, pair_cat.
    unfold Mright_skew.
(* Horrible mess *)
Admitted.


(* Show that the behaviour of a system satisfies the weaker definition of causal. *)
Lemma behaviour_mixed_causal :
  forall {UA UD X Y : Type}
    (s : @System UA UD X Y),
      mixed_causal (behaviour s).
Proof.
  intros UA UD X Y. intro s. unfold mixed_causal.
  intros u u'.
  remember (unzip u) as uad eqn:Euad. destruct uad as [ua ud].
  remember (unzip u') as uad' eqn:Euad'. destruct uad' as [ua' ud'].
  intro n.
  intros Hua Hud.
  assert (proj n u = proj n u') as Hu. {
    rewrite <- agree_proj. intros k p.
    destruct (unzip_proj_at Euad k) as [Euak Eudk].
    destruct (unzip_proj_at Euad' k) as [Euak' Eudk'].
    rewrite -> (surjective_pairing (u k)).
    rewrite -> (surjective_pairing (u' k)).
    f_equal.
    - rewrite <- Euak, <- Euak'.
      assert (k < S n) as q by lia.
      specialize (Hua (ord k q)).
      rewrite -> proj_at, -> proj_at in Hua. exact Hua.
    - rewrite <- Eudk, <- Eudk'.
      specialize (Hud (ord k p)).
      rewrite -> proj_at, -> proj_at in Hud. exact Hud.
  }
  destruct s as (f,h,e).
  unfold behaviour.
  unfold signal.
  rewrite -> Mlift_associative.
  rewrite -> Mlift_associative.
  unfold compose.
  replace (fun xs => proj (S n) (fun k => h (xs k) (fst (u' k)))) with ( compose (fun (xw : Wrd (S n) X) => fun kp => h (xw kp) (fst (u kp))) (fun xs => proj (S n) xs) ).
  rewrite <- Mlift_associative.
  replace (Mlift (fun xs => proj (S n) xs) (trajectory f e u'))
    with (finite_trajectory f e u' (S n)).
  replace (fun xs => proj (S n) (fun k => h (xs k) (fst (u k)))) with ( compose (fun (xw : Wrd (S n) X) => fun kp => h (xw kp) (fst (u kp))) (fun xs => proj (S n) xs) ).
  rewrite <- Mlift_associative.
  replace (Mlift (fun xs => proj (S n) xs) (trajectory f e u))
    with (finite_trajectory f e u (S n)).
  f_equal.
  apply finite_trajectory_strictly_causal.
  exact Hu.
  - symmetry; apply proj_trajectory.
  - apply functional_extensionality. intro xs. 
    unfold compose. simpl.
    apply functional_extensionality. intro kp. 
    rewrite -> proj_at,  -> proj_at. reflexivity.
  - symmetry; apply proj_trajectory.
  - apply functional_extensionality. intro xs. 
    unfold compose. simpl.
    apply functional_extensionality. intro kp. 
    rewrite -> proj_at,  -> proj_at.
    specialize (Hua kp).
    rewrite -> proj_at, -> proj_at in Hua.
    f_equal. 
    destruct kp as [k p]. simpl in *.
    replace (fst (u k)) with (ua k)
      by exact (proj1 (unzip_proj_at Euad k)).
    replace (fst (u' k)) with (ua' k)
      by exact (proj1 (unzip_proj_at Euad' k)).
    exact Hua.
Qed.



(* Define the composition of state space models. *)
Definition compose_systems {UA UD X1 X2 Y1 Y2 : Type}
  (s1 : System UA      (UD*Y2) X1 Y1)
  (s2 : System (UA*Y1)      UD X2 Y2)
  : (System UA UD (X1*X2) (Y1*Y2)) :=
    match s1 with
    | state_space_model f1 h1 e1 =>
      match s2 with
      | state_space_model f2 h2 e2 =>
        let e12 : M (X1*X2) := Mproduct e1 e2 in

        let h_y1 : X1*X2->UA->Y1 :=
          fun x12 ua => h1 (fst x12) ua in

        let h_y2 : X1*X2->UA->Y2 :=
          fun x12 ua => h2 (snd x12) (ua, h_y1 x12 ua) in

        let h12 : X1*X2->UA->Y1*Y2 :=
          fun x12 ua => (h_y1 x12 ua,
                         h_y2 x12 ua) in

        let f12 : X1*X2->UA*UD->M (X1*X2) :=
          (fun x12 u =>
            let f1xu:=f1 (fst x12) ((fst u), ((snd u), h_y2 x12 (fst u))) in
            let f2xu:=f2 (snd x12) (((fst u), h_y1 x12 (fst u)), (snd u)) in
              Mproduct f1xu f2xu) in
        state_space_model f12 h12 e12
      end
    end
.


(*
Lemma bind_factor {X Y Z} :
  forall (F : W -> M Z) (p : W -> X) (q : Z -> Y),
    (forall w w', p w = p w' -> Mlift q (F z) = Mlift q (F z')) ->
*)
 
Definition is_composed_behaviour {UA UD Y1 Y2 : Type}
  (b1 : Tr (UA*(UD*Y2)) -> M (Tr Y1))
  (b2 : Tr ((UA*Y1)*UD) -> M (Tr Y2))
  (b12 : Tr (UA*UD) -> M (Tr (Y1*Y2))) : Prop :=
    forall (u : Tr (UA*UD)),
    let (ua,ud) := unzip u in
      let b1' := (fun y2 => b1 (ua;(ud;y2))) : Tr Y2 -> M (Tr Y1) in
      let b2' := (fun y1 => b2 ((ua;y1);ud)) : Tr Y1 -> M (Tr Y2) in
        let y12 := (b12 (ua;ud)) : M (Tr (Y1*Y2)) in
        let y1 := (Mlift fst_unzip y12) : M (Tr Y1) in         
        let y2 := (Mlift snd_unzip y12) : M (Tr Y2) in
          Mbind b1' y2 = y1 /\ Mbind b2' y1 = y2.

Definition is_fixed_behaviour {X} (b : Tr X -> M (Tr X)) (B : M (Tr X)) :=
  Mbind b B = B.

Proposition fixed_structly_causal_behaviour_unique' {X} :
  forall (b : Tr X -> M (Tr X)) (B B' : M (Tr X)) (x_default : X), 
    strictly_causal b ->
      is_fixed_behaviour b B -> is_fixed_behaviour b B' ->
        forall n, Mlift (proj n) B = Mlift (proj n) B'.
Proof.
  assert (preserves_constants Monad_M) as Hpc
    by exact preserves_constants_M.
  intros b B B' x_default Hscb HB HB'.
  unfold is_fixed_behaviour in HB, HB'.
  unfold strictly_causal in Hscb.
  assert (exists bn : forall n, Wrd n X -> M (Wrd (S n) X), forall n xs, Mlift (proj (S n)) (b xs) = bn n (proj n xs)) as Hbn. {
    set (Hbw := word_strictly_causal b Hscb x_default).
    destruct Hbw as [bw Hbw].
    exists bw.
    intros n xs. symmetry. apply (Hbw xs n).
  }
  induction n.
  - unfold preserves_constants in Hpc.
    unfold Mlift.
    replace (fun xs => Mpure (proj 0 xs)) with (fun (xs : Seq X) => Mpure (@null_wrd X)).
     rewrite -> Hpc, -> Hpc. reflexivity.
    -- apply functional_extensionality. intro xs. 
       f_equal. now apply wrd_0_eq.
  - (*
    assert (n=0 \/ 0<n) as Hn by lia.
    destruct Hn as [Hn0|p].   
      rewrite -> Hn0 in *.
      rewrite <- HB, <- HB'.
      unfold Mlift. rewrite -> Massociativity, -> Massociativity.
      replace (fun xs => Mbind (fun xs' => Mpure (proj 1 xs')) (b xs))
        with (fun xs => Mlift (proj 1) (b xs)).
      apply IHn.
      assert (0<n) as p by admit.
    *)
    rewrite <- HB, <- HB'.
    unfold Mlift. rewrite -> Massociativity, -> Massociativity. 
    replace (fun xs => Mbind (fun xs' => Mpure (proj (S n) xs')) (b xs))
      with (fun xs => Mlift (proj (S n)) (b xs)).
    2: { apply functional_extensionality. intros xs. reflexivity. }
    destruct Hbn as [bn Hbn].
    replace (fun xs => Mlift (proj (S n)) (b xs))
      with (compose (bn n) (proj n)).
    rewrite <- Mlift_compose, <- Mlift_compose.
    f_equal. exact IHn.
    -- unfold compose. apply functional_extensionality; intro xs.
       now rewrite <- Hbn. 
Qed.

Theorem composed_mixed_causal_behaviour_unique
  {UA UD Y1 Y2 : Type} :
  forall (b1 : Behaviour (UA*(UD*Y2)) Y1)
         (b2 : Behaviour ((UA*Y1)*UD) Y2)
         (b12 b12' : Behaviour (UA*UD) (Y1*Y2)),
           mixed_causal b1 ->
           mixed_causal b2 ->
           is_composed_behaviour b1 b2 b12 ->
           is_composed_behaviour b1 b2 b12'
             -> forall (u : nat->UA*UD),
                  b12 u = b12' u.
Proof.
  intros b1 b2 b12 b12' Hmcb1 Hmcb2 Hb12 Hb12' u.
  generalize Hb12 Hb12'. intros Hb12c Hb12c'.
  unfold is_composed_behaviour in Hb12, Hb12'.
  specialize (Hb12 u); specialize (Hb12' u).
  remember (unzip u) as uad eqn:Huad; destruct uad as [ua ud];
  destruct (unzip_proj Huad) as [Hua Hud].
  
  remember (fun y2 => b1 (ua;(ud;y2))) as bu1 eqn:Ebu1.
  remember (fun y1 => b2 ((ua;y1);ud)) as bu2 eqn:Ebu2.

  assert (strictly_causal bu1) as Hscbu1. {
    unfold strictly_causal. intros y2 y2' n Hy2.
    rewrite -> Ebu1. apply Hmcb1. 
    simpl. reflexivity.
    simpl. intros kp. rewrite -> proj_at, -> proj_at.
    specialize (Hy2 kp). rewrite -> proj_at, -> proj_at in Hy2.
    destruct kp as [k p]. unfold zip. simpl.
    apply injective_projections. reflexivity.
    simpl. exact Hy2.
  }

  assert (causal bu2) as Hcbu2. {
    unfold causal. intros y1 y1' n Hy1.
    rewrite -> Ebu2. 
    destruct n. (* Need to consider n=0 case separately *)
    - replace (proj 0) with (fun (y2: Tr Y2) => @null_wrd Y2).
      unfold Mlift. repeat (rewrite -> preserves_constants_M).
      reflexivity.
      apply functional_extensionality. intro y2. 
      apply wrd_0_eq.
    - apply Hmcb2. 
      simpl. intros kp. rewrite -> proj_at, -> proj_at.
      specialize (Hy1 kp). rewrite -> proj_at, -> proj_at in Hy1.
      destruct kp as [k p]. unfold zip. simpl.
      apply injective_projections. reflexivity.
      simpl. exact Hy1.
      simpl. reflexivity.
  }

  remember (fun y2 => Mbind bu2 (bu1 y2)) as bu12 eqn:Ebu12.
  assert (strictly_causal bu12) as Hscbu12. {
    unfold strictly_causal. rewrite -> Ebu12.
    intros y2 y2' n Hy2.
    unfold causal in Hcbu2.
    repeat (rewrite -> Mlift_bind_associativity).
    remember (@proj Y1 (S n)) as q1 eqn:Eq1. 
    remember (@proj Y2 (S n)) as q2 eqn:Eq2. 
    remember (@proj Y2 n) as p2.
    set (r1 := fun (y1w : Wrd (S n) Y1) => fun (k : nat) =>    
      match Compare_dec.le_lt_dec (S n) k with 
        | left p => y1w (ord 0 (Nat.lt_0_succ n)) | right p => y1w (ord k p) end). 
    assert (forall w1, q1 (r1 w1) = w1) as Hr1. {
      intros w1. unfold r1. rewrite -> Eq1. unfold proj.
      apply functional_extensionality. intro kp.
      destruct kp as [k p]. 
      replace (val (S n) {| val := k; val_lt := p |}) with k.
      destruct (Compare_dec.le_lt_dec (S n) k) as [HSnlek|HkltSn].
      - lia. (* Contradiction *)
      - apply wrd_at_eq.
      - reflexivity.
    }
(*
    replace (fun y1 => Mlift q2 (bu2 y1)) with
      (fun y1 => Mlift q2 (bu2 (r1 (q1 y1)))).
    2: { apply functional_extensionality. intro y1. 
         remember (r1 (q1 y1)) as y1' eqn:Ey1'.
         rewrite -> Eq2. apply Hcbu2.
         intro kp. rewrite -> Ey1'. rewrite <- Eq1. 
         rewrite -> Hr1. reflexivity. }
    replace (fun y1 => Mlift q2 (bu2 (r1 (q1 y1))))
      with (compose (fun y1 => Mlift q2 (bu2 (r1 y1))) q1).
    repeat (rewrite <- Mlift_compose).
    rewrite -> Eq1. rewrite -> Hscbu1.
    - reflexivity.   
    - rewrite -> Heqp2 in Hy2. exact Hy2.
    - reflexivity.
  }

  assert (forall b, is_composed_behaviour b1 b2 b -> is_fixed_behaviour bu12 (Mlift snd_unzip (b (ua;ud)))) as fixed_composed_behaviour. {
    intros b Hb. specialize (Hb (ua;ud)). simpl in Hb.
    replace (fun n => ua n) with ua in Hb by trivial.
    replace (fun n => ud n) with ud in Hb by trivial.
    destruct Hb as [Hb1 Hb2].
    unfold is_fixed_behaviour.
    rewrite -> Ebu12.
    rewrite -> Ebu1, -> Ebu2.
    rewrite <- Massociativity.
    transitivity (Mbind (fun y1 : Tr Y1 => b2 ((ua; y1); ud))
        (Mlift fst_unzip (b (ua;ud)))).
    f_equal. exact Hb1.
    exact Hb2.
  }

  assert (forall n, Mlift (proj n) (Mlift snd_unzip (b12 (ua;ud))) = Mlift (proj n) (Mlift snd_unzip (b12' (ua;ud)))) as Hby2. {
    intros n.
    apply fixed_structly_causal_behaviour_unique' with (b:=bu12).
    - admit.
    - exact Hscbu12.
    - apply fixed_composed_behaviour. assumption.
    - apply fixed_composed_behaviour. assumption.
  }
  clear fixed_composed_behaviour.

  assert (forall n, Mlift (proj n) (Mlift fst_unzip (b12  (ua;ud))) = Mlift (proj n) (Mlift fst_unzip (b12'  (ua;ud)))) as Hby1. {
    admit.
  }

  assert (forall n, Mlift (proj n) (b12 (ua;ud)) = Mlift (proj n) (b12'  (ua;ud))) as Hpad. {
    intros n.
    admit.
  }

  assert (forall n, Mlift (proj n) (b12 u) = Mlift (proj n) (b12' u)) as Hp. {
    intros n.
    admit.
  }

  set (Huniquelim := unique_inverse_limits_M).
  unfold unique_inverse_limits in Huniquelim.
  apply Huniquelim with (A := fun n => Mlift (proj n) (b12 u)).
  - unfold is_inverse_sequence. intros m n p.
    rewrite -> Mlift_associative.
    f_equal.
  - unfold is_inverse_limit. reflexivity.
  - replace (fun n : nat => Mlift (proj n) (b12 u)) with 
        (fun n : nat => Mlift (proj n) (b12' u)) 
      by (apply functional_extensionality_dep; symmetry; now apply Hp).
    unfold is_inverse_limit. reflexivity.
*)
Admitted.

Theorem behaviour_composition_mixed_causal {UA UD Y1 Y2} :
  forall b1 b2 (b12 : Behaviour (UA*UD) (Y1*Y2)),
    (mixed_causal b1) -> (mixed_causal b2) ->  
      (is_composed_behaviour b1 b2 b12) ->
        (mixed_causal b12).
Proof.
Admitted.





(* Composing trajectories at system level doesn't work nicely. Definition is_composed_trajectory {UA UD X1 X2 Y1 Y2}
    (t1 : Tr (UA*(UD*X2)) -> M (Tr X1))
    (t2 : Tr ((UA*X1)*UD) -> M (Tr X2))
    (t12 : Tr (UA*UD) -> M (Tr (X1*X2))) : Prop :=
  forall (u : Tr (UA*UD)),
  let (ua,ud) := unzip u in
    let mx12 := (t12 (ua;ud)) : M (Tr (X1*X2)) in
    let mx1 := (Mlift fst_unzip mx12) : M (Tr X1) in         
    let mx2 := (Mlift snd_unzip mx12) : M (Tr X2) in
    let t1' := (fun x1x2 => t1 (ua;(ud;o2' (fst x1x2) (snd x1x2)))) : ((Tr X1) * (Tr X2)) -> M (Tr X1) in
    let t2' := (fun x1  => t2 ((ua;o1' x1);ud)) : Tr X1 -> M (Tr X2) in
      let mx12 := Mproduct mx1 mx2 in
        Mbind t1' mx12 = mx1 /\ Mbind t2' mx1 = mx2.

Definition system_trajectory {UA UD X Y} (s : System UA UD X Y) := 
  match s with | state_space_model f h e => trajectory f e end.

(* Show that the behaviour of the composition of two systems
   is a composition of the behaviours of the components. *)
Theorem composed_system_behaviour {UA UD X1 X2 Y1 Y2 : Type} :
   forall (s1 : System UA (UD*Y2) X1 Y1)
          (s2 : System (UA*Y1) UD X2 Y2),
          is_composed_trajectory 
            (system_trajectory s1)
            (system_trajectory s2)
            (system_trajectory (compose_systems s1 s2))
.
Proof.
   intros s1 s2.
   remember (compose_systems s1 s2) as s12 eqn:Es12.
   destruct s1 as (f1,h1,e1).
   destruct s2 as (f2,h2,e2).
   destruct s12 as (f12,h12,e12).
   unfold compose_systems in Es12.
   injection (Es12) as Ef12 Eh12 Ee12. clear Es12.
   unfold is_composed_trajectory.
   intros u.
   simpl; simpl in *.
   remember (trajectory f12 e12 u) as x12 eqn:Ex12.
*)

Lemma proj_trajectory_succ {U X} :
    forall (f : X -> U -> M X) (e : M X) (u : Tr U) (n : nat),
  Mlift (proj (S n)) (trajectory f e u) = 
     Mlift pair_cat (Mright_skew (Mlift (proj n) (trajectory f e u)) (fun xw : Wrd n X => next f e u xw)).
Proof.
  intros f e u n.
  rewrite -> proj_trajectory, -> proj_trajectory.
  now apply finite_trajectory_succ.
Qed.

Definition get {X} n (xs : Tr X) := xs n.
Definition get_pair {X} n (xs : Tr X) := (xs n, xs (S n)).

Lemma get_wrd {X} : forall n (xs : Tr X), 
  get n xs = proj (S n) xs (ord n (Nat.lt_succ_diag_r n)).
Proof.
  intros n xs. unfold get. now rewrite -> proj_at. Qed.

Lemma get_last {X} : forall n (xs : Tr X), 
  get n xs = last (proj (S n) xs).
Proof.
  intros n xs. unfold get, last. now rewrite -> proj_at. Qed.

Lemma trajectory_pair {U X} :
    forall (f : X -> U -> M X) (e : M X) (u : Tr U) (n : nat),
  Mlift (get_pair n) (trajectory f e u) = 
     Mright_skew (Mlift (get n) (trajectory f e u)) (fun x : X => f x (u n)).
Proof.
  intros f e u n.
  replace (get n) with (compose (@last X n) (@proj X (S n))).
  rewrite <- Mlift_associative.
  rewrite -> proj_trajectory.
admit.
Admitted.


(* Show that the behaviour of the composition of two systems
   is a composition of the behaviours of the components. *)
Theorem composed_system_behaviour {UA UD X1 X2 Y1 Y2 : Type} :
   forall (s1 : System UA (UD*Y2) X1 Y1)
          (s2 : System (UA*Y1) UD X2 Y2),
          is_composed_behaviour
            (behaviour s1)
            (behaviour s2)
            (behaviour (compose_systems s1 s2)).
Proof.
   intros s1 s2.
   remember (compose_systems s1 s2) as s12 eqn:Es12.
   unfold is_composed_behaviour.
   intros u.
   destruct (unzip u) as (ua,ud).
   set (pi1 := fst_unzip). set (pi2 := snd_unzip).
(* 
Mbind (fun y2 : Tr Y2 => behaviour s1 (ua; (ud; y2)))
  (Mlift pi2 (behaviour s12 (ua; ud))) =
Mlift pi1 (behaviour s12 (ua; ud)) /\
Mbind (fun y1 : Tr Y1 => behaviour s2 ((ua; y1); ud))
  (Mlift pi1 (behaviour s12 (ua; ud))) =
Mlift pi2 (behaviour s12 (ua; ud))
*)
   remember (behaviour s1) as b1 eqn:Eb1.
   remember (behaviour s2) as b2 eqn:Eb2.
   remember (behaviour s12) as b12 eqn:Eb12.

   destruct s1 as (f1,h1,e1).
   destruct s2 as (f2,h2,e2).
   destruct s12 as (f12,h12,e12).

   unfold compose_systems in Es12.
   injection (Es12) as Ef12 Eh12 Ee12. clear Es12.
   revert Ef12 Eh12 Ee12; intros Ef12 Eh12 Ee12.

   remember (trajectory f12 e12 u) as mx12 eqn:Emx12.
   assert (mx12 = trajectory f12 e12 (ua;ud)) as Emx12ad by admit.
   unfold behaviour in Eb12.
   assert (b12 (ua;ud) = signal h12 (trajectory f12 e12 (ua;ud)) ua) as Hbmx12 
     by now rewrite -> Eb12.
   rewrite -> lift_signal in Hbmx12.
   rewrite <- Emx12ad in Hbmx12.
   remember (b12 (ua;ud)) as my12 eqn:Emy12.
   remember (Mlift pi1 my12) as my1 eqn:Emy1.
   remember (Mlift pi2 my12) as my2 eqn:Emy2.
(*
Mbind (fun y2 : Tr Y2 => b1 (ua; (ud; y2))) my2 = my1 /\
Mbind (fun y1 : Tr Y1 => b2 ((ua; y1); ud)) my1 = my2
*)
   set (Htp := @trajectory_pair). 
   set (Hmx12 := trajectory_pair f12 e12 (ua;ud)).
   rewrite <- Emx12ad in Hmx12.
  assert ( forall n, 
    Mlift (proj n) (Mbind (fun y2 => b1 (ua;(ud;y2))) my2)
      = Mlift (proj n) my1 /\ 
    Mlift (proj n) (Mbind (fun y1 => b2 ((ua;y1);ud)) my1) 
      = Mlift (proj n) my2 ).
  destruct n as [|n].
  2: induction n.
  - (* n=0 case is trivial since words are 0 *)
    split.
    -- admit. 
    -- admit. 
  - (* n=1 case is easy since words are based on e *)
   assert (Mlift (@proj (X1*X2) 1) mx12 = Mlift unit_wrd e12) as He12. {
     rewrite -> Emx12. rewrite -> proj_trajectory. 
     unfold finite_trajectory, next.
     unfold Mright_skew.

     replace (Mlift (fun (x : X1 * X2) (_ : Ordinal 0) => x) e12) 
       with (Mpure (@null_wrd (X1*X2))).
     rewrite -> Mleft_identity.
     rewrite -> Mlift_associative.
     apply Mlift_extensional. intros x12.
     unfold compose, pair_cat, null_wrd, unit_wrd, cat. simpl.
     apply functional_extensionality. intro kp. 
     destruct kp as [k p]. simpl.
     set (cmp := Compare_dec.le_lt_eq_dec k 0 (proj1 (Nat.lt_succ_r k 0) p)). destruct cmp.
     lia. reflexivity.
     replace (fun (x : X1 * X2) (_ : Ordinal 0) => x)
       with (fun (_ : X1 * X2) => @null_wrd (X1*X2)).
     unfold Mlift. now rewrite -> preserves_constants_M.
     apply functional_extensionality. intro x1x2.
     apply wrd_0_eq.
   }
   rewrite -> Ee12 in He12.

   set (n:=1).
   specialize (Hmx12 n).
   rewrite -> Ef12 in Hmx12.
   replace (fst ((ua;ud) n)) with (ua n) in Hmx12 by auto.
   replace (snd ((ua;ud) n)) with (ud n) in Hmx12 by auto.
   set (f1' := fun (n:nat) (x:X1*X2) => let x1 := fst x in let x2 := snd x in let y1 := h1 x1 (ua n) in let y2 := h2 x2 (ua n, y1) in 
         f1 (x1) (ua n, (ud n, y2))).
   set (f2' := fun (n:nat) (x:X1*X2) => let x1 := fst x in let x2 := snd x in let y1 := h1 x1 (ua n) in let y2 := h2 x2 (ua n, y1) in 
         f2 (x2) ((ua n, y1),(ud n))).
   assert (Mlift (get_pair n) mx12 = 
       Mright_skew (Mlift (get n) mx12) (fun x => Mproduct (f1' n x) (f2' n x))) as Hmx12'. {
     unfold f1', f2'. exact Hmx12. }

  set (zip_pair := fun x1x2 : (Tr X1) * (Tr X2) => zip (fst x1x2) (snd x1x2)).
  remember (Mlift unzip mx12) as mx1x2 eqn:Emx1x2.
  assert (mx12 = Mlift zip_pair mx1x2) as Emx12z. {
    rewrite -> Emx1x2.
    rewrite -> Mlift_associative.
    replace (compose zip_pair unzip) 
      with (fun x12 : Tr (X1*X2) => x12).
    unfold Mlift. now rewrite -> Mright_identity.
    apply functional_extensionality. intros x1x2.
    unfold compose, zip_pair, zip, unzip. simpl.
    apply functional_extensionality. intros k.
    now apply surjective_pairing.
  }
  remember (Mlift fst mx1x2) as mx1 eqn:Emx1.
  remember (Mlift snd mx1x2) as mx2 eqn:Emx2.

(* FINISH *)

(*
split.
   rewrite -> Mbind_lift_associativity.
   assert (x12 = trajectory f12 e12 (ua;ud)) as Hx12. {
     rewrite -> Ex12. apply trajectory_input_extensional.
     intro n. unfold zip. rewrite -> Eua, -> Eud. 
     now apply surjective_pairing. 
   }
   rewrite <- Hx12.
   unfold signal.
   rewrite -> Mlift_associativity.
   transitivity (Mlift (fun x12s => (fun n => h1 (fst (x12s n)) (ua n)) : Tr Y1) x12).
   2: { apply Mlift_extensional. intro xs. simpl.
          unfold compose, fst_unzip, unzip. simpl.
          apply functional_extensionality. intro n.
          rewrite -> Eh12. reflexivity.
   }
   rewrite -> Mbind_lift_associativity.
   unfold compose.
   transitivity (signal h1 x1 ua).
   2: { unfold signal. rewrite -> Ex1. 
        rewrite -> Mlift_associativity.
        apply Mlift_extensional. intro x12s.
        unfold compose, fst_unzip, unzip.
        apply functional_extensionality. intro n. 
        simpl. reflexivity.
  }
  remember (fun (xs : nat -> X1) (n:nat) => h1 (xs n) (ua n)) as h1'.
  remember (fun a : nat -> X1 * X2 =>
   Mlift h1'
     (trajectory f1 e1
        (ua; (ud; snd_unzip (fun n : nat => h12 (a n) (ua n)))))) as fa.
  assert ( forall x12, snd_unzip (fun n => h12 (x12 n) (ua n)) = fun n => h2 ((snd_unzip x12) n) ) as Ha. { admit. }


  transitivity (Mbind (compose (fun x1 => 
  rewrite -> Mbind_lift_associativity.
b (fun x => l g (B x)) A
*)   
(*
   remember (signal h12 x12 (fun k => fst (u k))) as y12 eqn:Ey12.
   remember (trajectory f1 e1 (fun k =>
      (fst (u k), (snd (u k), snd (y12 k))))) as x1 eqn:Ex1.


   remember (trajectory f2 e2 (fun k =>
      ((fst (u k), fst (y12 k)), snd (u k)))) as x2 eqn:Ex2.
   remember (signal h1 x1) as y1 eqn:Ey1.
   remember (signal h2 x2) as y2 eqn:Ey2.

   assert ( forall n m:nat, m<=n -> x1 m = fst (x12 m) /\ x2 m = snd (x12 m) ) as SHx.
   { induction n.
     - intros m. intros Hmle0.
       assert (m=0) as Hmeq0. { apply Nat.le_0_r. assumption. }
       rewrite -> Hmeq0.
       rewrite -> Ex12. rewrite -> Ex1. rewrite -> Ex2.
       unfold trajectory. rewrite -> Ee12. simpl. split. reflexivity. reflexivity.
     - intro m. rewrite -> Nat.le_succ_r. apply or_ind.
       -- apply IHn.
       -- intro HmeqSn. rewrite -> HmeqSn.

          assert ( x1 (S n) = f1 (x1 n) (fst (u n), (snd (u n), h2 (x2 n) (fst (u n), h1 (x1 n) (fst (u n)))))) as Hx1Sn.
          { rewrite -> Ex1. simpl. f_equal. f_equal.
            rewrite -> Ey12. unfold signal. rewrite -> Eh12. simpl.
            assert ( x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hnx.
            { apply IHn. apply Nat.le_refl. }
            assert (x2 n = snd (x12 n)) as Hx2n. { apply Hnx. }
            rewrite <- Hx2n.
            assert (x1 n = fst (x12 n)) as Hx1n. { apply Hnx. }
            rewrite <- Hx1n.
            f_equal. f_equal. f_equal.
            rewrite -> Ex1. f_equal.
            rewrite -> Ey12. unfold signal. rewrite -> Eh12.
            reflexivity.
          }

          assert ( x2 (S n) = f2 (x2 n) ((fst (u n), h1 (x1 n) (fst (u n))), snd (u n))) as Hx2Sn.
          { rewrite -> Ex2. simpl. f_equal.
            rewrite -> Ey12. unfold signal. rewrite -> Eh12. simpl.
            assert ( x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hnx.
            { apply IHn. apply Nat.le_refl. }
            assert (x1 n = fst (x12 n)) as Hx1n. { apply Hnx. }
            rewrite <- Hx1n. reflexivity.
          }

          assert ( x12 (S n) = f12 (x12 n) (u n) ) as Hx12Sn.
          { rewrite -> Ex12. simpl. reflexivity. }


          assert (  f12 (x12 n) (u n) =
            ( f1 (fst (x12 n)) ((fst (u n)), ((snd (u n)), h2 (snd (x12 n)) ((fst (u n)), h1 (fst (x12 n)) (fst (u n))))),
              f2 (snd (x12 n)) ((fst (u n), h1 (fst (x12 n)) (fst (u n))), snd (u n)
            ))) as Hx12n.
          { rewrite -> Ef12. reflexivity. }

          assert (x1 n = fst (x12 n) /\ x2 n = snd (x12 n)) as Hx1a2n. { apply IHn. apply Nat.le_refl. }
          split.
          --- rewrite -> Hx1Sn. rewrite -> Hx12Sn. rewrite -> Hx12n. simpl. f_equal.
              ---- apply IHn. apply Nat.le_refl.
              ---- assert (x2 n = snd (x12 n)) as Hx2n. { apply Hx1a2n. }
                   rewrite <- Hx2n.
                   assert (x1 n = fst (x12 n)) as Hx1n. { apply Hx1a2n. }
                   rewrite <- Hx1n. reflexivity.
          --- rewrite -> Hx2Sn. rewrite -> Hx12Sn. rewrite -> Hx12n. simpl. f_equal.
              ---- apply IHn. apply Nat.le_refl.
              ---- assert (x1 n = fst (x12 n)) as Hx1n. { apply Hx1a2n. }
                   rewrite <- Hx1n. reflexivity.
   }

   assert ( forall n : nat, n<=n -> x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hnx.
   { intros n. apply SHx. }
   assert ( forall n : nat, x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hx.
   { intros n. apply Hnx. apply Nat.le_refl. }

   intros n.
   rewrite -> Ey12. rewrite -> Ey1. rewrite -> Ey2.
   unfold signal. rewrite -> Eh12. simpl. split.
   - f_equal. symmetry. apply Hx.
   - f_equal. symmetry. apply Hx.
*)
Admitted.



(* The composed behaviour of two systems should be unique. *)

(* Intermediate step to show how this theorem easily follows from last theorem *)

(* From above Theorem composed_mixed_causal_system_behaviour_unique, get systems involved
   - replace b12' by (behaviour (compose_systems s1 s2)).
   - use (behaviour s1) for b1, (behaviour s2) for b2.
*)

Lemma Hb12eqbehav {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : System UA (UD*Y2) X1 Y1)
         (s2 : System (UA*Y1) UD X2 Y2)
         (b12 : Behaviour (UA*UD) (Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12 ->
    is_composed_behaviour (behaviour s1) (behaviour s2) (behaviour (compose_systems s1 s2))
      -> b12 = behaviour (compose_systems s1 s2).
Proof.
(*
   intros s1 s2 b12 H0 H1.
   remember (behaviour (compose_systems s1 s2)) as b12' eqn:Eb12'.
   remember (behaviour s1) as b1 eqn:Eb1.
   remember (behaviour s2) as b2 eqn:Eb2.
   intros u n.
   (* Check composed_mixed_causal_system_behaviour_unique. *)
   apply @composed_mixed_causal_behaviour_unique
     with (b1:=b1) (b2:=b2) (b12':=b12').

   - apply X1. (* ? *)
   - apply X2. (* ? *)
   - rewrite Eb1. apply behaviour_mixed_causal.
   - rewrite Eb2. apply behaviour_mixed_causal.
   - exact H0.
   - exact H1.
*)
Admitted.

(* The composed behaviour of two systems should be unique. *)
(* One condition can go, because it is already proven to be true *)
Theorem composed_system_behaviour_unique {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : System UA (UD*Y2) X1 Y1)
         (s2 : System (UA*Y1) UD X2 Y2)
         (b12 : Tr (UA*UD) -> M (Tr (Y1*Y2))),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12
      -> b12 = behaviour (compose_systems s1 s2).
Proof.
  intros s1 s2 b12 Hb12.
  apply Hb12eqbehav.
  - exact Hb12.
  - apply composed_system_behaviour.
Qed.


Definition compose_behaviours {UA UD Y1 Y2} (y1_default : Y1)
  (b1 : Behaviour (UA*(UD*Y2)) Y1) (b2 : Behaviour ((UA*Y1)*UD) Y2)
    : Behaviour (UA*UD) (Y1*Y2).
Admitted.

Theorem compose_mixed_causal_behaviours_correct {UA UD Y1 Y2} (y1d : Y1) :
  forall (b1 : Behaviour (UA*(UD*Y2)) Y1) 
         (b2 : Behaviour ((UA*Y1)*UD) Y2),
    mixed_causal b1 -> mixed_causal b2 ->
      is_composed_behaviour b1 b2 (compose_behaviours y1d b1 b2).
Proof.
Admitted.


Definition associate {Y1 Y2 Y3}
  (y12_3 : Tr ((Y1*Y2)*Y3)) : Tr (Y1*(Y2*Y3)) :=
    let (y12,y3) := unzip y12_3 in
      let (y1,y2) := unzip y12 in
        (y1;(y2;y3)).
Definition unassociate {Y1 Y2 Y3}
  (y1_23 : Tr (Y1*(Y2*Y3))) : Tr ((Y1*Y2)*Y3) :=
    let (y1,y23) := unzip y1_23 in
      let (y2,y3) := unzip y23 in
        ((y1;y2);y3).
Definition preprocess1 {UA UD Y1 Y2 Y3}
  ( b1 : Behaviour (UA * (UD*(Y2*Y3))) Y1 )
    : Behaviour (UA*((UD*Y3)*Y2)) Y1 :=
  fun (uaudy3y2 : Tr (UA*((UD*Y3)*Y2))) => 
    let (ua,udy3y2):=unzip uaudy3y2 in
    let (udy3,y2):=unzip udy3y2 in
    let (ud,y3):=unzip udy3 in
      b1 (ua;(ud;(y2;y3))).
Definition preprocess3 {UA UD Y1 Y2 Y3} 
  ( b3 : Behaviour ((UA*(Y1*Y2)) * UD) Y3 )
    : Behaviour (((UA*Y1)*Y2)*UD) Y3 :=
  fun (uay1y2ud : Tr (((UA*Y1)*Y2)*UD)) => 
    let (uay1y2,ud):=unzip uay1y2ud in
    let (uay1,y2):=unzip uay1y2 in
    let (ua,y1):=unzip uay1 in
      b3 ((ua;(y1;y2));ud).
Definition postprocess {UA UD Y1 Y2 Y3}
  ( b123 : Behaviour (UA * UD) (Y1*(Y2*Y3)) )
    : Behaviour (UA*UD) ((Y1*Y2)*Y3) :=
  fun (u : Tr (UA*UD)) => Mlift unassociate (b123 u).
Definition unpostprocess {UA UD Y1 Y2 Y3} 
  ( b123 : Behaviour (UA * UD) ((Y1*Y2)*Y3) )
    : Behaviour (UA*UD) (Y1*(Y2*Y3)) :=
  fun (u : Tr (UA*UD)) =>  Mlift associate (b123 u).

Theorem compose_behaviours_associative {UA UD Y1 Y2 Y3} :
  forall (b1 : Behaviour (UA*(UD*(Y2*Y3))) Y1)
         (b2 : Behaviour ((UA*Y1)*(UD*Y3)) Y2)
         (b3 : Behaviour ((UA*(Y1*Y2))*UD) Y3)
         (y1_default : Y1) (y2_default : Y2),
    let pb1 := (preprocess1 b1) in
    let pb3 := (preprocess3 b3) in
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
      (compose_behaviours (y1_default,y2_default) (compose_behaviours y1_default pb1 b2) b3)
          = (postprocess (compose_behaviours y1_default b1 (compose_behaviours y2_default b2 pb3))).
Proof.
Admitted.

Check Tr.
Check Behaviour.
Check mixed_causal.
(* Check extensional. *)
(* Check mixed_causal_behaviour_extensional. *)
(* Check mixed_causal_equivalent_behaviours. *)

Check System.
Check behaviour.
Check behaviour_mixed_causal.
Check compose_systems.
Check composed_system_behaviour.
  Check composed_system_behaviour_unique.

Check is_composed_behaviour.
  (* Check is_composed_behaviour_input_extensional. *)
  (* Check is_composed_behaviour_output_extensional. *)
Check composed_mixed_causal_behaviour_unique.
Check behaviour_composition_mixed_causal.

Check compose_behaviours.
Check compose_mixed_causal_behaviours_correct.
  (* Check is_three_composed_behaviours_unique. *)
  (* Check is_three_composed_behaviours_unique. *)
Check compose_behaviours_associative.

