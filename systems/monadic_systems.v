(******************************************************************************
 *  systems/monadic_systems.v
 *
 *  Copyright 2023 Sacha L. Sindorf
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


Require Import Coq.Arith.PeanoNat.
Require Import Monads.
Require Import LimitMonads.

Definition Seq (X : Type) := nat -> X.

Fixpoint proj {X} (n : nat) (s : nat -> X) : list X :=
  match n with | 0 => nil | S m => cons (s m) (proj m s) end.

Context `{M : Type -> Type } `{Monad_M : Monad M} 
  `{is_limit_monad_M : has_infinite_skew_product M Monad_M}.

Definition Behaviour {U Y} : Type := (nat -> U) -> M (nat -> Y).

Inductive System {UA UD X Y : Type} : Type :=
  | state_space_model (f:X->UA*UD->M X) (h:X->UA->Y) (e:M X)
.

Definition next {X} (F : X -> M X) (e : M X) (xl : list X) : M X :=
  match xl with | nil => e | cons x _ => F x end.

(* S is "successor" function: S n => n+1 *)
(* Trajectory x:ℕ→X is defined by x[n+1] = f(x[n], u[n]) *)
Fixpoint trajectory_list {U X : Type}
  (f:X->U->M X) (e:M X) (u:nat->U) (n:nat) : M (list X) :=
    let hf :=
      (fun (u:U) => fun (xl:list X) => match xl with | nil => e | cons x _ => f x u end) in
    match n with
    | 0 => Mlift (fun x => cons x nil) e
    | S n' => Mlift lcons (Mright_skew (trajectory_list f e u n') (hf (u (S n'))))
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

Definition trajectory' {U X : Type} (H : has_infinite_skew_product M Monad_M)
  (f:X->U->M X) (e:M X) (u:nat->U) : M (nat -> X).
Proof.
  unfold has_infinite_skew_product in H.
  specialize ( H X (fun (xl:list X) => match xl with | nil => e | cons x _ => f x (u 0) end) ).
  destruct H as [x _].
  exact x.
Qed.

Definition trajectory {U X : Type} (f:X->U->M X) (e:M X) (u:nat->U) : M (nat -> X) :=
  @trajectory' U X is_limit_monad_M f e u.

(* Output signal y:ℕ→Y is defined by y[n] = h(x[n], u[n]) *)
(* Definition signal {X:Type } {U:Type} {Y:Type} *)
Definition signal {X U Y : Type }
  (h:X->U->Y)
  (x:M (nat->X))
  (u:nat->U)
  : M (nat -> Y) := Mlift (fun xs => fun n => h (xs n) (u n)) x
.

Definition behaviour {UA UD Y X : Type}
  (s:@System UA UD X Y) : @Behaviour (UA*UD) Y := 
    fun (u:nat->UA*UD) =>
      match s with
      | state_space_model f h e =>
        signal h (trajectory f e u) (fun k => fst (u k))
      end
.

Definition zip {T1 T2} (s1 : Seq T1) (s2 : Seq T2) := fun n => (s1 n, s2 n).
Definition unzip {T1 T2} (s : Seq (T1*T2)) := (fun n=>fst (s n), fun n => snd (s n)).
Notation "( s1 ; s2 )" := (zip s1 s2) (at level 0).

Definition mixed_causal {UA UD Y : Type} (b : (nat -> UA*UD) -> M (nat -> Y)) :=
  forall u1 u2 : nat -> UA*UD, forall n,
    let (ua1,ud1) := unzip u1 in
    let (ua2,ud2) := unzip u2 in
     (forall m, m<=n -> ua1 m = ua2 m) -> (forall m, m<n -> ud1 m = ud2 m) ->
       (forall m, m<=n -> Mlift (proj (S n)) (b u1) = Mlift (proj (S n)) (b u2))
.

(* Show that the behaviour of a system satisfies the weaker definition of causal. *)
Lemma behaviour_mixed_causal :
  forall {UA UD X Y : Type}
    (s : @System UA UD X Y),
      mixed_causal (behaviour s).
Proof.
(*
  intros UA UD X Y. intro s. unfold mixed_causal.
  intros u u'. intro n.
  intros H0 H1.
  destruct s as (f,h,e).
  unfold behaviour. unfold signal.
  f_equal.
  - induction n.
    + unfold trajectory. reflexivity.
    + assert (forall m0: nat, m0 <= n  -> fst (u m0) = fst (u' m0)) as Hlen. { auto. }
      assert (forall m1: nat, m1 < n  -> snd (u m1) = snd (u' m1)) as Hltn. { auto. }
      assert (fst (u n) = fst (u' n)) as Heqn0. { auto. }
      assert (snd (u n) = snd (u' n)) as Heqn1. { auto. }

      assert (trajectory f e u n = trajectory f e u' n).
      { apply IHn. assumption. assumption. }
      remember (trajectory f e u n) as x eqn:Ex.
      remember (trajectory f e u' n) as x' eqn:Ex'.
      assert (trajectory f e u (S n) = f (trajectory f e u n) (u n)) as Hn.
      { simpl. reflexivity. }
      assert (trajectory f e u' (S n) = f (trajectory f e u' n) (u' n)) as Hn'.
      { simpl. reflexivity. }
      rewrite -> Hn. rewrite <- Ex.
      rewrite -> Hn'. rewrite <- Ex'.
      f_equal.
      * assumption.
      * destruct (u n) as [uan udn].
        destruct (u' n) as [uan' udn'].
        apply pair_equal_spec. split.
        -- apply Heqn0.
        -- apply Heqn1.
  - rewrite <- H0.
    * reflexivity.
    * apply Nat.le_refl.
*)
Admitted.

Definition Mproduct {X1 X2} : M X1 -> M X2 -> M (X1*X2) := @Mright_product M Monad_M X1 X2.

(* Define the composition of state space models. *)
Definition compose_systems {UA UD X1 X2 Y1 Y2 : Type}
  (s1 : @System UA      (UD*Y2) X1 Y1)
  (s2 : @System (UA*Y1)      UD X2 Y2)
  : (@System UA UD (X1*X2) (Y1*Y2)) :=
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

Definition is_composed_behaviour {UA UD Y1 Y2 : Type}
  (b1 : (nat -> UA*(UD*Y2)) -> M (nat -> Y1))
  (b2 : (nat -> (UA*Y1)*UD) -> M (nat -> Y2))
  (b12 : (nat -> UA*UD) -> M (nat -> Y1*Y2)) : Prop.
Proof.
Admitted.


(* Show that the behaviour of the composition of two systems
   is a composition of the behaviours of the components. *)
Theorem composed_system_behaviour {UA UD X1 X2 Y1 Y2 : Type} :
   forall (s1 : @System UA (UD*Y2) X1 Y1)
          (s2 : @System (UA*Y1) UD X2 Y2),
          is_composed_behaviour
            (behaviour s1)
            (behaviour s2)
            (behaviour (compose_systems s1 s2))
.
Proof.
(*
   intros s1 s2.
   remember (compose_systems s1 s2) as s12 eqn:Es12.
   destruct s1 as (f1,h1,e1).
   destruct s2 as (f2,h2,e2).
   destruct s12 as (f12,h12,e12).
   unfold compose_systems in Es12.
   injection (Es12) as Ef12 Eh12 Ee12. clear Es12.
   unfold is_composed_behaviour.
   intros u.
   simpl.

   remember (trajectory f12 e12 u) as x12 eqn:Ex12.
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
  forall (s1 : @System UA (UD*Y2) X1 Y1)
         (s2 : @System (UA*Y1) UD X2 Y2)
         (b12 : (nat->UA*UD)->M (nat->Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12 ->
    is_composed_behaviour (behaviour s1) (behaviour s2) (behaviour (compose_systems s1 s2))
      -> forall (u : nat->UA*UD) (n:nat),
        b12 = behaviour (compose_systems s1 s2).
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
  forall (s1 : @System UA (UD*Y2) X1 Y1)
         (s2 : @System (UA*Y1) UD X2 Y2)
         (b12 : (nat->UA*UD)->M (nat->(Y1*Y2))),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12
      -> b12 = behaviour (compose_systems s1 s2).
Proof.
  intros s1 s2 b12 Hb12.
  apply Hb12eqbehav.
  - exact Hb12.
  - apply composed_system_behaviour.
Admitted.
