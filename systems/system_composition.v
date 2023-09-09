(* ---------------------------------------------------------------- *)
(* Author:       SINDORF, S.L. & COLLINS, P.
   Date:         20221017
   Supervisor:   COLLINS, P.
   Description:  Coq, Gallina-code

                 Proof that behavior of composed system is composed
                 behavior of components.

                 Master's Thesis Artificial Intelligence
                 Maastricht University
*)
(* ---------------------------------------------------------------- *)

Require Import Coq.Arith.PeanoNat.

Require Export causality.
Require Export behaviour_composition.

Notation mixed_causal := causality.mixed_causal.
Notation mixed_causal' := causality.mixed_causal'.
Notation mixed_causal_equivalent :=  causality.mixed_causal_equivalent.

(* System theory using functions to represent infinite signals. *)

(* The only systems we consider now are state-space models of the given form. *)
Inductive System {UA UD X Y : Type} : Type :=
  | state_space_model (f:X->UA*UD->X) (h:X->UA->Y) (e:X)
.

(* S is "successor" function: S n => n+1 *)
(* Trajectory x:ℕ→X is defined by x[n+1] = f(x[n], u[n]) *)
Fixpoint trajectory {U X : Type}
  (f:X->U->X)
  (e:X)
  (u:nat->U)
  (n:nat)
  : X :=
    match n with
    | 0 => e
    | S n' => f (trajectory f e u n') (u n')
    end
.



Check trajectory.

(* Output signal y:ℕ→Y is defined by y[n] = h(x[n], u[n]) *)
(* Definition signal {X:Type } {U:Type} {Y:Type} *)
Definition signal {X U Y : Type }
  (h:X->U->Y)
  (x:nat->X)
  (u:nat->U)
  (n:nat)
  : Y := h (x n) (u n)
.

(* By Currying, signal' below is equivalent to signal above. *)
Definition signal' {Y:Type} {X:Type} {U:Type}
  (h:X->U->Y)
  (x:nat->X)
  (u:nat->U)
  : (nat->Y) := fun n:nat => h (x n) (u n)
.

Check signal.

(* The behaviour of a system is the input-output map
   taking input signals ℕ→U to the corresponding output ℕ→Y. *)
Definition behaviour {UA UD Y X : Type}
  (s:@System UA UD X Y)
  (u:nat->UA*UD)
  (n:nat)
  : Y :=
    match s with
    | state_space_model f h e =>
      signal h (trajectory f e u) (fun k => fst (u k)) n
    end
.

 (* By Currying, behaviour' and behaviour'' below are equivalent to behaviour above. *)
Definition behaviour' {UA UD Y X : Type}
  (s : @System UA UD X Y)
  (u:nat->UA*UD)
  : (nat->Y) :=
    match s with
    | state_space_model f h e => (fun n =>
      signal h (trajectory f e u) (fun k => fst (u k)) n)
    end
.

Definition behaviour'' {UA UD Y X : Type}
   (s : @System UA UD X Y) :
   (nat->UA*UD) -> (nat->Y) :=
   match s with
   | state_space_model f h e => (fun u => (fun n =>
     signal h (trajectory f e u) (fun k => fst (u k)) n))
   end
 .

Check behaviour.
 
(* Show that the behaviour of a system satisfies the weaker definition of causal. *)
Lemma behaviour_mixed_causal' :
  forall {UA UD X Y : Type}
    (s : @System UA UD X Y),
      mixed_causal' (behaviour s).
Proof.
  intros UA UD X Y. intro s. unfold mixed_causal'.
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
Qed.

(* Show that the behaviour of a system (usplit) is causal. *)
Theorem behaviour_mixed_causal :
  forall {UA UD X Y : Type}
    (s : @System UA UD X Y),
      mixed_causal (behaviour s).
Proof.
  intros UA UD X Y s.
  apply mixed_causal_equivalent.
  apply behaviour_mixed_causal'.
Qed.


(* Define the composition of state space models. *)
Definition compose_systems {UA UD X1 X2 Y1 Y2 : Type}
  (s1 : @System UA (UD*Y2) X1 Y1)
  (s2 : @System (UA*Y1) UD X2 Y2)
  : (@System UA UD (X1*X2) (Y1*Y2)) :=
    match s1 with
    | state_space_model f1 h1 e1 =>
      match s2 with
      | state_space_model f2 h2 e2 =>
        let e12 : X1*X2 := (e1, e2) in

        let h_y1 : X1*X2->UA->Y1 :=
          fun x12 ua => h1 (fst x12) ua in

        let h_y2 : X1*X2->UA->Y2 :=
          fun x12 ua => h2 (snd x12) (ua, h_y1 x12 ua) in

        let h12 : X1*X2->UA->Y1*Y2 :=
          fun x12 ua => (h_y1 x12 ua,
                         h_y2 x12 ua) in

        let f12 : X1*X2->UA*UD->X1*X2 :=
          fun x12 u => (f1 (fst x12) ((fst u), ((snd u), h_y2 x12 (fst u))),
                        f2 (snd x12) (((fst u), h_y1 x12 (fst u)), (snd u))) in

          state_space_model f12 h12 e12
      end
    end
.

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
 Qed.



(* The composed behaviour of two systems should be unique. *)

(* Intermediate step to show how this theorem easily follows from last theorem *)

(* From above Theorem composed_mixed_causal_system_behaviour_unique, get systems involved
   - replace b12' by (behaviour (compose_systems s1 s2)).
   - use (behaviour s1) for b1, (behaviour s2) for b2.
*)

Lemma Hb12eqbehav {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : @System UA (UD*Y2) X1 Y1)
         (s2 : @System (UA*Y1) UD X2 Y2)
         (b12 : @Behaviour (UA*UD) (Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12 ->
    is_composed_behaviour (behaviour s1) (behaviour s2) (behaviour (compose_systems s1 s2))
      -> forall (u : nat->UA*UD) (n:nat),
        b12 u n = behaviour (compose_systems s1 s2) u n.
Proof.
   intros s1 s2 b12 Hb12 Hb12'.
   remember (behaviour (compose_systems s1 s2)) as b12' eqn:Eb12'.
   remember (behaviour s1) as b1 eqn:Eb1.
   remember (behaviour s2) as b2 eqn:Eb2.
   intros u n.
   (* Check composed_mixed_causal_system_behaviour_unique. *)
   apply @composed_mixed_causal_behaviour_unique
     with (b1:=b1) (b2:=b2) (b12':=b12').
   - rewrite Eb1. apply behaviour_mixed_causal.
   - rewrite Eb2. apply behaviour_mixed_causal.
   - exact Hb12.
   - exact Hb12'.
Qed.

(* The composed behaviour of two systems should be unique. *)
(* One condition can go, because it is already proven to be true *)
Theorem composed_system_behaviour_unique {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : @System UA (UD*Y2) X1 Y1)
         (s2 : @System (UA*Y1) UD X2 Y2)
         (b12 : @Behaviour (UA*UD) (Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12
      -> forall (u : nat->UA*UD) (n:nat),
        b12 u n = behaviour (compose_systems s1 s2) u n.
Proof.
  intros s1 s2 b12 Hb12 u n.
  apply Hb12eqbehav.
  - exact Hb12.
  - apply composed_system_behaviour.
Qed.
