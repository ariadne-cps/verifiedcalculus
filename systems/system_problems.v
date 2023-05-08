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

Require Export definitions.

Require Export definitions.

Notation mixed_causal := definitions.mixed_causal.
Notation mixed_causal' := definitions.mixed_causal'.
Notation mixed_causal_equivalent :=  definitions.mixed_causal_equivalent.

(* System theory using functions to represent infinite signals. *)

(* The only systems we consider now are state-space models of the given form. *)
Inductive system {UA UD X Y : Type} : Type :=
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
  (s:@system UA UD X Y)
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
  (s : @system UA UD X Y)
  (u:nat->UA*UD)
  : (nat->Y) :=
    match s with
    | state_space_model f h e => (fun n =>
      signal h (trajectory f e u) (fun k => fst (u k)) n)
    end
.

Definition behaviour'' {UA UD Y X : Type}
   (s : @system UA UD X Y) :
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
    (s : @system UA UD X Y),
      mixed_causal' (behaviour s).
Proof.
  intros UA UD X Y. intro s. unfold mixed_causal'.
  intros ua ua' ud ud'. intro n.
  intros H0 H1.
  destruct s as (f,h,e).
  unfold behaviour. unfold signal.
  f_equal.
  - induction n.
    + unfold trajectory. reflexivity.
    + assert (forall m0: nat, m0 <= n  -> ua m0 = ua' m0) as Hlen. { auto. }
      assert (forall m1: nat, m1 < n  -> ud m1 = ud' m1) as Hltn. { auto. }
      assert (ua n = ua' n) as Heqn0. { auto. }
      assert (ud n = ud' n) as Heqn1. { auto. }

      assert (trajectory f e (fun k => (ua k, ud k)) n = trajectory f e (fun k => (ua' k, ud' k)) n).
      { apply IHn. assumption. assumption. }
      remember (trajectory f e (fun k => (ua k, ud k)) n) as x eqn:Ex.
      remember (trajectory f e (fun k => (ua' k, ud' k)) n) as x' eqn:Ex'.
      assert (trajectory f e (fun k => (ua k, ud k)) (S n) = f (trajectory f e (fun k => (ua k, ud k)) n) (ua n, ud n)) as Hn.
      { simpl. reflexivity. }
      assert (trajectory f e (fun k => (ua' k, ud' k)) (S n) = f (trajectory f e (fun k => (ua' k, ud' k)) n) (ua' n, ud' n)) as Hn'.
      { simpl. reflexivity. }
      rewrite -> Hn. rewrite <- Ex.
      rewrite -> Hn'. rewrite <- Ex'.
      f_equal.
      * assumption.
      * rewrite pair_equal_spec. split.
        -- apply Heqn0.
        -- apply Heqn1.
  - rewrite <- H0.
    * reflexivity.
    * apply Nat.le_refl.
Qed.

(* Show that the behaviour of a system (usplit) is causal. *)
Theorem behaviour_mixed_causal :
  forall {UA UD X Y : Type}
    (s : @system UA UD X Y),
      mixed_causal (behaviour s).
Proof.
  intros UA UD X Y s.
  apply mixed_causal_equivalent.
  apply behaviour_mixed_causal'.
Qed.


(* UA1 = UA,       UA2 = UA * Y1
   UD1 = UD * Y2,  UD2 = UD
*)


(* A predicate which is true if b12 is a composed behaviour of b1 and b2.
   b12 is a composed behaviour if the projections onto inputs/outputs
   of the component systems b1 and b2 give the component behaviour.
   For non-strictly-causal systems, composed behaviours need not be unique. *)
Definition  is_composed_behaviour'
  {UA UD Y1 Y2 : Type}
  (b1 : (nat->(UA*(UD*Y2)))->(nat->Y1))
  (b2 : (nat->((UA*Y1)*UD))->(nat->Y2))
  (b12 : (nat->UA*UD)->(nat->Y1*Y2))
  : Prop :=
    forall (u:nat->UA*UD) (n:nat),
      let ua := (fun k => fst (u k)) in
      let ud := (fun k => snd (u k)) in

      (* Separate outputs of composition *)
      (* Perhaps as functions and use again *)
      let py1: Y1 := fst (b12 u n) in
      let py2: Y2 := snd (b12 u n) in

      (* Outputs from separate behaviours *)
      let gy1: Y1 := b1 (fun k => (ua k, (ud k, snd (b12 u k)))) n in
      let gy2: Y2 := b2 (fun k => ((ua k, fst (b12 u k)), ud k)) n in

        py1 = gy1 /\ py2 = gy2
.


(* A predicate which is true if b12 is a composed behaviour of b1 and b2.
   b12 is a composed behaviour if the projections onto inputs/outputs
   of the component systems b1 and b2 give the component behaviour.
   For non-strictly-causal systems, composed behaviours need not be unique. *)
  Definition  is_composed_behaviour {UA UD Y1 Y2 : Type}
    (b1 : (nat->(UA*(UD*Y2)))->(nat->Y1))
    (b2 : (nat->((UA*Y1)*UD))->(nat->Y2))
    (b12 : (nat->UA*UD)->(nat->Y1*Y2))
    : Prop :=
    forall (u:nat->UA*UD) (n:nat),

       (* Separate inputs *)
       let ua : (nat -> UA) := (fun k => fst (u k)) in
       let ud : (nat -> UD) := (fun k => snd (u k)) in

       (* Separate outputs of composition *)
       let py1 : (nat -> Y1) := (fun k => fst (b12 u k)) in
       let py2 : (nat -> Y2) := (fun k => snd (b12 u k)) in


       (* Outputs from separate behaviours *)
       let gy1 : (nat -> Y1) := b1 (fun k => (ua k, (ud k, py2 k))) in
       let gy2 : (nat -> Y2) := b2 (fun k => ((ua k, py1 k), ud k)) in

         py1 n = gy1 n /\ py2 n = gy2 n
  .

Check is_composed_behaviour.


(* Define the composition of state space models. *)
Definition compose_systems {UA UD X1 X2 Y1 Y2 : Type}
  (s1 : @system UA      (UD*Y2) X1 Y1)
  (s2 : @system (UA*Y1)      UD X2 Y2)
  : (@system UA UD (X1*X2) (Y1*Y2)) :=
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
   forall (s1 : @system UA (UD*Y2) X1 Y1)
          (s2 : @system (UA*Y1) UD X2 Y2),
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


(* The composition of two mixed causal behaviours should be unique. *)
Theorem composed_mixed_causal_system_behaviour_unique
  {UA UD X1 X2 Y1 Y2 : Type} :
  forall (b1 : (nat->(UA*(UD*Y2)))->(nat->Y1))
         (b2 : (nat->((UA*Y1)*UD))->(nat->Y2))
         (b12 b12' : (nat->UA*UD)->(nat->Y1*Y2)),
           mixed_causal b1 ->
           mixed_causal b2 ->
           is_composed_behaviour b1 b2 b12 ->
           is_composed_behaviour b1 b2 b12'
             -> forall (u : nat->UA*UD) (n:nat),
                  b12 u n = b12' u n.
Proof.
  intros b1 b2 b12 b12' Hmcb1 Hmcb2.
  unfold is_composed_behaviour.
  intros HPcompb12 HPcompb12'.
  intros u.

  (* Clear up, isolate inputs and projections from pairs *)
  remember (fun k => fst (u k)) as ua eqn:Eua.
  remember (fun k => snd (u k)) as ud eqn:Eud.
  remember (fun k => fst (b12 u k)) as py1 eqn:Epy1.
  remember (fun k => snd (b12 u k)) as py2 eqn:Epy2.
  remember (fun k => fst (b12' u k)) as py1' eqn:Epy1'.
  remember (fun k => snd (b12' u k)) as py2' eqn:Epy2'.

  (* HPcompb12 after clear up *)
  assert (forall (n:nat),
    py1 n = b1 (fun k => (ua k, (ud k, py2 k))) n /\
    py2 n = b2 (fun k => ((ua k, py1 k), ud k)) n
  ) as HPcompb12_clear.
  { rewrite Epy1. rewrite Epy2.
    rewrite Eua. rewrite Eud.
    apply HPcompb12. }

  (* HPcompb12' after clear up *)
  assert (forall (n:nat),
    py1' n = b1 (fun k => (ua k, (ud k, py2' k))) n /\
    py2' n = b2 (fun k => ((ua k, py1' k), ud k)) n
  ) as HPcompb12_clear'.
  { rewrite Epy1'. rewrite Epy2'.
    rewrite Eua. rewrite Eud.
    apply HPcompb12'. }

  (* Asserts to jump between perspectives for the
     composed system and the components system
  *)

  (* ... At composed system pair element level *)

  assert (forall (n:nat),
    py1 n = b1 (fun k => (ua k, (ud k, py2 k))) n
  ) as HPcompb12_b1.
  { apply HPcompb12_clear. }

  assert (forall (n:nat),
    py2 n = b2 (fun k => ((ua k, py1 k), ud k)) n
  ) as HPcompb12_b2.
  { apply HPcompb12_clear. }

  assert (forall (n:nat),
    py1' n = b1 (fun k => (ua k, (ud k, py2' k))) n
  ) as HPcompb12_b1'.
  { apply HPcompb12_clear'. }

  assert (forall (n:nat),
    py2' n = b2 (fun k => ((ua k, py1' k), ud k)) n
  ) as HPcompb12_b2'.
  { apply HPcompb12_clear'. }

  (* ... At composed system full pair level *)

  assert (forall (n:nat),
    b12 u n =
      ( b1 (fun k => (ua k, (ud k, py2 k))) n,
        b2 (fun k => ((ua k, py1 k), ud k)) n  )
  ) as Hb12un.
  { intros n.
    (* Check (HPcompb12_b1). *)
    rewrite <- HPcompb12_b1.
    (* Check (HPcompb12_b2). *)
    rewrite <- HPcompb12_b2.
    (* Search (_ = (fst _, snd _)). *)
    rewrite Epy1. rewrite Epy2.
    rewrite <- surjective_pairing. reflexivity.
  }

  assert (forall (n:nat),
    b12' u n =
      ( b1 (fun k => (ua k, (ud k, py2' k))) n,
        b2 (fun k => ((ua k, py1' k), ud k)) n )
  ) as Hb12un'.
  { intros n.
    (* Check (HPcompb12_b1). *)
    rewrite <- HPcompb12_b1'.
    (* Check (HPcompb12_b2). *)
    rewrite <- HPcompb12_b2'.
    (* Search (_ = (fst _, snd _)). *)
    rewrite Epy1'. rewrite Epy2'.
    rewrite <- surjective_pairing. reflexivity.
  }

  (* Causal on compositions  *)

  (* Key insights

     1) Causality defines a relation between all possible inputs
        with the behaviour's output.
        For a subset of inputs there must also be a useful relation.
        This subset of inputs can be the output from the other connected behaviour.

     2) The composition has a circular structure.
        Output b1 is input to b2, output of b2 is input to b1.
        In in compositional perspective this can be seen as
        b1, b2 influences b1, b2

     3) Causality contains an implication that is just one step further in time.
        Strict causality.
        It is an ideal candidate to get a grip on with induction.

     4) In order for induction to work a zero condition is needed.
        The starting point for induction - what is it for behaviours?

        Took a while to realize that ex falso can be used here.
        There is no n<0.

     With above insights it should be possible to prove that the behaviour
     of two equal composed systems always should the same behaviour for all
     possible inputs.
     In other words, this behaviour is unique.
  *)

  (* In 3 steps
     For b1
     Step 1: Use causality to get setup circular dependency
     between b1, b2 behaviours.
     Only partly circular, will be closed later.
     Step 2: Get rid of unnecessary inputs. Keep only the useful.
     Step 3: Bring up clearly the behaviour dependency.

     For b2
     Different steps but leading to the same goal:
       the component behaviour dependency between the 2 components

  *)

  (* Step 1 b1 *)
  assert (forall (n:nat),
    (forall m : nat, m<n -> (ud m, py2 m) = (ud m, py2' m))
      ->
      (forall m : nat, m<=n ->
         b1 (fun k => (ua k, (ud k, py2 k))) m =
         b1 (fun k => (ua k, (ud k, py2' k))) m)

   ) as Hb1eq'.
   { intros n H0.
     (* apply behaviour_mixed_causal. *)
     apply Hmcb1.
     - reflexivity.
     - apply H0.
   }

  (* Step 2 b1 *)
  assert (forall (n:nat),
      (forall m : nat, m<n -> py2 m = py2' m)
      ->
      (forall m : nat, m<=n ->
       b1 (fun k => (ua k, (ud k, py2 k))) m =
       b1 (fun k => (ua k, (ud k, py2' k))) m)
  ) as Hb1eq''.
  { intros n H0.
    apply Hb1eq'. intros m H1.
    rewrite pair_equal_spec. split.
    - reflexivity.
    - apply H0. apply H1.
  }

  (* Step 3 b1 *)
  assert (forall (n:nat),
      (forall m : nat, m<n ->
        b2 (fun k => ((ua k, py1 k), ud k)) m =
        b2 (fun k => ((ua k, py1' k), ud k)) m) ->
      (forall m : nat, m<=n ->
        b1 (fun k => (ua k, (ud k, py2 k))) m =
        b1 (fun k => (ua k, (ud k, py2' k))) m)
  ) as Hb1eq'''.
  { intros n H0.
    apply Hb1eq''. intros m H1.
    rewrite HPcompb12_b2. rewrite HPcompb12_b2'.
    apply H0. apply H1.
  }

  (* Step 1 b2 *)
  assert (forall (n:nat),
      (forall m : nat, m<=n -> (ua m, py1 m) = (ua m, py1' m))
      ->
      (forall m : nat, m<=n ->
         b2 (fun k => ((ua k, py1 k), ud k)) m =
         b2 (fun k => ((ua k, py1' k), ud k)) m)
  ) as Hb2eq'.
  { intros n H0.
    apply Hmcb2.
    - apply H0.
    - reflexivity.
  }

  (* Step 2 b2 *)
  assert (forall (n:nat),
      (forall m : nat, m<=n -> py1 m = py1' m)
      ->
      (forall m : nat, m<=n ->
        b2 (fun k => ((ua k, py1 k), ud k)) m =
        b2 (fun k => ((ua k, py1' k), ud k)) m)
  ) as Hb2eq''.
  { intros n H0.
    apply Hb2eq'.
    intros m H1. rewrite pair_equal_spec. split.
    - reflexivity.
    - apply H0. apply H1.
  }

  assert (forall (n:nat),
      (forall m : nat, m<=n ->
        b1 (fun k => (ua k, (ud k, py2 k))) m =
        b1 (fun k => (ua k, (ud k, py2' k))) m)
      ->
      (forall m : nat, m<=n ->
        b2 (fun k => ((ua k, py1 k), ud k)) m =
        b2 (fun k => ((ua k, py1' k), ud k)) m)
  ) as Hb2eq'''.
  { intros n H0.
    apply Hb2eq''. intros m H1.
    (* Check HPcompb12_b1. *)

    rewrite HPcompb12_b1. rewrite HPcompb12_b1'.
    apply H0. exact H1.
  }

  (* Now, close the circular structure.
     From behaviours b1, b2 to behaviours b1, b2

     Resulting assert will be a candidate for induction.
     To proof that behaviours must be equal in b12 and b12'.

     The conclusion states the same as the two premisses.
     But the conclusion is valid one step further.
     Fit for induction, which will come in the assertion
     after this one.
  *)

  assert (forall (n:nat),
      (forall m : nat, m<n ->
        b2 (fun k => ((ua k, py1 k), ud k)) m =
        b2 (fun k => ((ua k, py1' k), ud k)) m) ->
      (forall m : nat, m<=n ->
        b1 (fun k => (ua k, (ud k, py2 k))) m =
        b1 (fun k => (ua k, (ud k, py2' k))) m)
      ->
      (forall m : nat, m<=n ->
        b1 (fun k => (ua k, (ud k, py2 k))) m =
        b1 (fun k => (ua k, (ud k, py2' k))) m /\
        b2 (fun k => ((ua k, py1 k), ud k)) m =
        b2 (fun k => ((ua k, py1' k), ud k)) m)
  ) as Hb12eq.
  { intros n H0 H1 m H2. split.
    - apply Hb1eq''' with (n:=n).
      + intros m0 H3. apply H0. exact H3.
      + exact H2.
    - apply Hb2eq''' with (n:=n).
      + intros m0 H3. apply H1. exact H3.
      + exact H2.
  }

  (* The induction step
     Everything before in this lemma worked towards this step.
     After this it is simple.
  *)

  (* Helper assert. Zero hypothesis for induction.
     Need this twice later.
  *)
  assert (
    b1 (fun k =>  (ua k, (ud k, py2 k))) 0 =
    b1 (fun k => (ua k, (ud k, py2' k))) 0
  ) as Hb1zero.
  { (* Check Hb1eq'''. *)
    rewrite Hb1eq''' with (n:=0).
    - reflexivity.
    - (* Search ( _ < 0 ).
         Nat.nlt_0_r: forall n : nat, ¬ n < 0 *)
         intros m H0.
         apply Nat.nlt_0_r in H0.
         exfalso. exact H0.

         (* Intuitively I find this hard to follow.
            From a false hypothesis one can conclude anything.
         *)
    - reflexivity.
  }

  assert (forall (n:nat),
    (forall m : nat, m<=n ->
      b1 (fun k => (ua k, (ud k, py2 k))) m =
      b1 (fun k => (ua k, (ud k, py2' k))) m /\
      b2 (fun k => ((ua k, py1 k), ud k)) m =
      b2 (fun k => ((ua k, py1' k), ud k)) m)
  ) as Hb12eq'.
  { intros n. induction n as [|n' IHn'].
    - (* n = 0 *)
      intros m H0. apply Nat.le_0_r in H0. rewrite H0. split.

      + apply Hb1zero.
      + (* Check Hb2eq'''. *)
        rewrite Hb2eq''' with (n:=0). (* split. *)
        * reflexivity.
        * intros m0 H1.
          apply Nat.le_0_r in H1. rewrite H1. exact Hb1zero.
        * reflexivity.

    - (* n =  S n' *)
      apply Hb12eq.
      + intros m H0.
        apply (Nat.lt_succ_r m n') in H0.
        apply IHn'. exact H0.
      + intros m H0.
        (* Check Hb1eq'''. *)
        apply Hb1eq''' with (n:=S n').
        (* Same as just above *)
        * intros m0 H1.
          apply (Nat.lt_succ_r m0 n') in H1.
          apply IHn'. exact H1.
        * exact H0.
  }

  (* Above assert states the same equality with overkill.
     'Everytime up until n valid for all m.'
     Might as well say it is 'valid for all n'.
  *)

  assert (forall (n:nat),
      b1 (fun k => (ua k, (ud k, py2 k))) n =
      b1 (fun k => (ua k, (ud k, py2' k))) n /\
      b2 (fun k => ((ua k, py1 k), ud k)) n =
      b2 (fun k => ((ua k, py1' k), ud k)) n
  ) as Hb12eq''.
  { intros n. split.
    - apply Hb12eq' with (n:=n). reflexivity.
    - apply Hb12eq' with (n:=n). reflexivity.
  }

   intros n.
   (* Check (Hb12un). *)

   (* Bring it to component behaviour level
      Assertion Hb12eq'' has been set up for that.
   *)
   rewrite Hb12un. rewrite Hb12un'.

   rewrite pair_equal_spec. split.
   - apply Hb12eq''.
   - apply Hb12eq''.

Qed.


(* The composed behaviour of two systems should be unique. *)

(* Intermediate step to show how this theorem easily follows from last theorem *)

(* From above Theorem composed_mixed_causal_system_behaviour_unique, get systems involved
   - replace b12' by (behaviour (compose_systems s1 s2)).
   - use (behaviour s1) for b1, (behaviour s2) for b2.
*)

Lemma Hb12eqbehav {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : @system UA (UD*Y2) X1 Y1)
         (s2 : @system (UA*Y1) UD X2 Y2)
         (b12 : (nat->UA*UD)->(nat->Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12 ->
    is_composed_behaviour (behaviour s1) (behaviour s2) (behaviour (compose_systems s1 s2))
      -> forall (u : nat->UA*UD) (n:nat),
        b12 u n = behaviour (compose_systems s1 s2) u n.
Proof.
   intros s1 s2 b12 H0 H1.
   remember (behaviour (compose_systems s1 s2)) as b12' eqn:Eb12'.
   remember (behaviour s1) as b1 eqn:Eb1.
   remember (behaviour s2) as b2 eqn:Eb2.
   intros u n.
   (* Check composed_mixed_causal_system_behaviour_unique. *)
   apply @composed_mixed_causal_system_behaviour_unique
     with (b1:=b1) (b2:=b2) (b12':=b12').

   - apply X1. (* ? *)
   - apply X2. (* ? *)
   - rewrite Eb1. apply behaviour_mixed_causal.
   - rewrite Eb2. apply behaviour_mixed_causal.
   - exact H0.
   - exact H1.
Qed.

(* The composed behaviour of two systems should be unique. *)
(* One condition can go, because it is already proven to be true *)
Theorem composed_system_behaviour_unique {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : @system UA (UD*Y2) X1 Y1)
         (s2 : @system (UA*Y1) UD X2 Y2)
         (b12 : (nat->UA*UD)->(nat->Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12
      -> forall (u : nat->UA*UD) (n:nat),
        b12 u n = behaviour (compose_systems s1 s2) u n.
Proof.
  intros s1 s2 b12 Hb12 u n.
  apply Hb12eqbehav.
  - exact Hb12.
  - apply composed_system_behaviour.
Qed.
