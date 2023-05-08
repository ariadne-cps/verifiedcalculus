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

Notation mixed_causal := causality.mixed_causal.
Notation mixed_causal' := causality.mixed_causal'.
Notation mixed_causal_equivalent :=  causality.mixed_causal_equivalent.

(* System theory using functions to represent infinite signals. *)

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


(* The composition of two mixed causal behaviours should be unique. *)
Theorem composed_mixed_causal_behaviour_unique
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
