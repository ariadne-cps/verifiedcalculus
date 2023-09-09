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

Notation Behaviour := causality.Behaviour.
Notation mixed_causal := causality.mixed_causal.
Notation mixed_causal' := causality.mixed_causal'.
Notation mixed_causal_equivalent :=  causality.mixed_causal_equivalent.

(* System theory using functions to represent infinite signals. *)

(* A predicate which is true if b12 is a composed behaviour of b1 and b2.
   b12 is a composed behaviour if the projections onto inputs/outputs
   of the component systems b1 and b2 give the component behaviour.
   For non-strictly-causal systems, composed behaviours need not be unique. *)
Definition is_composed_behaviour {UA UD Y1 Y2 : Type}
  (b1 : @Behaviour (UA*(UD*Y2)) Y1)
  (b2 : @Behaviour ((UA*Y1)*UD) Y2)
  (b12 : @Behaviour (UA*UD) (Y1*Y2))
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

Lemma is_composed_behaviour_output_extensional {UA UD Y1 Y2 : Type} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1)
         (b2 : @Behaviour ((UA*Y1)*UD) Y2)
         (b12 b12' : @Behaviour (UA*UD) (Y1*Y2)),
    mixed_causal b1 -> mixed_causal b2 ->
      (forall (u:nat->UA*UD) (n:nat), b12 u n = b12' u n) -> 
        (is_composed_behaviour b1 b2 b12 -> is_composed_behaviour b1 b2 b12').
Proof.
  unfold is_composed_behaviour.
  intros b1 b2 b12 b12' Hcb1 Hcb2 Hu Hb12 u n.
  specialize (Hb12 u n).
  destruct Hb12 as [Hb1 Hb2].
  rewrite <- Hu.
  split.
  - rewrite -> Hb1. apply (causality.mixed_causal_behaviour_extensional b1 Hcb1).
    intro m. rewrite <- Hu. reflexivity.
  - rewrite -> Hb2. apply (causality.mixed_causal_behaviour_extensional b2 Hcb2).
    intro m. rewrite <- Hu. reflexivity.
Qed.

Lemma is_composed_behaviour_input_extensional {UA UD Y1 Y2 : Type} :
  forall (b1 b1' : @Behaviour (UA*(UD*Y2)) Y1)
         (b2 b2' : @Behaviour ((UA*Y1)*UD) Y2)
         (b12 : @Behaviour (UA*UD) (Y1*Y2)),
    mixed_causal b1 -> mixed_causal b1' -> mixed_causal b2 -> mixed_causal b2' ->
      (forall (uy2:nat->UA*(UD*Y2)) (n:nat), b1 uy2 n = b1' uy2 n) -> 
        (forall (uy1:nat->(UA*Y1)*UD) (n:nat), b2 uy1 n = b2' uy1 n) -> 
          (is_composed_behaviour b1 b2 b12 -> is_composed_behaviour b1' b2' b12).
Proof.
  unfold is_composed_behaviour.
  intros b1 b1' b2 b2' b12 Hcb1 Hcb1' Hcb2 Hcb2' Hb1e Hb2e Hb12 u n.
  specialize (Hb12 u n).
  destruct Hb12 as [Hb1 Hb2].
  rewrite -> Hb1, -> Hb2.
  split.
  - apply Hb1e.
  - apply Hb2e.
Qed.


(* The composition of two mixed causal behaviours should be unique. *)
Proposition composed_mixed_causal_outputs_unique
  {UA UD Y1 Y2 : Type} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1)
         (b2 : @Behaviour ((UA*Y1)*UD) Y2),
           mixed_causal b1 ->
           mixed_causal b2 ->
           forall (u : nat->UA*UD), 
             forall (y1 y1' : nat -> Y1) (y2 y2': nat -> Y2),
               (forall n, b1 (fun m => (fst (u m),(snd (u m),y2 m))) n = y1 n) ->
               (forall n, b1 (fun m => (fst (u m),(snd (u m),y2' m))) n = y1' n) ->
                 (forall n, b2 (fun m => ((fst (u m),y1 m),snd (u m))) n = y2 n) ->
                 (forall n, b2 (fun m => ((fst (u m),y1' m),snd (u m))) n = y2' n) ->
(*
                   (forall n, y1 n = y1' n /\ y2 n = y2' n).
*)
                   (forall n, (y1 n, y2 n) = (y1' n, y2' n)).
Proof.
  intros b1 b2 Hmcb1 Hmcb2.
  intros u.

  (* Clear up, isolate inputs and projections from pairs *)
  remember (fun k => fst (u k)) as ua eqn:Eua.
  remember (fun k => snd (u k)) as ud eqn:Eud.
  intros py1 py1' py2 py2'.
  intros Hpy1 Hpy1' Hpy2 Hpy2'.

  (* HPcompb12 after clear up *)
  assert (forall (n:nat),
    py1 n = b1 (fun k => (ua k, (ud k, py2 k))) n /\
    py2 n = b2 (fun k => ((ua k, py1 k), ud k)) n
  ) as HPcompb12_clear.
  { intros n. split. 
    apply eq_sym. rewrite <- Hpy1. f_equal. rewrite -> Eua, -> Eud. reflexivity.
    apply eq_sym. rewrite <- Hpy2. f_equal. rewrite -> Eua, -> Eud. reflexivity. }


  (* HPcompb12' after clear up *)
  assert (forall (n:nat),
    py1' n = b1 (fun k => (ua k, (ud k, py2' k))) n /\
    py2' n = b2 (fun k => ((ua k, py1' k), ud k)) n
  ) as HPcompb12_clear'.
  { intros n. split. 
    apply eq_sym. rewrite <- Hpy1'. f_equal. rewrite -> Eua, -> Eud. reflexivity.
    apply eq_sym. rewrite <- Hpy2'. f_equal. rewrite -> Eua, -> Eud. reflexivity. }

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

  remember (fun n => (py1 n, py2 n)) as y12 eqn:Ey12.
  remember (fun n => (py1' n, py2' n)) as y12' eqn:Ey12'.
  
  assert (forall (n:nat),
    y12' n =
      ( b1 (fun k => (ua k, (ud k, py2' k))) n,
        b2 (fun k => ((ua k, py1' k), ud k)) n )
  ) as Hb12un'.
  { intros n.
    rewrite -> Ey12'.
    rewrite <- HPcompb12_b1'.
    rewrite <- HPcompb12_b2'.
    reflexivity.
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
  { rewrite Hb1eq''' with (n:=0).
    - reflexivity.
    -    intros m H0.
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
      + rewrite Hb2eq''' with (n:=0). (* split. *)
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

  assert (forall (n:nat),
      b1 (fun k => (fst (u k), (snd (u k), py2 k))) n =
      b1 (fun k => (fst (u k), (snd (u k), py2' k))) n /\
      b2 (fun k => ((fst (u k), py1 k), snd (u k))) n =
      b2 (fun k => ((fst (u k), py1' k), snd (u k))) n
  ) as Hb12eq'''.
  { rewrite -> Eua, -> Eud in Hb12eq''. 
    exact Hb12eq''.
  }
  

   intros n.

   (* Bring it to component behaviour level
      Assertion Hb12eq'' has been set up for that.
   *)
   rewrite <- Hpy1, <- Hpy2. rewrite <- Hpy1', <- Hpy2'. 
   apply pair_equal_spec.
   apply Hb12eq'''.
Qed.


(* The composition of two mixed causal behaviours should be unique. *)


(* The composition of two mixed causal behaviours should be unique. *)
Theorem composed_mixed_causal_behaviour_unique
  {UA UD Y1 Y2 : Type} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1)
         (b2 : @Behaviour ((UA*Y1)*UD) Y2)
         (b12 b12' : @Behaviour (UA*UD) (Y1*Y2)),
           mixed_causal b1 ->
           mixed_causal b2 ->
           is_composed_behaviour b1 b2 b12 ->
           is_composed_behaviour b1 b2 b12'
             -> forall (u : nat->UA*UD) (n:nat),
                  b12 u n = b12' u n.
Proof.
  intros b1 b2 b12 b12' Hmcb1 Hmcb2.
  intros HPcompb12 HPcompb12'.
  intros u.
  set (y12 := b12 u).
  set (y1 := fun n => fst (y12 n)).
  set (y2 := fun n => snd (y12 n)).
  set (y12' := b12' u).
  set (y1' := fun n => fst (y12' n)).
  set (y2' := fun n => snd (y12' n)).
  assert (forall n, y12 n = (y1 n, y2 n)) as Hy12. {
    intros n. unfold y1, y2. rewrite <- surjective_pairing. reflexivity. }
  assert (forall n, y12' n = (y1' n, y2' n)) as Hy12'. {
    intros n. unfold y1', y2'. rewrite <- surjective_pairing. reflexivity. }
  intro n. rewrite -> Hy12, -> Hy12'. revert n.
  unfold is_composed_behaviour in HPcompb12, HPcompb12'.
  
  apply (composed_mixed_causal_outputs_unique b1 b2 Hmcb1 Hmcb2 u).
  - intro n. apply eq_sym. unfold y1, y2, y12. exact (proj1 (HPcompb12 u n)).
  - intro n. apply eq_sym. unfold y1', y2', y12'. exact (proj1 (HPcompb12' u n)).
  - intro n. apply eq_sym. unfold y1, y2, y12. exact (proj2 (HPcompb12 u n)).
  - intro n. apply eq_sym. unfold y1', y2', y12'. exact (proj2 (HPcompb12' u n)).
Qed.

(*
Theorem composed_mixed_causal_behaviour_unique'
  {UA UD Y1 Y2 : Type} :
  forall (b1 : @Behaviour ((UA*(UD*Y2))) Y1)
         (b2 : @Behaviour (((UA*Y1)*UD)) Y2)
         (b12 b12' : @Behaviour (UA*UD) (Y1*Y2)),
           mixed_causal b1 ->
           mixed_causal b2 ->
           is_composed_behaviour b1 b2 b12 ->
           is_composed_behaviour b1 b2 b12'
             -> b12 = b12'.
Proof.
  intros b1 b2 b12 b12' Hmcb1 Hmcb2 Hb12 Hb12'.
  apply functional_extensionality. intro u.
  apply functional_extensionality. intro n.
  apply (composed_mixed_causal_behaviour_unique b1 b2 _ _ Hmcb1 Hmcb2 Hb12 Hb12').
Qed.
*)


Lemma pair_equal_fst_snd T1 T2 : forall (p1 p2 : T1*T2), (fst p1 = fst p2) -> (snd p1 = snd p2) -> p1 = p2.
Proof.
  intros p1 p2. intros Hfst Hsnd.
  destruct p1 as (p1fst,p1snd).
  destruct p2 as (p2fst,p2snd).
  f_equal.
  exact Hfst.
  exact Hsnd.
Qed.

Theorem behaviour_composition_mixed_causal {UA UD Y1 Y2} :
  forall b1 b2 (b12 : @Behaviour (UA*UD) (Y1*Y2)),
    (mixed_causal b1) -> (mixed_causal b2) -> (is_composed_behaviour b1 b2 b12) ->
      (mixed_causal b12).
Proof.
  intros b1 b2 b12 Hcb1 Hcb2 Hb12.
  unfold mixed_causal in *.
  unfold is_composed_behaviour in *.
  intros u u'.
(*
  specialize (Hb12 u') as Hb12'.
  specialize (Hb12 u) as Hb12.
*)
  induction n.
  - intros Hua _. intros m Hm.
    assert (m=0) as Hm0; [apply Nat.le_0_r; exact Hm|].
    rewrite -> Hm0.
    destruct (Hb12 u 0) as (Hy1,Hy2).
    destruct (Hb12 u' 0) as (Hy1',Hy2').
    assert (fst (b12 u 0) = fst (b12 u' 0)) as Hbu1. {
      rewrite -> Hy1. rewrite -> Hy1'.
      apply Hcb1 with (n:=0).
      - intros m0 Hm0le0.
        assert (m0=0) as Hm0eq0; [apply Nat.le_0_r; exact Hm0le0|].
        rewrite -> Hm0eq0.
        simpl.
        apply Hua.
        exact (Nat.le_refl 0).
      - intros m0 Hm0lt0.
        apply Nat.nlt_0_r in Hm0lt0.
        contradiction.
      - exact (Nat.le_refl 0).
    }
    assert (snd (b12 u 0) = snd (b12 u' 0)) as Hbu2. {
      rewrite -> Hy2. rewrite -> Hy2'.
      apply Hcb2 with (n:=0).
      - intros m0 Hm0le0.
        assert (m0=0) as Hm0eq0; [apply Nat.le_0_r; exact Hm0le0|].
        rewrite -> Hm0eq0.
        simpl.
        f_equal.
        apply Hua.
        exact (Nat.le_refl 0).
        exact Hbu1.
      - intros m0 Hm0lt0.
        apply Nat.nlt_0_r in Hm0lt0.
        contradiction.
      - exact (Nat.le_refl 0).
    }
    apply pair_equal_fst_snd.
    exact Hbu1.
    exact Hbu2.
  - intros HuaSn HudSn.
    assert (forall m0, m0 <= n -> fst (u m0) = fst (u' m0)) as Huan. {
      intros m0 Hm0len. apply HuaSn. apply Nat.le_le_succ_r. exact Hm0len.
    }
    assert (forall m0, m0 < n -> snd (u m0) = snd (u' m0)) as Hudn. {
      intros m0 Hm0ltn. apply HudSn. apply Nat.lt_lt_succ_r. exact Hm0ltn.
    }
    specialize (IHn Huan Hudn) as Hy12n.
    destruct (Hb12 u (S n)) as (Hy1,Hy2).
    destruct (Hb12 u' (S n)) as (Hy1',Hy2').
    assert (fst (b12 u (S n)) = fst (b12 u' (S n))) as Hbu1. {
      rewrite -> Hy1. rewrite -> Hy1'.
      apply Hcb1 with (n:=(S n)).
      - simpl.
        exact HuaSn.
      - simpl.
        intros m0 Hm0ltSn.
        f_equal.
        exact (HudSn m0 Hm0ltSn).
        f_equal.
        apply Hy12n.
        apply Nat.lt_succ_r.
        exact Hm0ltSn.
      - exact (Nat.le_refl (S n)).
    }
    assert (snd (b12 u (S n)) = snd (b12 u' (S n))) as Hbu2. {
      rewrite -> Hy2. rewrite -> Hy2'.
      apply Hcb2 with (n:=(S n)).
      - simpl.
        intros m0 Hm0leSn.
        f_equal.
        exact (HuaSn m0 Hm0leSn).

        apply Nat.le_succ_r in Hm0leSn.
        destruct Hm0leSn as [Hm0len|Hm0eqSn].
        -- f_equal.
           exact (Hy12n m0 Hm0len).
        -- rewrite -> Hm0eqSn.
           exact Hbu1.
      - simpl.
        exact HudSn.
      - exact (Nat.le_refl (S n)).
    }
    assert (b12 u (S n) = b12 u' (S n)) as Hy12Sn. {
      apply pair_equal_fst_snd.
      exact Hbu1. exact Hbu2.
    }
    intros m0 Hm0leSn.
    apply Nat.le_succ_r in Hm0leSn.
    destruct Hm0leSn as [Hm0len|Hm0eqSn].
    -- exact (Hy12n m0 Hm0len).
    -- rewrite -> Hm0eqSn.
       exact Hy12Sn.
Qed.
