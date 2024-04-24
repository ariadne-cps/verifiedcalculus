(******************************************************************************
 *  systems/nondeterministic_time_systems.v
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


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sets.Ensembles.

Require Import EnsembleMonad.
Require Import Words.
Require Import DependentChoice.

Require Export nondeterministic_system_models.

Section NondeterministicSystems.

Notation M := Ensemble.


Definition zip {T1 T2} (s1 : Seq T1) (s2 : Seq T2) := fun n => (s1 n, s2 n).
Definition unzip {T1 T2} (s : Seq (T1*T2)) := (fun n=>fst (s n), fun n => snd (s n)).
Notation "( u1 ; u2 )" := (zip u1 u2) (at level 0).
Notation "x ∈ S" := (element x S) (at level 80).


Definition Behaviour {U Y : Type} :=
  Seq U -> M (Seq Y).


Definition trajectory {U X : Type}
  (f:X->U->M X) (e:M X) (u:nat->U) : M (Seq X) :=
    fun x => element (x 0) e /\ forall n, element (x (S n)) (f (x n) (u n)).

Definition signal {X U Y : Type}
  (h:X->U->Y) (x:nat->X) (u:nat->U) : nat -> Y := 
    fun n => h (x n) (u n).

Definition behaviour {U Y X : Type}
  (s : @System U X Y) : @Behaviour U Y :=
    match s with
    | state_space_model f h e =>
      fun u => apply (fun x => signal h x (fun n => u n)) (trajectory f e u)
    end.


Lemma is_output {U X Y} :
  forall (s : @System U X Y) u y, 
      element y (behaviour s u) 
       = match s with | state_space_model f h e => 
           exists x, element (x 0) e  
             /\ (forall n, element (x (S n)) (f (x n) (u n))) 
               /\ (forall n, y n = h (x n) (u n))
    end.
Proof.
  intros s u y.
  destruct s as [f h e].
  apply propositional_extensionality. 
  unfold behaviour, Mlift, Mbind, Mpure. 
  simpl.
  unfold image, singleton, signal, trajectory, element.
  split.
  - intros Hx. destruct Hx as [x [[He Hf] Hh]].
    exists x. split; [|split]. 
    exact He. 
    exact Hf. 
    intro n. rewrite <- Hh. reflexivity.
  - intros Hx. destruct Hx as [x [He Hfh]].
    exists x. split; [split|]. 
    exact He. 
    apply Hfh.
    apply functional_extensionality.
    intro n. apply eq_sym. apply Hfh.
Qed.



Definition causal {U Y : Type}
  (b : (Seq U) -> M (Seq Y)) : Prop :=
    forall n, forall u1 u2 : Seq U, agree n u1 u2 ->
      forall y : Seq Y, 
        (exists y1 : Seq Y, element y1 (b u1) /\ agree n y1 y) <-> 
          (exists y2 : Seq Y, element y2 (b u2) /\ agree n y2 y).

Definition mixed_causal {UA UD Y : Type}
  (b : @Behaviour (UA*UD) Y) : Prop :=
    forall n, forall u1 u2 : Seq (UA*UD), 
      let (ua1,ud1) := unzip u1 in let (ua2,ud2) := unzip u2 in
        agree_le n ua1 ua2 ->
        agree_lt n ud1 ud2 ->
          forall y : Seq Y, 
            (exists y1 : Seq Y, element y1 (b u1) /\ agree_le (S n) y1 y) <-> 
            (exists y2 : Seq Y, element y2 (b u2) /\ agree_le (S n) y2 y).

Definition input_nontrivial {U Y} (b : Seq U -> M (Seq Y)) :=
  Logic.inhabited U -> exists (u : Seq U), exists y, element y (b u).

Definition input_accepting {U Y} (b : Seq U -> M (Seq Y)) :=
  forall (u : Seq U), exists y, element y (b u).

Definition input_enabling {U Y} (b : Seq U -> M (Seq Y)) :=
  input_nontrivial b /\
    forall (u : Seq U), 
      forall (n : nat) (u' : Seq U) (y' : Seq Y), 
        b u' y' -> (agree n u u') ->
         exists (y : Seq Y), b u y /\ agree n y y'.

Lemma input_accepting_implies_nontrivial : forall {U Y : Type},
  forall (b : @Behaviour U Y), 
    input_accepting b -> input_nontrivial b.
Proof.
  intros U Y b Hia.
  unfold input_accepting, input_nontrivial in *.
  intro Huv. destruct Huv as [uv]. set (u := fun n:nat => uv).
  destruct (Hia u) as [y Hy].
  exists u, y.
  exact Hy.
Qed.

Proposition input_enabling_implies_accepting : 
  forall {U Y} (b : Seq U -> M (Seq Y)), 
    input_enabling b -> input_accepting b.
Proof.
  intros U Y b Hie u.
  destruct Hie as [Hnt Hie].
  unfold input_nontrivial in Hnt.  
  unfold input_accepting.
  specialize (Hnt (Logic.inhabits (u 0))).
  destruct Hnt as [u' [y' Huy']].
  assert (agree 0 u u') as Hu0. {
    unfold agree. intros n p. apply (Nat.nlt_0_r) in p as f. contradiction.
  }
  specialize (Hie u 0 u' y' Huy' Hu0).
  destruct Hie as [y [Huy Hy0]].
  exists y. exact Huy.
Qed.

Proposition input_enabling_implies_causal : 
  forall {U Y} (b : Seq U -> M (Seq Y)), 
    input_enabling b -> causal b.
Proof.
  intros U Y b Hie.
  destruct Hie as [_ Hie].
  unfold causal.
  assert (forall n u1 u2 y, agree n u1 u2 -> (exists y1, b u1 y1 /\ agree n y1 y) 
          -> (exists y2, b u2 y2 /\ agree n y2 y)) as H. {
    intros n u1 u2 y Hu.
    apply (agree_sym) in Hu.
    unfold apply.
    intros [y1 [Huy1 Hyw1]].
    specialize (Hie u2 n u1 y1 Huy1 Hu).
    destruct Hie as [y2 [Huy2 Hy]].
    exists y2.
    split.
    exact Huy2.
    apply (agree_trans n _ y1 _).
    exact Hy.
    exact Hyw1.
  }
  intros n u1 u2 Hu y.
  split.
  - apply H. exact Hu.
  - apply H. apply agree_sym. exact Hu.
Qed.

Proposition causal_and_input_nontrivial_implies_enabling : 
  forall {U Y} (b : Seq U -> M (Seq Y)), 
     causal b -> input_nontrivial b -> input_enabling b.
Proof.
  unfold causal, input_enabling.
  intros U Y b Hc Hin.
  split. exact Hin. clear Hin.
  intros u n u' y' Huy' Hu.
  specialize (Hc n u u' Hu y').
  apply (proj2 Hc).
  exists y'.
  split.
  exact Huy'.
  exact (agree_refl n y').
Qed.






Lemma nonblocking_trajectory : forall {U X : Type}
  (f : X -> U -> Ensemble X) (e : Ensemble X),
    (forall x u, inhabited (f x u)) -> (inhabited e) ->
      forall u, exists x, trajectory f e u x.
Proof.
  intros U X f e Hf He u.
  set (R nx nx' := fst nx' = S (fst nx) /\ element (snd nx') (f (snd nx) (u (fst nx)))).
  assert (forall nx, exists nx', R nx nx') as Hi. {
    intros [n x].
    set (n' := S n).
    specialize (Hf x (u n)).
    destruct Hf as [x' Hx'].
    exists (n',x').    unfold R, n'.
    simpl.
    split. reflexivity. exact Hx'.
  }
  destruct He as [x0 Hx0].
  assert (exists nxs, (nxs 0 = (0,x0)) /\ forall n, R (nxs n) (nxs (S n))) as Hc. {
    apply functional_dependent_choice.
    exact Hi.
  }
  destruct Hc as [nxs [Hnx0 Hnxs]].
  exists (fun n => snd (nxs n)).
  split.
  unfold element. rewrite -> Hnx0. simpl. exact Hx0.
  intros n.
  assert (forall n, fst (nxs n) = n) as Hn. {
    intros m. induction m. rewrite -> Hnx0. reflexivity.
    specialize (Hnxs m). unfold R in Hnxs. destruct Hnxs as [Hnxm _].
    rewrite -> Hnxm. rewrite -> IHm. reflexivity.
  }  
  specialize (Hnxs n).
  unfold R in Hnxs.
  destruct Hnxs as [_ Hnxs].
  rewrite -> Hn in Hnxs.
  exact Hnxs. 
Qed.


Proposition nonblocking_input_accepting :
 forall {U X Y} (s : @System U X Y),
   nonblocking s -> input_accepting (behaviour s).
Proof.
  intros U X Y s Hs u.
  destruct s as [f h e].
  assert (exists x, trajectory f e u x) as Hx. {
    destruct Hs as [He Hf]. 
    apply nonblocking_trajectory.
    exact Hf. exact He.
  }
  destruct Hx as [x Hx].
  set (y:=signal h x u).
  exists y.
  unfold element, behaviour, apply.
  exists x.
  split.
  exact Hx.
  unfold y. reflexivity.
Qed.



Theorem nonblocking_output_extension :
 forall {U X Y} (s : @System U X Y) (u u' : Seq U) (n : nat) (y : Seq Y),
   nonblocking s -> (agree n u u') -> (behaviour s u y) ->
     exists (y' : Seq Y), (behaviour s u' y' /\ agree n y y').
Proof.
  intros U X Y s u u' n y Hs Hua Huy.
  destruct s as [f h e].
  destruct Hs as [He Hf].
  unfold behaviour, apply in Huy.
  destruct Huy as [x [Hx Hy]].
  set (xn := x n).
  set (yn := y n).
  set (en := fun x => x = xn).
  assert (inhabited en) as Hen. { unfold inhabited. exists xn. unfold en. reflexivity. }
  set (ue' := fun k => u' (n+k)).
  assert (exists xe', trajectory f en ue' xe') as Hxe'. {
    apply nonblocking_trajectory.
    exact Hf. exact Hen.
  }
  destruct Hxe' as [xe' Hxe'].
  destruct Hx as [Hx0 Hx].
  destruct Hxe' as [Hxe0' Hxe'].
  unfold element, en in Hxe0'.
  set (x' := fun k => match Compare_dec.le_lt_dec n k with | left _ => xe' (k-n) | right p => x k end).
  assert (forall m, m<=n -> x' m = x m) as Hxle. {
    unfold x'. intros m Hmlen.
    destruct (Compare_dec.le_lt_dec n m) as [Hnlem|Hmltn].
    - assert (m=n) as Hmeqn. 
        exact (Nat.le_antisymm _ _ Hmlen Hnlem).
      rewrite -> Hmeqn.
      rewrite -> Nat.sub_diag.
      exact Hxe0'.
    - reflexivity.
  }
  assert (forall m, m<n -> x' m = x m) as Hxlt. {
    intros m Hmltn. apply Hxle. exact (Nat.lt_le_incl _ _ Hmltn).
  }
  assert (forall m, n<=m -> x' m = xe' (m-n)) as Hxge. {
    unfold x'. intros m Hmlen.
    destruct (Compare_dec.le_lt_dec n m) as [Hn|Hn].
    - reflexivity.
    - set (Hfalse := Nat.lt_irrefl m (Nat.lt_le_trans _ _ _ Hn Hmlen)).
      contradiction.
  }
  assert (agree n x x') as Hxa. {
    unfold agree. intros m Hmltn.
    symmetry.
    exact (Hxlt m Hmltn).
  }
  set (y' := signal h x' u').
  exists y'.
  split.
  unfold behaviour.
  exists x'.
  split.
  - unfold trajectory.
    split.
    -- rewrite -> Hxle.
       exact Hx0.
       exact (Nat.le_0_l n).
    -- intro m.
       destruct (Compare_dec.le_lt_dec n m) as [Hnlem|Hmltn].
       --- assert (n <= S m) as Hnlesm. exact (Nat.le_le_succ_r _ _ Hnlem).
           rewrite -> (Hxge _ Hnlem), (Hxge _ Hnlesm).
           rewrite -> (Nat.sub_succ_l _ _ Hnlem).
           unfold ue' in Hxe'.
           replace (u' m) with (u' (n+(m-n))).
           apply (Hxe' (m-n)).
           rewrite -> Nat.add_comm.
           rewrite -> (Nat.sub_add _ _ Hnlem).
           reflexivity.
       --- assert (S m <= n) as Hsmlen. apply Nat.le_succ_l. exact Hmltn.
           rewrite -> (Hxlt _ Hmltn), (Hxle _ Hsmlen).
           replace (u' m) with (u m).
           exact (Hx m).
           exact (Hua _ Hmltn).
  - unfold y'.
    reflexivity.
  - rewrite <- Hy. unfold y', agree.
    unfold signal.
    intros m Hmltn.
    assert (m <= n) as Hmlen. exact (Nat.lt_le_incl _ _ Hmltn).
    f_equal.
    symmetry.
    exact (Hxle m Hmlen).
    exact (Hua m Hmltn).
Qed.

Proposition nonblocking_behaviour_causal : forall {U X Y : Type}
    (s : @System U X Y),
      nonblocking s -> causal (behaviour s).
Proof.
  intros U X Y s Hs.
  unfold nonblocking. 
  unfold causal.
  assert (forall n u1 u2, agree n u1 u2 -> forall y : Seq Y,  
            (exists y1, element y1 (behaviour s u1) /\ agree n y1 y) -> 
            (exists y2, element y2 (behaviour s u2) /\ agree n y2 y)) as H. {
    intros n u1 u2 Hu y.
    destruct s as [f h e].
    intros [y1 [Huy1 Hyw1]].
    unfold element.
    assert (exists y2, behaviour (state_space_model f h e) u2 y2 /\ agree n y1 y2) as H'.
    apply (nonblocking_output_extension _ u1).
    - exact Hs.
    - exact Hu.
    - exact Huy1. 
    - destruct H' as [y2 [Huy2 Hyw12]].
      exists y2.
      split.
      exact Huy2.
      apply (agree_trans _ _ y1 _).
      apply agree_sym. exact Hyw12.
      exact Hyw1.
  }
  intros n u1 u2 Hu.
  split. apply H. exact Hu. apply H. apply agree_sym. exact Hu.
Qed.

Theorem nonblocking_behaviour_input_enabling : forall {U X Y : Type}
    (s : @System U X Y),
      nonblocking s -> input_enabling (behaviour s).
Proof.
  intros U X Y s Hs.
  apply causal_and_input_nontrivial_implies_enabling.
  apply nonblocking_behaviour_causal; [exact Hs].
  apply input_accepting_implies_nontrivial.
  apply nonblocking_input_accepting; [exact Hs].
Qed.




(*
Definition input_nontrivial {U Y} (b : Seq U -> M (Seq Y)) :=
  Logic.inhabited U -> exists u, exists y, element y (b u).

Definition input_accepting {U Y} (b : Seq U -> M (Seq Y)) :=
  forall (u : Seq U), exists y, element y (b u).

Definition input_enabling {U Y} (b : Seq U -> M (Seq Y)) :=
  input_nontrivial b /\
    forall n, forall u1 u2, agree n u1 u2 ->
      forall y1, exists y2, element y2 (b u2) /\ (element y1 (b u1) -> agree n y1 y2).
*)

(*
Definition partial_behaviours {U Y} (b : Seq U -> M (Seq Y)) {n} (uw : Wrd n U) : M (Wrd n Y) :=
  fun yw => exists us ys, proj n us = uw /\ proj n ys = yw /\ element ys (b us).

Definition input_enabling
' {U Y} (b : Seq U -> M (Seq Y)) :=
  forall u, forall n, let uw := proj n u in
    (exists yw : Wrd n Y, element yw (partial_behaviours b uw))
      /\ forall yw : Wrd n Y,
           element yw (partial_behaviours b uw)
             -> exists y, element y (b u) /\ yw = proj n y.
*)

Proposition input_enabling_implies_input_accepting :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    input_enabling b -> input_accepting b.
Proof.
  unfold input_enabling, input_accepting, input_nontrivial.
  intros U Y b [Hnt Hie] u.
  specialize (Hnt (Logic.inhabits (u 0))).
  destruct Hnt as [u' [y' Huy']].
  assert (agree 0 u u') as Hu. {
    unfold agree. intros m Hm. apply Nat.nlt_0_r in Hm. contradiction. }
  specialize (Hie u 0 u' y' Huy' Hu).
  destruct Hie as [y [Hy _]].
  exists y.
  exact Hy.
Qed.

(*
Proposition input_enabling_implies_causal :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    input_enabling b -> causal b.
Proof.
  unfold input_enabling, causal.
  intros U Y b Hia.
  intros n u1 u2 Hu12.
  apply ensemble_equal.
  intro yw1.
  revert Hu12. revert u1 u2.
  assert (forall u1 u2, agree n u1 u2 -> element yw1 (apply (proj n) (b u1)) -> element yw1 (apply (proj n) (b u2))) as H. {
    intros u1 u2 Hu12.
    unfold apply.
    intro Hy1.
    destruct Hy1 as [y1 [Hby1 Hpy1]].
    specialize (Hia u2 n).
    destruct Hia as [_ Hia].
    unfold partial_behaviours in Hia.
    unfold element in *.
    specialize (Hia yw1).
    assert ((exists y2 : Seq Y, b u2 y2 /\ yw1 = proj n y2) -> (exists x : Seq Y, b u2 x /\ proj n x = yw1)) as Hs. {
      intros [y2 Hy2]. exists y2. split. exact (proj1 Hy2). apply (eq_sym). exact (proj2 Hy2).
    }
    apply Hs.
    apply Hia.
    exists u1, y1.
    split; [|split].
    - exact (proj1 (agree_proj n u1 u2) Hu12).
    - exact Hpy1.
    - exact Hby1.
  }
  intros u1 u2 Hu12.
  split.
  - apply H. exact Hu12.
  - apply H. apply agree_sym. exact Hu12.
Qed.
*)

(*
Proposition causal_and_input_accepting_implies_input_enabling :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    causal b -> input_accepting b -> input_enabling b.
Proof.
  unfold causal, input_accepting, input_enabling.
  unfold element, partial_behaviours.
  intros U Y b Hic Hie.
  intros u n.
  split.
  - specialize (Hie u).
    destruct Hie as [y Hy].
    exists (proj n y).
    exists u, y.
    split; [|split].
    -- reflexivity.
    -- reflexivity.
    -- exact Hy.
  - intros yw Hyw.
    destruct Hyw as [us [ys Hyw]].
    destruct Hyw as [Hus [Hys Hbus]].
    specialize (Hic n u us).
    apply agree_proj in Hus.
    apply agree_sym in Hus.
    specialize (Hic Hus).
    unfold apply in Hic.
    apply equal_f with (x:=yw) in Hic.
    assert (exists y : Seq Y, b u y /\ proj n y = yw) as Hy. {
      rewrite -> Hic.
      exists ys.
      split. exact Hbus. exact Hys.
    }
    destruct Hy as [y [Hby Hpy]]. exists y. split. exact Hby. apply eq_sym. exact Hpy.
Qed.
*)

Example not_behaviour_causal : exists (U X Y : Type)
    (s : @System U X Y),
      not (causal (behaviour s)).
Proof.
  exists Double, Double, Double.
  set (f:=fun (x u x': Double) => (x=first) /\ (x'=u)).
  set (h:=fun (x u : Double) => x).
  set (e:=fun (x0 : Double) => (x0=first)).
  set (s:=state_space_model f h e).
  exists s.
  unfold causal.
  intros H.
  set (u1:=fun n:nat => first).
  set (u2:=fun n:nat => match n with | 0 => first | _ => second end).
  specialize (H 1 u1 u2).
  set (x1:=fun n:nat => first).
  set (y1:=fun n:nat => first).
  assert (element y1 (behaviour s u1)) as H1. {
    unfold behaviour, Mlift, Mbind. simpl. 
    unfold signal, trajectory, image, singleton, element.
    exists x1. split. split.
    unfold e, x1. reflexivity.
    intro n. unfold f, u1, x1. split. reflexivity. reflexivity.
    apply functional_extensionality. intro n. unfold h, u1, x1, y1. reflexivity.
  }
  assert (forall y2, not (element y2 (behaviour s u2))) as H2. {
    intros y2.
    unfold behaviour, Mlift, Mbind. simpl. 
    unfold signal, trajectory, image, singleton, element.
    unfold f, h, e.
    intro Hy2.
    destruct Hy2 as [x2 [[He2 Hf2] Hh2]].
    assert (x2 1 = first) as Hx21. {
      specialize (Hf2 0). unfold u2 in Hf2. apply Hf2. }
    assert (x2 2 = second) as Hx22. {
      specialize (Hf2 1). unfold u2 in Hf2. apply Hf2. }
    specialize (Hf2 2). destruct Hf2 as [Hf2 _]. rewrite -> Hx22 in Hf2. discriminate Hf2.
  }
  assert (agree 1 u1 u2) as Hu. {
    unfold agree. intros m Hm.
    replace m with 0.
    unfold u1, u2. reflexivity.
    apply eq_sym. apply Nat.lt_1_r. exact Hm.
  }
  specialize (H Hu).
  set (yw := (fun k:nat => first)).
  assert (exists y1, element y1 (behaviour s u1) /\ agree 1 y1 yw) as Hyw1. {
    unfold element in H1.
    unfold element, apply.
    exists y1.
    split.
    exact H1.
    unfold agree.
    intros m Hm.
    assert (m=0) as Hm0. apply Nat.lt_1_r. exact Hm.
    rewrite -> Hm0.
    simpl.
    reflexivity.
  }
  assert (not (exists y2, element y2 (behaviour s u2) /\ agree 1 y2 yw)) as Hyw2. {
    unfold element.
    intros [y2 [Hy2 _]].
    exact (H2 y2 Hy2).
  }
  rewrite <- H in Hyw2.
  contradiction.
Qed.

Definition is_mixed_causal_system (UA UD Y1: Type) {X Y2 : Type} (s : @System ((UA*UD)*Y1) X Y2) :=
  match s with | state_space_model _ h _ => 
      forall x ua ud ud' y1 y1', h x ((ua,ud),y1) = h x ((ua,ud'),y1') 
  end.

Print System.

(*
Record MixedCausalSystem (UA UD X Y) :=
  { f : X -> (UA*UD) -> M X;  h : X -> UA -> Y;  e : M X }.
*)
Inductive MixedCausalSystem (UA UD X Y : Type) : Type :=
  mixed_state_space_model (f : X -> (UA*UD) -> M X) (h : X -> UA -> Y) (e : M X).
Arguments mixed_state_space_model {UA UD X Y}.


(* Define the composition of state space models. *)
Definition compose_mixed_causal_systems {UA UD X1 X2 Y1 Y2 : Type}
  (s1 : MixedCausalSystem UA (UD*Y2) X1 Y1)
  (s2 : MixedCausalSystem (UA*Y1) UD X2 Y2)
  : (MixedCausalSystem UA UD (X1*X2) (Y1*Y2)) :=
    match s1 with
    | mixed_state_space_model f1 h1 e1 =>
      match s2 with
      | mixed_state_space_model f2 h2 e2 =>
        let e12 : M (X1*X2) := ensemble_product e1 e2 in
        let h12 : (X1*X2) -> (UA) -> (Y1*Y2) := fun x12 u =>
          (let y1:=h1 (fst x12) u in let y2:=h2 (snd x12) (u,y1) in (y1,y2)) in
        let f12 : (X1*X2) -> (UA*UD) -> M (X1*X2) :=
          (fun x12 u x12' => 
            let ua:=fst u in let ud:=snd u in
            let x1:=fst x12 in let x2:=snd x12 in
            let y1:=h1 x1 ua in let y2:=h2 x2 (ua,y1) in          
            let x1':=fst x12' in let x2':=snd x12' in
              element x1' (f1 x1 (ua,(ud,y2)))
                /\ element x2' (f2 x2 ((ua,y1),ud))) in
        mixed_state_space_model f12 h12 e12
      end
    end
.


Definition is_mixed_composed_behaviour {UA UD Y1 Y2}
  (b1 : @Behaviour (UA*(UD*Y2)) Y1)
  (b2 : @Behaviour ((UA*Y1)*UD) Y2)
  (b12 : @Behaviour (UA*UD) (Y1*Y2)) := 
    forall (u:nat->UA*UD), let (ua,ud) := unzip u in
      forall (y12:nat->Y1*Y2), let (y1,y2) := unzip y12 in 
        y12 ∈ b12 u <-> y1 ∈ b1 (ua;(ud;y2)) /\ y2 ∈ b2 ((ua;y1);ud).

Definition is_composed_behaviour {U Y1 Y2}
      (b1 : @Behaviour (U*Y2) Y1)
      (b2 : @Behaviour (U*Y1) Y2)
      (b12 : @Behaviour U (Y1*Y2))
    : Prop :=
  forall (u : Seq U) (y12 : Seq (Y1*Y2)),
    let (y1,y2) := unzip  y12 in
      y12 ∈ b12 u <-> y1 ∈ b1 (u;y2) /\ y2 ∈ b2 (u;y1).

Definition compose_mixed_behaviours {UA UD Y1 Y2}
    (b1 : @Behaviour (UA*(UD*Y2)) Y1)
    (b2 : @Behaviour ((UA*Y1)*UD) Y2)
      : @Behaviour (UA*UD) (Y1*Y2) :=
  fun (u:nat->UA*UD) => let (ua,ud) := unzip u in
    fun(y12:nat->Y1*Y2) => let (y1,y2) := unzip y12 in
      y1 ∈ b1 (ua;(ud;y2)) /\ y2 ∈ b2 ((ua;y1);ud).

Theorem compose_mixed_behaviours_correct {UA UD Y1 Y2} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1) (b2 : @Behaviour ((UA*Y1)*UD) Y2),
    is_mixed_composed_behaviour b1 b2 (compose_mixed_behaviours b1 b2).
Proof.
  intros b1 b2.
  unfold is_mixed_composed_behaviour, compose_mixed_behaviours.
  intros u. remember (unzip u) as uad. destruct uad as [ua ud].
  intros y12. remember (unzip y12) as y1y2. destruct y1y2 as [y1 y2].
  unfold element. simpl.
  replace (fun n => fst  (y12 n)) with y1.
  replace (fun n => snd  (y12 n)) with y2.
  tauto.
  injection Heqy1y2. tauto.
  injection Heqy1y2. tauto.
Qed.

Theorem composed_mixed_behaviour_unique {UA UD Y1 Y2} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1) (b2 : @Behaviour ((UA*Y1)*UD) Y2)
    (b12 b12' : @Behaviour (UA*UD) (Y1*Y2)),
      is_mixed_composed_behaviour b1 b2 b12 -> 
        is_mixed_composed_behaviour b1 b2 b12' -> b12=b12'.
Proof.
  intros b1 b2 b12 b12'.
  unfold is_mixed_composed_behaviour.
  intros Hb12 Hb12'.
  apply functional_extensionality. intro u.
  apply functional_extensionality. intro y.
  apply propositional_extensionality.
  specialize (Hb12 u y).
  specialize (Hb12' u y).
  apply iff_sym in Hb12'.
  apply (@iff_trans _ _ _ Hb12 Hb12').
Qed.

Theorem composed_mixed_causal_behaviour_causal {UA UD Y1 Y2} :
  forall (b1 : @Behaviour (UA*(UD*Y2)) Y1) (b2 : @Behaviour ((UA*Y1)*UD) Y2)
    (b12 : @Behaviour (UA*UD) (Y1*Y2)),
      is_mixed_composed_behaviour b1 b2 b12 -> 
        mixed_causal b1 -> mixed_causal b2 -> mixed_causal b12.
Proof.
Admitted.


(* Show that the behaviour of the composition of two systems
   is a composition of the behaviours of the components. *)
(*
Theorem composed_system_behaviour {U X1 X2 Y1 Y2 : Type} :
   forall (s1 : @System U X1 Y1)
          (s2 : @System (U*Y1) X2 Y2),
          is_composed_behaviour
            (behaviour s1)
            (behaviour s2)
            (behaviour (compose_mixed_causal_systems s1 s2))
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
Admitted.
*)



(* The composed behaviour of two systems should be unique. *)

(* Intermediate step to show how this theorem easily follows from last theorem *)

(* From above Theorem composed_mixed_causal_system_behaviour_unique, get systems involved
   - replace b12' by (behaviour (compose_systems s1 s2)).
   - use (behaviour s1) for b1, (behaviour s2) for b2.
*)

(*
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
   apply @composed_mixed_causal_behaviour_unique
     with (b1:=b1) (b2:=b2) (b12':=b12').

   - apply X1. (* ? *)
   - apply X2. (* ? *)
   - rewrite Eb1. apply behaviour_mixed_causal.
   - rewrite Eb2. apply behaviour_mixed_causal.
   - exact H0.
   - exact H1.
Qed.
*)

(* The composed behaviour of two systems should be unique. *)
(* One condition can go, because it is already proven to be true *)
(*
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
*)

End NondeterministicSystems.
