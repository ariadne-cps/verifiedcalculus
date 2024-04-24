(******************************************************************************
 *  systems/nondeterministic_system_conversions.v
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
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sets.Ensembles.

Require Import Words.
Require Import EnsembleMonad.

Require Import DependentChoice.

Require Import nondeterministic_infinite_time_systems.
Require Import nondeterministic_finite_time_systems.


Section NondeterministicSystems.

Notation M := Ensemble.

Notation proj := Words.proj.

(* Equivalent? definition based on words. *)
Definition infinite_causal' {U Y : Type}
  (b : (Seq U) -> M (Seq Y)) : Prop :=
    forall n, forall u1 u2 : Seq U, agree n u1 u2 ->
      apply (proj n) (b u1) = apply (proj n) (b u2).

(* Equivalent? definition based on finite_input_enabling. *)
Definition infinite_input_enabling' {U Y} (b : Seq U -> M (Seq Y)) :=
  forall (u : Seq U), forall (m:nat), let uw := proj m u in
    (exists yw : Wrd m Y, exists y : Seq Y, yw = projw m y /\ element y (b u))
      /\ forall yw : Wrd m Y,
           (exists u' y', agree m u u' -> yw = projw m y' -> element y' (b u'))
             -> exists y, element y (b u) /\ yw = projw m y.

Definition infinite_trajectory {U X : Type} := @trajectory U X.
Definition infinite_signal {X Y : Type} := @signal X Y.
Definition infinite_behaviour {U Y X : Type} := @behaviour U Y X.
Definition nonblocking_infinite_trajectory {U X : Type} := @nonblocking_trajectory U X.
Definition InfiniteBehaviour {U Y : Type} := @Behaviour U Y.
Definition infinite_input_nontrivial {U Y : Type} := @input_nontrivial U Y.
Definition infinite_input_enabling {U Y : Type} := @input_enabling U Y.
Definition infinite_input_accepting {U Y : Type} := @input_accepting U Y.
Definition infinite_causal {U Y : Type} := @causal U Y.


Theorem nonblocking_infinite_output_extension :
 forall {U X Y} (s : @System U X Y) (u : Seq U) {n : nat} (yw : Wrd (S n) Y),
   nonblocking s -> (finite_behaviour s) (S n) (projw (S n) u) (yw) ->
     exists (y : Seq Y), (infinite_behaviour s) u y /\ (projw (S n) y = yw). 
Proof.
(*
  intros U X Y s u n yw Hs Hyw.
  unfold finite_behaviour in Hyw.
  destruct s as [f h e].
  unfold apply in Hyw.
  destruct Hyw as [xw [Hxw Hyw]].
  set (pnltSn := Nat.lt_succ_diag_r n).
  set (xn := xw (ord n pnltSn)).
  set (en := fun x => x=xn).
  set (ue := fun k => u (n+k)).
  assert (exists xe, infinite_trajectory f en ue xe) as Hxe. {
    apply nonblocking_infinite_trajectory.
      unfold nonblocking in Hs. apply Hs.
      unfold inhabited. exists xn. reflexivity. 
  }
  destruct Hxe as [xe Hxe].
  assert (exists x, (projw (S n) x = xw)  /\ infinite_trajectory f e u x). {
    set (x := splice xw xe).
    exists x.
    split.
    - unfold x, proj.
      apply functional_extensionality. intros [k p].
      rewrite -> splice_word_element with (p:=p).
      f_equal. 
    - unfold infinite_trajectory.
      split.
      -- apply Hxw.
      -- intros k.
         assert ({k<n}+{k=n}+{k>n}) as Hk. { exact (Compare_dec.lt_eq_lt_dec k n). }
         destruct Hk as [ [Hkltn | Hkeqn] | Hkgtn ].
         --- unfold x.
             assert (S k < S n) as Hskltsn. { apply (Nat.succ_lt_mono k n). exact Hkltn. }
             assert (k < S n) as Hkltsn. { apply Nat.lt_lt_succ_r. exact Hkltn. }
             rewrite -> splice_word_element with (p:=Hskltsn).
             rewrite -> splice_word_element with (p:=Hkltsn).
             unfold finite_trajectory in Hxw.
             destruct Hxw as [_ Hxw].
             specialize (Hxw k Hskltsn).
             set (xwSk := xw (ord (S k) Hskltsn)) in *.
             replace (ord k (Nat.lt_succ_l k (S n) Hskltsn)) with (ord k Hkltsn) in Hxw.
             replace (proj (S n) u (ord k Hkltsn)) with (u k) in Hxw.
             exact Hxw.
             unfold proj. simpl. reflexivity.
             apply ord_eq. reflexivity.
         --- assert (k < S n) as Hkltsn. { rewrite -> Hkeqn. apply Nat.lt_succ_diag_r. }
             unfold x.
             rewrite -> splice_sequence_element.
             rewrite -> splice_word_element with (p:=Hkltsn).
             replace (xw (ord k Hkltsn)) with (xe 0).
             replace (S k - n) with (S 0).
             replace (u k)  with (u (n+0)).
             apply Hxe.
             rewrite -> Nat.add_0_r. rewrite -> Hkeqn. reflexivity.
             rewrite -> Hkeqn. rewrite -> Nat.sub_succ_l. rewrite -> Nat.sub_diag. reflexivity.
             exact (Nat.le_refl n).
             destruct Hxe as [Hxe0 _].
             rewrite -> (Hxe0). unfold xn.
             f_equal. apply ord_eq. apply eq_sym. exact Hkeqn.
             unfold ge. rewrite -> Hkeqn. apply Nat.le_refl.
         --- unfold x.
             rewrite -> splice_sequence_element.
             rewrite -> splice_sequence_element.
             set (m:=k-n).
             replace (S k - n) with (S m).
             replace (k) with (n+m).
             apply Hxe.
             apply Nat.add_sub_eq_nz. unfold m. apply Nat.sub_gt. exact Hkgtn. reflexivity.
             unfold m. apply eq_sym. apply Nat.sub_succ_l. apply Nat.lt_le_incl. exact Hkgtn.
             apply Nat.le_succ_l. exact Hkgtn.
             apply le_n_S. apply Nat.lt_le_incl. exact Hkgtn.
  }
  destruct H as [x [Hpx Htx]].
  exists (infinite_signal h x u).
  split.
  - unfold infinite_behaviour, apply. simpl.
    unfold image, singleton.
    exists x.
    split.
    -- exact Htx.
    -- f_equal.
  - rewrite <- Hyw.
    rewrite <- Hpx. 
    unfold finite_signal, infinite_signal, proj.
    reflexivity.
Qed.
*)
Admitted.

Lemma proj_output : forall {U X Y : Type}
  (s : @System U X Y) (u : Seq U) (y : Seq Y),
    element y (infinite_behaviour s u) -> 
      forall n, element (projw (S n) y) (finite_behaviour s (S n) (projw (S n) u)).
Proof.
  intros U X Y s u y Hy n.
  destruct s as [f h e].
  unfold infinite_behaviour, apply, element in Hy.
  unfold finite_behaviour, apply, element, proj.
  destruct Hy as [x [[Hx0 Hx] Hy]].
  exists (projw (S n) x).
  split.
  - unfold finite_trajectory. unfold infinite_trajectory in Hx.
    split.
    -- destruct (Compare_dec.zerop (S n)). trivial.
       unfold proj. simpl. exact Hx0.
    -- intros m q.
       unfold proj. simpl. exact (Hx m).   
  - unfold finite_signal.
    rewrite <- Hy.     
    reflexivity.
Qed.



Definition infinite_behaviour_from_finite {U Y : Type}
  (bw : forall [n : nat], Wrd n U -> M (Wrd n Y)) : Seq U -> M (Seq Y) :=
    fun u y => forall n, element (projw n y) (bw (projw n u)).

Definition finite_behaviour_from_infinite {U Y : Type}
  (bs : Seq U -> M (Seq Y)) : forall [n : nat], Wrd n U -> M (Wrd n Y) :=
    fun (n:nat) u y => exists us ys, projw n us = u /\ projw n ys = y /\ element ys (bs us).

Definition is_infinite_behaviour {U Y : Type}
  (bw : forall {n : nat}, Wrd n U -> M (Wrd n Y))
  (bs : Seq U -> M (Seq Y))
  := forall (u : Seq U) (y : Seq Y),
       element y (bs u) <-> forall n, element (projw n y) (bw (projw n u)).

Proposition infinite_behaviour_superset :
  forall {U Y} b, forall u,
  subset (b u) (@infinite_behaviour_from_finite U Y (finite_behaviour_from_infinite b) u).
Proof.
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  intros U Y b u y H n.
  exists u, y.
  split. reflexivity. split. reflexivity. exact H.
Qed.

Proposition finite_behaviour_subset :
  forall {U Y} (b : forall [n : nat], Wrd n U -> M (Wrd n Y)), forall n, forall u,
  subset (@finite_behaviour_from_infinite U Y (infinite_behaviour_from_finite b) n u) (b u).
Proof.
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  intros U Y b.
  intros n u y.
  intro H.
  destruct H as [us [ys [Hu [Hy Hb]]]].
  rewrite <- Hu, <- Hy.
  exact (Hb n).
Qed.

Example finite_behaviour_not_superset :
  exists (U Y : Type) (b : forall [n : nat], Wrd n U -> M (Wrd n Y)), exists n, exists u,
  not (subset (b u) (@finite_behaviour_from_infinite U Y (infinite_behaviour_from_finite b) n u)).
Proof.
  exists Single, Single.
  set (b := fun (n : nat) (u y : Wrd n Single) => n < 2).
  set (n := 1).
  set (u := fun (u : ordinal 1) => only).
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  exists b.
  exists n.
  exists u.
  intro H.
  assert (b n u u) as Hbu. { unfold b, n, u. auto. }
  specialize (H u Hbu).
  destruct H as [us [ys H]].
  destruct H as [_ [_ H]].
  specialize (H 2).
  unfold b in H.
  exact ((Nat.lt_irrefl 2) H).
Qed.

Example infinite_behaviour_not_subset :
  exists (U Y: Type) b u, not (subset (@infinite_behaviour_from_finite U Y (finite_behaviour_from_infinite b) u) (b u)).
Proof.
  exists Double, Double.
  set (b := fun (u y : Seq Double) => (forall n, u n = y n) /\ not (forall n, u n = first)).
  set (u0 := fun (n : nat) => first).
  exists b.
  exists u0.
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  intros Hn.
  specialize (Hn u0).
  apply Hn.
  - intro n.
    set (u := fun (k : nat) => if (k <? n) then first else second).
    exists u, u.
    assert (projw n u = projw n u0) as Hp. {
      apply agree_projw. unfold agree. unfold u, u0.
      intros m Hmltn.
      apply Nat.ltb_lt in Hmltn.
      rewrite -> Hmltn.
      reflexivity.
    }
    split. exact Hp. split. exact Hp.
    unfold b.
    split.
    -- reflexivity.
    -- intros Ht.
       specialize (Ht n).
       unfold u in Ht.
       rewrite -> Nat.ltb_irrefl in Ht.
       discriminate Ht.
  - unfold u0.
    reflexivity.
Qed.


Definition infinite_continuous {U Y : Type}
  (b : @InfiniteBehaviour U Y) :=
    forall u y, (forall n, exists y', element y' (b u) /\ agree n y y') -> element y (b u).
    
Proposition infinite_behaviour_from_finite_continuous :
  forall {U Y} (b : @FiniteBehaviour U Y), 
    infinite_continuous (infinite_behaviour_from_finite b).
Proof.
   intros U Y b.
   unfold infinite_continuous, infinite_behaviour_from_finite.
   unfold element.
   intros u y H n.
   specialize (H n).
   destruct H as [yn [Huyn Hy]].
   replace (projw n y) with (projw n yn).
   exact (Huyn n).
   apply agree_projw.
   apply agree_sym.
   exact Hy.
Qed.




Definition system_input_enabling {U X Y} (s : @System U X Y) :=
  match s with 
  | state_space_model f h e =>
      forall (u : Seq U), forall (n:nat), let uw := projw n u in
        (exists xw : Wrd n X, finite_trajectory f e uw xw)
          /\ forall xw : Wrd n X,
               finite_trajectory f e uw xw
                 -> exists x, infinite_trajectory f e u x /\ xw = projw n x
  end.

Example not_system_input_enabling_and_behaviour_input_enabling :
  exists U X Y (s : @System U X Y), 
    ~ (system_input_enabling s) /\ infinite_input_enabling (infinite_behaviour s).
Proof.
  set (U:=Single). set (X:=Double). set (Y:=Single).
  set (f:=fun (x:X) (u:U) (x':X) => match x with | first => True | second => False end).
  set (h:=fun (x:X) (u:U) => only : Y).
  set (e:=fun (x:X) => x=first).
  set (s:=state_space_model f h e).
  exists U, X, Y, s.
  split.
  - intro H.
    unfold system_input_enabling in H. simpl in H.
    set (u := fun (n : nat) => only : U).
    set (x := fun n => match n with | 0 => first | _ => second end).
    specialize (H u 2).
    destruct H as [_ H].
    set (uw := projw 2 u).
    set (xw := projw 2 x).
    specialize (H xw).
    assert (finite_trajectory f e uw xw) as Huxw. {
      unfold finite_trajectory, element, f, e, uw, xw, x. simpl.
      split.
      - rewrite -> projw_at. simpl. reflexivity.
      - intros m q. rewrite -> projw_at. simpl. replace m with 0. tauto.
        apply eq_sym. apply Nat.lt_1_r. apply Nat.succ_lt_mono. exact q.
    }
    specialize (H Huxw).
    destruct H as [x' [Hux' Hx']].
    unfold xw in Hx'.
    apply agree_projw in Hx'. 
    unfold agree in Hx'.
    specialize (Hx' 1 Nat.lt_1_2).
    unfold x in Hx'.
    unfold infinite_trajectory in Hux'.
    destruct Hux' as [_ Hfux'].
    specialize (Hfux' 1).
    rewrite <- Hx' in Hfux'.
    unfold element, f in Hfux'.
    contradiction.
  - unfold infinite_input_enabling.
    split.
    -- unfold infinite_input_nontrivial, infinite_behaviour.
       intros _.
       set (u := fun (n : nat) => only : U).
       set (x := fun (n : nat) => first : X).
       set (y := fun (n : nat) => only : Y).
       exists u, y.
       simpl.
       unfold element, apply. simpl.
       exists x.
       split.
       --- unfold infinite_trajectory.
           unfold element, f, e, u, x.
           split. reflexivity. intros m. unfold element. tauto.
       --- unfold infinite_signal. unfold h, u, x, y. reflexivity.     
    -- intros u n u' y' _ _.
       set (x := fun (n : nat) => first : X).
       set (y := fun (n : nat) => only : Y).
       exists y.
       split.
       --- unfold infinite_behaviour, apply. simpl.
           exists x.
           split.
           ---- unfold infinite_trajectory.
                split.
                ----- unfold element, e, x. reflexivity.
                ----- intro m. unfold element, f, x. tauto.
           ---- unfold infinite_signal, h, x, y. reflexivity.
       --- unfold agree, y. intros m _. destruct (y' m). reflexivity.
Qed.






Definition causal {U Y : Type}
  (bs : Seq U -> M (Seq Y)) : Prop :=
    exists bw : forall n, Wrd n U -> M (Wrd n Y),
      finite_prefix_conform bw /\ is_infinite_behaviour bw bs.


(* Probably not true, since infinite causal requires infinite_trajectory to exist (non-blocking). *)
Proposition prefix_conform_implies_infinite_causal :
  forall {U Y} (b : Seq U -> M (Seq Y)), causal b -> infinite_causal b.
Proof.
  unfold causal, finite_prefix_conform, infinite_causal, is_infinite_behaviour.
  intros U Y bs.
  intros [bw Hc].
  assert (forall n u1 u2, agree n u1 u2 -> subset (apply (projw n) (bs u1)) (apply (projw n) (bs u2))) as Hic. {
    intros n u1 u2 Hu.
    unfold subset, apply, element.
    intros yw.
    intros [y1 Hy1].
    set (uw := proj n u1).
      assert (exists m, S m = n) as Hn. { admit. }
      destruct Hn as [m Hm].
    destruct Hc as [Hfc Hib].
    unfold subset, apply in Hfc.
    assert (exists y2 : Wrd (S n) Y, bw (S n) (projw (S n) u2) y2 /\ restr n (Nat.le_succ_diag_r n) y2 = yw) as IH. {
      set (uw2 := projw (S n) u2).
      specialize (Hfc n u1).
      unfold element in Hfc.
Admitted.

Definition partial_behaviours {U Y} (b : Seq U -> M (Seq Y)) {n} : (Wrd n U) -> M (Wrd n Y) :=
  fun uw => fun yw => exists us ys, projw n us = uw /\ projw n ys = yw /\ element ys (b us).

Definition input_enabling' {U Y} (b : Seq U -> M (Seq Y)) :=
  forall u, forall n, let uw := projw n u in
    (exists yw : Wrd n Y, element yw (partial_behaviours b uw))
      /\ forall yw : Wrd n Y,
           element yw (partial_behaviours b uw)
             -> exists y, element y (b u) /\ yw = projw n y.





End NondeterministicSystems.

