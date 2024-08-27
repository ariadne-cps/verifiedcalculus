(******************************************************************************
 *  systems/compose_behaviours.v
 *
 *  Copyright 2023 Sacha L. Sindorf
 *                 Master's Thesis Artificial Intelligence
 *                 Maastricht University
 *
 *
 *  Copyright 2023 Pieter Collins
 *
 *  Definition and correctness proof of composition of
 *  mixed causal behaviours.
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

Require Export causality.
Require Export behaviour_composition.

Import causality.


Fixpoint iterated_behaviour_noinputs {Y} (y_default : Y)
  (b : Behaviour Y Y) (n : nat) : (Tr Y) :=
    match n with
      | O => b (fun _ => y_default)
      | S n' => b (iterated_behaviour_noinputs y_default b n')
    end.

Definition fixed_behaviour_noinputs {Y} (y_default : Y)
  (b : Behaviour Y Y) : (Tr Y) :=
    fun n => (iterated_behaviour_noinputs y_default b (S n)) n.

Definition is_fixed_behaviour_noinputs {Y} (b : Behaviour Y Y) (ys : Tr Y) : Prop
  := forall (n:nat), (b ys) n = ys n.

Lemma causal_fixed_noinputs_zero {Y : Type} :
  forall (b : @Behaviour Y Y) (u u' : Tr Y),
    (strictly_causal b) -> b u 0 = b u' 0.
Proof.
  intros b u u'.
  unfold strictly_causal.
  intros Hscb.
  apply Hscb with (n:=0).
  - intros m H0.
    apply Nat.nlt_0_r in H0.
    exfalso. apply H0.
  - reflexivity.
Qed.

Lemma causal_fixed_noinputs_succ {Y : Type} :
  forall (b : Behaviour Y Y) (u u' : Tr Y) (n : nat),
    (strictly_causal b) -> (u |≤ n |≡ u') -> b u (S n) = b u' (S n).
Proof.
  intros b u u' n.
  unfold strictly_causal.
  intros Hscb Hun.
  apply Hscb with (n:= S n).
  - intros m HuSn.
    apply (Nat.lt_succ_r m n) in HuSn.
    apply Hun. apply HuSn.
  - reflexivity.
Qed.

Lemma iterated_behaviour_eventually_fixed {Y : Type} (B : nat -> Tr Y) :
  (forall n m, m<n -> B (S n) m = B n m) ->
   forall n m, m<n -> B n m = B (S m) m.
Proof.
  intros HSn.

  assert (forall n m k, m<n -> B (n+k) m = B n m) as Hnk.
  { intros n m. induction k.
    - auto.
    - intro Hmltn.
       assert ((n + S k) = S (n+k)) as HSnk. auto.
       rewrite -> HSnk. rewrite <- IHk.
       + apply HSn.
         apply Nat.lt_le_trans with n; [exact Hmltn|].
         apply Nat.le_add_r.
       + exact Hmltn.
  }

  assert (forall n1 n2 m, m<n1 -> n1<=n2 -> B n2 m = B n1 m) as Hn1n2m. { (* [n<=n+k] *)
    intros n1 n2 m.
    remember (n2-n1) as k.
    intros Hmltn Hnltn'.
    rewrite <- (Hnk n1 m k).
    - assert (n2=n1+k) as Hn1n2k.
      { rewrite Heqk.
        rewrite Nat.add_comm.
        symmetry.
        apply Nat.sub_add with (m:=n2) (n:=n1).
        exact Hnltn'.
      }
      rewrite <- Hn1n2k.
      reflexivity.
    - exact Hmltn.
  }

  assert(forall n m, m<=n -> B (S n) m = B (S m) m ) as HSnSmm. (* [n1=S m, n2=S n] *)
  { intros n m Hmlen.
    apply Hn1n2m with (n2:=S n) (n1:=S m).
    - apply Nat.lt_succ_diag_r.
    - rewrite <- Nat.succ_le_mono.
      apply Hmlen.
  }

  intros n m Hmltn.
  induction n as [|n' IHn'].
  - apply Nat.nlt_0_r in Hmltn.
    exfalso. exact Hmltn.
  - apply HSnSmm.
    apply (Nat.lt_succ_r m n') in Hmltn.
    exact Hmltn.
Qed.

Lemma causal_iterated_behaviours_noinputs {Y : Type} (y_default : Y) (b : @Behaviour Y Y) :
  (strictly_causal b) -> (forall n, forall m, m<n ->
    iterated_behaviour_noinputs y_default b n m =
    iterated_behaviour_noinputs y_default b (S m) m).
Proof.
  intros Hscb.

  (* Condition in iterated_behaviour_eventually_fixed *)
  assert (forall n m,
     m<n ->
      iterated_behaviour_noinputs y_default b (S n) m =
      iterated_behaviour_noinputs y_default b n m
  ) as Hdef.
  { intros n. (* m H0. *)
    induction n as [|n' IHn'].
    - intros m H0.
      apply Nat.nlt_0_r in H0. exfalso. exact H0.
    - intros m H0. simpl.
      assert (forall u u', forall n, u |< n |≡ u' -> b u n = b u' n) as Hwscb. {
        intros u u' n Hu. 
        exact (Hscb u u' n Hu n (Nat.le_refl n)). }
      apply Hwscb.
      simpl in IHn'.
      intros m0 H1.
      rewrite IHn'.
      + reflexivity.
      + apply (Nat.lt_succ_r m n') in H0.
        apply Nat.lt_le_trans with (m:=m).
        * exact H1.
        * exact H0.
  }

  intros n m H0.
  rewrite iterated_behaviour_eventually_fixed.
  - reflexivity.
  - intros n0 m0 H1.
    rewrite Hdef.
    + reflexivity.
    + exact H1.
  - exact H0.
Qed.

Proposition strictly_causal_fixed_noinputs {Y} (y_default : Y) :
  forall (b : Behaviour Y Y),
    (strictly_causal b) ->
       let y := fixed_behaviour_noinputs y_default b in
         b y ≡ y.
Proof.
  intros b.
  intros Hscb.
  unfold is_fixed_behaviour_noinputs.
  intros n.
  unfold fixed_behaviour_noinputs.

  induction n as [|n IHn].
  - simpl.
    apply causal_fixed_noinputs_zero.
    exact Hscb.
  - simpl.
    apply causal_fixed_noinputs_succ.
    -- exact Hscb.
    -- intros m Hmlen.
       assert (b (iterated_behaviour_noinputs y_default b m) =
         (iterated_behaviour_noinputs y_default b (S m)) ) as HSm 
           by reflexivity.
      rewrite -> HSm. 
      symmetry.
      rewrite <- causal_iterated_behaviours_noinputs with (n:=S n).
      --- reflexivity.
      --- exact Hscb.
      --- apply Nat.lt_succ_r. exact Hmlen.
Qed.



Definition compose_behaviours_noinputs {Y1 Y2} (y1_default : Y1)
  (b1 : Behaviour Y2 Y1) (b2 : Behaviour Y1 Y2) : Tr (Y1*Y2) :=
    let y1s : Tr Y1 := fixed_behaviour_noinputs y1_default (fun y1s => b1 (b2 y1s)) in
      (y1s ; b2 y1s).

Definition compose_behaviours {UA UD Y1 Y2} (y1_default : Y1)
  (b1 : Behaviour (UA*(UD*Y2)) Y1) (b2 : Behaviour ((UA*Y1)*UD) Y2)
    : Behaviour (UA*UD) (Y1*Y2) :=
      fun u => let (ua,ud):=unzip u in
        let b1' := fun y2 => b1 (ua;(ud;y2)) in
        let b2' := fun y1 => b2 ((ua;y1);ud) in
          compose_behaviours_noinputs y1_default b1' b2'.





Theorem mixed_causal_composed {UA UD Y1 Y2} (y1d : Y1) :
  forall (b1 : Behaviour (UA*(UD*Y2)) Y1) 
         (b2 : Behaviour ((UA*Y1)*UD) Y2),
    mixed_causal b1 -> mixed_causal b2 ->
      is_composed_behaviour b1 b2 (compose_behaviours y1d b1 b2).
Proof.
  intros b1 b2 Hb1 Hb2.
  unfold is_composed_behaviour.
  intros u.
  remember (unzip u) as uad.
  destruct uad as [ua ud].
  unfold compose_behaviours.
  rewrite <- Hequad.
  set (b1' := (fun y2 => b1 (ua;(ud;y2)))).
  set (b2' := (fun y1 => b2 ((ua;y1);ud))).
  set (b12' := (fun y1 => b1' (b2' y1))).
  
  assert (strictly_causal b1') as Hscb1'. { 
    unfold strictly_causal. intros y2 y2' n Hy2. 
    unfold b1'. apply Hb1.
    reflexivity.
    intros m Hm. unfold zip. simpl. f_equal. exact (Hy2 _ Hm).
  }
  assert (causal b2') as Hcb2'. {
    unfold causal, b2'. intros y1 y1' n Hy1. apply Hb2.
    intros m Hm. unfold zip. simpl. f_equal. exact (Hy1 _ Hm).
    reflexivity.
  }
  assert (strictly_causal b12') as Hscb. {
    unfold strictly_causal.
    intros y1 y1' n Hy1.
    apply Hscb1'. 
    destruct n as [|n]. intros m Hm. apply Nat.nlt_0_r in Hm. contradiction.
    intros m Hm. unfold causal in Hcb2'. apply (Hcb2' _ _ n). intros m' Hm'. apply Hy1. all: apply Nat.lt_succ_r. exact Hm'. exact Hm.
  }

  remember (fixed_behaviour_noinputs y1d b12') as y1'.
  remember (b2' y1') as y2'.

  unfold compose_behaviours_noinputs.
  assert (is_fixed_behaviour_noinputs b12' y1') as Hfxy1. { 
    rewrite -> Heqy1'.
    Check strictly_causal_fixed_noinputs.
    Print is_fixed_behaviour_noinputs.
    apply strictly_causal_fixed_noinputs. exact Hscb. }
  unfold is_fixed_behaviour_noinputs, b12' in Hfxy1.
  rewrite <- Heqy2' in Hfxy1.

  unfold b12' in Heqy1'. rewrite <- Heqy1'. 
  unfold b12' in Heqy2'. rewrite <- Heqy2'.
  replace (unzip (y1';y2')) with (y1',y2') 
    by (unfold unzip, zip; f_equal).
  split.
  - unfold b1' in Hfxy1. intro n. now rewrite -> Hfxy1.
  - unfold b2' in Heqy2'. intro n. now rewrite <- Heqy2'.
Qed.



Theorem composed_behaviour_is_mixed_causal {UA UD Y1 Y2} (y1_default : Y1) :
  forall (b1 : Behaviour (UA*(UD*Y2)) Y1) (b2 : Behaviour ((UA*Y1)*UD) Y2),
    (mixed_causal b1) -> (mixed_causal b2) ->
      mixed_causal (compose_behaviours y1_default b1 b2).
Proof. 
  intros b1 b2 Hb1 Hb2.
  set (b12 := compose_behaviours y1_default b1 b2).
  apply (behaviour_composition_mixed_causal b1 b2 b12 Hb1 Hb2).
  now apply (mixed_causal_composed _ _ _ Hb1 Hb2).
Qed.

  
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
  fun (u : Tr (UA*UD)) => unassociate (b123 u).
Definition unpostprocess {UA UD Y1 Y2 Y3} 
  ( b123 : Behaviour (UA * UD) ((Y1*Y2)*Y3) )
    : Behaviour (UA*UD) (Y1*(Y2*Y3)) :=
  fun (u : Tr (UA*UD)) => associate (b123 u).


Lemma mixed_causal_preprocess1  {UA UD Y1 Y2 Y3} :
  forall (b1 : @Behaviour(UA*(UD*(Y2*Y3))) Y1),
    mixed_causal b1 -> mixed_causal (preprocess1 b1).
Proof.
  intros b1 Hc1.
  unfold mixed_causal, preprocess1.
  unfold mixed_causal in Hc1.
  intros u u' n.
  intros Hua1 Hud1.
  set (ua:=fun n=>fst (u n)); set (ud:=fun n=>(fst (fst (snd (u n)))));
  set (y2:=fun n=>snd (snd (u n))); set (y3:=fun n=>snd (fst (snd (u n)))).
  set (ua':=fun n=>fst (u' n)); set (ud':=fun n=>(fst (fst (snd (u' n)))));
  set (y2':=fun n=>snd (snd (u' n))); set (y3':=fun n=>snd (fst (snd (u' n)))).
  assert (forall n, ua n = fst (u n)) as Huan; [unfold ua; reflexivity|].
  assert (forall n, ua' n = fst (u' n)) as Huan'; [unfold ua'; reflexivity|].
  assert (forall n, snd (u n) = ((ud n,y3 n),y2 n)) as Hudn; [unfold ud, y2, y3; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity|].
  assert (forall n, snd (u' n) = ((ud' n,y3' n),y2' n)) as Hudn'. { unfold ud', y2', y3'; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity. }
  apply Hc1.
  - unfold ua, ua'. exact Hua1.
  - intros m Hmltn.
    simpl.
    specialize (Hud1 m Hmltn).
    rewrite -> Hudn, -> Hudn' in Hud1.
    unfold ud, y2, y3, ud', y2', y3' in Hud1.
    rewrite -> pair_equal_spec, -> pair_equal_spec in Hud1.
    unfold zip. simpl. 
    f_equal; [|f_equal].
    apply Hud1. apply Hud1. apply Hud1.
Qed.

Lemma mixed_causal_preprocess3  {UA UD Y1 Y2 Y3} :
  forall (b3 : @Behaviour ((UA*(Y1*Y2))*UD) Y3),
    mixed_causal b3 -> mixed_causal (preprocess3 b3).
Proof.
  intros b3 Hc3.
  unfold mixed_causal, preprocess3.
  unfold mixed_causal in Hc3.
  intros u u' n.
  intros Hua3 Hud3.
  set (ua:=fun n=>fst (fst (fst (u n)))); set (ud:=fun n=>(snd (u n)));
  set (y1:=fun n=>snd (fst (fst (u n)))); set (y2:=fun n=>snd (fst (u n))).
  set (ua':=fun n=>fst (fst (fst (u' n)))); set (ud':=fun n=>(snd (u' n)));
  set (y1':=fun n=>snd (fst (fst (u' n)))); set (y2':=fun n=>snd (fst (u' n))).
  assert (forall n, fst (u n) = ((ua n,y1 n),y2 n)) as Huan; [unfold ua, y1, y2; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity|].
  assert (forall n, fst (u' n) = ((ua' n,y1' n),y2' n)) as Huan'; [unfold ua', y1', y2'; intros m;
    rewrite <- surjective_pairing, <- surjective_pairing; reflexivity|].
  assert (forall n, ud n = snd (u n)) as Hudn; [unfold ud; reflexivity|].
  assert (forall n, ud' n = snd (u' n)) as Hudn'; [unfold ud'; reflexivity|].
  apply Hc3.
  - intros m Hmlen.
    simpl.
    specialize (Hua3 m Hmlen).
    rewrite -> Huan, -> Huan' in Hua3.
    unfold ua, y1, y2, ua', y1', y2' in Hua3.
    rewrite -> pair_equal_spec, -> pair_equal_spec in Hua3.
    unfold zip. simpl.
    f_equal; [|f_equal].
    apply Hua3. apply Hua3. apply Hua3.
  - unfold ud, ud'. exact Hud3.
Qed.

Lemma mixed_causal_postprocess {UA UD Y1 Y2 Y3} :
  forall (b123 : Behaviour (UA*UD) (Y1*(Y2*Y3))),
    mixed_causal b123 -> mixed_causal (postprocess b123).
Proof.
  intros b123 Hmcb123. 
  unfold mixed_causal, postprocess.
  intros u u' n.
  unfold mixed_causal in Hmcb123. specialize (Hmcb123 u u' n).
  intros Hua Hud. specialize (Hmcb123 Hua Hud). clear Hua Hud.
  remember (b123 u) as y123.
  remember (b123 u') as y123'.
  
  unfold unassociate.
  intros m Hmlen. unfold zip. simpl.
  specialize (Hmcb123 m Hmlen).
  rewrite <- Hmcb123.
  reflexivity.
Qed.

Definition is_three_composed_behaviours {UA UD Y1 Y2 Y3}
    (b1 : Behaviour (UA * (UD*(Y2*Y3))) Y1)
    (b2 : Behaviour ((UA*Y1) * (UD*Y3)) Y2)
    (b3 : Behaviour ((UA*(Y1*Y2)) * UD) Y3)
      ( b123 : Behaviour (UA*UD) ((Y1*Y2)*Y3) ) : Prop
  := forall (ua : Tr UA) (ud : Tr UD),
       let y123 := b123 (ua;ud) in
       let y12 := fst (unzip y123) in
         let y1 := fst (unzip y12) in
         let y2 := snd (unzip y12) in
         let y3 := snd (unzip y123) in
           y1 ≡ b1 (ua ; (ud;(y2;y3))) /\
             y2 ≡ b2 ((ua;y1) ; (ud;y3)) /\
               y3 ≡ b3 ((ua;(y1;y2)) ; ud).

Definition unzip3 {Y1 Y2 Y3} (y123 : Tr (Y1*Y2*Y3)) := 
  let (y12,y3) := unzip y123 in
    let (y1,y2) := unzip y12 in
      (y1,y2,y3).

Definition zip3prod {Y1 Y2 Y3} ( y1y2y3 : prod (prod (Tr Y1) (Tr Y2)) (Tr Y3) ) :=
  ((fst (fst y1y2y3);snd (fst y1y2y3));snd y1y2y3).

Lemma zip_unzip3' {Y1 Y2 Y3} (y123 : Tr (Y1*Y2*Y3))
  : let (y12,y3) := unzip3 y123 in
      let (y1,y2) := y12 in
        ((y1;y2);y3) ≡ y123.
Proof.
  unfold unzip, zip. intro n. symmetry.
  set (y12n := fst (y123 n)).
  assert (y12n = (fst (y12n), snd (y12n))) as H12.
  now apply surjective_pairing.
  rewrite <- H12. unfold y12n.
  now apply surjective_pairing.
Qed.

Lemma is_three_composed_behaviours_unique {UA UD Y1 Y2 Y3} :
  forall b1 b2 b3 (b123 b123' : Behaviour (UA*UD) (Y1*Y2*Y3)),
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
    mixed_causal b123 -> mixed_causal b123' -> 
      is_three_composed_behaviours b1 b2 b3 b123 ->
      is_three_composed_behaviours b1 b2 b3 b123' ->
        forall u, b123 u ≡ b123' u.
Proof.
  intros b1 b2 b3 b123 b123'.
  intros Hmcb1 Hmcb2 Hmcb3 Hmcb123 Hmcb123'.
  intros Hb123 Hb123' u.
  remember (unzip u) as uad eqn:Huad. destruct uad as [ua ud].
  assert (u ≡ (ua;ud)) as Hu. symmetry; now apply unzip_prod.
  unfold is_three_composed_behaviours in *.
  specialize (Hb123 ua ud). 
  remember (b123 (ua;ud)) as y123 eqn:Hy123.
(*
  remember (unzip3 y123) as y1y2y3 eqn:Hy1y2y3.
  destruct y1y2y3 as [[y1 y2] y3].
  set (Hzy123 := zip_unzip3 y123).
*)
  remember (fst (unzip y123)) as y12.
  remember (fst (unzip y12)) as y1.
  remember (snd (unzip y12)) as y2.
  remember (snd (unzip y123)) as y3.
  specialize (Hb123' ua ud).
  remember (b123' (ua;ud)) as y123' eqn:Hy123'.
  remember (fst (unzip y123')) as y12'.
  remember (fst (unzip y12')) as y1'.
  remember (snd (unzip y12')) as y2'.
  remember (snd (unzip y123')) as y3'.
  assert (forall n, y1 |< n |≡ y1' /\ y2 |< n |≡ y2' /\ y3 |< n |≡ y3' ) as Hind. {
    destruct Hb123 as [Hb1 [Hb2 Hb3]].
    destruct Hb123' as [Hb1' [Hb2' Hb3']].
    induction n.
    - split. 2:split. 
      intros n Hnlt0. now apply Nat.nlt_0_r in Hnlt0.
      intros n Hnlt0. now apply Nat.nlt_0_r in Hnlt0.
      intros n Hnlt0. now apply Nat.nlt_0_r in Hnlt0.
    - destruct IHn as [IHn1 [IHn2 IHn3]].
      assert (y1 |≤ n |≡ y1') as IHSn1. {
         intros m Hmlen.
         transitivity (b1 (ua; (ud; (y2'; y3'))) m).
         transitivity (b1 (ua; (ud; (y2; y3))) m).
         - exact (Hb1 m).
         - revert m Hmlen.
           apply Hmcb1.
           -- intros m _. simpl. reflexivity.
           -- intros m Hmltn. unfold zip. simpl.
              f_equal. 
              f_equal. 
              exact (IHn2 m Hmltn). 
              exact (IHn3 m Hmltn).   
         - symmetry; exact (Hb1' m).
      }
      assert (y2 |≤ n |≡ y2') as IHSn2. {
         intros m Hmlen.
         transitivity (b2 ((ua;y1'); (ud;y3')) m).
         transitivity (b2 ((ua;y1); (ud;y3)) m).
         - exact (Hb2 m).
         - revert m Hmlen.
           apply Hmcb2.
           -- intros m Hmlen. unfold zip. simpl. 
              f_equal. exact (IHSn1 m Hmlen).
           -- intros m Hmltn. unfold zip. simpl.
              f_equal. exact (IHn3 m Hmltn).   
         - symmetry; exact (Hb2' m).
      }
      assert (y3 |≤ n |≡ y3') as IHSn3. {
         intros m Hmlen.
         transitivity (b3 ((ua;(y1';y2')); ud) m).
         transitivity (b3 ((ua;(y1;y2)); ud) m).
         - exact (Hb3 m).
         - revert m Hmlen.
           apply Hmcb3.
           -- intros m Hmlen. unfold zip. simpl.
              f_equal. f_equal.
              exact (IHSn1 m Hmlen). exact (IHSn2 m Hmlen).
           -- intros m Hmltn. simpl. reflexivity.
         - symmetry; exact (Hb3' m).
      }
      split. 2:split.
      -- apply eqv_le_lt_succ. exact IHSn1.
      -- apply eqv_le_lt_succ. exact IHSn2.
      -- apply eqv_le_lt_succ. exact IHSn3.
   }
   assert (y1 ≡ y1' /\ y2 ≡ y2' /\ y3 ≡ y3') as Hy1y2y3. {
     split. 2: split.
     - apply all_eqv_lt. exact (fun n => proj1 (Hind n)).
     - apply all_eqv_lt. exact (fun n => proj1 (proj2 (Hind n))).
     - apply all_eqv_lt. exact (fun n => proj2 (proj2 (Hind n))).
  }
  assert (y12 ≡ y12') as Hy12y12'. {
    transitivity (y1';y2').
    transitivity (y1;y2).
    - rewrite -> Heqy1, -> Heqy2.
      unfold zip, unzip. intro n. simpl.
      now apply surjective_pairing. 
    - apply zip_prod. split. apply Hy1y2y3. apply Hy1y2y3.  
    - rewrite -> Heqy1', -> Heqy2'.
      unfold zip, unzip. intro n. simpl.
      symmetry. now apply surjective_pairing. 
  }
  assert (b123 u ≡ b123 (ua;ud)) as Hb123u. {
    apply mixed_causal_behaviour_extensional. 
    exact Hmcb123. exact Hu. }
  assert (b123' u ≡ b123' (ua;ud)) as Hb123u'. {
    apply mixed_causal_behaviour_extensional. 
    exact Hmcb123'. exact Hu. }
  transitivity (b123' (ua;ud)).
    2: symmetry; now apply Hb123u'.
  transitivity (b123 (ua;ud)).
    1: now apply Hb123u.
  rewrite <- Hy123, <- Hy123'.
  transitivity (y12';y3').
  transitivity (y12;y3).
  - symmetry; apply unzip_prod.
    rewrite -> surjective_pairing.
    rewrite -> Heqy12, -> Heqy3. 
    reflexivity.
  - apply zip_prod.
    split. 
    exact Hy12y12'.
    now apply Hy1y2y3.
  - apply unzip_prod.
    rewrite -> surjective_pairing.
    rewrite -> Heqy12', -> Heqy3'.
    reflexivity.
Qed.

Lemma pair_eq {Y1 Y2} :
  forall (y1 y1' : Y1) (y2 y2' : Y2),
    (y1,y2) = (y1',y2') -> y1 = y1' /\ y2 = y2'.
Proof.
  intros y1 y1' y2 y2' H. split.
  apply (f_equal fst) in H. exact H. 
  apply (f_equal snd) in H. exact H. 
Qed.

Lemma eval_eq {X Y} : forall (x : X) (f1 f2 : X -> Y),
  f1 = f2 -> f1 x = f2 x.
Proof.
  intros x f1 f2 H. rewrite <- H. reflexivity.
Qed.

Lemma unzip_equiv {Y1 Y2} : 
  forall (y y' : Tr (Y1*Y2)) (y1 y1' : Tr Y1) (y2 y2' : Tr Y2), 
    (y1,y2) = unzip y -> (y1',y2') = unzip y' ->
      y ≡ y' -> y1 ≡ y1' /\ y2 ≡ y2'.
Proof.
  intros y y' y1 y1' y2 y2' Hy Hy' He.
  assert (forall n, y1 n = y1' n /\ y2 n = y2' n) as Hs. {
    intros n. specialize (He n).
    rewrite <- (unzip_zip y1 y2) in Hy. unfold unzip in Hy. 
    rewrite <- (unzip_zip y1' y2') in Hy'. unfold unzip in Hy'.
    simpl in Hy. simpl in Hy'.
    apply pair_eq in Hy. destruct Hy as [Hy1 Hy2].
    apply pair_eq in Hy'. destruct Hy' as [Hy1' Hy2'].
    rewrite -> (eval_eq n _ _ Hy1).
    rewrite -> (eval_eq n _ _ Hy1').
    rewrite -> (eval_eq n _ _ Hy2).
    rewrite -> (eval_eq n _ _ Hy2').
    rewrite <- He.
    split; reflexivity.
  }
  split; intro n; apply Hs.
Qed.

Lemma input_zip1 {UA UD Y2 Y3} :
  forall (ua : Tr UA) (ud : Tr UD) (y2 y2' : Tr Y2) (y3 y3' : Tr Y3),
    y2 ≡ y2' -> y3 ≡ y3' -> 
      (ua;(ud;(y2;y3))) ≡ (ua;(ud;(y2';y3'))).
Proof.
  intros. 
  apply zip_prod; split. 1: reflexivity.
  apply zip_prod; split. 1: reflexivity.
  apply zip_prod; split. assumption. assumption.
Qed.
Lemma input_zip2 {UA UD Y1 Y3} :
  forall (ua : Tr UA) (ud : Tr UD) (y1 y1' : Tr Y1) (y3 y3' : Tr Y3),
    y1 ≡ y1' -> y3 ≡ y3' -> 
      ((ua;y1);(ud;y3)) ≡ ((ua;y1');(ud;y3')).
Proof.
  intros. 
  apply zip_prod; split. 
  apply zip_prod; split. reflexivity. assumption.
  apply zip_prod; split. reflexivity. assumption.
Qed.
Lemma input_zip3 {UA UD Y1 Y2} :
  forall (ua : Tr UA) (ud : Tr UD) (y1 y1' : Tr Y1) (y2 y2' : Tr Y2),
    y1 ≡ y1' -> y2 ≡ y2' -> 
      ((ua;(y1;y2));ud) ≡ ((ua;(y1';y2'));ud).
Proof.
  intros.
  apply zip_prod; split. 2: reflexivity.
  apply zip_prod; split. 1: reflexivity.
  apply zip_prod; split. assumption. assumption.
Qed.
Lemma input_zip3' {UA UD Y1 Y2} :
  forall (ua : Tr UA) (ud : Tr UD) (y12 y12' : Tr (Y1*Y2)),
    y12 ≡ y12' ->
      ((ua;y12);ud) ≡ ((ua;y12');ud).
Proof.
  intros.
  apply zip_prod; split. 2: reflexivity.
  apply zip_prod; split. 1: reflexivity. assumption.
Qed.

Lemma compose_behaviours_associative_left {UA UD Y1 Y2 Y3} :
  forall (b1 : Behaviour (UA*(UD*(Y2*Y3))) Y1)
         (b2 : Behaviour ((UA*Y1)*(UD*Y3)) Y2)
         (b3 : Behaviour ((UA*(Y1*Y2))*UD) Y3)
         (y1d : Y1) (y2d : Y2),
    let pb1 := (preprocess1 b1) in
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
      is_three_composed_behaviours b1 b2 b3 
        (compose_behaviours (y1d,y2d) 
          (compose_behaviours y1d pb1 b2) b3) .
Proof.
  intros b1 b2 b3 y1d y2d pb1 Hcb1 Hcb2 Hcb3.
  set (b12 := compose_behaviours y1d pb1 b2).
  set (b123 := compose_behaviours (y1d, y2d) b12 b3).
  assert (mixed_causal pb1) as Hcpb1. { 
    apply mixed_causal_preprocess1. exact Hcb1. }
  assert (is_composed_behaviour pb1 b2 b12) as Hpb12. {
    apply mixed_causal_composed. exact Hcpb1. exact Hcb2. }
  assert (mixed_causal b12) as Hcb12. {
    exact (behaviour_composition_mixed_causal pb1 b2 b12 Hcpb1 Hcb2 Hpb12). }
  assert (is_composed_behaviour b12 b3 b123) as Hb123. {
    apply mixed_causal_composed. exact Hcb12. exact Hcb3. }
  unfold is_three_composed_behaviours.
  unfold is_composed_behaviour in Hpb12, Hb123.
  intros ua ud.
  assert ((ua,ud)=unzip (ua;ud)) as Huad by apply unzip_zip.
  specialize (Hb123 (ua;ud)).
  rewrite <- Huad in Hb123.
  remember (b123 (ua;ud)) as y123 eqn:Hy123.

  (* Take (yt1,yt2) = unzip y12 
       with yt12 = (b12 (ua;(ud;y3))) 
     In goal, take (y1,y2)=unzip y12 
       with y12 = fst (unzip y123) 
     This keeps y1,y2,y3 in goal.
  *)
  remember (unzip y123) as y12y3 eqn:Ey12y3.
  destruct y12y3 as [y12 y3].
  remember (unzip y12) as y1y2 eqn:Ey1y2.
  destruct y1y2 as [y1 y2].
  assert ((y1;y2)≡y12) as Ey12. {
    apply unzip_prod. exact Ey1y2. }
  destruct Hb123 as [Hy12 Hy3].
  replace (fst (y12,y3)) with y12 by auto.
  rewrite <- Ey1y2. simpl.

  revert Hpb12; intro Hpb12.
  specialize (Hpb12 (ua;(ud;y3))). 

  remember (b12 (ua; (ud; y3))) as yt12 eqn:Hyt12.
  remember (unzip yt12) as yt1yt2 eqn:Eyt1yt2.
  destruct yt1yt2 as [yt1 yt2].
  replace (unzip (ua;(ud;y3))) with (ua,(ud;y3)) in Hpb12
    by reflexivity.
  destruct Hpb12 as [Hpyt1 Hyt2].
  assert (yt1 ≡ b1 (ua; (ud;(yt2;y3)))) as Hyt1. {
    unfold pb1, preprocess1 in Hpyt1. exact Hpyt1. }
  clear Hpyt1.
  revert Hyt1 Hyt2 Hy12 Hy3; intros Hyt1 Hyt2 Hy12 Hy3.
  revert Hy12; intros Eyt12.
  assert (yt1 ≡ y1 /\ yt2 ≡ y2) as Eyt1yt2'. { 
    apply (unzip_equiv yt12 y12).
    exact Eyt1yt2. exact Ey1y2. symmetry; exact Eyt12. }
  destruct Eyt1yt2' as [Eyt1 Eyt2].
  split. 2: split.
  - transitivity (b1 (ua; (ud; (yt2; y3)))). transitivity yt1.
    2: exact Hyt1. 1: symmetry; exact Eyt1.
    apply (mixed_causal_behaviour_extensional _ Hcb1).
    apply input_zip1. assumption. reflexivity.
  - transitivity (b2 ((ua; yt1); (ud; y3))). transitivity yt2.
    2: exact Hyt2. 1: symmetry; exact Eyt2.
    apply (mixed_causal_behaviour_extensional _ Hcb2).
    apply input_zip2. assumption. reflexivity.
  - transitivity (b3 ((ua; y12); ud)).
    exact Hy3.
    apply (mixed_causal_behaviour_extensional _ Hcb3).
    apply input_zip3'. symmetry; assumption.
Qed.

Lemma compose_behaviours_associative_right {UA UD Y1 Y2 Y3} :
  forall (b1 : Behaviour (UA*(UD*(Y2*Y3))) Y1)
         (b2 : Behaviour ((UA*Y1)*(UD*Y3)) Y2)
         (b3 : Behaviour ((UA*(Y1*Y2))*UD) Y3)
         (y1d : Y1) (y2d : Y2),
    let pb3 := (preprocess3 b3) in
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
      is_three_composed_behaviours b1 b2 b3 
        ( postprocess (compose_behaviours y1d b1 
          (compose_behaviours y2d b2 pb3)) ).
Proof.
  intros b1 b2 b3 y1d y2d pb3 Hcb1 Hcb2 Hcb3.
  set (b23 := compose_behaviours y2d b2 pb3).
  set (b123 := compose_behaviours y1d b1 b23).
  set (pb123 := postprocess b123).
  assert (mixed_causal pb3) as Hcpb3. { 
    apply mixed_causal_preprocess3. exact Hcb3. }
  assert (is_composed_behaviour b2 pb3 b23) as Hpb23. {
    apply mixed_causal_composed. exact Hcb2. exact Hcpb3. }
  assert (mixed_causal b23) as Hcb23. {
    exact (behaviour_composition_mixed_causal b2 pb3 b23 Hcb2 Hcpb3 Hpb23). }
  assert (is_composed_behaviour b1 b23 b123) as Hb123. {
    apply mixed_causal_composed. exact Hcb1. exact Hcb23. }
  unfold is_three_composed_behaviours.
  unfold is_composed_behaviour in Hpb23, Hb123.
  intros ua ud.
  assert ((ua,ud)=unzip (ua;ud)) as Huad by apply unzip_zip.
  specialize (Hb123 (ua;ud)).
  rewrite <- Huad in Hb123.

  remember (pb123 (ua;ud)) as y123 eqn:Hy123.
  remember (fst (unzip y123)) as y12 eqn:Ey12.
  remember (fst (unzip y12)) as y1 eqn:Ey1.
  remember (snd (unzip y12)) as y2 eqn:Ey2.
  remember (snd (unzip y123)) as y3 eqn:Ey3.
  assert ((y12,y3) = unzip y123) as Ey12y3. {
    rewrite -> Ey12, -> Ey3. now apply surjective_pairing. }
  assert ((y1,y2) = unzip y12) as Ey1y2. {
    rewrite -> Ey1, -> Ey2. now apply surjective_pairing. }
  revert Hb123 Hpb23 Hy123 Ey12 Ey1 Ey2 Ey3.
  intros Hb123 Hpb23 Hy123 Ey12 Ey1 Ey2 Ey3.

  remember (b123 (ua;ud)) as y123' eqn:Hy123'.
  remember (unzip y123') as y1y23' eqn:Hy12y3'.
  destruct y1y23' as [y1' y23'].

  assert (y123' ≡ (y1;(y2;y3))) as Ey123'. {
    unfold pb123, postprocess in Hy123.
    rewrite <- Hy123' in Hy123.
    transitivity (associate y123).
    - rewrite -> Hy123.
      unfold associate, unassociate. 
      transitivity (zip (fst (unzip y123')) (snd (unzip y123'))).
      symmetry; apply zip_unzip.
      apply zip_prod. split.
      -- reflexivity.
      -- unfold zip. intro n. simpl. apply surjective_pairing.  
    - unfold associate. now rewrite <- Ey12y3, <- Ey1y2.
  }
  assert (y1' ≡ y1) as Ey1'. {
    replace y1' with (fst (unzip y123')).
    transitivity (fst (unzip (y1;(y2;y3)))).
    apply fst_unzip_prod. exact Ey123'.
    now rewrite -> unzip_zip.
    now rewrite <- Hy12y3'.
  }
  assert (y23' ≡ (y2;y3)) as Ey23'. {
    replace y23' with (snd (unzip y123')).
    transitivity (snd (unzip (y1;(y2;y3)))).
    apply snd_unzip_prod. exact Ey123'.
    now rewrite -> unzip_zip.
    now rewrite <- Hy12y3'.
  }

  specialize (Hpb23 ((ua;y1);ud)).
  replace (unzip ((ua;y1);ud)) with ((ua;y1),ud) in Hpb23 by auto.
  remember (unzip (b23 ((ua;y1);ud))) as y2y3' eqn:Hy2y3'.
  destruct y2y3' as [y2' y3'].
  unfold pb3, preprocess3 in Hpb23.
  replace (unzip (((ua; y1); y2'); ud)) with (((ua;y1);y2'),ud) in Hpb23 by auto.
  replace (unzip ((ua; y1); y2')) with ((ua;y1),y2') in Hpb23 by auto.
  replace (unzip (ua; y1)) with (ua,y1) in Hpb23 by auto.

  assert (y23' ≡ (y2'; y3')) as Ey23''. {
    assert (b23 ((ua;y1);ud) ≡ b23 ((ua; y1'); ud)) as Ha1d. {
      apply mixed_causal_behaviour_extensional. exact Hcb23.
      apply zip_prod_r. apply zip_prod_l. symmetry; exact Ey1'.
   }
   assert ((y2';y3') ≡ b23 ((ua; y1); ud)) as E23. {
     apply unzip_prod in Hy2y3'. exact Hy2y3'.
   }
   transitivity (b23 ((ua; y1); ud)).
   transitivity (b23 ((ua; y1'); ud)).
   apply Hb123.
   symmetry; exact Ha1d.
   symmetry; exact E23.
  }
  assert (y2' ≡ y2 /\ y3' ≡ y3) as Ey2y3'. {
    apply zip_prod.
    transitivity y23'. 
    symmetry; assumption.
    assumption.
  }
  destruct Ey2y3' as [Ey2' Ey3'].

  split. 2: split.
  - transitivity y1'. 
    symmetry; assumption.
    transitivity (b1 (ua; (ud; y23'))). apply Hb123.
    apply mixed_causal_behaviour_extensional. exact Hcb1.
    apply zip_prod_l. apply zip_prod_l. exact Ey23'.
  - transitivity y2'.
    symmetry; exact Ey2'.
    transitivity (b2 ((ua; y1); (ud; y3'))).
    exact (proj1 Hpb23).
    apply mixed_causal_behaviour_extensional. exact Hcb2.
    apply zip_prod_l. apply zip_prod_l. exact Ey3'.
  - transitivity y3'.
    symmetry; exact Ey3'.
    transitivity (b3 ((ua; (y1; y2')); ud)).
    exact (proj2 Hpb23).
    apply mixed_causal_behaviour_extensional. exact Hcb3.
    apply zip_prod_r. apply zip_prod_l. apply zip_prod_l.
    exact Ey2'.
Qed.

Theorem compose_behaviours_associative {UA UD Y1 Y2 Y3} :
  forall (b1 : Behaviour (UA*(UD*(Y2*Y3))) Y1)
         (b2 : Behaviour ((UA*Y1)*(UD*Y3)) Y2)
         (b3 : Behaviour ((UA*(Y1*Y2))*UD) Y3)
         (y1_default : Y1) (y2_default : Y2),
    let pb1 := (preprocess1 b1) in
    let pb3 := (preprocess3 b3) in
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
      forall u,
        (compose_behaviours (y1_default,y2_default) (compose_behaviours y1_default pb1 b2) b3) u
          ≡ (postprocess (compose_behaviours y1_default b1 (compose_behaviours y2_default b2 pb3))) u.
Proof.
  intros b1 b2 b3 y1d y2d pb1 pb3 Hmcb1 Hmcb2 Hmcb3.
  assert (mixed_causal pb1) as Hmcpb1. { 
    apply mixed_causal_preprocess1. exact Hmcb1. }
  assert (mixed_causal pb3) as Hmcpb3. { 
    apply mixed_causal_preprocess3. exact Hmcb3. }
  set (b12 := compose_behaviours y1d pb1 b2).
  set (b123 := compose_behaviours (y1d, y2d) b12 b3).
  set (b23' := compose_behaviours y2d b2 pb3).
  set (b123' := compose_behaviours y1d b1 b23').
  assert (is_composed_behaviour pb1 b2 b12) as Hb12. {
    apply mixed_causal_composed. exact Hmcpb1. exact Hmcb2. }
  assert (mixed_causal b12) as Hmcb12. {
    exact (behaviour_composition_mixed_causal pb1 b2 b12 Hmcpb1 Hmcb2 Hb12). }
  assert (is_composed_behaviour b12 b3 b123) as Hb123. {
    apply mixed_causal_composed. exact Hmcb12. exact Hmcb3. }
  assert (is_composed_behaviour b2 pb3 b23') as Hb23'. {
    apply mixed_causal_composed. exact Hmcb2. exact Hmcpb3. }
  assert (mixed_causal b23') as Hmcb23'. {
    exact (behaviour_composition_mixed_causal b2 pb3 b23' Hmcb2 Hmcpb3 Hb23'). }
  assert (is_composed_behaviour b1 b23' b123') as Hb123'. {
    apply mixed_causal_composed. exact Hmcb1. exact Hmcb23'. }
  assert (mixed_causal b123) as Hmcb123. { 
    exact (behaviour_composition_mixed_causal b12 b3 b123 Hmcb12 Hmcb3 Hb123). }
  assert (mixed_causal b123') as Hmcb123'. { 
    exact (behaviour_composition_mixed_causal b1 b23' b123' Hmcb1 Hmcb23' Hb123'). }
  assert (mixed_causal (postprocess b123')) as Hmcpb123'. { 
    apply mixed_causal_postprocess. exact Hmcb123'. }

  revert Hb12 Hb123 Hb23' Hb123'.
  intros Hb12 Hb123 Hb23' Hb123'.

  assert (is_three_composed_behaviours b1 b2 b3 b123) as Htcb123
    by now apply compose_behaviours_associative_left.

  assert (is_three_composed_behaviours b1 b2 b3 (postprocess b123')) as Htcb123'
    by now apply compose_behaviours_associative_right.
 
  apply (is_three_composed_behaviours_unique b1 b2 b3).
  all: assumption.
Qed.


Theorem behaviour_composition_associative {UA UD Y1 Y2 Y3 : Type} :
  forall (b1 : @Behaviour (UA * (UD*(Y2*Y3))) Y1)
         (b2 : @Behaviour ((UA*Y1) * (UD*Y3)) Y2)
         (b3 : @Behaviour ((UA*(Y1*Y2)) * UD) Y3)
         (b123 : @Behaviour (UA * UD) ((Y1*Y2)*Y3)),
    mixed_causal b1 -> mixed_causal b2 -> mixed_causal b3 ->
    (inhabited (UA * UD)) ->
    ( exists b12 : @Behaviour (UA * (UD*Y3)) (Y1*Y2),
        (is_composed_behaviour (preprocess1 b1) b2 b12) /\ (is_composed_behaviour b12 b3 b123) )
    <->
    ( exists b23 : @Behaviour ((UA*Y1) * UD) (Y2*Y3),
        (is_composed_behaviour b2 (preprocess3 b3) b23) /\ (is_composed_behaviour b1 b23 (unpostprocess b123)) )
.
Proof.
  intros b1 b2 b3 b123 Hcb1 Hcb2 Hcb3.
  intro Hu; destruct Hu as [u_default].
  set (y123_default := b123 (fun n => u_default) 0).
  destruct y123_default as [[y1_default y2_default] _].
  set (pb1 := preprocess1 b1). set (pb3 := preprocess3 b3).
  assert (mixed_causal pb1) as Hcpb1. { apply mixed_causal_preprocess1. exact Hcb1. }
  assert (mixed_causal pb3) as Hcpb3. { apply mixed_causal_preprocess3. exact Hcb3. }
  set (b23 := compose_behaviours y2_default b2 pb3).
  assert (is_composed_behaviour b2 pb3 b23) as Hb23. {
    apply mixed_causal_composed. exact Hcb2. exact Hcpb3. }
  assert (mixed_causal b23) as Hcb23. {
    apply (behaviour_composition_mixed_causal b2 pb3). exact Hcb2. exact Hcpb3. exact Hb23. }
  set (b1_23 := compose_behaviours y1_default b1 b23).
  assert (is_composed_behaviour b1 b23 b1_23) as Hb1_23. {
    apply mixed_causal_composed. exact Hcb1. exact Hcb23. }
  set (b12 := compose_behaviours y1_default pb1 b2).
  assert (is_composed_behaviour pb1 b2 b12) as Hb12. {
    apply mixed_causal_composed. exact Hcpb1. exact Hcb2. }
  assert (mixed_causal b12) as Hcb12. {
    apply (behaviour_composition_mixed_causal pb1 b2). exact Hcpb1. exact Hcb2. exact Hb12. }
  set (b12_3 := compose_behaviours (y1_default,y2_default) b12 b3).
  assert (is_composed_behaviour b12 b3 b12_3) as Hb12_3. {
    apply mixed_causal_composed. exact Hcb12. exact Hcb3. }
  assert (forall u, b12_3 u ≡ postprocess b1_23 u) as Hb123p. {
    apply compose_behaviours_associative.
    exact Hcb1. exact Hcb2. exact Hcb3.
  }

  assert (forall u, unpostprocess b12_3 u ≡ b1_23 u) as Hb123up.
  {
    intros u.
    transitivity (unpostprocess (postprocess b1_23) u).
    unfold unpostprocess, postprocess.
    unfold postprocess in Hb123p.
    apply associate_extensional.
    exact (Hb123p u).
    unfold unpostprocess, postprocess.
    now apply associate_unassociate_eqv.
  }

  split.
  - intros H.
    exists b23.
    split.
    -- apply mixed_causal_composed. exact Hcb2. exact Hcpb3.
    -- destruct H as [b12' [Hb12' Hb123']].
       assert (forall u n, b12 u n = b12' u n) as Hb12e. {
         exact (composed_mixed_causal_behaviour_unique pb1 b2 b12 b12' Hcpb1 Hcb2 Hb12 Hb12'). }
       assert (mixed_causal b12') as Hcb12'. {
         exact (mixed_causal_equivalent_behaviours b12 b12' Hb12e Hcb12). }
       assert (is_composed_behaviour b12 b3 b123) as Hb123. {
         apply (is_composed_behaviour_input_extensional b12' b12 b3 b3 b123).
         intros uy2 n. apply eq_sym. apply Hb12e.
         reflexivity. exact Hb123'.
       }
       assert (forall u n, b123 u n = b12_3 u n) as Hb123e. {
         exact (composed_mixed_causal_behaviour_unique b12 b3 b123 b12_3 Hcb12 Hcb3 Hb123 Hb12_3). }
       assert (is_composed_behaviour b1 b23 (unpostprocess b12_3)) as Hb12_3'. {
         apply (is_composed_behaviour_output_extensional b1 b23 b1_23 (unpostprocess b12_3) Hcb1 Hcb23).
         intros u n; apply eq_sym; exact (Hb123up u n). exact Hb1_23.
       }
       apply (is_composed_behaviour_output_extensional b1 b23 b1_23 (unpostprocess b123) Hcb1 Hcb23).
       intros u. rewrite <- Hb123up. 
       unfold unpostprocess. unfold zip,unzip.
         apply associate_extensional.
         symmetry. intro n. apply Hb123e.
       exact Hb1_23.
  - intros H.
    exists b12.
    split.
    -- apply mixed_causal_composed. exact Hcpb1. exact Hcb2.
    -- destruct H as [b23' [Hb23' Hb123']].
       assert (forall u n, b23 u n = b23' u n) as Hb23e. {
         exact (composed_mixed_causal_behaviour_unique b2 pb3 _ _ Hcb2 Hcpb3 Hb23 Hb23'). }
       assert (mixed_causal b23') as Hcb23'. {
         exact (mixed_causal_equivalent_behaviours b23 b23' Hb23e Hcb23). }
       assert (is_composed_behaviour b1 b23 (unpostprocess b123)) as Hb123. {
         apply (is_composed_behaviour_input_extensional b1 b1 b23' b23 (unpostprocess b123)).
         reflexivity.
         apply (composed_mixed_causal_behaviour_unique b2 pb3 b23' b23 Hcb2 Hcpb3 Hb23' Hb23).
         exact Hb123'.
       }
       assert (forall u n, unpostprocess b123 u n = b1_23 u n) as Hb123e'. {
         exact (composed_mixed_causal_behaviour_unique b1 b23 (unpostprocess b123) b1_23 Hcb1 Hcb23 Hb123 Hb1_23). }
       assert (forall u n, b12_3 u n = b123 u n) as Hb123e. {
         intros u n. rewrite -> Hb123p.
         unfold postprocess.
         unfold zip,unzip.
         transitivity ((unassociate (associate (b123 u))) n).
         apply unassociate_extensional.
         intro n'. rewrite <- Hb123e'.
         unfold unpostprocess.
         reflexivity.
         now apply unassociate_associate_eqv.
       }
       exact (is_composed_behaviour_output_extensional b12 b3 b12_3 b123 Hcb12 Hcb3 Hb123e Hb12_3).
Qed.

