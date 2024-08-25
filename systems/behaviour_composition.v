(******************************************************************************
 *  systems/behaviour_composition.v
 *
 *  Copyright 2023 Sacha L. Sindorf
 *                 Master's Thesis Artificial Intelligence
 *                 Maastricht University
 *
 *  Copyright 2023-24 Pieter Collins
 *
 *  Proof that behavior of composed system is composed
 *  behaviour of components.
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


(* ---------------------------------------------------------------- *)

Require Import Coq.Arith.PeanoNat.

Require Export causality.
Import causality.

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
  forall (u: Tr (UA*UD)),

     (* Separate inputs *)
     let (ua,ud) := unzip u in

     (* Separate outputs of composition *)
     let (y1,y2) := unzip (b12 u) in
       y1 ≡ b1 (ua;(ud;y2)) /\ y2 ≡ b2 ((ua;y1);ud)
.


Lemma is_composed_behaviour_output_extensional {UA UD Y1 Y2 : Type} :
  forall (b1 : Behaviour (UA*(UD*Y2)) Y1)
         (b2 : Behaviour ((UA*Y1)*UD) Y2)
         (b12 b12' : Behaviour (UA*UD) (Y1*Y2)),
    mixed_causal b1 -> mixed_causal b2 ->
      (forall u, b12 u ≡ b12' u) ->
        (is_composed_behaviour b1 b2 b12 ->
           is_composed_behaviour b1 b2 b12').
Proof.
  unfold is_composed_behaviour.
  intros b1 b2 b12 b12' Hcb1 Hcb2 Hu Hb12 u.
  specialize (Hb12 u).
  destruct Hb12 as [Hb1 Hb2].
  split.
  - intro n. rewrite <- Hu. rewrite -> Hb1. 
    apply (mixed_causal_behaviour_extensional b1 Hcb1).
    intro m. unfold zip. rewrite <- Hu. reflexivity.
  - intro n. rewrite <- Hu. rewrite -> Hb2. 
    apply (mixed_causal_behaviour_extensional b2 Hcb2).
    intro m. unfold zip. rewrite <- Hu. reflexivity.
Qed.

Lemma is_composed_behaviour_input_extensional {UA UD Y1 Y2 : Type} :
  forall (b1 b1' : Behaviour (UA*(UD*Y2)) Y1)
         (b2 b2' : Behaviour ((UA*Y1)*UD) Y2)
         (b12 : Behaviour (UA*UD) (Y1*Y2)),
      (forall (uy2:nat->UA*(UD*Y2)), b1 uy2 ≡ b1' uy2) ->
        (forall (uy1:nat->(UA*Y1)*UD), b2 uy1 ≡ b2' uy1) ->
          (is_composed_behaviour b1 b2 b12 ->
            is_composed_behaviour b1' b2' b12).
Proof.
  unfold is_composed_behaviour.
  intros b1 b1' b2 b2' b12 Hb1e Hb2e Hb12 u.
  specialize (Hb12 u).
  destruct Hb12 as [Hb1 Hb2].
  split.
  - intro n. rewrite -> Hb1. apply Hb1e.
  - intro n. rewrite -> Hb2. apply Hb2e.
Qed.



(* The composition of two mixed causal behaviours should be unique. *)
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
                  b12 u ≡ b12' u.
Proof.
  intros b1 b2 b12 b12' Hmcb1 Hmcb2 Hcompb12 Hcompb12'.
  intro u.

  unfold is_composed_behaviour in Hcompb12, Hcompb12'.
  specialize (Hcompb12 u). specialize (Hcompb12' u).
  unfold unzip in Hcompb12, Hcompb12'.

  remember (fun k => fst (u k)) as ua eqn:Eua.
  remember (fun k => snd (u k)) as ud eqn:Eud.
  remember (fun k => fst (b12 u k)) as y1 eqn:Ey1.
  remember (fun k => snd (b12 u k)) as y2 eqn:Ey2.
  remember (fun k => fst (b12' u k)) as y1' eqn:Ey1'.
  remember (fun k => snd (b12' u k)) as y2' eqn:Ey2'.
  
  destruct Hcompb12 as [Hy1 Hy2].
  destruct Hcompb12' as [Hy1' Hy2'].

  (* 
     In 3 phases:
     - Use causality of b1 b2 to get dependency between y1, y2.
     - Set-up circlular dependency on y2 (or y1), 
         and use induction to unroll y2 = y2'.
     - Push equivalent onto y1 and then to b12.
  *)

  (* Step 1 b1 *)
  assert (forall n, y2 |< n |≡ y2' -> y1 |≤ n |≡ y1' ) as Hb1. { 
    intros n Hy2ltn.
    intros m Hmlen.
    rewrite -> Hy1'.
    rewrite -> Hy1. 
    revert m Hmlen.
    apply Hmcb1.
    - intros m Hmlen. simpl. exact (eq_refl (ua m)).
    - intros m Hmltn. unfold zip. simpl.
      apply injective_projections.
      -- simpl. exact (eq_refl (ud m)).
      -- simpl. exact (Hy2ltn m Hmltn).
  }

  (* Step 2 b2 *)
  assert (forall n, y1 |≤ n |≡ y1' -> y2 |≤ n |≡ y2' ) as Hb2. { 
    intros n Hy1len.
    intros m Hmlen.
    rewrite -> Hy2. 
    rewrite -> Hy2'.
    revert m Hmlen.
    apply Hmcb2.
    - intros m Hmlen. unfold zip. simpl.
      apply injective_projections.
      -- simpl. exact (eq_refl (ua m)).
      -- simpl. exact (Hy1len m Hmlen).
    - intros m Hmltn. simpl. exact (eq_refl (ud m)).
  }

  (* Step 3 y2 extension *)
  assert (forall n, y2 |< n |≡ y2' -> y2 |≤ n |≡ y2' ) as H2''. {
    intros n H.
    apply Hb2.
    apply Hb1.
    exact H.
  }

  (* Step 4 induction *)
  assert (forall n, y2 |≤ n |≡ y2' ) as H2'. {
    induction n.
    - apply H2''. intros n Hnlt0.
      apply (Nat.nlt_0_r n) in Hnlt0.
      contradiction.
    - apply H2''.
      intros m HmltSn.
      assert (m <= n) as Hmlen
        by exact (proj1 (Nat.lt_succ_r m n) HmltSn).
      exact (IHn m Hmlen).
  }

  (* Step 5 Unroll y2  *)
  assert (y2 ≡ y2') as H2. {
    intro n. apply (H2' n). exact (Nat.le_refl n).
  }

  (* Step 6 Unroll y1  *)
  assert (y1 ≡ y1') as H1. {
    intro n. apply (Hb1 n).
    - intros m Hmltn. exact (H2 m).
    - exact (Nat.le_refl n).
  }

  (* Step 7 Unzip outputs  *)
  intros n.
  apply injective_projections.
   - specialize (H1 n).
    rewrite -> Ey1 in H1.
    rewrite -> Ey1' in H1.
    exact H1.
   - specialize (H2 n).
    rewrite -> Ey2 in H2.
    rewrite -> Ey2' in H2.
    exact H2.
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
  remember (fun k => fst (u k)) as ua eqn:Eua.
  remember (fun k => snd (u k)) as ud eqn:Eud.
  remember (fun k => fst (u' k)) as ua' eqn:Eua'.
  remember (fun k => snd (u' k)) as ud' eqn:Eud'.
  remember (fun k => fst (b12 u k)) as y1 eqn:Ey1.
  remember (fun k => snd (b12 u k)) as y2 eqn:Ey2.
  remember (fun k => fst (b12 u' k)) as y1' eqn:Ey1'.
  remember (fun k => snd (b12 u' k)) as y2' eqn:Ey2'.
  specialize (Hcb1 (ua;(ud;y2)) (ua';(ud';y2'))). simpl in Hcb1.
  specialize (Hcb2 ((ua;y1);ud) ((ua';y1');ud')). simpl in Hcb2.
  set (Hb1b2 := Hb12 u). unfold unzip in Hb1b2. simpl in Hb1b2.
  rewrite <- Eua, <- Eud, <- Ey1, <- Ey2 in Hb1b2.
  set (Hb1b2' := Hb12 u'). unfold unzip in Hb1b2'. simpl in Hb1b2'.
  rewrite <- Eua', <- Eud', <- Ey1', <- Ey2' in Hb1b2'.
  destruct Hb1b2 as [Hb1 Hb2].
  destruct Hb1b2' as [Hb1' Hb2'].
  assert (unzip u = (ua,ud)) as Hu. {
    symmetry. unfold unzip. f_equal. exact Eua. exact Eud. }
  assert (unzip u' = (ua',ud')) as Hu'. {
    symmetry. unfold unzip. f_equal. exact Eua'. exact Eud'. }
  rewrite -> Hu, -> Hu'.
  induction n.
  - intros Hua0 _. intros m Hm.
    assert (m=0) as Hm0 by (apply Nat.le_0_r; exact Hm).
    rewrite -> Hm0.
    assert (y1 0 = y1' 0) as Hy10. {
      rewrite -> Hb1. 
      rewrite -> Hb1'.
      apply Hcb1 with (n:=0).
      - exact Hua0.
      - intros k Hklt0. apply Nat.nlt_0_r in Hklt0. contradiction.
      - exact (Nat.le_refl 0).
    }
    assert (y2 0 = y2' 0) as Hy20. {
      rewrite -> Hb2. 
      rewrite -> Hb2'.
      apply Hcb2 with (n:=0).
      - intros k Hkle0.
        assert (k=0) as Hkeq0
          by exact (proj1 (Nat.le_0_r k) Hkle0).
        rewrite -> Hkeq0. unfold zip. apply injective_projections.
        -- simpl. exact (Hua0 0 (Nat.le_refl 0)).
        -- simpl. exact Hy10.
      - intros k Hklt0. apply Nat.nlt_0_r in Hklt0. contradiction.
      - exact (Nat.le_refl 0).
    }
    apply injective_projections.
    -- rewrite -> Ey1, -> Ey1' in Hy10. exact Hy10.
    -- rewrite -> Ey2, -> Ey2' in Hy20. exact Hy20.
  - intros HuaSn HudSn.
    assert (ua |≤ n |≡ ua') as Huan. {
      intros m Hmlen. apply HuaSn. 
      apply Nat.le_le_succ_r. exact Hmlen.
    }
    assert (ud |< n |≡ ud') as Hudn. {
      intros m Hmltn. apply HudSn. 
      apply Nat.lt_lt_succ_r. exact Hmltn.
    }
    specialize (IHn Huan Hudn).
    assert (y1 |≤ n |≡ y1') as Hy1. {
      rewrite -> Ey1, Ey1'. intros m Hmlen. 
      f_equal. exact (IHn m Hmlen). }
    assert (y2 |≤ n |≡ y2') as Hy2. {
      rewrite -> Ey2, Ey2'. intros m Hmlen. 
      f_equal. exact (IHn m Hmlen). }
    assert (y1 (S n) = y1' (S n)) as Hbu1. {
      rewrite -> Hb1. 
      rewrite -> Hb1'.
      apply Hcb1 with (n:=(S n)).
      - exact HuaSn.
      - intros m HmltSn.
        assert (m ≤ n) as Hmlen. { 
          apply Nat.lt_succ_r. exact HmltSn. }
        unfold zip.
        apply injective_projections.
        -- simpl. exact (HudSn m HmltSn).
        -- simpl. exact (Hy2 m Hmlen).
      - exact (Nat.le_refl (S n)).
    }
    assert (y2 (S n) = y2' (S n)) as Hbu2. {
      rewrite -> Hb2. 
      rewrite -> Hb2'.
      apply Hcb2 with (n:=(S n)).
      - intros m HmleSn.
        unfold zip. apply injective_projections.
        -- simpl. exact (HuaSn m HmleSn).
        -- apply Nat.le_succ_r in HmleSn.
           destruct HmleSn as [Hmlen|HmeqSn].
           --- simpl. exact (Hy1 m Hmlen).
           --- simpl. rewrite -> HmeqSn. exact Hbu1.
      - exact HudSn.
      - exact (Nat.le_refl (S n)).
    }
    assert (b12 u (S n) = b12 u' (S n)) as Hy12Sn. {
      apply injective_projections.
      - rewrite -> Ey1, -> Ey1' in Hbu1. exact Hbu1. 
      - rewrite -> Ey2, -> Ey2' in Hbu2. exact Hbu2. 
    }
    intros m HmleSn.
    apply Nat.le_succ_r in HmleSn.
    destruct HmleSn as [Hmlen|HmeqSn].
    -- exact (IHn m Hmlen).
    -- rewrite -> HmeqSn. exact Hy12Sn.
Qed.
