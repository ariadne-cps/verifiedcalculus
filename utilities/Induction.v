(************************************************************************)
(* Copyright 2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 3                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl-3.0.txt>               *)
(************************************************************************)

Require Import Coq.Arith.Lt.

Module Induction.

Theorem strong_induction : forall (p:nat->Prop), (forall (n : nat), (forall (m:nat), m < n -> p m) -> p n) -> (forall (k:nat), p k).
Proof.
  assert ( forall (p:nat->Prop), 
    (forall (n : nat), ((forall (m:nat), m < n -> p m) -> p n)) -> 
                         (forall (k : nat), (forall (j:nat), j <= k -> p j)) ) as strong_induction'.
  {
    intros p. 
    intros SIH.
    induction k.
    - intro j. intro Hjle0. apply Nat.le_0_r in Hjle0 as Hjeq0. rewrite -> Hjeq0. 
      apply SIH. intro m. intro Hmlt0. unfold lt in Hmlt0. apply Nat.le_0_r in Hmlt0. discriminate Hmlt0.
    - intro j.
      assert (p (S k)) as pSk. {
        apply SIH. intros m. 
        assert (m<S k -> m<=k). { unfold lt. apply le_S_n. }
        auto.
      }
      assert (j <= S k -> j<=k \/ j=S k) as HleSkleeq.
      {
        intros HleS.
        apply Nat.lt_eq_cases in HleS.
        assert (j<(S k)->j<=k) as Hlt. { unfold lt. apply le_S_n. } 
        destruct HleS.
        --- left. apply Hlt. assumption.
        --- right. assumption.
      }
      assert (j<=k \/ j=S k -> p j) as HjleoreqS.
      {
        intros Hor. destruct Hor.
        --- apply IHk. assumption.
        --- rewrite -> H. assumption.
      }
      auto. 
  }
  intros p. 
  intros SIH.
  assert (forall k:nat, forall j:nat, j<=k -> p j).
    { apply strong_induction'. assumption. }
  intros k. assert (forall j:nat, j<=k -> p j) as Hjlek. { apply H. } apply Hjlek. auto. 
Qed.
    
End Induction.
