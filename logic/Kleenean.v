(******************************************************************************
 *  logic/Kleenean.v
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


Require Import PeanoNat.

Definition all_after {A:Type} s := forall n, s n <> @None A -> s (S n) = s n.


Inductive Kleenean := kleene (k:nat -> option bool) (p : all_after k).

Definition seq s := match s with kleene s _ => s end.

(*
Definition prp (s : Sierpinskian) : Prop := match s with sier seq prp => end.
*)

Module K.

Definition eqv_seq (s1 s2 : nat -> option bool) := exists n, forall m, n<=m -> s1 m = s2 m.

Definition eqv (k1 k2 : Kleenean) := eqv_seq (seq k1) (seq k2).

Definition definitely (k : Kleenean) : Prop :=
  exists n, seq k n = Some true.

Lemma definitely_eqv_iff : forall k1 k2, eqv k1 k2 -> (definitely k1 -> definitely k2).
Proof.
  intros k1 k2 He12 Hd1.
  destruct k1 as [s1 H1].
  unfold all_after, definitely, eqv, eqv_seq in *.
  destruct He12 as [ne12 He12].
  destruct Hd1 as [nd1 Hd1].
  destruct (Nat.le_ge_cases ne12 nd1) as [Hc|Hc].
  - exists nd1.
    specialize (He12 nd1).
    apply He12 in Hc as He.
    rewrite <- He.
    exact Hd1.
  - exists ne12.
    simpl in Hd1.
    assert (forall m, s1 (nd1+m) = s1 nd1) as Hnd1addm. {
      induction m.
      - rewrite -> Nat.add_0_r. reflexivity.
      - rewrite -> Nat.add_succ_r. rewrite -> H1. exact IHm.
        rewrite -> IHm. rewrite -> Hd1. discriminate.
    }
    assert (forall n, nd1 <= n -> s1 n = s1 nd1) as Hnd1m. {
      admit.
    }
Admitted.

Definition and_seq (s1 s2 : nat -> option bool) :=
  fun n => match s1 n, s2 n with
           | Some b1, Some b2 => Some (andb b1 b2) | _ , _ => None end.

Lemma all_after_and : forall k1 k2, all_after k1 -> all_after k2 -> all_after (and_seq k1 k2).
Proof.
  intros s1 s2 Hs1 Hs2. intros n Hs12.
  unfold all_after in *.
  unfold and_seq in *.
(*
  apply andb_prop in Hs12.
  rewrite -> Hs1, -> Hs2; tauto.
*)
  admit.
Admitted.


Definition and k1 k2 :=
  match k1 with | kleene s1 p1 => match k2 with | kleene s2 p2 =>
    kleene (and_seq s1 s2) (all_after_and s1 s2 p1 p2)
  end end.

