(******************************************************************************
 *  logic/Sierpinskian.v
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


Definition all_after s := forall n, s n = true -> s (S n) = true.


Inductive Sierpinskian := sier (s:nat -> bool) (p : all_after s).

Definition seq s := match s with sier s _ => s end.

(*
Definition prp (s : Sierpinskian) : Prop := match s with sier seq prp => end.
*)

Module S.

Definition eqv_seq (s1 s2 : nat -> bool) := (exists n1, s1 n1 = true) <-> (exists n2, s2 n2 = true).

Definition eqv (s1 s2 : Sierpinskian) := eqv_seq (seq s1) (seq s2).

Definition definitely (s : Sierpinskian) : Prop :=
  exists n, seq s n = true.

Lemma definitely_eqv_iff : forall s1 s2, eqv s1 s2 -> (definitely s1 -> definitely s2).
Proof.
  intros s1 s2 Heqv12.
  unfold definitely, eqv, eqv_seq in *.
  apply Heqv12.
Qed.

Definition and_seq (s1 s2 : nat -> bool) := fun n => andb (s1 n) (s2 n).

Lemma all_after_and : forall s1 s2, all_after s1 -> all_after s2 -> all_after (and_seq s1 s2).
Proof.
  intros s1 s2 Hs1 Hs2 n Hs12.
  unfold and_seq, all_after in *.
  apply andb_prop in Hs12.
  rewrite -> Hs1, -> Hs2; tauto.
Qed.


Definition and s1 s2 :=
  match s1 with | sier s1 p1 => match s2 with | sier s2 p2 =>
    sier (and_seq s1 s2) (all_after_and s1 s2 p1 p2)
  end end.

End S.

