(******************************************************************************
 *  numbers/ConstructiveRealComparison.v
 *
 *  Copyright 2025-26 Pieter Collins
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

(* This file contains various properties of R that are not in the standard library. *)

Require Import Logic.Kleenean.
(*
Print Kleeneans.
*)

From Stdlib Require Import Reals.Abstract.ConstructiveReals.

(*
Fail Print Reals.Abstract.
Print Reals.Abstract.ConstructiveReals.
Print ConstructiveReals.
Check ConstructiveReals.
Print ConstructiveReals.CRcarrier.
*)

Notation CRCarrier := ConstructiveReals.CRcarrier.
(*
Print CRcarrier.
Check ConstructiveReals.
Check CRcarrier.
*)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
(*
Print Reals.Cauchy.ConstructiveCauchyReals.
Print ConstructiveCauchyReals.
*)
From Stdlib Require Import QArith_base.
From Stdlib Require Import Lra.



(*
Print CReal.
*)

Example x := inject_Q 3.
Example tq : Q := 3.

Lemma eqv_inject_Q : forall (q1 q2 : Q),
  (q1 == q2) -> (inject_Q q1 == inject_Q q2)%CReal.
Proof.
  intros q1 q2 Hq.
  pose proof (inject_Q_morph_Proper) as Hinj.
  now apply Hinj.
Qed.

Lemma neq_inject_Q : forall (q1 q2 : Q),
  ~ (q1 == q2)%Q -> (inject_Q q1 <> inject_Q q2)%CReal.
Proof.
  intros q1 q2 Hnq Hr.
  pose proof (QOrderedType.QOrder.TO.lt_total q1 q2) as Hqlt.
  destruct Hqlt as [Hqlt|[Hqeq|Hqlt]].
  1,3: apply inject_Q_lt in Hqlt; rewrite <- Hr in Hqlt; now apply CRealLt_irrefl in Hqlt.
  1: { contradiction. }
Qed.

Lemma appart_inject_Q : forall (q1 q2 : Q),
  ~ (q1 == q2)%Q -> (inject_Q q1 # inject_Q q2)%CReal.
Proof.
  intros q1 q2 Hq.
  pose proof (Q_dec q1 q2) as Hqlt.
  destruct Hqlt as [Hqlgt|Hqeq].
  destruct Hqlgt as [Hqlt|Hqgt].
  3: { contradiction. }
  2: { right. apply (inject_Q_lt). assumption. }
  1: { left. apply (inject_Q_lt). assumption. }
Qed.

Example zero := (inject_Q 0 : CReal).
Example one := (1 : CReal).
Example two := CReal_plus one one.
Example three' := CReal_plus two one.
Example three := (inject_Q 3 : CReal).

Lemma three_neq_zero : three <> zero.
Proof.
  apply neq_inject_Q.
  unfold Qeq. simpl. discriminate.
Qed.

Lemma three_appart_zero : CReal_appart three zero.
Proof.
  apply appart_inject_Q.
  unfold Qeq. simpl. discriminate.
Qed.


Example third : CReal := CReal_inv three three_appart_zero .

Example three_thirds := CReal_mult three third.

Check @Kleenean.indeterminate nat Topologic.nat_Lattice.

Definition PKindeterminate := @Kleenean.indeterminate nat Topologic.nat_Lattice.
Definition Kindeterminate : Kleenean.Kleenean := PKindeterminate.


#[global]
Instance CRealLt_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CRealLt.
Proof.
  intros x y Hxeqy x0 y0 Hx0eqy0.
  destruct Hxeqy as [Hylex Hxley].
  destruct Hx0eqy0 as [Hy0lex0 Hx0ley0].
  split.
  - intro Hxltx0; destruct (CRealLt_dec x x0 y).
    + assumption.
    + contradiction.
    + destruct (CRealLt_dec y x0 y0).
      * assumption.
      * assumption.
      * contradiction.
  - intro Hylty0; destruct (CRealLt_dec y y0 x).
    + assumption.
    + contradiction.
    + destruct (CRealLt_dec x y0 x0).
      * assumption.
      * assumption.
      * contradiction.
Qed.

(*
Lemma CRealLtForget : forall x y : CReal,
    CRealLt x y -> CRealLtProp x y.
Proof.
  intros. destruct H. exists x0. exact q.
Qed.
*)

Notation Tribool := Kleenean.Tribools.Tribool.
Notation Kleenean := Kleenean.Kleenean.

Notation indt := Kleenean.Tribools.indt.

Fixpoint make_monotone (s : nat -> Tribool) (n : nat) : Tribool :=
  match n with 
    | O => s O 
    | S m => match make_monotone s m with  
             | indt => s n
             | _ => make_monotone s m
             end
end.

Lemma make_monotone_succ : forall s n, 
  make_monotone s n <> indt -> make_monotone s (S n) = make_monotone s n.
Proof. 
  intros. 
  remember (make_monotone s n) as msn.
  destruct msn.
  - contradiction.
  - simpl. rewrite <- Heqmsn. reflexivity.
Qed.

Lemma make_monotone_succ' : forall s n, 
  make_monotone s n = indt \/ make_monotone s (S n) = make_monotone s n.
Proof. 
  intros. 
  remember (make_monotone s n) as msn.
  destruct msn.
  - left. reflexivity.
  - right. simpl. rewrite <- Heqmsn. reflexivity.
Qed.


Lemma make_monotone_correct : forall s : nat -> Tribool,
  @Kleenean.is_monotone nat (Topologic.nat_Lattice) (make_monotone s).
Proof.
  intros s. 
  unfold Kleenean.is_monotone.
  unfold Topologic.BasicTopologic.is_monotone.
  unfold Topologic.BasicTopologic.refines.
  simpl.
  assert (forall m k, Kleenean.Tribools.refines (make_monotone s (m+k)) (make_monotone s m)) as Hplus. {
    intros m. induction k.
    - replace (m+0)%nat with m.
      apply Kleenean.Tribools.refines_refl.
      now rewrite -> PeanoNat.Nat.add_0_r.
    - apply (Kleenean.Tribools.refines_trans _ (make_monotone s (m+k)) _).
      2: exact IHk.
      replace (m+S k)%nat with (S (m+k))%nat.
      2: now rewrite <- PeanoNat.Nat.add_succ_r.
      
      remember (make_monotone s (m+k)) as msn.
      destruct msn.
      -- unfold Kleenean.Tribools.refines.
         destruct (make_monotone s (Kleenean.succ (m + k))). tauto. destruct b; tauto.
      -- rewrite -> make_monotone_succ. rewrite <- Heqmsn.
         simpl. destruct b; tauto.
         rewrite <- Heqmsn. discriminate.
  }
  intros m n Hmn.
  set (k := (n - m)%nat).
  assert ((n = m + k)%nat) as H.
  pose proof (PeanoNat.Nat.sub_add m n Hmn).
  unfold k.
  now rewrite -> PeanoNat.Nat.add_comm.
  rewrite -> H.
  apply Hplus.
Qed.


Definition make_kleenean (s : nat -> Tribool) : Kleenean :=
  Kleenean.mkPreKleenean (make_monotone s) (make_monotone_correct s).

Definition CRls (r1 r2 : CReal) : Kleenean.Kleenean :=
  let tbs :=
    fun n : nat =>
      let z := (- Z.of_nat n)%Z in
      let Hltge := Qlt_le_dec (seq r1 z + 2 ^ z) (seq r2 z - 2 ^ z) in
      let Hgtle := Qlt_le_dec (seq r2 z + 2 ^ z) (seq r1 z - 2 ^ z) in
        match Hltge with
        | left _ => Kleenean.Tribools.tru
        | right _ =>
              match Hgtle with 
              | left _ => Kleenean.Tribools.fls
              | right _ => Kleenean.Tribools.indt
              end
        end in
          make_kleenean tbs  
.

(*
  let tbs :=
    fun n : nat =>
      let z := (- Z.of_nat n)%Z in
      let Hltge := Qlt_le_dec (seq r1 z + 2 ^ z) (seq r2 z - 2 ^ z) in
        match Hltge with
        | left _ => Kleenean.Tribools.tru
        | right _ =>
            let Hgtle := Qlt_le_dec (seq r2 z + 2 ^ z) (seq r1 z - 2 ^ z) in
              match Hgtle with 
              | left _ => Kleenean.Tribools.fls
              | right _ => Kleenean.Tribools.indt
              end
        end in
          make_kleenean tbs  
*)

(*
Proof.
  assert (nat -> Kleeneans.Tribools.Tribool) as tbs. {
    intro n.
    set (z := (- (Z.of_nat n))%Z).
    pose proof ( Qlt_le_dec ((seq r1 z) + 2^z) ((seq r2 z) - 2^z) ) as Hltge.
    destruct Hltge as [Hlt|Hge].
    - exact Kleeneans.Tribools.tru.
    - pose proof ( Qlt_le_dec ((seq r2 z) + 2^z) ((seq r1 z) - 2^z) ) as Hgtle.
      destruct Hgtle as [Hgt|Hle].
      -- exact Kleeneans.Tribools.fls.
      -- exact Kleeneans.Tribools.indt.
  }
  exact (make_kleenean tbs).
Qed.
*)
Print CRls.


