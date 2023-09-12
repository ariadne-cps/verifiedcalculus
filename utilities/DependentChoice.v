(******************************************************************************
 *  utilities/DependentChoice.v
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


Require Import List.
Require Import Arith_base.

Section DependentChoice.

Axiom functional_dependent_choice :
  forall {A : Type} (R:A->A->Prop),
    (forall x, exists y, R x y) -> forall x0,
    (exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).


Fixpoint proj {X:Type} (n : nat) (xs : nat -> X) : list X :=
  match n with
    | O => nil
    | S n' => cons (xs n') (proj n' xs)
  end.

Lemma proj_zero : forall {X:Type} (xs:nat->X), proj O xs = nil.
Proof. intros X xs. simpl. reflexivity. Qed.
Lemma proj_succ : forall {X:Type} (n:nat) (xs:nat->X), proj (S n) xs = cons (xs n) (proj n xs).
Proof. intros X n xs. simpl. reflexivity. Qed.
Lemma length_proj : forall {X : Type} (xs : nat -> X) (n : nat), length (proj n xs) = n.
Proof.
  intros X xs. induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.



Definition is_chosable {X : Type} (f : list X -> X -> Prop) :=
  forall xl, exists x, f xl x.

Definition is_choice_sequence {X : Type} (f : list X -> X -> Prop) (xs : nat -> X) :=
  forall n, (f (proj n xs)) (xs n).

Fixpoint is_choice_list {X : Type} (f : list X -> X -> Prop) (xl : list X) :=
  match xl with
  | nil => True
  | cons hd tl => f tl hd /\ is_choice_list f tl
  end.



Proposition list_dependent_choice : forall {X:Type} (f : list X -> X -> Prop),
  (is_chosable f) -> (exists xs : nat -> X, is_choice_sequence f xs).
Proof.
  intros X f Hf.
  set (R := fun xlx xlx' => f (fst xlx') (snd xlx') /\ (fst xlx') = cons (snd xlx) (fst xlx)).
  assert (forall xlx, exists xlx', R xlx xlx') as HR. {
    unfold R.
    intros xlx.
    destruct xlx as [xl x].
    set (xl' := cons x xl).
    specialize (Hf xl').
    destruct Hf as [x' Hfx'].
    exists (xl',x').
    simpl.
    split.
    - exact Hfx'.
    - reflexivity.
  }
  assert (exists x0, f nil x0) as Hfx0. { apply Hf. }
  destruct Hfx0 as [x0 Hx0].
  set (xlx0 := (nil : list X,x0)).
  assert (exists xlxs : nat -> (list X*X), xlxs 0 = xlx0 /\ forall n, R (xlxs n) (xlxs (S n))) as Hxlxs. {
    exact (functional_dependent_choice R HR xlx0). }
  destruct Hxlxs as [xlxs [Hxlxs0 Hxlxs]].
  set (xls := fun n => fst (xlxs n)).
  set (xs := fun n => snd (xlxs n)).
  exists xs.
  assert (forall m, fst (xlxs m) = xls m) as Hxls. {
    intro m. unfold xls. reflexivity. }
  assert (forall m, snd (xlxs m) = xs m) as Hxs. {
    intro m. unfold xs. reflexivity. }
  assert (forall n, proj n xs = xls n) as Hp. {
    induction n.
    unfold proj, xs, xls. rewrite -> Hxlxs0. simpl. reflexivity.
    rewrite -> proj_succ.
    rewrite -> IHn.
    rewrite <- Hxls, <- Hxls, <- Hxs.
    specialize (Hxlxs n).
    unfold R in Hxlxs.
    destruct Hxlxs as [_ Hxlxs].
    apply eq_sym.
    exact Hxlxs.
  }
  intro n.
  rewrite -> Hp.
  unfold R in Hxlxs.
  destruct n.
  - rewrite <- Hxls, <- Hxs, -> Hxlxs0. unfold xlx0. simpl. exact Hx0.
  - specialize (Hxlxs n).
    rewrite -> Hxls, -> Hxs in Hxlxs.
    apply Hxlxs.
Qed.


Lemma length_cons : forall {X : Type} (a : X) (l : list X),
  length (cons a l) = S (length l).
Proof. intros X a l. auto. Qed.

Definition cons_seq {X : Type} (a : X) (s : nat -> X) : nat -> X :=
  fun n => match n with | O => a | S m => s m end.

Fixpoint app_seq {X : Type} (l : list X) (s : nat -> X) : nat -> X :=
  match l with
  | nil => s
  | cons hd tl => app_seq tl (cons_seq hd s)
  end.

Lemma app_seq_at : forall {X : Type} (l : list X) (s : nat -> X) (m : nat),
  (app_seq l s) (length l + m) = s m.
Proof.
  intros X l.
  induction l.
  - intros s m. auto.
  - intros s m.
    replace (app_seq (a::l) s) with (app_seq l (cons_seq a s)).
    replace (length (a::l)+m) with (length l + S m).
    -- rewrite -> (IHl (cons_seq a s)).
       unfold cons_seq.
       reflexivity.
    -- rewrite -> length_cons.
       apply eq_sym.
       rewrite -> plus_Sn_m, <- plus_n_Sm.
       reflexivity.
    -- auto.
Qed.

Lemma proj_cons_seq : forall {X : Type} (a : X) (s : nat -> X) (m : nat),
  proj (S m) (cons_seq a s) = app (proj m s) (cons a nil).
Proof.
  intros X a s m.
  revert a s.
  induction m.
  - intros a s. auto.
  - intros a s.
    rewrite -> (proj_succ (S m)).
    rewrite -> IHm.
    rewrite -> (proj_succ m).
    rewrite -> List.app_comm_cons.
    unfold cons_seq.
    reflexivity.
Qed.

Lemma proj_app_seq : forall {X : Type} (l : list X) (s : nat -> X) (m : nat),
  proj (length l + m) (app_seq l s) = app (proj m s) l.
Proof.
  intros X.
  intros l.
  induction l.
  - intros s m. simpl. apply List.app_nil_end.
  - assert (length (a :: l) = S (length l)) as Hlen. { auto. }
    intros s m.
    assert (app_seq (a::l) s = app_seq l (cons_seq a s)) as Happ. {
      auto. }
    rewrite -> Hlen, Happ.
    replace (S (length l) + m) with (S (length l + m)); [|apply PeanoNat.Nat.add_succ_l].
    rewrite -> proj_succ.
    rewrite -> IHl.
    rewrite -> app_seq_at.
    rewrite -> (List.app_comm_cons _ l).
    rewrite <- proj_succ.
    rewrite -> proj_cons_seq.
    rewrite -> List.app_assoc_reverse.
    simpl.
    reflexivity.
Qed.

Lemma proj_length_app_seq : forall {X : Type} (l : list X) (s : nat -> X),
  proj (length l) (app_seq l s) = l.
Proof.
  intros X l s.
  replace (length l) with (length l + 0).
  apply proj_app_seq.
  apply PeanoNat.Nat.add_0_r.
Qed.



Lemma is_choice_list_cons : forall {X} (f:list X -> X -> Prop) (a:X) (l:list X),
  is_choice_list f (cons a l) <-> f l a /\ is_choice_list f l.
Proof. intros X f a l; split; auto. Qed.

Lemma is_choice_prefix_of_sequence : forall {X} (f:list X -> X -> Prop) (xs : nat -> X),
  is_choice_sequence f xs -> forall n, is_choice_list f (proj n xs).
Proof.
  intros X f xs H.
  induction n.
  - simpl. trivial.
  - rewrite -> proj_succ.
    apply is_choice_list_cons.
    split.
    -- apply H.
    -- exact IHn.
Qed.

Lemma is_choice_prefix_of_list : forall {X} (f:list X -> X -> Prop) (xs : nat -> X),
  forall m n, is_choice_list f (proj (m+n) xs) -> is_choice_list f (proj m xs).
Proof.
  intros X f xs.
  intros m.
  induction n.
  - rewrite <- plus_n_O. trivial.
  - replace (m + S n) with (S (m+n)).
    rewrite -> proj_succ.
    intros H.
    apply IHn.
    apply (is_choice_list_cons f (xs(m+n)) (proj (m+n) xs)) in H.
    apply H.
    apply eq_sym.
    apply PeanoNat.Nat.add_succ_r.
Qed.


Proposition list_dependent_choice_from : forall {X:Type} (f : list X -> X -> Prop) (xl : list X),
  is_chosable f -> is_choice_list f xl -> (exists xs : nat -> X, (proj (length xl) xs = xl) /\ is_choice_sequence f xs).
Proof.
  intros X f xl Hf Hxl.

  set ( g:=fun xt => f (app xt xl) ).
  assert (exists xs, forall n, g (proj n xs) (xs n)) as Hg. {
    apply list_dependent_choice.
    unfold g.
    intros xt.
    apply Hf.
  }
  destruct Hg as [xt Ht].
  set ( xs := app_seq xl xt ).
  exists xs.
  split.
  - unfold xs.
    apply proj_length_app_seq.
  - intros n.
    assert (n < length xl \/ length xl <= n) as Hnl. {
      apply PeanoNat.Nat.lt_ge_cases. }
    destruct Hnl as [Hnltl|Hllen].
    -- assert (is_choice_list f (proj (length xl) xs)) as Hl. {
         unfold xs.
         rewrite -> proj_length_app_seq.
         exact Hxl.
       }
       assert (forall n, n<=length xl -> is_choice_list f (proj n xs)) as Hc. {
         intros m Hm.
         apply is_choice_prefix_of_list with (n:=(length xl - m)).
         replace (m + (length xl - m)) with (length xl).
         apply Hl.
         rewrite -> (Arith_prebase.le_plus_minus_r_stt _ _ Hm).
         reflexivity.
       }
       apply (Hc (S n)).
       apply Arith_prebase.lt_le_S_stt.
       exact Hnltl.
    -- unfold xs.
       assert (exists m:nat, n=length xl + m) as Hm. {
         apply PeanoNat.Nat.le_exists_sub in Hllen.
         destruct Hllen as [m Hm].
         exists m.
         rewrite -> PeanoNat.Nat.add_comm.
         apply Hm.
       }
       destruct Hm as [m Hm].
       rewrite -> Hm.
       rewrite -> proj_app_seq.
       rewrite -> app_seq_at.
       unfold g in Ht.
       apply Ht.
Qed.


End DependentChoice.
