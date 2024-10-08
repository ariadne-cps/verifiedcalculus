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

Require Import Words.

Section DependentChoice.

Axiom functional_dependent_choice :
  forall {A : Type} (R:A->A->Prop),
    (forall x, exists y, R x y) -> forall x0,
    (exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).



Definition is_chosable {X : Type} (f : list X -> X -> Prop) :=
  forall xl, exists x, f xl x.

Definition is_choice_sequence {X : Type} (f : list X -> X -> Prop) (xs : nat -> X) :=
  forall n, (f (proj_list n xs)) (xs n).

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
  assert (forall n, proj_list n xs = xls n) as Hp. {
    induction n.
    unfold proj_list, xs, xls. rewrite -> Hxlxs0. simpl. reflexivity.
    rewrite -> proj_list_succ.
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

Lemma proj_list_cons_seq : forall {X : Type} (a : X) (s : nat -> X) (m : nat),
  proj_list (S m) (cons_seq a s) = app (proj_list m s) (cons a nil).
Proof.
  intros X a s m.
  revert a s.
  induction m.
  - intros a s. auto.
  - intros a s.
    rewrite -> (proj_list_succ (S m)).
    rewrite -> IHm.
    rewrite -> (proj_list_succ m).
    rewrite -> List.app_comm_cons.
    unfold cons_seq.
    reflexivity.
Qed.

Lemma proj_list_app_seq : forall {X : Type} (l : list X) (s : nat -> X) (m : nat),
  proj_list (length l + m) (app_seq l s) = app (proj_list m s) l.
Proof.
  intros X.
  intros l.
  induction l.
  - intros s m. simpl. symmetry. apply List.app_nil_r.
  - assert (length (a :: l) = S (length l)) as Hlen. { auto. }
    intros s m.
    assert (app_seq (a::l) s = app_seq l (cons_seq a s)) as Happ. {
      auto. }
    rewrite -> Hlen, Happ.
    replace (S (length l) + m) with (S (length l + m)); [|apply PeanoNat.Nat.add_succ_l].
    rewrite -> proj_list_succ.
    rewrite -> IHl.
    rewrite -> app_seq_at.
    rewrite -> (List.app_comm_cons _ l).
    rewrite <- proj_list_succ.
    rewrite -> proj_list_cons_seq.
    rewrite <- List.app_assoc.
    simpl.
    reflexivity.
Qed.

Lemma proj_list_length_app_seq : forall {X : Type} (l : list X) (s : nat -> X),
  proj_list (length l) (app_seq l s) = l.
Proof.
  intros X l s.
  replace (length l) with (length l + 0).
  apply proj_list_app_seq.
  apply PeanoNat.Nat.add_0_r.
Qed.



Lemma is_choice_list_cons : forall {X} (f:list X -> X -> Prop) (a:X) (l:list X),
  is_choice_list f (cons a l) <-> f l a /\ is_choice_list f l.
Proof. intros X f a l; split; auto. Qed.

Lemma is_choice_prefix_of_sequence : forall {X} (f:list X -> X -> Prop) (xs : nat -> X),
  is_choice_sequence f xs -> forall n, is_choice_list f (proj_list n xs).
Proof.
  intros X f xs H.
  induction n.
  - simpl. trivial.
  - rewrite -> proj_list_succ.
    apply is_choice_list_cons.
    split.
    -- apply H.
    -- exact IHn.
Qed.

Lemma is_choice_prefix_of_list : forall {X} (f:list X -> X -> Prop) (xs : nat -> X),
  forall m n, is_choice_list f (proj_list (m+n) xs) -> is_choice_list f (proj_list m xs).
Proof.
  intros X f xs.
  intros m.
  induction n.
  - rewrite <- plus_n_O. trivial.
  - replace (m + S n) with (S (m+n)).
    rewrite -> proj_list_succ.
    intros H.
    apply IHn.
    apply (is_choice_list_cons f (xs(m+n)) (proj_list (m+n) xs)) in H.
    apply H.
    apply eq_sym.
    apply PeanoNat.Nat.add_succ_r.
Qed.


Proposition list_dependent_choice_from : forall {X:Type} (f : list X -> X -> Prop) (xl : list X),
  is_chosable f -> is_choice_list f xl -> (exists xs : nat -> X, (proj_list (length xl) xs = xl) /\ is_choice_sequence f xs).
Proof.
  intros X f xl Hf Hxl.

  set ( g:=fun xt => f (app xt xl) ).
  assert (exists xs, forall n, g (proj_list n xs) (xs n)) as Hg. {
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
    apply proj_list_length_app_seq.
  - intros n.
    assert (n < length xl \/ length xl <= n) as Hnl. {
      apply PeanoNat.Nat.lt_ge_cases. }
    destruct Hnl as [Hnltl|Hllen].
    -- assert (is_choice_list f (proj_list (length xl) xs)) as Hl. {
         unfold xs.
         rewrite -> proj_list_length_app_seq.
         exact Hxl.
       }
       assert (forall n, n<=length xl -> is_choice_list f (proj_list n xs)) as Hc. {
         intros m Hm.
         apply is_choice_prefix_of_list with (n:=(length xl - m)).
         replace (m + (length xl - m)) with (length xl).
         apply Hl.
         rewrite -> (Arith_base.le_plus_minus_r_stt _ _ Hm).
         reflexivity.
       }
       apply (Hc (S n)).
       apply Arith_base.lt_le_S_stt.
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
       rewrite -> proj_list_app_seq.
       rewrite -> app_seq_at.
       unfold g in Ht.
       apply Ht.
Qed.




Definition is_word_choice_sequence {X : Type} (f : forall n, Wrd n X -> X -> Prop) (xs : nat -> X) :=
  forall n, (f n (proj_word n xs)) (xs n).

Definition is_word_chosable {X : Type} (f : forall n, Wrd n X -> X -> Prop) :=
  forall n xw, exists x, f n xw x.

Definition is_choice_word {X : Type} (f : forall n, Wrd n X -> X -> Prop) {n : nat} (xw : Wrd n X) :=
  forall m (p : m < n), f m (restr m (Nat.lt_le_incl _ _ p) xw) (xw (ord m p)).

Proposition word_dependent_choice_from : forall {X:Type} (f : forall n, Wrd n X -> X -> Prop) {n : nat} (xw : Wrd n X),
  is_word_chosable f -> is_choice_word f xw -> (exists xs : nat -> X, (proj_word n xs = xw) /\ is_word_choice_sequence f xs).
Proof.
  intros X f n xw.
  assert (forall {n1 n2 : nat} (e : n1=n2) w1 x1 w2 x2, cast_wrd e w1 = w2 -> x1 = x2 -> f n1 w1 x1 -> f n2 w2 x2) as Hfeq. {
    intros n1 n2 e w1 w2 x1 x2 Hw Hx. rewrite <- Hw, <- Hx. unfold cast_wrd. destruct e. tauto. }
  assert (forall {n1 n2 : nat} (e : n1=n2) w1 w2 x, cast_wrd e w1 = w2 -> f n1 w1 x -> f n2 w2 x) as Hfeq'. {
    intros n1 n2 e w1 w2 x Hw. exact (Hfeq n1 n2 e w1 x w2 x Hw (eq_refl x)). }
  intros Hf Hxw.
  set (fl := fun xl => f (length xl) (list_to_word xl)).
  assert (is_chosable fl) as Hfl. {  
    unfold is_word_chosable in Hf.
    unfold is_chosable.
    intros xl'.
    set (xw' := list_to_word xl').
    specialize (Hf _ xw').
    destruct Hf as [x Hfx].
    exists x.
    unfold fl.
    unfold xw' in Hfx.
    exact Hfx.
  }
  set (xl := word_to_list xw).
  assert (is_choice_list fl xl) as Hfxl. {
    generalize Hxw.
    clear Hxw.
    intros Hxw.
    induction n.
    - unfold xl, word_to_list, is_choice_list. tauto.
    - unfold xl. 
      unfold fl.
      rewrite -> word_to_list_succ.
      apply is_choice_list_cons. split.
      -- unfold is_choice_word in Hxw.
         specialize (Hxw n (Nat.lt_succ_diag_r n)).
         set (xn := xw (ord n (Nat.lt_succ_diag_r n))) in *.
         set (n' := length (word_to_list (restr n (Nat.le_succ_diag_r n) xw))).
         set (xt := (list_to_word (word_to_list (restr n (Nat.le_succ_diag_r n) xw)))).
         assert (n = n') as Hneqn'. { unfold n'. rewrite -> word_to_list_length. reflexivity. }
         apply (Hfeq n n' Hneqn' (restr n (Nat.lt_le_incl n (S n) (Nat.lt_succ_diag_r n)) xw) xn); [|reflexivity|apply Hxw].
         unfold xt.
         rewrite -> word_to_list_to_word_id'.
         apply cast_wrd_eq.
         intros k p1 p2 kp1 kp2.
         rewrite -> (restr_eq _ (Nat.le_succ_diag_r n)).
         f_equal. apply ord_eq. reflexivity. 
      -- apply IHn. unfold is_choice_word in *.
         intros m p.
         specialize (Hxw m (Nat.lt_trans _ _ _ p (Nat.lt_succ_diag_r n))).
         apply (Hfeq _ _ (eq_refl m) (restr m (Nat.lt_le_incl m (S n) (Nat.lt_trans m n (S n) p (Nat.lt_succ_diag_r n))) xw) (xw (ord m (Nat.lt_trans m n (S n) p (Nat.lt_succ_diag_r n))))).
         --- rewrite -> restr_restr. 
             rewrite -> cast_wrd_restr. 
             apply restr_eq.
         --- rewrite -> restr_at.
             apply wrd_at_eq. 
         --- apply Hxw.
  }
  assert (exists xs : nat -> X, proj_list (length xl) xs = xl /\ is_choice_sequence fl xs) as Exs. {
    apply list_dependent_choice_from.
    - exact Hfl.
    - exact Hfxl.
  }
  destruct Exs as [xs [Hpxs Hfxs]].
  exists xs.
  split.
  - rewrite <- (word_to_list_to_word_id xw).
    apply eq_sym.
    rewrite <- (@proj_to_word_list X xs n n (length_proj_list xs n)).
    apply cast_list_to_wrd_eq.
    replace (word_to_list xw) with xl; [|unfold xl; reflexivity].
    replace (length xl) with n in Hpxs.
    -- symmetry. exact Hpxs.
    -- unfold xl. symmetry. apply word_to_list_length.
  - unfold is_word_choice_sequence.
    unfold is_choice_sequence in Hfxs.
    intros m. specialize (Hfxs m).
    unfold fl in Hfxs.
    apply (Hfeq (length (proj_list m xs)) m (length_proj_list xs m) (list_to_word (proj_list m xs)) (xs m)).
    -- apply proj_to_word_list'.
    -- reflexivity.
    -- exact Hfxs.
Qed.


End DependentChoice.
