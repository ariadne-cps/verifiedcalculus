(* Require Import Coq.Classes.RelationClasses. *)
From Stdlib Require Import Logic.ConstructiveEpsilon.
From Stdlib Require Import PeanoNat.


Definition mkEqualityPartialOrder {X : Type} {le : X -> X -> Prop}
  (le_PreOrder : RelationClasses.PreOrder le)
  (le_antisymm : forall x1 x2, le x1 x2 -> le x2 x1 -> x1 = x2)
    : RelationClasses.PartialOrder (@eq X) le.
Proof.
  intros n1 n2. split.
  - intros H. rewrite <- H. split; now apply le_PreOrder.
  - intros [H1 H2]. now apply le_antisymm.
Qed.


Class Lattice (X : Type) := {
  bot : X;
  le : X -> X -> Prop;
  le_refl : forall x, le x x;
  le_antisymm : forall x1 x2, le x1 x2 -> le x2 x1 -> x1 = x2;
  le_trans : forall x1 x2 x3, le x1 x2 -> le x2 x3 -> le x1 x3;
  le_pre_order : @RelationClasses.PreOrder X le;
  le_partial_order : @RelationClasses.PartialOrder X (@eq X) (@RelationClasses.eq_equivalence X) le le_pre_order;
  max : X -> X -> X;
  le_max_l : forall x1 x2, le x1 (max x1 x2);
  le_max_r : forall x1 x2, le x2 (max x1 x2);
}.

Global Instance Lattice_Reflexive {X : Type} `(Lattice X) : RelationClasses.Reflexive le := le_refl.
Global Instance Lattice_Transitive {X : Type} `(Lattice X) : RelationClasses.Transitive le := le_trans.

#[export] 
Instance nat_Lattice : Lattice nat := {
  bot := 0;
  le := Peano.le;
  le_refl := Nat.le_refl;
  le_antisymm := Nat.le_antisymm;
  le_trans := Nat.le_trans;
  le_pre_order := Nat.le_preorder;
  le_partial_order := Nat.le_partialorder;
  max := Nat.max;
  le_max_l := Nat.le_max_l;
  le_max_r := Nat.le_max_r;
}.



Module ExtendedNat.

Inductive NatInf : Set :=
  | infinity | finite : nat -> NatInf.

Coercion finite : nat >-> NatInf.

Definition le (n1 n2 : NatInf) : Prop :=
  match n1, n2 with 
  | _, infinity => True
  | infinity, _ => False 
  | finite m1, finite m2 => Nat.le m1 m2
  end.

Lemma le_refl : forall n, le n n.
Proof. unfold le. destruct n. tauto. now apply Nat.le_refl. Qed.
Lemma le_antisymm : forall n1 n2, le n1 n2 -> le n2 n1 -> n1 = n2.
Proof.
  unfold le. destruct n1 as [|m1], n2 as [|m2]. 1-3: tauto. intros H1 H2.
  now rewrite <- (Nat.le_antisymm m1 m2 H1 H2). 
Qed.
Lemma le_trans : forall n1 n2 n3, le n1 n2 -> le n2 n3 -> le n1 n3.
Proof.
  unfold le. destruct n1 as [|m1], n2 as [|m2], n3 as [|m3]. 1-7: tauto. 
  exact (Nat.le_trans m1 m2 m3). 
Qed.

#[export] 
Instance NatInf_Reflexive : RelationClasses.Reflexive le := le_refl.
#[export] 
Instance NatInf_Transitive : RelationClasses.Transitive le := le_trans.
#[export] 
Instance NatInf_PreOrder : RelationClasses.PreOrder le := { }.
#[export] 
Instance NatInf_PartialOrder : RelationClasses.PartialOrder (@eq NatInf) le
  := mkEqualityPartialOrder NatInf_PreOrder le_antisymm.


Definition lt (n1 : nat) (n2 : NatInf) : Prop :=
  match n2 with 
  | infinity => True
  | finite m2 => Nat.lt n1 m2
  end.

Definition max (n1 n2 : NatInf) : NatInf :=
  match n1, n2 with 
  | finite m1, finite m2 => finite (Nat.max m1 m2)
  | _, _ => infinity
  end.

Lemma le_max_l : forall n1 n2 : NatInf, le n1 (max n1 n2).
Proof. 
  unfold le, max. intros n1 n2. destruct n1,n2. 1,2,3: tauto. now apply Nat.le_max_l.
Qed.
Lemma le_max_r : forall n1 n2 : NatInf, le n2 (max n1 n2).
Proof. 
  unfold le, max. intros n1 n2. destruct n1,n2. 1,2,3: tauto. now apply Nat.le_max_r.
Qed.

#[export]
Instance NatInf_Lattice : Lattice NatInf := {
  bot := finite 0;
  le := le;
  le_refl := le_refl;
  le_antisymm := le_antisymm;
  le_trans := le_trans;
  max := max;
  le_max_l := le_max_l;
  le_max_r := le_max_r;
}.

End ExtendedNat.


Module RestrictedNat.

Axiom propositional_extensionality : forall (P : Prop), forall (p q : P), p = q.

Definition NatLe (n : nat) : Set :=  { m : nat | Nat.le m n }.

Definition le {n : nat} (m1 m2 : NatLe n) : Prop := Nat.le (proj1_sig m1) (proj1_sig m2).
Lemma le_refl {n : nat} : forall (m : NatLe n), le m m.
Proof. intro m. unfold le. exact (Nat.le_refl (proj1_sig m)). Qed.
Lemma le_antisymm {n : nat} : forall (m1 m2 : NatLe n), le m1 m2 -> le m2 m1 -> m1 = m2.
Proof. 
  intros m1 m2. unfold le. intros H12 H21.
  apply eq_sig_hprop. intros x. now apply propositional_extensionality.
   now rewrite (@Nat.le_antisymm _ _ H12 H21).
Qed.
Lemma le_trans {n : nat} : forall (m1 m2 m3 : NatLe n), le m1 m2 -> le m2 m3 -> le m1 m3.
Proof. intros m1 m2 m3. unfold le. intros H12 H23. exact (Nat.le_trans _ _ _ H12 H23). Qed.

#[export] 
Instance NatLe_Reflexive (n : nat) : RelationClasses.Reflexive (@le n) := @le_refl n.
#[export] 
Instance NatLe_Transitive (n : nat) : RelationClasses.Transitive (@le n) := @le_trans n.
#[export] 
Instance NatLe_PreOrder (n : nat) : RelationClasses.PreOrder (@le n) := { }.
#[export] 
Instance NatLe_PartialOrder (n : nat) : RelationClasses.PartialOrder (@eq (NatLe n)) (@le n) :=
  mkEqualityPartialOrder (NatLe_PreOrder n) le_antisymm.

Definition max {n : nat} (m1 m2 : NatLe n) : (NatLe n) := 
  exist (fun m => Nat.le m n) (Nat.max (proj1_sig m1) (proj1_sig m2)) 
    (Nat.max_lub _ _  _ (proj2_sig m1) (proj2_sig m2)) .
Lemma le_max_l {n : nat} : forall (m1 m2 : NatLe n), le m1 (max m1 m2).
Proof. intros m1 m2. now apply Nat.le_max_l. Qed.
Lemma le_max_r {n : nat} : forall (m1 m2 : NatLe n), le m2 (max m1 m2).
Proof. intros m1 m2. now apply Nat.le_max_r. Qed.

Definition bot {n : nat} : NatLe n :=
  exist (fun m => Nat.le m n) 0 (Nat.le_0_l n).

#[export] 
Instance Lattice_NatLe : forall n, Lattice (NatLe n) := { 
  bot := @bot n;
  le := @le n;
  le_refl := @le_refl n;
  le_antisymm := @le_antisymm n;
  le_trans := @le_trans n;
  le_pre_order := NatLe_PreOrder n;
  le_partial_order := NatLe_PartialOrder n;
  max := @max n;
  le_max_l := @le_max_l n;
  le_max_r := @le_max_r n;
}.

End RestrictedNat.


(* Computable Topological Spaces *)
Module BasicTopologic.

Notation succ := S.


Class Basis (BS : Set) := {
  refines : BS -> BS -> Prop;
  refines_refl : forall bs : BS, refines bs bs;
  refines_trans : forall bs1 bs2 bs3 : BS, 
    refines bs1 bs2 -> refines bs2 bs3 -> refines bs1 bs3;
}.

(*
Instance refines_is_reflexive {BS : Set} {T : Basis BS}
  : CRelationClasses.Reflexive refines := refines_refl.
Instance refines_is_transitive {BS : Set} {T : Basis BS}
   : CRelationClasses.Transitive refines := refines_trans.
*)

Definition lift_unary {T X Y : Type} (f : X -> Y) (x : T -> X) : T -> Y :=
  fun t => f (x t).

Definition lift_binary {T X1 X2 Y : Type} (f : X1 -> X2 -> Y) (x1 : T -> X1) (x2 : T -> X2) : T -> Y :=
  fun t => f (x1 t) (x2 t).


Section MonotoneEquivalence.

Context `{N : Set} `{l : Lattice N}.
Infix "<=" := le.
Context `{BS : Set} `{T : Basis BS}.

Definition is_monotone_weak (s : nat -> BS) : Prop :=
  forall n, refines (s (succ n)) (s n).


Definition is_monotone (s : N -> BS) : Prop :=
  forall (m n : N), m <= n -> refines (s n) (s m).
Definition is_monotone_strong := is_monotone.

Section Monotone.

Local Instance refines_is_reflexive
  : RelationClasses.Reflexive refines := refines_refl.
Local Instance refines_is_transitive
   : RelationClasses.Transitive refines := refines_trans.



Lemma is_monotone_extensional : forall (s1 s2 : N -> BS),
  (forall n, s1 n = s2 n) -> is_monotone s1 -> is_monotone s2.
Proof.
  intros s1 s2 Heq Hs1. unfold is_monotone in *.
  intros m n Hmlen.
  rewrite <- Heq, <- Heq.
  now apply Hs1.
Qed.


Definition is_monotone_unary_operator (op : BS -> BS) : Prop :=
  forall bs bs', refines bs' bs ->
    refines (op bs') (op bs).

Definition is_monotone_binary_operator (op : BS -> BS -> BS) : Prop :=
  forall bs1 bs1' bs2 bs2', refines bs1' bs1 -> refines bs2' bs2 ->
    refines (op bs1' bs2') (op bs1 bs2).

Lemma is_monotone_constant : forall (c : BS),
  is_monotone (fun _ : N => c).
Proof.
  unfold is_monotone. 
  intros c m n Hmn.
  exact (refines_refl c). 
Qed.

Lemma is_monotone_unary_lift : forall (op : BS -> BS) (s : N -> BS),
  is_monotone_unary_operator op -> is_monotone s ->
    is_monotone (fun n => op (s n)).
Proof.
  unfold is_monotone_unary_operator, is_monotone.
  intros op s Hop Hs m n Hmn.
  apply Hop. exact (Hs m n Hmn). 
Qed.

Lemma is_monotone_binary_lift : forall (op : BS -> BS -> BS) (s1 s2 : N -> BS),
  is_monotone_binary_operator op -> is_monotone s1 -> is_monotone s2 ->
    is_monotone (fun n => op (s1 n) (s2 n)).
Proof.
  unfold is_monotone_binary_operator, is_monotone.
  intros op s1 s2 Hop Hs1 Hs2 m n Hmn.
  apply Hop. exact (Hs1 m n Hmn). exact (Hs2 m n Hmn).
Qed.

End Monotone.


(*

Section MonotoneWeak.

Lemma monotone_weak_implies_strong {BS' : Set} {T' : Basis BS'} : 
  forall s, @is_monotone_weak BS' T' s -> @is_monotone nat Nat.le BS' T' s.
Proof.
  intros s Hmw.
  assert (forall n k, refines (s (n+k)) (s n)) as Hm. {
    intro n. induction k.
    - rewrite -> Nat.add_0_r. apply T.(refines_refl).
    - apply (T.(refines_trans) _ (s (n+k)) _).
      rewrite -> Nat.add_succ_r. exact (Hmw (n+k)).
      exact IHk.
  }
  intros m n Hmn.
  pose proof (Nat.le_exists_sub m n Hmn) as He.
  destruct He as [k [Hk _]].
  rewrite -> Nat.add_comm in Hk.
  rewrite -> Hk.
  exact (Hm m k).
Qed.

End MonotoneWeak.

*)


Section Equivalence.

Definition eqv_seq (s1 s2 : N -> BS) :=
  forall bs : BS, (exists n1, refines (s1 n1) bs) <-> (exists n2, refines (s2 n2) bs).

Lemma eqv_seq_refl : forall s : N -> BS, eqv_seq s s.
Proof. unfold eqv_seq. now apply iff_refl. Qed.

Lemma eqv_seq_sym' : forall s1 s2 : N -> BS, eqv_seq s1 s2 <-> eqv_seq s2 s1.
Proof. unfold eqv_seq. intros s1 s2. now apply iff_sym. Qed.
Lemma eqv_seq_sym : forall s1 s2 : N -> BS, eqv_seq s1 s2 -> eqv_seq s2 s1.
Proof. now apply eqv_seq_sym'. Qed.

Lemma eqv_seq_trans : forall s1 s2 s3 : N -> BS, 
  eqv_seq s1 s2 -> eqv_seq s2 s3 -> eqv_seq s1 s3.
Proof. 
  unfold eqv_seq. intros s1 s2 s3 H12 H23. 
  intro bs. specialize H12 with bs; specialize H23 with bs.
  split.
  - intro H1. apply H23. apply H12. exact H1.
  - intro H3. apply H12. apply H23. exact H3.
Qed.

Instance eqv_seq_is_cequivalence : CRelationClasses.Equivalence (eqv_seq) :=
  CRelationClasses.Build_Equivalence eqv_seq eqv_seq_refl eqv_seq_sym eqv_seq_trans.
Instance eqv_seq_is_equivalence : RelationClasses.Equivalence (eqv_seq) :=
  RelationClasses.Build_Equivalence eqv_seq eqv_seq_refl eqv_seq_sym eqv_seq_trans.

Definition pre_eqv_seq (s1 s2 : N -> BS) :=
  forall bs : BS, (exists n1, refines (s1 n1) bs) -> (exists n2, refines (s2 n2) bs).

Theorem monotone_unary_operator_respectful :
  forall op (s s' : N -> BS), 
    is_monotone s -> is_monotone s' -> 
      is_monotone_unary_operator op -> eqv_seq s s' -> 
        eqv_seq (lift_unary op s) (lift_unary op s').
Proof.
  assert (forall op s s',
    is_monotone s -> is_monotone s' -> 
      is_monotone_unary_operator op -> eqv_seq s s' -> 
        pre_eqv_seq (lift_unary op s) (lift_unary op s'))
          as monotone_unary_operator_respectful'. {
    unfold pre_eqv_seq, is_monotone_unary_operator, lift_unary.
    intros op s s' Hms Hms' Hop Hes.
    intro bs. 
    intro Hr. 
    assert (forall m, exists m', refines (s' m') (s m)) as Hm. {
      intro m. apply (Hes (s m)). exists m. exact (refines_refl (s m)). }
    assert (forall n, exists n', refines (op (s' n')) (op (s n))) as Hn. {
      intro n. specialize Hm with n.
      destruct Hm as [m Hm]. exists m.
      apply Hop. exact Hm.
    }
    destruct Hr as [n Hr].
    specialize Hn with n. destruct Hn as [n' Hr'].
    exists n'.
    apply (refines_trans _ (op (s n)) _).
    exact Hr'.
    exact Hr.
  }
  intros op s s' Hs Hs' Hop He.
  split.
  - now apply monotone_unary_operator_respectful'; assumption.
  - apply eqv_seq_sym in He. 
    now apply monotone_unary_operator_respectful'; assumption.
Qed.

Theorem monotone_binary_operator_respectful :
  forall op s1 s1' s2 s2', 
    is_monotone s1 -> is_monotone s1' -> is_monotone s2 -> is_monotone s2' ->
      is_monotone_binary_operator op -> eqv_seq s1 s1' -> eqv_seq s2 s2' ->
        eqv_seq (lift_binary op s1 s2) (lift_binary op s1' s2').
Proof.
  assert (forall op s1 s1' s2 s2', 
    is_monotone s1 -> is_monotone s1' -> is_monotone s2 -> is_monotone s2' ->
      is_monotone_binary_operator op -> eqv_seq s1 s1' -> eqv_seq s2 s2' ->
        pre_eqv_seq (lift_binary op s1 s2) (lift_binary op s1' s2'))
          as monotone_binary_operator_respectful'. {
    unfold pre_eqv_seq, is_monotone_binary_operator, lift_binary.
    intros op s1 s1' s2 s2' Hms1 Hms1' Hms2 Hms2' Hop Hes1 Hes2.
    intro bs. 
    intro Hr1. 
    assert (forall m1, exists m1', refines (s1' m1') (s1 m1)) as Hm1. {
      intro m1. apply (Hes1 (s1 m1)). exists m1. exact (refines_refl (s1 m1)). }
    assert (forall m2, exists m2', refines (s2' m2') (s2 m2)) as Hm2. {
      intro m2. apply (Hes2 (s2 m2)). exists m2. exact (refines_refl (s2 m2)). }
    assert (forall n, exists n', refines (op (s1' n') (s2' n')) (op (s1 n) (s2 n))) as Hn. {
      intro n. specialize Hm1 with n. specialize Hm2 with n.
      destruct Hm1 as [m1' Hm1]. destruct Hm2 as [m2' Hm2].
      set (m12' := max m1' m2'). exists m12'.
      apply Hop.
      - apply (refines_trans _ (s1' m1') _). apply Hms1'. now apply le_max_l. exact Hm1.
      - apply (refines_trans _ (s2' m2') _). apply Hms2'. now apply le_max_r. exact Hm2.
    }
    destruct Hr1 as [n Hr].
    specialize Hn with n. destruct Hn as [n' Hr'].
    exists n'.
    apply (refines_trans _ (op (s1 n) (s2 n)) _).
    exact Hr'.
    exact Hr.
  }
  intros op s1 s1' s2 s2' Hs1 Hs1' Hs2 Hs2' Hop He1 He2.
  split.
  - now apply monotone_binary_operator_respectful'; assumption.
  - apply eqv_seq_sym in He1, He2. 
    now apply monotone_binary_operator_respectful'; assumption.
Qed.

End Equivalence.

End MonotoneEquivalence.

End BasicTopologic.
