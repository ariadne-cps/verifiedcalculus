Require Import Coq.Logic.ConstructiveEpsilon.
Require Import PeanoNat.

(* The constructive Kleenean logical type. *)


Module Tribool.

Notation B := bool.
Notation N := nat.

Inductive Tribool : Set := | tru | indt | fls.

Definition not (t : Tribool) : Tribool :=
  match t with
  | tru => fls
  | indt => indt
  | fls => tru
  end.

Definition impl (t1 t2 : Tribool) : Tribool :=
  match (t1,t2) with
  | (fls,_) => tru
  | (_,tru) => tru
  | (indt,_) => indt
  | (_,indt) => indt
  | (_,_) => fls
  end.

Definition and (t1 t2 : Tribool) : Tribool :=
  match (t1,t2) with
  | (fls,_) => fls
  | (_,fls) => fls
  | (indt,_) => indt
  | (_,indt) => indt
  | (_,_) => tru
  end.

Definition or (t1 t2 : Tribool) : Tribool :=
  match (t1,t2) with
  | (tru,_) => tru
  | (_,tru) => tru
  | (indt,_) => indt
  | (_,indt) => indt
  | (_,_) => fls
  end.

Definition iff (t1 t2 : Tribool) : Tribool :=
  match (t1,t2) with
  | (indt,_) => indt
  | (_,indt) => indt
  | (tru,tru) => tru
  | (fls,fls) => tru
  | (tru,fls) => fls
  | (fls,tru) => fls
  end.

Definition Tribool_of_Bool : B -> Tribool :=
  fun b => match b with | true => tru | false => fls end.

Lemma eq_dne : forall t1 t2 : Tribool, ~ (t1 <> t2) -> t1 = t2. 
Proof. 
  intros t1 t2. destruct t1, t2.
  1,5,9: intro H; reflexivity.
  all: intro H; exfalso; apply H; discriminate.
Qed.

Lemma eq_dec : forall (t1 t2 : Tribool), {t1 = t2} + {t1 <> t2 }.
Proof. 
  destruct t1, t2. 
  1,5,9: left; reflexivity. 
  all: right; discriminate. 
Qed.

Lemma not_eq_dec : forall (t1 t2 : Tribool), {t1 <> t2} + {~ t1 <> t2 }.
Proof. 
  destruct t1, t2.
  1,5,9: right; intro H; apply H; reflexivity.
  all: left; discriminate.
Qed.

Lemma tru_or_fls_dec : forall t, (t = tru \/ t = fls) -> {t=tru} + {t=fls}.
Proof. intro t. destruct t; intro H.
  - left; reflexivity.
  - exfalso. destruct H; discriminate.
  - right; reflexivity.
Qed.

Lemma tru_or_fls_iff_not_indt : forall t: Tribool, t = tru \/ t = fls <-> t <> indt.
Proof. 
  intro t. destruct t.
  - split. discriminate. intro H; left; reflexivity.
  - split. intros Htf Hni; destruct Htf; discriminate. intro H. exfalso; apply H; reflexivity.
  - split. discriminate. intro H; right; reflexivity.
Qed.

Lemma impl_tru : forall t1 t2, impl t1 t2 = tru -> t1 = fls \/ t2 = tru.
Proof. intros t1 t2 H. destruct t1, t2. 6: discriminate H. all: tauto. Qed.

Lemma impl_fls : forall t1 t2, impl t1 t2 = fls -> t1 = tru /\ t2 = fls.
Proof. intros t1 t2 H. destruct t1, t2. 3: split; reflexivity. all: discriminate H. Qed.

Lemma and_tru : forall t1 t2, and t1 t2 = tru -> t1 = tru /\ t2 = tru.
Proof. intros t1 t2 H. destruct t1, t2. 1: split; reflexivity. all: discriminate H. Qed.

Lemma and_fls: forall t1 t2 : Tribool, and t1 t2 = fls -> t1 = fls \/ t2 = fls.
Proof. intros t1 t2. destruct t1, t2. all: tauto. Qed.


Lemma not_eq_impl_fls : forall t, not t = impl t fls.
Proof. destruct t; reflexivity. Qed.

Lemma or_eq_impl_not : forall t1 t2, or t1 t2 = impl (not t1) t2.
Proof. destruct t1, t2; reflexivity. Qed.

Lemma and_eq_not_impl_not : forall t1 t2, and t1 t2 = not (impl t1 (not t2)).
Proof. destruct t1, t2; reflexivity. Qed.

Lemma iff_eq_impl_and_rimpl : forall t1 t2, iff t1 t2 = and (impl t1 t2) (impl t2 t1).
Proof. destruct t1, t2; reflexivity. Qed.

Lemma and_eq_not_or_not : forall t1 t2, and t1 t2 = not (or (not t1) (not t2)).
Proof. destruct t1, t2; reflexivity. Qed.

Lemma or_eq_not_and_not : forall t1 t2, or t1 t2 = not (and (not t1) (not t2)).
Proof. destruct t1, t2; reflexivity. Qed.

Lemma impl_eq_or_not : forall t1 t2, impl t1 t2 = or (not t1) t2.
Proof. destruct t1, t2; reflexivity. Qed.

End Tribool.


Module Kleene.

Notation B := bool.
Notation N := nat.

Import PeanoNat.

(*
Import Tribool.
*)

Notation TB := Tribool.Tribool.

Notation TBtru := Tribool.tru.
Notation TBindt := Tribool.indt.
Notation TBfls := Tribool.fls.
Notation TBnot := Tribool.not.
Notation TBimpl := Tribool.impl.
Notation TBand := Tribool.and.
Notation TBor := Tribool.or.
Notation TBiff := Tribool.iff.



Definition monotone (tbs : N -> TB) : Prop
  := forall (i : N), (tbs i = Tribool.tru -> tbs (S i) = Tribool.tru) /\ (tbs i = Tribool.fls -> tbs (S i) = Tribool.fls).

Lemma monotone_indt : forall (tbs : N -> TB), 
  monotone tbs -> forall i, (tbs (S i) = Tribool.indt -> tbs i = Tribool.indt).
Proof. 
  unfold monotone. intros tbs H i HSi. specialize H with i. destruct H as [Ht Hf].
  destruct (tbs (S i)). 1,3: discriminate.
  destruct (tbs i). symmetry; now apply Ht. reflexivity. symmetry; now apply Hf.
Qed.

Lemma monotone_extensional : forall (k1 k2 : N -> TB),
  (forall n, k1 n = k2 n) -> monotone k1 -> monotone k2.
Proof.
  intros k1 k2 Hk1eqk2 Hmk1. unfold monotone in *.
  intros i; specialize Hmk1 with i.
  now rewrite <- Hk1eqk2, <- Hk1eqk2.
Qed.




Declare Scope Kleenean_scope.

Record Kleenean := mkKleenean {
  tbs :> N -> TB;
  proper : monotone tbs
}.

Notation K := Kleenean.


(* ?? Declare scope Kleenean_scope with key Kleenean *)
Delimit Scope Kleenean_scope with Kleenean.

(* Automatically open scope Kleenean_scope for arguments of type Kleenean *)
Bind Scope Kleenean_scope with Kleenean.

Local Open Scope Kleenean_scope.


Definition definitely (k : K) : Prop := exists i, k i = TBtru.
(* Equivalently, forall i, ~ (ki = TBfls) *)

Definition possibly (k : K) : Prop := ~ (exists i, k i = TBfls).


Definition eqv (k1 k2 : K) : Prop := exists i, forall j, i <= j -> k1 j = k2 j.
Infix "==" := eqv (at level 70, no associativity) : Kleenean_scope.

Lemma eqv_refl : forall k : K, k == k.
Proof. unfold eqv. intro k. exists 0. intros j Hilej. reflexivity. Qed.

Lemma eqv_sym : forall k1 k2 : K, k1 == k2 -> k2 == k1.
Proof. unfold eqv. intros k1 k2 [i He]. exists i. intros j Hilej. specialize He with j. symmetry. exact (He Hilej). Qed.

Lemma eqv_trans : forall k1 k2 k3 : K, k1 == k2 -> k2 == k3 -> k1 == k3.
Proof. 
  unfold eqv. intros k1 k2 k3 [i12 He12] [i23 He23].
  set (i13 := max i12 i23); exists i13.
  intro j; specialize He12 with j; specialize He23 with j.
  intro Hi13lej. rewrite -> He12. rewrite <- He23. reflexivity.
  - assert (i23 <= i13) as Hi23lei13 by (apply Nat.le_max_r). apply (Nat.le_trans _ i13); assumption.
  - assert (i12 <= i13) as Hi12lei13 by (apply Nat.le_max_l). apply (Nat.le_trans _ i13); assumption.
Qed.



Definition apart (k1 k2 : K) := exists i : N, k1 i <> TBindt /\ k2 i <> TBindt /\ k1 i <> k2 i.
Infix "#" := apart (at level 55, no associativity) : Kleenean_scope.

Lemma apart_irrefl : forall k : K, k # k -> False.
Proof.
  intros k. unfold apart. intros H. destruct H as [i [_ [_ Hn]]]. tauto.
Qed.

Lemma apart_sym : forall k1 k2 : K, k1 # k2 -> k2 # k1.
Proof.
  intros k1 k2. unfold apart. intros [i [H1 [H2 Hne]]]. exists i. 
  split. exact H2. split. exact H1. apply not_eq_sym. exact Hne.
Qed.



Definition lt (k1 k2 : K) : Set
  := { i : N |  k1 i = TBfls /\ k2 i = TBtru }.

Definition gt k1 k2 := lt k2 k1.

Definition lt_prop (k1 k2 : K) : Prop
  := exists i : N, k1 i = TBfls /\ k2 i = TBtru.

Infix "<" := lt : Kleenean_scope.
Infix ">" := gt : Kleenean_scope.

Lemma lt_irrefl : forall k : K, k < k -> False.
Proof.
  intros k. unfold lt. intros H. destruct H as [n [Hf Ht]]. rewrite -> Ht in Hf. discriminate Hf.
Qed.


(* lt_prop can be extracted as a sigma type *)
Lemma lt_sigma : forall k1 k2 : K,
    lt_prop k1 k2 -> k1 < k2.
Proof.
  intros k1 k2 H. unfold lt_prop in H.
  apply constructive_indefinite_ground_description_nat in H.
  - apply H.
  - intros i.
    destruct (tbs k1 i), (tbs k2 i); try (right; intro Hf; destruct Hf as [H1 H2]; discriminate).
    left. tauto.
Qed.

Lemma lt_forget : forall k1 k2 : K,
    k1 < k2 -> lt_prop k1 k2.
Proof.
  intros k1 k2 H. destruct H as [i Hi]. exists i. exact Hi.
Qed.


Definition le (k1 k2 : K) : Prop := lt k2 k1 -> False.
Definition ge (k1 k2 : K) := le k2 k1.



Lemma cnst_monotone : forall t : TB, monotone (fun _ => t).
Proof. unfold monotone. intros t i. tauto. Qed.

Definition constant (t : TB) := mkKleenean (fun _ => t) (cnst_monotone t).

Definition true := constant TBtru.
Definition indeterminate := constant TBindt.
Definition false := constant TBfls.

Lemma true_apart_false : apart true false.
Proof. unfold apart. exists O. unfold true, false. simpl. split; try split; discriminate. Qed.

Lemma indeterminate_not_apart : forall (k : Kleenean), ~ (indeterminate # k).
Proof. intro k. unfold apart. intros [i [H _]]. apply H. unfold indeterminate. reflexivity. Qed.



Lemma not_monotone (k : N -> TB) (Hk : monotone k)
  : monotone (fun n => TBnot (k n)).
Proof.
  unfold monotone in *.
  intros i. specialize Hk with i.
  destruct (k i).
  - split. 
    -- intro Hf. unfold TBnot in Hf. discriminate.
    -- intro Ht. rewrite -> (proj1 Hk (eq_refl TBtru)). now unfold TBnot.
  - split; unfold TBnot; discriminate.
  - split.
    -- intro Ht. rewrite -> (proj2 Hk (eq_refl TBfls)). now unfold TBnot.
    -- intro Hf. unfold TBnot in Hf. discriminate.
Qed.

Definition not (k : Kleenean) : Kleenean :=
  mkKleenean (fun i => TBnot (k i)) (not_monotone k (proper k)).


Lemma impl_monotone (k1 k2 : N -> TB) (Hk1 : monotone k1) (Hk2 : monotone k2)
  : monotone (fun n => TBimpl (k1 n) (k2 n)).
Proof.
  unfold monotone in *.
  intros i. specialize Hk1 with i. specialize Hk2 with i.
  split.
  + intro Ht.
    destruct (k1 i); destruct (k2 i).
    7,8,9: rewrite -> (proj2 Hk1 (eq_refl TBfls)); now unfold TBimpl.
    1,4: rewrite -> (proj1 Hk2 (eq_refl TBtru));
         unfold TBimpl; destruct (k1 (S i)); reflexivity. 
    1,2,3,4: unfold TBimpl; discriminate.
  + intro Hf.
    set (k1i := k1 i); set (k2i := k1 i).
    destruct (k1 i); destruct (k2 i).
    1,2,4,5,6,7,8,9: unfold TBimpl; discriminate.
    1: apply Tribool.impl_fls in Hf. destruct Hf as [Hf1 Hf2].
       rewrite -> (proj1 Hk1 (eq_refl TBtru)).
       rewrite -> (proj2 Hk2 (eq_refl TBfls)).
       now unfold TBimpl.
Qed.

Definition impl (k1 k2 : Kleenean) : Kleenean :=
  mkKleenean (fun i => TBimpl (k1 i) (k2 i)) (impl_monotone k1 k2 (proper k1) (proper k2)).

Lemma not_monotone' (k : N -> TB) (Hk : monotone k)
  : monotone (fun n => TBnot (k n)).
Proof.
  apply ( monotone_extensional ( fun n : N => TBimpl (k n) TBfls ) ).
  intro n. rewrite -> Tribool.not_eq_impl_fls. reflexivity.
  apply impl_monotone.
  exact Hk.
  now apply cnst_monotone.
Qed.


Lemma and_monotone (k1 k2 : N -> TB) (Hk1 : monotone k1) (Hk2 : monotone k2)
  : monotone (fun n => TBand (k1 n) (k2 n)).
Proof.
  apply ( monotone_extensional ( fun n : N => TBnot (TBimpl (k1 n) (TBnot (k2 n))) ) ).
  intro n. rewrite -> Tribool.and_eq_not_impl_not. reflexivity.
  apply not_monotone.
  apply impl_monotone.
  exact Hk1.
  apply not_monotone; exact Hk2.
Qed.

Lemma and_monotone' (k1 k2 : N -> TB) (Hk1 : monotone k1) (Hk2 : monotone k2)
  : monotone (fun n => TBand (k1 n) (k2 n)).
Proof.
  unfold monotone in *.
  intros i. specialize Hk1 with i. specialize Hk2 with i.
  split.
  + intro Ht.
    set (k1i := k1 i); set (k2i := k1 i).
    destruct (k1 i); destruct (k2 i).
    2,3,4,5,6,7,8,9: unfold TBand; discriminate.
    1: apply Tribool.and_tru in Ht. destruct Ht as [Ht1 Ht2]. 
       rewrite -> (proj1 Hk1 (eq_refl TBtru)).
       rewrite -> (proj1 Hk2 (eq_refl TBtru)).
       now unfold TBand.
  + intro Ht.
    destruct (k1 i); destruct (k2 i).
    7,8,9: rewrite -> (proj2 Hk1 (eq_refl TBfls)); now unfold TBand.
    3,6: rewrite -> (proj2 Hk2 (eq_refl TBfls));
         unfold TBand; destruct (k1 (S i)); reflexivity. 
    1,2,3,4: unfold TBand; discriminate.
Qed.

Definition and (k1 k2 : Kleenean) : Kleenean :=
  mkKleenean (fun i => TBand (k1 i) (k2 i)) (and_monotone k1 k2 (proper k1) (proper k2)).


Lemma or_monotone (k1 k2 : N -> TB) (Hk1 : monotone k1) (Hk2 : monotone k2)
  : monotone (fun n => TBor (k1 n) (k2 n)).
Proof.
  apply ( monotone_extensional ( fun n : N => TBnot (TBand (TBnot (k1 n)) (TBnot (k2 n))) ) ).
  intro n. rewrite -> Tribool.or_eq_not_and_not. reflexivity.
  apply not_monotone.
  apply and_monotone.
  apply not_monotone; exact Hk1.
  apply not_monotone; exact Hk2.
Qed.

Definition or (k1 k2 : Kleenean) : Kleenean :=
  mkKleenean (fun i => TBor (k1 i) (k2 i)) (or_monotone k1 k2 (proper k1) (proper k2)).


Lemma iff_monotone (k1 k2 : N -> TB) (Hk1 : monotone k1) (Hk2 : monotone k2)
  : monotone (fun n => TBiff (k1 n) (k2 n)).
Proof.
  apply ( monotone_extensional ( fun n : N => TBand (TBimpl (k1 n) (k2 n)) (TBimpl (k2 n) (k1 n)) ) ).
  intro n. rewrite -> Tribool.iff_eq_impl_and_rimpl. reflexivity.
  apply and_monotone.
  apply impl_monotone. exact Hk1. exact Hk2.
  apply impl_monotone. exact Hk2. exact Hk1.
Qed.

Definition iff (k1 k2 : Kleenean) : Kleenean :=
  mkKleenean (fun i => TBiff (k1 i) (k2 i)) (iff_monotone k1 k2 (proper k1) (proper k2)).





Definition all_indt_or_exists_tru_or_fls (k : K) : Prop := (forall i, k i = TBindt) \/ (exists i, k i = TBtru \/ k i = TBfls).

Lemma all_ge : forall (p : N -> Prop) (i : N), (p i) -> (forall j, p j -> p (S j)) -> (forall j, i <= j -> p j).
Proof.
  intros p i pi pIj j Hilej.
  assert (forall k, p (i + k)) as Hpk. { 
    induction k.
    - rewrite -> Nat.add_0_r. exact pi.
    - rewrite -> Nat.add_succ_r. apply pIj. exact IHk.
  }
  set (Hk := Nat.le_exists_sub i j Hilej). destruct Hk as [k [Hk _]].
  rewrite -> Nat.add_comm in Hk. rewrite -> Hk. exact (Hpk k).
Qed.


Add Parametric Relation : K eqv
    reflexivity proved by eqv_refl
    symmetry proved by eqv_sym
    transitivity proved by eqv_trans
      as eqv_rel.

#[global]
Instance eqv_relT : CRelationClasses.Equivalence eqv.
Proof.
  split.
  - exact eqv_refl.
  - exact eqv_sym.
  - exact eqv_trans.
Qed.


Lemma all_from_not_indt : forall k : K, forall i, (k i <> TBindt -> forall j, i <= j -> k j = k i).
Proof.
  intro k. destruct k as [tbs Htbs]. unfold monotone in *. simpl. 
  intros i Hi. apply all_ge. reflexivity.
  intros j; specialize Htbs with j.
  destruct (tbs i).
  - exact (proj1 Htbs).
  - contradiction.
  - exact (proj2 Htbs).
Qed.

Lemma lt_prop_respectful : forall k1 k1' k2 k2', eqv k1 k1' -> eqv k2 k2' -> lt_prop k1 k2 -> lt_prop k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2 Hlt.
  unfold eqv, lt_prop in *.
  destruct Hk1 as [i1 Hk1i].
  destruct Hk2 as [i2 Hk2i].
  destruct Hlt as [i Hlt].
  set (i' := max i (max i1 i2)).
  assert (i <= i') as Hi by (now apply Nat.le_max_l).
  assert (i1 <= i') as Hi1. apply (Nat.le_trans _ (max i1 i2)). apply Nat.le_max_l. now apply Nat.le_max_r.
  assert (i2 <= i') as Hi2. apply (Nat.le_trans _ (max i1 i2)). apply Nat.le_max_r. now apply Nat.le_max_r.
  exists i'.
  rewrite <- (Hk1i _ Hi1). 
  rewrite <- (Hk2i _ Hi2). 
  split.
  - rewrite <- (proj1 Hlt). apply all_from_not_indt. rewrite -> (proj1 Hlt). discriminate. exact Hi.
  - rewrite <- (proj2 Hlt). apply all_from_not_indt. rewrite -> (proj2 Hlt). discriminate. exact Hi.
Qed.

Lemma impl_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> impl k1 k2 == impl k1' k2'.
Proof.
  intros k1 k1' k2 k2' [i1 Hk1] [i2 Hk2].
  unfold eqv in *.
  set (i := max i1 i2).
  exists i. intros j Hilej.
  specialize Hk1 with j; specialize Hk2 with j.
  unfold impl. simpl.
  rewrite <- Hk1, <- Hk2. reflexivity.
  - apply (Nat.le_trans _ i). now apply Nat.le_max_r. exact Hilej.
  - apply (Nat.le_trans _ i). now apply Nat.le_max_l. exact Hilej.
Qed.


Lemma not_respectful : forall k k' : K, k == k' -> not k == not k'.
Proof.
  intros k k' [i Hk].
  unfold eqv in *.
  exists i. intros j Hilej. specialize Hk with j.
  unfold not. simpl.
  rewrite <- Hk. reflexivity. exact Hilej.
Qed.

Lemma not_eq_impl_false : forall k : K, not k == impl k false.
Proof.
  intros k. unfold eqv, not, false, impl. simpl.
  exists 0. intros j H0lej. now apply Tribool.not_eq_impl_fls. 
Qed.

Lemma not_respectful' : forall k k' : K, k == k' -> not k == not k'.
Proof.
  intros k k' Hk.
  apply (eqv_trans _ (impl k false)).
  exact (not_eq_impl_false k).
  apply (eqv_trans _ (impl k' false)).
  apply impl_respectful.
  exact Hk.
  exact (eqv_refl false).
  apply eqv_sym.
  exact (not_eq_impl_false k').
Qed.
 
Lemma not_respectful'' : Classes.CMorphisms.respectful eqv eqv not not.
Proof.
  intros k k' [i Hk].
  unfold eqv in *.
  exists i. intros j Hilej. specialize Hk with j.
  unfold not. simpl.
  rewrite <- Hk. reflexivity. exact Hilej.
Qed.


Lemma or_eq_impl_not : forall k1 k2 : K, or k1 k2 == impl (not k1) k2.
Proof.
  intros k1 k2. unfold eqv, or, impl, not. simpl.
  exists 0. intros j H0lej. now apply Tribool.or_eq_impl_not.
Qed.

Lemma or_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> or k1 k2 == or k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  apply (eqv_trans _ (impl (not k1) k2)).
  exact (or_eq_impl_not k1 k2).
  apply (eqv_trans _ (impl (not k1') k2')).
  apply impl_respectful. apply not_respectful. exact Hk1. exact Hk2.
  apply eqv_sym.
  exact (or_eq_impl_not k1' k2').
Qed.


Lemma and_eq_not_impl_not : forall k1 k2 : K, and k1 k2 == not (impl k1 (not k2)).
Proof.
  intros k1 k2. unfold eqv, and, not, impl, not. simpl.
  exists 0. intros j H0lej. now apply Tribool.and_eq_not_impl_not.
Qed.

Lemma and_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> and k1 k2 == and k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  apply (eqv_trans _ (not (impl k1 (not k2)))).
  exact (and_eq_not_impl_not k1 k2).
  apply (eqv_trans _ (not (impl k1' (not k2')))).
  apply not_respectful. apply impl_respectful. exact Hk1. apply not_respectful. exact Hk2.
  apply eqv_sym.
  exact (and_eq_not_impl_not k1' k2').
Qed.


Lemma iff_eq_impl_and_rimpl : forall k1 k2 : K, iff k1 k2 == and (impl k1 k2) (impl k2 k1).
Proof.
  intros k1 k2. unfold eqv, iff, and, impl, impl. simpl.
  exists 0. intros j H0lej. now apply Tribool.iff_eq_impl_and_rimpl.
Qed.

Lemma iff_respectful : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> iff k1 k2 == iff k1' k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  apply (eqv_trans _ (and (impl k1 k2) (impl k2 k1))).
  exact (iff_eq_impl_and_rimpl k1 k2).
  apply (eqv_trans _ (and (impl k1' k2') (impl k2' k1'))).
  apply and_respectful. 
  apply impl_respectful. exact Hk1. exact Hk2.
  apply impl_respectful. exact Hk2. exact Hk1.
  apply eqv_sym.
  exact (iff_eq_impl_and_rimpl k1' k2').
Qed.



Lemma apart_respectful
  : forall k1 k1' k2 k2' : K, k1 == k1' -> k2 == k2' -> k1 # k2 -> k1' # k2'.
Proof.
  intros k1 k1' k2 k2' Hk1 Hk2.
  unfold eqv, apart in *.
  intros Hapart.
  destruct Hapart as [i Hapart].
  destruct Hk1 as [i1 Hk1].
  destruct Hk2 as [i2 Hk2].
  set (i' := max i (max i1 i2)). exists i'.
  assert (i <= i') as Hi by (now apply Nat.le_max_l).
  assert (i1 <= i') as Hi1. apply (Nat.le_trans _ (max i1 i2)). now apply Nat.le_max_l. now apply Nat.le_max_r.
  assert (i2 <= i') as Hi2. apply (Nat.le_trans _ (max i1 i2)). now apply Nat.le_max_r. now apply Nat.le_max_r.
  rewrite <- (Hk1 _ Hi1); rewrite <- (Hk2 _ Hi2).
  destruct Hapart as [Hn1i [Hn2i Ha]].
  split; (try split).
  - rewrite -> (all_from_not_indt k1 i Hn1i i' Hi). exact Hn1i.
  - rewrite -> (all_from_not_indt k2 i Hn2i i' Hi). exact Hn2i.
  - rewrite -> (all_from_not_indt k1 i Hn1i i' Hi).
    rewrite -> (all_from_not_indt k2 i Hn2i i' Hi). 
    exact Ha.
Qed.

Notation Proper := CMorphisms.Proper.
Notation respectful := CMorphisms.respectful.


#[global]
Instance not_morph_T : Proper (respectful eqv eqv) not.
Proof. intros a a' Ha. now apply not_respectful. Qed.

#[global]
Instance impl_morph_T : Proper (respectful eqv (respectful eqv eqv)) impl.
Proof. intros a a' Ha b b' Hb. now apply impl_respectful. Qed.

#[global]
Instance and_morph_T : Proper (respectful eqv (respectful eqv eqv)) and.
Proof. intros a a' Ha b b' Hb. now apply and_respectful. Qed.

#[global]
Instance or_morph_T : Proper (respectful eqv (respectful eqv eqv)) or.
Proof. intros a a' Ha b b' Hb. now apply or_respectful. Qed.

#[global]
Instance iff_morph_T : Proper (respectful eqv (respectful eqv eqv)) iff.
Proof. intros a a' Ha b b' Hb. now apply iff_respectful. Qed.

#[global]
Instance apart_morph_T : Proper (respectful eqv (respectful eqv CRelationClasses.iffT)) apart.
Proof.
  intros a a' Ha b b' Hb. split. now apply apart_respectful. apply apart_respectful; now apply eqv_sym.
Qed.



Lemma defined_dec : forall k,
  (k == true \/ k == false) -> ({k == true} + {k == false}).
Proof.
  intros k H.
  assert (exists i, k i = TBtru \/ k i = TBfls) as Hi. {
    destruct H as [[i H]|[i H]]; specialize H with i; exists i.
    - left; exact (H (Nat.le_refl i)).
    - right; exact (H (Nat.le_refl i)).
  }
  assert ({ i | k i = TBtru \/ k i = TBfls}) as Hsi. {
    apply constructive_indefinite_ground_description_nat.
    - intros i. destruct (k i).
      -- left. left. reflexivity.
      -- right. intro Hf. destruct Hf. discriminate. discriminate.
      -- left. right. reflexivity.
    - exact Hi.
  }
  destruct Hsi as [i Hsi].
  assert ({k i = TBtru} + {k i = TBfls}) as Hssi. {
    destruct (k i). 
    - left; reflexivity.
    - exfalso. destruct Hsi; discriminate.
    - right; reflexivity.
  }
  destruct Hssi as [Ht|Hf].
  - left. unfold eqv. exists i. unfold true. simpl. rewrite <- Ht. apply all_from_not_indt. rewrite -> Ht. discriminate.
  - right. unfold eqv, false. simpl. exists i. rewrite <- Hf. apply all_from_not_indt. rewrite -> Hf. discriminate.
Qed.


Lemma and_up : forall a b, (and a b == true) <-> (a == true /\ b == true).
Proof.
  intros a b. unfold eqv, and, true. simpl.
  split.
  - intro Hand.
    destruct Hand as [i Hand]. 
    split.
    exists i. intros j Hilej. specialize Hand with j. apply Hand in Hilej as Handj.
    apply Tribool.and_tru in Handj. exact (proj1 Handj).
    exists i. intros j Hilej. specialize Hand with j. apply Hand in Hilej as Handj.
    apply Tribool.and_tru in Handj. exact (proj2 Handj).
  - intros [[ia Ha] [ib Hb]]. set (iab := max ia ib). exists iab.
    intros j Hj. rewrite -> (Ha j), -> (Hb j). unfold TBand. reflexivity.
    apply (Nat.le_trans _ iab). apply Nat.le_max_r. exact Hj. 
    apply (Nat.le_trans _ iab). apply Nat.le_max_l. exact Hj.
Qed.

Lemma and_down : forall a b, (and a b == false) <-> (a == false \/ b == false).
Proof.
  intros a b. unfold eqv, and, false. simpl.
  split.
  - intro Hand.
    destruct Hand as [i Hand].
    assert (TBand (a i) (b i) = TBfls) as Handi by exact (Hand i (Nat.le_refl i)).
    assert (a i = TBfls \/ b i = TBfls) as Habi by exact (Tribool.and_fls _ _ Handi).
    destruct Habi as [Hai|Hbi].
    -- left. exists i. rewrite <- Hai. apply (all_from_not_indt a i). rewrite -> Hai. discriminate.
    -- right. exists i. rewrite <- Hbi. apply (all_from_not_indt b i). rewrite -> Hbi. discriminate.
  - intro Hor.
    destruct Hor as [[i Hai] | [i Hbi]].
    -- exists i. intros j Hilej. rewrite -> (Hai j Hilej). now unfold TBand.
    -- exists i. intros j Hilej. rewrite -> (Hbi j Hilej). unfold TBand. destruct (a j); reflexivity.
Qed.

End Kleene.


Module AbstractKleene.

Class AbstractKleenean (K : Set) :=
  {
    true : K;
    false : K;

    eqv : K -> K -> Prop;
    apart : K -> K -> Prop;

    not : K -> K;
    impl : K -> K -> K;
    or : K -> K -> K;
    and : K -> K -> K;
 
    and_respectful : forall a a' b b', eqv a a' -> eqv b b' -> eqv (and a b) (and a' b');

    and_up : forall a b, (eqv (and a b) true) <-> (eqv a true) /\ (eqv b true);
    and_down : forall a b, (eqv (and a b) false) <-> (eqv a false) \/ (eqv b false);

    distinct : apart false true;
    defined_dec : forall k,
        (eqv k true \/ eqv k false) -> ({eqv k true} + {eqv k false});

(*
    neg_up : forall k, (neg k = true) = (k = false);
    neg_down : forall k, (neg k = false) = (k = true);

    and_up : forall a b, (and a b = true) = (a = true /\ b = true);
    and_down : forall a b, (and a b = false) = (a = false \/ b = false);

    or_up : forall a b, (or a b = true) = (a = true \/ b = true);
    or_down : forall a b, (or a b = false) = (a = false /\ b = false);
    countable_or: forall (c : forall (n :nat), ), {k | k <> false /\ (k = true <-> exists n, (c n) = true)}
*)
  }.


#[refine]
Instance instance : AbstractKleenean Kleene.Kleenean := 
{
  true := Kleene.true;  
  false := Kleene.false;

  eqv := Kleene.eqv;
  apart := Kleene.apart;

  not := Kleene.not;
  impl := Kleene.impl;
  or:= Kleene.or;
  and := Kleene.and;

  distinct := Kleene.apart_sym _ _ Kleene.true_apart_false;
  defined_dec := Kleene.defined_dec;

  and_respectful := Kleene.and_respectful;
  and_up := Kleene.and_up;
  and_down := Kleene.and_down;
}.
Proof.
Qed.

End AbstractKleene.






Module ClassicalKleene.

Notation B := bool.
Notation Btrue := true.
Notation Bfalse := false.

Import Kleene.
Infix "==" := Kleene.eqv.


Definition ClassicalKleenean := Tribool.Tribool.

(* The Limited Principle of Omniscence *)
Definition LPO := forall p : N -> Prop, (forall n : N, {p n} + {~ p n}) ->
  { exists n : N, p n } + { forall n : N, ~ p n }.

Lemma eqv_true_or_indeterminate_or_false_dec : 
  LPO -> forall k : K, { k == true } + { k == indeterminate } + { k == false } .
Proof.
  intros lpo k.
  set (p := fun n => k n <> TBindt).
  assert (forall n, {p n} + {~ p n}) as Hpdec by (intro n; now apply Tribool.not_eq_dec).
  set (H := lpo p Hpdec).
  unfold p in H.
  destruct H as [Hni|Hi].
  - apply (constructive_indefinite_ground_description_nat) in Hni.
    2: exact Hpdec.
    destruct Hni as [i Hni].
    remember (k i) as ki. 
    rewrite -> Heqki in Hni.
    set (Hj := all_from_not_indt k i Hni).
    destruct ki.
    -- left; left. unfold eqv. exists i. rewrite <- Heqki in Hj. exact Hj. 
    -- clear Hj. rewrite <- Heqki in Hni. contradiction.
    -- right. unfold eqv. exists i. rewrite <- Heqki in Hj. exact Hj. 
  - left; right. unfold eqv. exists 0. intros j H0lej. 
    specialize Hi with j. apply Tribool.eq_dne in Hi. exact Hi.
Qed.

Definition to_classical (lpo : LPO) (k : Kleenean) : ClassicalKleenean :=
  let Hk := eqv_true_or_indeterminate_or_false_dec lpo k in
    match Hk with
    | inleft Hti =>
         match Hti with
         | left Ht => TBtru
         | right Hf => TBindt
         end
    | inright Hf => TBfls
    end
.

Lemma constant_eqv : forall {c1 c2 : TB}, constant c1 == constant c2 -> c1 = c2.
Proof. intros c1 c2 H. unfold eqv in H. destruct H as [i H]. exact (H i (Nat.le_refl i)). Qed.  

Lemma compare_with_constants : forall {k : K} {c1 c2 : TB}, k == constant c1 -> k == constant c2 -> c1 = c2.
Proof. intros k c1 c2 H1 H2. symmetry in H1. set (H := eqv_trans _ _ _ H1 H2). now apply constant_eqv. Qed.  

Theorem to_classical_bijection (lpo : LPO) : forall (k : Kleenean) (t : ClassicalKleenean), 
  k == constant t <-> to_classical lpo k = t.
Proof.
  intros k. unfold to_classical. split.
  - intro H. 
    set (Hk := eqv_true_or_indeterminate_or_false_dec lpo k).
    destruct Hk as [[H'|H']|H']; set (Htb := compare_with_constants H' H); assumption.
  - intro H.
    remember (eqv_true_or_indeterminate_or_false_dec lpo k) as Hk.
    destruct Hk as [[H'|H']|H']; rewrite <- H; exact H'.
Qed.

End ClassicalKleene.
