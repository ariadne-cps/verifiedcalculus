(******************************************************************************
 *  utilities/Words.v
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


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.


Section Words.

Definition Seq (X : Type) := nat -> X.

Definition agree_le {X} (n : nat) (u1 u2 : Seq X) :=
  forall m, m<=n -> u1 m = u2 m.
Definition agree_lt {X} (n : nat) (u1 u2 : Seq X) :=
  forall m, m< n -> u1 m = u2 m.

Definition agree {X} (n : nat) (u1 u2 : Seq X) :=
  forall m, m<n -> u1 m = u2 m.

Lemma agree_refl : forall {X} (n : nat) (u : Seq X),
  agree n u u.
Proof.
  unfold agree. intros X n u m Hmltn.
  reflexivity.
Qed.

Lemma agree_sym : forall {X} (n : nat) (u1 u2 : Seq X),
  agree n u1 u2 -> agree n u2 u1.
Proof.
  unfold agree. intros X n u1 u2 H m Hmltn.
  symmetry. exact (H m Hmltn).
Qed.

Lemma agree_trans : forall {X} (n : nat) (u1 u2 u3 : Seq X),
  agree n u1 u2 -> agree n u2 u3 -> agree n u1 u3.
Proof.
  unfold agree. intros X n u1 u2 u3 H12 H23 m Hmltn.
  transitivity (u2 m). exact (H12 m Hmltn). exact (H23 m Hmltn).
Qed.



Record Ordinal (n : nat) := {
    val :> nat;
    val_lt : val < n;
}.

Definition ord {n : nat} (m : nat) (p : m < n) : Ordinal n := {| val:=m; val_lt := p |}.

Lemma ordinal_eq : forall {n:nat} (k1 k2 : Ordinal n),
  k1.(val n) = k2.(val n) -> k1 = k2.
Proof.
  intros n k1 k2.
  destruct k1 as [k1 p1].
  destruct k2 as [k2 p2].
  simpl.
  intros H.
  revert p1 p2.
  rewrite <- H.
  intros p1 p2.
  rewrite (proof_irrelevance _ p1 p2).
  reflexivity.
Qed.

Lemma ord_eq : forall {n:nat} (k1 k2 : nat) (p1 : k1<n) (p2 : k2<n),
  k1 = k2 -> ord k1 p1 = ord k2 p2.
Proof.
  intros n k1 k2 p1 p2 H.
  unfold ord.
  apply ordinal_eq.
  exact H.
Qed.


Definition cast {A B : Type} (p : A = B) (a : A) : B :=
  match p in _ = E return E with | eq_refl => a end.



Definition Wrd (n : nat) (X : Type) := (Ordinal n) -> X.
Definition Wrds (X : Type) := forall n, Wrd n X.

Definition null_wrd {X : Type} : Wrd 0 X :=
  fun k => match PeanoNat.Nat.nlt_0_r k.(val 0) k.(val_lt 0) with end.

Lemma wrd_at : forall {X} {n:nat} (x : Wrd n X) (k1 k2 : Ordinal n),
  k1.(val n) = k2.(val n) -> x k1 = x k2.
Proof.
  intros X n x k1 k2 H.
  apply f_equal.
  exact (ordinal_eq _ _ H).
Qed.

Lemma wrd_at_eq : forall {X n k p1 p2} (w : Wrd n X), w (ord k p1) = w (ord k p2).
Proof. intros X n k p1 p2 w. f_equal. apply ord_eq. reflexivity. Qed.

Lemma wrd_eq : forall {X} {n} (x1 x2 : Wrd n X),
  (forall kp : Ordinal n, x1 kp = x2 kp) -> x1 = x2.
Proof.
  intros X n x1 x2 Hkp; apply functional_extensionality; intros kp; apply Hkp.
Qed.

Lemma wrd_eq' : forall {X} {n} (x1 x2 : Wrd n X),
  (forall k, forall (p : k<n), let kp:={| val:=k; val_lt:=p |} in x1 kp = x2 kp) -> x1 = x2.
Proof.
  intros X n x1 x2 Hkp; apply functional_extensionality; intros [k p]; apply Hkp.
Qed.

Lemma wrd_0_eq : forall {X} (w w' : Wrd 0 X), w = w'.
Proof. 
  intros X w w'. apply wrd_eq. intros kp. destruct kp as [k p].
  contradiction (Nat.nlt_0_r k). 
Qed.

Lemma wrd_1_eq : forall {X} (x1 x2 : Wrd 1 X),
  x1 = x2 <-> x1 (ord 0 Nat.lt_0_1) = x2 (ord 0 Nat.lt_0_1).
Proof.
  intros X x1 x2. split.
  intro He. rewrite -> He. reflexivity.
  intro H. apply wrd_eq. intros [k p].
  assert (k=0) as Hk. { exact (proj1 (Nat.lt_1_r k) p). }
  transitivity (x1 (ord 0 Nat.lt_0_1)).
  unfold ord. apply wrd_at. simpl. exact Hk.
  rewrite -> H.
  unfold ord. apply wrd_at. simpl. symmetry. exact Hk.
Qed.


Definition cast_wrd {X : Type} {m n : nat} (e : m = n) (w : Wrd m X) : Wrd n X :=
  match e in _ = k return Wrd k X with | eq_refl => w end.

Lemma cast_wrd_at : forall {X m n} (e : m = n) k p q (w : Wrd m X), 
  cast_wrd e w (ord k p) = w (ord k q).
Proof. intros X m n e k p q w. unfold cast_wrd. destruct e. apply wrd_at_eq. Qed. 

Lemma cast_wrd_at' : forall {X m n} (e : m = n) k q (w : Wrd m X), 
  cast_wrd e w (ord k q) = w (ord k (eq_ind n (fun m' : nat => k < m') q m (eq_sym e))).
Proof. intros X m n e q w. apply cast_wrd_at. Qed.

Lemma cast_wrd_eq : forall {X} {n n1 n2} (e1 : n1 = n) (e2 : n2 = n) (x1 : Wrd n1 X) (x2 : Wrd n2 X),
  (forall k, forall (p1 : k<n1), forall (p2 : k<n2),
    let kp1:={| val:=k; val_lt:=p1 |} in let kp2:={| val:=k; val_lt:=p2 |} in
      x1 kp1 = x2 kp2) -> cast_wrd e1 x1 = cast_wrd e2 x2.
Proof.
  intros X n n1 n2 e1 e2 x1 x2 Hkp.
  unfold cast_wrd.
  destruct e1. destruct e2.
  apply wrd_eq'.
  intros k p.
  exact (Hkp k p p).
Qed.

Lemma cast_wrd_id : forall {X n} (w : Wrd n X), cast_wrd (eq_refl n) w = w.
Proof. intros X n w. unfold cast_wrd. reflexivity. Qed. 

Lemma cast_wrd_id' : forall {X n} {e : n=n} (w : Wrd n X), cast_wrd e w = w.
Proof. 
  intros X n e w. 
  replace e with (eq_refl n) by (apply proof_irrelevance).
  exact (cast_wrd_id w).
Qed.

Lemma cast_wrd_id'' : forall {X} {n1 n2} (e : n1 = n2) (w1 : Wrd n1 X) (w2 : Wrd n2 X),
  (forall k, forall (p1 : k<n1), forall (p2 : k<n2), 
    let kp1:={| val:=k; val_lt:=p1 |} in let kp2:={| val:=k; val_lt:=p2 |} in 
      w1 kp1 = w2 kp2) -> cast_wrd e w1 = w2.
Proof.
  intros X n1 n2 e w1 w2 Hkp.
  replace (w2) with (cast_wrd (eq_refl n2) w2).
  apply cast_wrd_eq.
  exact Hkp.
  exact (cast_wrd_id' w2).
Qed.

Lemma cast_cast_wrd : forall {X l m n} (p:l=m) (q:m=n) (r:l=n) (w:Wrd l X),
  cast_wrd q (cast_wrd p w) = cast_wrd r w.
Proof.
  intros X l m n p q r w.
  set (wn := cast_wrd r w).
  destruct p. destruct q. simpl. 
  unfold wn.
  apply eq_sym.
  apply cast_wrd_id''.
  intros k p1 p2.
  apply wrd_at.  
  reflexivity.
Qed.

Lemma cast_cast_wrd' : forall {X l m n} (p:l=m) (q:m=n) (w:Wrd l X),
  cast_wrd q (cast_wrd p w) = cast_wrd (eq_trans p q) w.
Proof. intros X l m n p q w. apply cast_cast_wrd with (r:=eq_trans p q). Qed.

Lemma cast_wrd_inj : forall {X m n} (e : m = n) (w1 w2 : Wrd m X),
  cast_wrd e w1 = cast_wrd e w2 -> w1 = w2.
Proof. intros X m n  e w1 w2. unfold cast_wrd. destruct e. tauto. Qed.





Definition projw {X : Type} (n : nat) (xs : Seq X) : Wrd n X :=
  fun kp => xs kp.(val n).

Lemma projw_at : forall {X} (n : nat) (xs : Seq X) (kp : Ordinal n),
    (projw n xs) kp = xs kp.(val n).
Proof.
  intros X n xs kp. unfold projw. reflexivity. 
Qed.

Lemma agree_projw : forall {X} (n : nat) (u1 u2 : Seq X),
  agree n u1 u2 <-> projw n u1 = projw n u2.
Proof.
  intros X n u1 u2.
  unfold agree, projw.
  split.
  - intro H.
    apply functional_extensionality.
    intros [m p].
    simpl.
    exact (H m p).
  - intro H.
    unfold agree.
    intros m p.
    apply equal_f with (x:=ord m p) in H.
    exact H.
Qed.


Definition restr {X : Type} {n : nat} (m : nat) (p : m <= n) (xs : Wrd n X) : Wrd m X :=
  fun kp => let k:=kp.(val m) in let q:=kp.(val_lt m) in
    xs {| val:=k; val_lt:=PeanoNat.Nat.lt_le_trans kp m n q p; |}.

Lemma restr_at : forall {X} {n:nat} (x : Wrd n X),
  forall (m : nat) (p:m<=n), forall (k:nat) (q:k<m), (restr m p x) (ord k q) = x (ord k (Nat.lt_le_trans k m n q p)).
Proof.
  intros X n x m p k q.
  unfold restr.
  reflexivity.
Qed.

Lemma restr_id : forall {X} {n} (p : n<=n) (x : Wrd n X), restr n p x = x.
Proof.
  unfold restr.
  intros X n p x.
  apply wrd_eq.
  intros [k q].
  apply f_equal.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma restr_eq' : forall {X} {m n1 n2} (e : n1=n2) (p1 : m<=n1) (p2 : m<=n2) (x1 : Wrd n1 X) (x2 : Wrd n2 X), cast_wrd e x1 = x2 -> restr m p1 x1 = restr m p2 x2.
Proof.
  unfold restr.
  intros X m n1 n2 e p1 p2 x1 x2 H.
  apply wrd_eq.
  rewrite <- H.
  intros [k q].
  simpl.
  rewrite -> cast_wrd_at'.
  f_equal.
  apply ord_eq.
  reflexivity.
Qed.

Lemma restr_eq : forall {X} {m n} (p1 p2 : m<=n) (x : Wrd n X), restr m p1 x = restr m p2 x.
Proof.
  unfold restr.
  intros X m n p1 p2 x.
  apply wrd_eq.
  intros [k q].
  apply f_equal.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma lt_eq  {l m n : nat} : m<=n -> m=l -> l<=n. 
Proof. intros Hp He. rewrite <- He. exact Hp. Qed.
Lemma eq_lt  {l m n : nat} : l<=m -> n=m -> l<=n. 
Proof. intros Hp He. rewrite -> He. exact Hp. Qed.

Lemma cast_wrd_restr : forall {X} {l m n} (p : m<=n) (x : Wrd n X) (e : m=l), 
  cast_wrd e (restr m p x) =  restr l (lt_eq p e) x.
Proof.
  intros X l m n p x e.
  apply wrd_eq.
  intros [k q].
  unfold cast_wrd. destruct e.
  unfold restr.
  simpl.
  apply wrd_at.
  simpl.
  reflexivity.
Qed.

Lemma restr_cast_wrd : forall {X} {l m n} (p : l<=m) (x : Wrd n X) (e : n=m), 
  restr l p (cast_wrd e x) =  restr l (eq_lt p e) x.
Proof.
  intros X l m n p x e.
  apply wrd_eq.
  intros [k q].
  unfold cast_wrd. destruct e.
  unfold restr.
  simpl.
  apply wrd_at.
  simpl.
  reflexivity.
Qed.

Lemma cast_wrd_restr_id : forall {X} {m n} (p : m<=n) (x : Wrd n X) (e : m=n), 
  cast_wrd e (restr m p x) =  x.
Proof.
  intros X m n p x e.
  rewrite -> cast_wrd_restr.
  apply restr_id.
Qed.

Lemma restr_cast_wrd_id : forall {X} {m n} (p : m<=n) (x : Wrd m X) (e : m=n), 
  restr m p (cast_wrd e x) =  x.
Proof.
  intros X m n p x e.
  rewrite -> restr_cast_wrd.
  apply restr_id.
Qed.

Lemma restr_cast_wrd_eq : forall {X} {m n} (e : m=n) (p : n<=m) (x : Wrd m X), 
  restr n p x = cast_wrd e x.
Proof.
  intros X m n e.
  rewrite -> e.
  intros p x.
  rewrite -> restr_id.
  apply cast_wrd_id.
Qed.


Lemma restr_restr' : forall {X} {n} m p l q r (x : Wrd n X),
  restr l q (restr m p x) = restr l r x.
Proof.
  intros X n m p l q r x.
  apply wrd_eq.
  intros [k s].
  simpl.
  rewrite -> restr_at.
  rewrite -> restr_at.
  rewrite -> restr_at.
  apply wrd_at.
  reflexivity.
Qed.

Lemma restr_restr : forall {X} {n} m p l q (x : Wrd n X),
  restr l q (restr m p x) = restr l (Nat.le_trans l m n q p) x.
Proof. intros X n m p l q x. apply restr_restr'. Qed.


Definition cat {X : Type} {n : nat} : (Wrd n X) -> X -> (Wrd (S n) X) :=
  fun xr x => fun xs => let k := (xs.(val (S n))) in let pkltSn := xs.(val_lt (S n)) in
    let pklen : (k<=n) := proj1 (Nat.lt_succ_r k n) pkltSn in
      let pkltnorkeqn := Compare_dec.le_lt_eq_dec k n pklen in
        match pkltnorkeqn with | left pkltn => xr {| val:=k; val_lt:=pkltn |}
                               | right pklen => x
        end.

Lemma cat_tail : forall {X} {n} (xw : (Wrd n X)) (x : X) (m:nat) (Hmltn : m < n) {HmltSn : m < S n},
  cat xw x (ord m HmltSn) = xw (ord m Hmltn).
Proof.
  intros X n xw x m Hmltn HmltSn. unfold cat, ord. simpl.
  destruct (Compare_dec.le_lt_eq_dec m n _).
  - apply wrd_at. reflexivity.
  - assert (m<n) as H; [exact Hmltn|]. rewrite -> e in H. apply Nat.lt_irrefl in H. contradiction.
Qed.

Lemma cat_head' : forall {X} {n} (xw : (Wrd n X)) (x : X) {m : nat} (HmltSn : m < S n),
  m = n -> cat xw x (ord m HmltSn) = x.
Proof.
  intros X n xw x m HmltSn Hmeqn. unfold cat, ord. simpl.
  destruct (Compare_dec.le_lt_eq_dec m n _).
  - assert (m<n) as H; [exact l|]. rewrite -> Hmeqn in H. apply Nat.lt_irrefl in H. contradiction.
  - reflexivity.
Qed.

Lemma cat_head'' : forall {X} n (xw : Wrd n X) (x : X) (HnltSn : n < S n), 
  (cat xw x) (ord n HnltSn) = x.
Proof.
  intros X n xw x HnltSn. unfold cat. simpl.
  destruct (le_lt_eq_dec n n). 
  contradiction (Nat.lt_irrefl n). 
  reflexivity.
Qed.

Lemma cat_head : forall {X} n (xw : Wrd n X) (x : X), 
  (cat xw x) (ord n (Nat.lt_succ_diag_r n)) = x.
Proof.
  intros X n xw x. unfold cat. simpl.
  destruct (le_lt_eq_dec n n). contradiction (Nat.lt_irrefl n). reflexivity.
Qed.

Lemma cat_head_tail : forall {X n} (w : Wrd (S n) X), 
  cat (restr n (Nat.le_succ_diag_r n) w) (w (ord n (Nat.lt_succ_diag_r n))) = w.
Proof.
  intros X n w.
  apply wrd_eq. destruct kp as [k p].
  assert (k<=n) as p'. { apply Nat.lt_succ_r. exact p. }
  unfold cat.
  set (d := le_lt_eq_dec (val (S n) {| val := k; val_lt := p |}) n).
  destruct d.
  simpl.
  rewrite -> restr_at.
  apply wrd_at.
  reflexivity.
  simpl in e.
  apply wrd_at.
  simpl.
  exact (eq_sym e).
Qed.

Lemma cat_wrd_eqv : forall {X n1 n2} (e : n1 = n2) (wt1 : Wrd n1 X) (wt2 : Wrd n2 X) (wh : X),
  (forall k p1 p2, wt1 (ord k p1) = wt2 (ord k p2)) -> (forall k p1 p2, cat wt1 wh (ord k p1) = cat wt2 wh (ord k p2)).
Proof. 
  intros X n1 n2 e wt1 wt2 wh.
  intro H.
  unfold cat.
  intros k p1 p2.
  set (q1 := le_lt_eq_dec (ord k p1) n1).
  set (q2 := le_lt_eq_dec (ord k p2) n2).
  destruct q1 as [r1|e1].
  - destruct q2 as [r2|e2].
    -- apply H.
    -- assert False. rewrite -> e in r1. rewrite <- e2 in r1. 
       unfold ord in r1. simpl in r1. contradiction (Nat.lt_asymm k k). contradiction.
  - destruct q2 as [r2|e2].
    -- assert False. rewrite <- e in r2. rewrite <- e1 in r2. 
       unfold ord in r2. simpl in r2. contradiction (Nat.lt_asymm k k). contradiction.
    -- reflexivity.
Qed.


Definition splice {X} {n} (xw : Wrd (S n) X) (xe : Seq X) : Seq X :=
  fun k => match Compare_dec.le_lt_dec (S n) k with | left _ => xe (k-n) | right p => xw (ord k p) end.

Lemma splice_word_element : forall {X} {n} (xw : Wrd (S n) X) (xe : Seq X) (k:nat) (p:k<S n), 
  (splice xw xe) k = xw (ord k p).
Proof.
  intros X n xw xe k p. unfold splice.
  destruct (Compare_dec.le_lt_dec (S n) k).
  - set (Hfalse := Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ p l)).
    contradiction.
  - f_equal. apply ord_eq. reflexivity.
Qed.

Lemma splice_sequence_element : forall {X} {n} (xw : Wrd (S n) X) (xe : Seq X) (k:nat) (p:k>=S n), 
  (splice xw xe) k = xe (k-n).
Proof.
  intros X n xw xe k p. unfold splice.
  destruct (Compare_dec.le_lt_dec (S n) k).
  - reflexivity.
  - unfold ge in p. 
    set (Hfalse := Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ l p)).
    contradiction.
Qed.

Lemma splice_word : forall {X} {n} (xw : Wrd (S n) X) (xe : Seq X), 
  projw (S n) (splice xw xe) = xw.
Proof.
  intros X n xw xe.
  unfold splice, projw.
  apply functional_extensionality. intro kp.
  destruct (Compare_dec.le_lt_dec (S n) (val (S n) kp)).
  - destruct kp as [k p]. unfold val in l. 
    set (Hfalse := Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ p l)).
    contradiction.
  - destruct kp as [k p]. unfold val in l. 
    f_equal.
    apply ordinal_eq.
    simpl.
    reflexivity.
Qed.


Lemma splice_sequence : forall {X} {n} (xw : Wrd (S n) X) (xe : Seq X), 
  xw (ord n (Nat.lt_succ_diag_r n)) = (xe 0) -> 
    (fun k => (splice xw xe) (n+k)) = xe.
Proof.
  intros X n xw xe Hxn.
  unfold splice, projw.
  apply functional_extensionality. intro k.
  destruct (Compare_dec.le_lt_dec (S n) (n+k)).
  - rewrite -> Nat.add_comm.
    rewrite -> Nat.add_sub.
    reflexivity.
  - destruct k.
    rewrite <- Hxn. f_equal. apply ord_eq. exact (Nat.add_0_r n).
    assert (S n + k < S n + 0) as Hf. { rewrite -> Nat.add_succ_comm. rewrite -> Nat.add_0_r. exact l. }
    apply Nat.add_lt_mono_l in Hf.
    apply Nat.nlt_0_r in Hf.
    contradiction.
Qed.




Lemma projw_restr_eq : forall {X} (xs : Seq X) (m n : nat) (p:m <= n),
  projw m xs = restr m p (projw n xs).
Proof.
  intros X xs m n p.
  unfold projw, restr.
  apply functional_extensionality.
  intros k.
  f_equal.
Qed.

Lemma restr_cat_id : forall {X} {n} (xw : Wrd n X) (x:X) (p:n<=S n),
  restr n p (cat xw x) = xw.
Proof.
  intros X n xw x HnleSn.
  apply wrd_eq.
  intros [m Hmltn].
  rewrite -> restr_at.
  apply cat_tail.
Qed.

Definition is_prefix {X} {m n : nat} (xw' : Wrd m X) (xw : Wrd n X) :=
  match Compare_dec.le_lt_dec m n with | left p => xw' = restr m p xw | right _ => False end.


(* List-only functions. *)
Lemma length_cons : forall {X : Type} (a : X) (l : list X),
  length (cons a l) = S (length l).
Proof. intros X a l. auto. Qed.
  
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



(* Word and list conversions. *)
Fixpoint word_to_list {X n} : Wrd n X -> list X :=
  match n with 
  | O => fun _ => nil
  | S m' => fun (w : Wrd (S m') X) => 
      let p := Nat.lt_succ_diag_r m' in let q := Nat.le_succ_diag_r m' in
          cons (w (ord m' p)) (word_to_list (restr m' q w))
  end.

Fixpoint list_to_word {X} (xl : list X) : Wrd (length xl) X :=
  match xl with 
  | nil => null_wrd
  | cons xh xt => (cat (list_to_word xt) xh) 
  end.

Lemma word_to_list_succ : forall {X n} (w : Wrd (S n) X),
  word_to_list w = cons (w (ord n (Nat.lt_succ_diag_r n))) (word_to_list (restr n (Nat.le_succ_diag_r n) w)).
Proof.
  intros X n w. reflexivity.
Qed.

Lemma word_to_list_length : forall {X n} (w : Wrd n X),
  length (word_to_list w) = n.
Proof. 
  intros X n. induction n. 
  - intro w. reflexivity.
  - intro w. 
    rewrite -> word_to_list_succ.
    rewrite -> length_cons.
    f_equal.
    apply IHn.
Qed.

Lemma list_to_word_cons_cat : forall {X} (xh : X) (xt : list X),
  cat (list_to_word xt) xh = list_to_word (cons xh xt).
Proof.
  intros X xh xt. apply wrd_eq. reflexivity.
Qed.

Lemma word_to_list_cat_cons : forall {X} {n} (xh : X) (xt : Wrd n X),
  cons xh (word_to_list xt) = word_to_list (cat xt xh).
Proof.
  intros X n xh xt.
  rewrite -> word_to_list_succ.
  f_equal.
  symmetry.
  apply cat_head.
  rewrite -> restr_cat_id.
  reflexivity.
Qed.

Lemma cast_list_to_wrd_eq : forall {X} (l1 l2 : list X) (n : nat) (e1 : length l1 = n) (e2 : length l2 = n),
  l1 = l2 -> cast_wrd e1 (list_to_word l1) = cast_wrd e2 (list_to_word l2).
Proof. 
  intros X l1 l2 n. intros e1 e2 H. generalize e1 e2.
  rewrite -> H. intros el1 el2. apply cast_wrd_eq.
  intros k p1 p2 kp1 kp2. apply wrd_at_eq.
Qed.

Lemma cast_list_to_wrd_eq' : forall {X} (l1 l2 : list X) (e : length l1 = length l2),
  l1 = l2 -> cast_wrd e (list_to_word l1) = list_to_word l2.
Proof. 
  intros X l1 l2. intros e H. generalize e.
  rewrite -> H. intros el. apply cast_wrd_id''.
  intros k p1 p2 kp1 kp2. apply wrd_at_eq.
Qed.


Lemma list_to_word_to_list_id : forall {X} (xl : list X), 
  (word_to_list (list_to_word xl)) = xl.
Proof.
  induction xl as [|xh xt].
  - simpl. reflexivity.
  - rewrite <- IHxt.
    rewrite <- list_to_word_cons_cat.
    rewrite -> word_to_list_cat_cons. 
    rewrite -> IHxt.
    reflexivity.
Qed.

 
Lemma word_to_list_to_word_id' : forall {X n} (w : Wrd n X), 
  list_to_word (word_to_list w) = cast_wrd (eq_sym (word_to_list_length w)) w.
Proof.
  intros X n. induction n.
  - intro w. apply wrd_0_eq.
  - intro w. 
    set (wh := w (ord n (Nat.lt_succ_diag_r n))).
    set (wt := restr n (Nat.le_succ_diag_r n) w).
    replace w with (cat wt wh).
    assert (length (word_to_list (cat wt wh)) = length (cons wh (word_to_list wt))) as Hl. {
      rewrite -> length_cons. rewrite -> word_to_list_length, -> word_to_list_length. reflexivity. }
    replace (list_to_word (word_to_list (cat wt wh))) with (cast_wrd (eq_sym Hl) (list_to_word (cons wh (word_to_list wt)))).
    assert (length (cons wh (word_to_list wt)) = S (length (word_to_list wt))) as Hl'. {
      rewrite -> length_cons. reflexivity. }
    replace (list_to_word (cons wh (word_to_list wt))) with (cast_wrd (Hl') (cat (list_to_word (word_to_list wt)) wh)).
    rewrite -> (IHn wt).
    assert (length (word_to_list (cat wt wh)) = S n) as Hl''. {
      rewrite -> word_to_list_length. reflexivity. }
    apply (cast_wrd_inj Hl'').
    rewrite -> cast_cast_wrd'.
    rewrite -> cast_cast_wrd'.
    rewrite -> cast_cast_wrd'.
    apply cast_wrd_eq.
    intros k p1 p2.
    apply cat_wrd_eqv.
    apply word_to_list_length.
    intros k' p1' p2'.
    apply cast_wrd_at.
    
    rewrite -> list_to_word_cons_cat.
    apply cast_wrd_id''.
    intros k p1 p2 kp1 kp2. f_equal. apply ord_eq. reflexivity.

    apply cast_list_to_wrd_eq'.
    apply word_to_list_cat_cons.

    apply cat_head_tail.
Qed.

Lemma word_to_list_to_word_id : forall {X n} (w : Wrd n X), 
  cast_wrd (word_to_list_length w) (list_to_word (word_to_list w)) = w.
Proof.
  intros X n w. rewrite -> word_to_list_to_word_id'. 
  rewrite -> (cast_cast_wrd _ _ (eq_refl n)). 
  exact (cast_wrd_id w).
Qed.



Lemma proj_to_word_list : forall {X} (xs : nat -> X) (n1 n2 : nat) (e : length (proj n1 xs) = n2), 
  cast_wrd e (list_to_word (proj n1 xs)) = projw n2 xs.
Proof.
  intros X xs n1.
  induction n1.
  - intros n2 el.
    apply wrd_eq.
    intros kp. destruct kp as [k p]. assert False; [|contradiction]. rewrite <- el in p. rewrite -> length_proj in p. contradiction (Nat.nlt_0_r k).
  - intros Sln2 Sle2.
    assert (length (proj (S n1) xs) = S n1) as Sle1. { apply length_proj. }
    simpl. apply wrd_eq.  unfold projw.
    intros kp. destruct kp as [k p].
    assert (k <= n1) as p'. { apply (Nat.lt_succ_r k n1). rewrite <- Sle1, -> Sle2. exact p. } 
    apply le_lt_eq_dec in p'.
    destruct p' as [Hkltn|Hkeqn].
    -- simpl. 
       rewrite -> cast_wrd_at'.
       assert (length (proj n1 xs) = n1) as Hle1. { apply length_proj. }
       assert (k < length (proj n1 xs)) as Hkltln1. { rewrite -> Hle1. exact Hkltn. }
       rewrite -> (cat_tail (list_to_word (proj n1 xs)) (xs n1) _ Hkltln1).
       specialize (IHn1 n1 Hle1).
       assert (list_to_word (proj n1 xs) = cast_wrd (eq_sym Hle1) (projw n1 xs)) as IHn1'. { 
         rewrite <- IHn1. rewrite -> cast_cast_wrd'. remember (list_to_word (proj n1 xs)) as w1. 
         rewrite <- (cast_wrd_id w1). rewrite -> cast_cast_wrd'. apply cast_wrd_eq.
         intros k' p1 p2. apply wrd_at_eq. }
       rewrite -> IHn1'.
       apply cast_wrd_at'. 
    -- rewrite -> cast_wrd_at'. rewrite -> cat_head'. 
       --- rewrite <- Hkeqn. reflexivity. 
       --- rewrite -> length_proj. exact Hkeqn. 
Qed.

Lemma proj_to_word_list' : forall {X} (xs : nat -> X) (n : nat), 
  cast_wrd (length_proj xs n) (list_to_word (proj n xs)) = projw n xs.
Proof. intros X xs n. apply proj_to_word_list. Qed.

End Words.

