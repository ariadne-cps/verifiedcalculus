(******************************************************************************
 *  systems/nondeterministic_systems.v
 *
 *  Copyright 2023 Sacha L. Sindorf
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
Require Import List.
Require Import Ensembles.

Require Import Coq.Arith.PeanoNat.
Require Import EnsembleMonad.

Notation M := Ensemble.

(* Should be in Ensembles or EnsembleMonad *)
Definition subset {X} (s1 s2 : Ensemble X) : Prop :=
  forall x, element x s1 -> element x s2.

Record ordinal (n : nat) := {
    val :> nat;
    val_lt : val < n;
}.

Definition ord {n : nat} (m : nat) (p : m < n) : ordinal n := {| val:=m; val_lt := p |}.
Definition ord_S {n : nat} (m : nat) (p : m < n) : ordinal (S n) := {| val:=S m; val_lt := Arith_prebase.lt_n_S_stt m n p |}.
Definition ord_s {n : nat} (m : nat) (p : m < n) : ordinal (S n) := {| val:=m; val_lt := Nat.lt_lt_succ_r m n p |}.

Lemma ordinal_eq : forall {n:nat} (k1 k2 : ordinal n),
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

Definition Seq (X : Type) := nat -> X.
Definition Wrd (n : nat) (X : Type) := (ordinal n) -> X.
Definition Wrds (X : Type) := forall n, Wrd n X.

Lemma ordinal_at : forall {X} {n:nat} (x : Wrd n X) (k1 k2 : ordinal n),
  k1.(val n) = k2.(val n) -> x k1 = x k2.
Proof.
  intros X n x k1 k2 H.
  apply f_equal.
  exact (ordinal_eq _ _ H).
Qed.

Lemma wrd_eq : forall {X} {n} (x1 x2 : Wrd n X),
  (forall kp : ordinal n, x1 kp = x2 kp) -> x1 = x2.
Proof.
  intros X n x1 x2 Hkp; apply functional_extensionality; intros kp; apply Hkp.
Qed.

Lemma wrd_eq' : forall {X} {n} (x1 x2 : Wrd n X),
  (forall k, forall (p : k<n), let kp:={| val:=k; val_lt:=p |} in x1 kp = x2 kp) -> x1 = x2.
Proof.
  intros X n x1 x2 Hkp; apply functional_extensionality; intros [k p]; apply Hkp.
Qed.


Definition null {X : Type} : Wrd 0 X :=
  fun k => match PeanoNat.Nat.nlt_0_r k.(val 0) k.(val_lt 0) with end.

Definition proj {X : Type} (n : nat) (xs : Seq X) : Wrd n X :=
  fun kp => xs kp.(val n).

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

Lemma restr_restr : forall {X} {n} m p l q r (x : Wrd n X),
  restr l r x = restr l q (restr m p x).
Proof.
  intros X n m p l q r x.
  apply wrd_eq.
  intros [k s].
  simpl.
  rewrite -> restr_at.
  rewrite -> restr_at.
  rewrite -> restr_at.
  apply ordinal_at.
  reflexivity.
Qed.


Definition cat {X : Type} {n : nat} : (Wrd n X) -> X -> (Wrd (S n) X) :=
  fun xr x => fun xs => let k := (xs.(val (S n))) in let pkltSn := xs.(val_lt (S n)) in
    let pklen : (k<=n) := Arith_prebase.lt_n_Sm_le k n pkltSn in
      let pkltnorkeqn := Compare_dec.le_lt_eq_dec k n pklen in
        match pkltnorkeqn with | left pkltn => xr {| val:=k; val_lt:=pkltn |}
                               | right pklen => x
        end.

Lemma cat_tail : forall {X} {n} (xw : (Wrd n X)) (x : X) (m:nat) (Hmltn : m < n) {HmltSn : m < S n},
  cat xw x (ord m HmltSn) = xw (ord m Hmltn).
Proof.
  intros X n xw x m Hmltn HmltSn. unfold cat, ord. simpl.
  destruct (Compare_dec.le_lt_eq_dec m n _).
  - apply ordinal_at. reflexivity.
  - assert (m<n) as H; [exact Hmltn|]. rewrite -> e in H. apply Nat.lt_irrefl in H. contradiction.
Qed.

Lemma cat_head : forall {X} {n} (xw : (Wrd n X)) (x : X) {m : nat} (HmltSn : m < S n),
  m = n -> cat xw x (ord m HmltSn) = x.
Proof.
  intros X n xw x m HmltSn Hmeqn. unfold cat, ord. simpl.
  destruct (Compare_dec.le_lt_eq_dec m n _).
  - assert (m<n) as H; [exact l|]. rewrite -> Hmeqn in H. apply Nat.lt_irrefl in H. contradiction.
  - reflexivity.
Qed.

Definition apply {X Y} (f : X -> Y) (xs : M X) : M Y
  := fun y => exists x, xs x /\ f x = y.

Definition agree {X} (n : nat) (u1 u2 : Seq X) :=
  forall m, m<n -> u1 m = u2 m.

Lemma agree_sym : forall {X} (n : nat) (u1 u2 : Seq X),
  agree n u1 u2 -> agree n u2 u1.
Proof.
  unfold agree. intros X n u1 u2 H m Hmltn.
  apply eq_sym. exact (H m Hmltn).
Qed.

Lemma agree_proj : forall {X} (n : nat) (u1 u2 : Seq X),
  agree n u1 u2 <-> proj n u1 = proj n u2.
Proof.
  intros X n u1 u2.
  unfold agree, proj.
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


(*
Inductive system {UA UD X Y : Type} : Type :=
  | state_space_model (f:X->UA*UD->M X) (h:X->UA->Y) (e:M X)
.
*)

Inductive System {U X Y : Type} : Type :=
  | state_space_model (f:X->U->M X) (h:X->U->Y) (e:M X)
.

Definition Behaviour {U Y : Type} :=
  Seq U -> M (Seq Y).
Definition FiniteBehaviour {U Y : Type} :=
  forall {n : nat}, (Wrd (S n) U) -> M (Wrd (S n) Y).

Definition next {X} (F : X -> M X) (e : M X) (xl : list X) : M X :=
  match xl with | nil => e | cons x _ => F x end.

Definition trajectory {U X : Type}
  (f:X->U->M X) (e:M X) (u:nat->U) : M (Seq X) :=
    fun x => element (x 0) e /\ forall n, element (x (S n)) (f (x n) (u n)).

Definition signal {X U Y : Type }
  (h:X->U->Y)
  (x:nat->X)
  (u:nat->U)
  : nat -> Y := fun n => h (x n) (u n)
.

Definition behaviour {U Y X : Type}
  (s:@System U X Y)
  (u:Seq U)
  : M (Seq Y) :=
    match s with
    | state_space_model f h e =>
      Mlift (fun x => signal h x (fun n => u n)) (trajectory f e u)
    end
.

Definition finite_trajectory' {U X : Type} {n : nat}
  (f:X->U->M X) (e:M X) : (Wrd (S n) U) -> M (Wrd (S n) X) :=
    fun u x => element (x (ord 0 (Nat.lt_0_succ n))) e
      /\ forall m, forall p:m<n, element (x (ord_S m p)) (f (x (ord_s m p)) (u (ord_s m p))).

Definition finite_trajectory {U X : Type} {n : nat}
  (f:X->U->M X) (e:M X) (u:Wrd n U) : M (Wrd n X) := fun x =>
    let p := Compare_dec.zerop n in
      match p with | left q => True | right q => element (x (ord 0 q)) e end
  /\ forall m, forall q : (S m < n), let p:=Nat.lt_succ_l m n q in
       element (x (ord (S m) q)) (f (x (ord m p)) (u (ord m p))).

Definition finite_signal {X U Y : Type } {n : nat}
  (h:X->U->Y)
  (x:Wrd n X)
  (u:Wrd n U)
  : Wrd n Y := fun n => h (x n) (u n)
.

Definition finite_behaviour {U X Y : Type}
  (s:@System U X Y) {n : nat} : (Wrd n U) -> M (Wrd n Y) :=
    match s with
    | state_space_model f h e =>
        fun u => apply (fun x => finite_signal h x u) (finite_trajectory f e u)
    end.

Definition infinite_behaviour_from_finite {U Y : Type}
  (bw : forall [n : nat], Wrd n U -> M (Wrd n Y)) : Seq U -> M (Seq Y) :=
    fun u y => forall n, element (proj n y) (bw (proj n u)).

Definition finite_behaviour_from_infinite {U Y : Type}
  (bs : Seq U -> M (Seq Y)) : forall [n : nat], Wrd n U -> M (Wrd n Y) :=
    fun (n:nat) u y => exists us ys, proj n us = u /\ proj n ys = y /\ element ys (bs us).

Definition is_infinite_behaviour {U Y : Type}
  (bw : forall {n : nat}, Wrd n U -> M (Wrd n Y))
  (bs : Seq U -> M (Seq Y))
  := forall (u : Seq U) (y : Seq Y),
       element y (bs u) <-> forall n, element (proj n y) (bw (proj n u)).

Proposition infinite_behaviour_superset :
  forall {U Y} b, forall u,
  subset (b u) (@infinite_behaviour_from_finite U Y (finite_behaviour_from_infinite b) u).
Proof.
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  intros U Y b u y H n.
  exists u, y.
  split. reflexivity. split. reflexivity. exact H.
Qed.

Proposition finite_behaviour_subset :
  forall {U Y} (b : forall [n : nat], Wrd n U -> M (Wrd n Y)), forall n, forall u,
  subset (@finite_behaviour_from_infinite U Y (infinite_behaviour_from_finite b) n u) (b u).
Proof.
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  intros U Y b.
  intros n u y.
  intro H.
  destruct H as [us [ys [Hu [Hy Hb]]]].
  rewrite <- Hu, <- Hy.
  exact (Hb n).
Qed.

Example finite_behaviour_not_superset :
  exists {U Y} (b : forall [n : nat], Wrd n U -> M (Wrd n Y)), exists n, exists u,
  not (subset (b u) (@finite_behaviour_from_infinite U Y (infinite_behaviour_from_finite b) n u)).
Proof.
  exists bool. exists bool.
  set (b := fun (n : nat) (u y : Wrd n bool) => n < 2).
  set (n := 1).
  set (u := fun (u : ordinal 1) => false).
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  exists b.
  exists n.
  exists u.
  intro H.
  assert (b n u u) as Hbu. { unfold b, n, u. auto. }
  specialize (H u Hbu).
  destruct H as [us [ys H]].
  destruct H as [_ [_ H]].
  specialize (H 2).
  unfold b in H.
  exact ((Nat.lt_irrefl 2) H).
Qed.

Example infinite_behaviour_not_subset :
  exists {U Y} b u, not (subset (@infinite_behaviour_from_finite U Y (finite_behaviour_from_infinite b) u) (b u)).
Proof.
  exists bool. exists bool.
  set (b := fun (u y : Seq bool) => (forall n, u n = y n) /\ not (forall n, u n = false)).
  set (u0 := fun (n : nat) => false).
  exists b.
  exists u0.
  unfold infinite_behaviour_from_finite, finite_behaviour_from_infinite.
  unfold subset, element.
  intros Hn.
  specialize (Hn u0).
  apply Hn.
  - intro n.
    set (u := fun (k : nat) => if (k <? n) then false else true).
    exists u, u.
    assert (proj n u = proj n u0) as Hp. {
      apply agree_proj. unfold agree. unfold u, u0.
      intros m Hmltn.
      apply Nat.ltb_lt in Hmltn.
      rewrite -> Hmltn.
      reflexivity.
    }
    split. exact Hp. split. exact Hp.
    unfold b.
    split.
    -- reflexivity.
    -- intros Ht.
       specialize (Ht n).
       unfold u in Ht.
       rewrite -> Nat.ltb_irrefl in Ht.
       discriminate Ht.
  - unfold u0.
    reflexivity.
Qed.



Fixpoint lproj {X:Type} (n : nat) (xs : Seq X) : list X :=
  match n with
    | O => nil
    | S n' => cons (xs n') (lproj n' xs)
  end.

Definition infinite_causal {U Y : Type}
  (b : (Seq U) -> M (Seq Y)) : Prop :=
    forall n, forall u1 u2 : Seq U, agree n u1 u2 ->
      apply (proj n) (b u1) = apply (proj n) (b u2).

Definition finite_prefix_conform {U Y : Type}
  (b : forall {n:nat}, Wrd n U -> M (Wrd n Y)) :=
     forall (n:nat) (u : Wrd n U) (m:nat) (p:m<=n),
       subset
           (apply (fun u => restr m p u) (b u))
           (b (restr m p u)).

Definition finite_causal' {U Y : Type}
  (b : forall {n:nat}, Wrd n U -> M (Wrd n Y)) :=
     forall n, forall u : Wrd (S n) U,
       let p : n <= S n := (Nat.le_succ_diag_r n) in
         subset
           (apply (fun u => restr n p u) (b u))
           (b (restr n p u)).

Definition causal {U Y : Type}
  (bs : Seq U -> M (Seq Y)) : Prop :=
    exists bw : forall n, Wrd n U -> M (Wrd n Y),
      finite_prefix_conform bw /\ is_infinite_behaviour bw bs.


(* Probably not true, since infinite causal requires trajectory to exist (non-blocking). *)
Proposition prefix_conform_implies_infinite_causal :
  forall {U Y} (b : Seq U -> M (Seq Y)), causal b -> infinite_causal b.
Proof.
  unfold causal, finite_prefix_conform, infinite_causal, is_infinite_behaviour.
  intros U Y bs.
  intros [bw Hc].
  assert (forall n u1 u2, agree n u1 u2 -> subset (apply (proj n) (bs u1)) (apply (proj n) (bs u2))) as Hic. {
    intros n u1 u2 Hu.
    unfold subset, apply, element.
    intros yw.
    intros [y1 Hy1].
    set (uw := proj n u1).
      assert (exists m, S m = n) as Hn. { admit. }
      destruct Hn as [m Hm].
    destruct Hc as [Hfc Hib].
    unfold subset, apply in Hfc.
    assert (exists y2 : Wrd (S n) Y, bw (S n) (proj (S n) u2) y2 /\ restr n (Nat.le_succ_diag_r n) y2 = yw) as IH. {
      set (uw2 := proj (S n) u2).
      specialize (Hfc n u1).
      unfold element in Hfc.
Admitted.

Definition finite_input_nontrivial {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)) :=
  exists n, exists (u : Wrd n U), exists y, element y (b u).

Definition finite_input_enabling {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)) :=
  forall (n:nat) (u : Wrd n U), exists y, element y (b u).

Definition finite_input_accepting {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)) :=
  forall {n:nat} (u : Wrd n U), forall (m:nat) (p:m<=n), let uw := restr m p u in
    (exists yw : Wrd m Y, element yw (b uw))
      /\ forall yw : Wrd m Y,
           element yw (b uw)
             -> exists y, element y (b u) /\ yw = restr m p y.

Lemma proj_restr : forall {X} (xs : Seq X) (m n : nat) (p:m <= n),
  proj m xs = restr m p (proj n xs).
Proof.
  intros X xs m n p.
  unfold proj, restr.
  apply functional_extensionality.
  intros k.
  f_equal.
Qed.

Proposition finite_behaviour_prefix_conform :
  forall {U X Y} (s : @System U X Y),
    finite_prefix_conform (@finite_behaviour U X Y s).
Proof.
  unfold finite_behaviour, finite_prefix_conform.
  intros U X Y s.
  destruct s as (f,h,e).
  intros n ue m Hmlen.
  unfold subset, apply, element.
  intros yw [ye Hye].
  destruct Hye as [[xe [Hxe Hye]] Hry].
  exists (restr m Hmlen xe).
  remember (restr m Hmlen ue) as uw.
  split.
  - unfold finite_trajectory in *.
    split.
    destruct Hxe as [Hxe _].
    destruct (Compare_dec.zerop m) as [Hmeq0|H0ltm].
    -- trivial.
    -- destruct (Compare_dec.zerop n) as [Hneq0|H0ltn].
       --- assert (0 < n) as H0. { exact (Nat.lt_le_trans 0 m n H0ltm Hmlen). }
           rewrite -> Hneq0 in H0. apply Nat.lt_irrefl in H0.
           contradiction.
       --- rewrite -> restr_at.
           replace (Nat.lt_le_trans 0 m n H0ltm Hmlen) with H0ltn; [|apply proof_irrelevance].
           exact Hxe.
     -- destruct Hxe as [_ Hxe].
        intros l HSlltm.
        assert (S l < n) as HSlltn. { exact (Nat.lt_le_trans _ _ _ HSlltm Hmlen). }
        specialize (Hxe l HSlltn).
        assert (l < n) as Hlltn. { exact (Nat.lt_trans l (S l) n (Nat.lt_succ_diag_r l) HSlltn). }
        replace (Nat.lt_succ_l l n HSlltn) with Hlltn in Hxe; [|apply proof_irrelevance].
        rewrite -> Hequw. rewrite -> restr_at, -> restr_at, -> restr_at.
        replace (Nat.lt_le_trans (S l) m n HSlltm Hmlen) with HSlltn; [|apply proof_irrelevance].
        replace (Nat.lt_le_trans l m n (Nat.lt_succ_l l m HSlltm) Hmlen) with Hlltn; [|apply proof_irrelevance].
        exact Hxe.
  - set (xw := restr m Hmlen xe).
    rewrite <- Hry, <- Hye.
    unfold finite_signal.
    apply wrd_eq.
    intros [k Hkltm].
    rewrite -> restr_at.
    f_equal.
    rewrite -> Hequw.
    rewrite -> restr_at.
    reflexivity.
Qed.

Lemma finite_trajectory_cons :
  forall {U X} (f : X -> U -> M X) (e : M X) {n:nat} (u : Wrd (S (S n)) U) (x : Wrd (S n) X) (xSn : X),
    let HSnleSSn := Nat.le_succ_diag_r (S n) in
    let HnltSn := Nat.lt_succ_diag_r n in
    let HnltSSn := Nat.lt_le_trans _ _ _ HnltSn HSnleSSn in
    finite_trajectory f e (restr (S n) HSnleSSn u) x ->
      f (x (ord n HnltSn)) (u (ord n HnltSSn)) xSn ->
        finite_trajectory f e u (cat x xSn).
Proof.
  intros U X f e n u x xSn.
  intros HSnleSSn HnltSn HnltSSn.
  unfold finite_trajectory.
  intros [Hx0 Hxs] Hxf.
  simpl in *.
  split.
  - unfold cat. simpl. unfold ord in Hx0. exact Hx0.
  - intros m HSmltSSn.
    assert (S m < S n \/ S m = S n) as Hmn. {
      apply Nat.le_lteq; apply (Nat.lt_succ_r (S m) (S n)); exact HSmltSSn. }
    assert (S m <= S m) as HSmleSm; [exact (Nat.le_refl (S m))|].
    destruct Hmn as [HSmltSn|HSmeqSn].
    -- assert (forall k p q, (k<=S m) -> cat x xSn (ord k p) = x (ord k q)) as Hxk. {
         intros k p q Hk.
         unfold cat. simpl.
         destruct (Compare_dec.le_lt_eq_dec k (S n) (Arith_prebase.lt_n_Sm_le k (S n) p)).
         --- unfold ord. apply ordinal_at. simpl. reflexivity.
         --- assert (k < S n) as H; [exact q|].
             rewrite -> e0 in H. apply Nat.lt_irrefl in H. contradiction.
       }
       rewrite -> (cat_tail x xSn (S m) HSmltSn).
       assert (m < S n) as HmltSn; [exact (Nat.lt_succ_l _ _ HSmltSn)|].
       rewrite -> (cat_tail x xSn m HmltSn).
       assert (m < S (S n)) as HmltSSn. exact (Nat.lt_succ_l _ _ HSmltSSn).
       assert (m <= S m) as HmleSm. exact (Nat.le_succ_diag_r m).
       replace (Nat.lt_succ_l m (S (S n)) HSmltSSn) with HmltSSn;
         [|apply proof_irrelevance].
       specialize (Hxs m HSmltSn).
       replace (Nat.lt_succ_l m (S n) HSmltSn) with HmltSn in Hxs;
         [|apply proof_irrelevance].
       rewrite -> restr_at in Hxs.
       replace ((Nat.lt_le_trans m (S n) (S (S n)) HmltSn HSnleSSn)) with HmltSSn in Hxs;
         [|apply proof_irrelevance].
       exact Hxs.
    -- assert (n=m) as Hneqm. { injection HSmeqSn. apply eq_sym. }
       replace (cat x xSn (ord (S m) HSmltSSn)) with xSn.
       replace (cat x xSn (ord m (Nat.lt_succ_l m (S (S n)) HSmltSSn))) with
         (x (ord n HnltSn)).
       replace (u (ord m (Nat.lt_succ_l m (S (S n)) HSmltSSn))) with
         (u (ord n HnltSSn)).
       exact Hxf.
       --- apply ordinal_at; simpl; exact Hneqm.
       --- assert (m < S (S n)) as HmltSSn; [exact (Nat.lt_succ_l m (S (S n)) HSmltSSn)|].
           assert (m < S n) as HmltSn; [rewrite <- Hneqm; exact (Nat.lt_succ_diag_r n)|].
           replace (Nat.lt_succ_l m (S (S n)) HSmltSSn) with HmltSSn;  [|apply proof_irrelevance].
           rewrite -> (cat_tail _ _ m HmltSn).
           apply ordinal_at.
           simpl.
           exact Hneqm.
       --- rewrite -> (cat_head _ _ _ HSmeqSn).
           reflexivity.
Qed.

Lemma finite_signal_cons :
  forall {U X Y} (h : X -> U -> Y) {n:nat} (u : Wrd (S n) U) (x : Wrd (S n) X) (p:n<S n) (q:n<=S n),
    finite_signal h x u = cat (finite_signal h (restr n q x) (restr n q u)) (h (x (ord n p)) (u (ord n p))).
Proof.
  intros U X Y h n u x HnltSn HnleSn.
  apply wrd_eq.
  intros [m HmltSn].
  assert (m<n \/ m=n) as Hm. {
    apply Nat.le_lteq; apply Nat.lt_succ_r; exact HmltSn. }
  unfold finite_signal.
  destruct Hm as [Hmltn|Hmeqn].
  - rewrite -> (cat_tail _ _ _ Hmltn).
    f_equal.
    -- rewrite -> restr_at. apply ordinal_at. unfold ord. reflexivity.
    -- rewrite -> restr_at.
       apply ordinal_at. unfold ord. reflexivity.
  - rewrite -> cat_head; [|exact Hmeqn].
    f_equal.
    -- apply ordinal_at. simpl. exact Hmeqn.
    -- apply ordinal_at. simpl. exact Hmeqn.
Qed.


Lemma restr_cons : forall {X} {n} (xw : Wrd n X) (x:X) (p:n<=S n),
  restr n p (cat xw x) = xw.
Proof.
  intros X n xw x HnleSn.
  apply wrd_eq.
  intros [m Hmltn].
  rewrite -> restr_at.
  apply cat_tail.
Qed.



Definition nonblocking {U X Y} (s : @System U X Y) :=
  match s with | state_space_model f _ e => inhabited e /\ forall x u, inhabited (f x u) end.

Proposition nonblocking_implies_finite_behaviour_input_accepting :
  forall {U X Y} (s : @System U X Y),
    nonblocking s -> finite_input_accepting (@finite_behaviour U X Y s).
Proof.
  unfold finite_behaviour, finite_input_accepting, nonblocking.
  intros U X Y s.
  destruct s as (f,h,e).
  unfold subset, inhabited, apply, element.
  intros [Hnb0 Hnbs].
  intros n ue m Hmlen.
  split.
  - destruct m as [|m].
    -- exists (@null Y).
       exists (@null X).
       split.
       --- unfold finite_trajectory. simpl. split. trivial.
           intros m HSmlt0.
           apply Nat.nlt_0_r in HSmlt0 as HF. contradiction.
       --- unfold finite_signal, null, restr.
           apply functional_extensionality.
           intros [k Hklt0].
           apply Nat.nlt_0_r in Hklt0 as HF. contradiction.
    -- induction m.
       destruct Hnb0 as [x0 Hx0].
       assert (0<n) as H0ltn. { rewrite <- Nat.le_succ_l. exact Hmlen. }
       set (u0 := ue (ord 0 H0ltn)).
       set (y0 := h x0 u0).
       set (yw := (fun _ => y0) : (Wrd 1 Y)).
       set (xw := (fun _ => x0) : (Wrd 1 X)).
       set (uw := restr 1 Hmlen ue).
       exists yw, xw.
       split.
       --- unfold finite_trajectory.
           simpl.
           split.
           ---- unfold xw. exact Hx0.
           ---- intros m HSmlt1.
                apply (proj2 (Nat.succ_lt_mono m 0)) in HSmlt1 as Hmlt0.
                apply Nat.nlt_0_r in Hmlt0. contradiction.
       --- unfold finite_signal.
           apply functional_extensionality.
           intros [z Hzlt1].
           unfold xw, uw, yw.
           rewrite -> restr_at.
           assert (0=z) as Hz0. { apply eq_sym. apply Nat.lt_1_r. exact Hzlt1. }
           replace (ue (ord z (Nat.lt_le_trans z 1 n Hzlt1 Hmlen))) with (ue (ord 0 H0ltn)).
           unfold y0, u0.
           reflexivity.
           apply ordinal_at.
           simpl.
           exact Hz0.
       --- rename Hmlen into HSSmlen.
           assert (S m < n) as HSmltn. { admit. }
           assert (S m <= n) as HSmlen. { admit. }
           assert (m < n) as Hmltn. { admit. }
           assert (m < S m) as HmltSm. { admit. }
           specialize (IHm HSmlen).
           destruct IHm as [yw [xw [Hxw Hyw]]].
           set (xm := xw (ord m HmltSm)).
           set (um := ue (ord m Hmltn)).
           set (uSm := ue (ord (S m) HSmltn)).
           destruct (Hnbs xm um) as [xSm HxSm].
           set (ySm := h xSm uSm).
           set (xe := cat xw xSm).
           set (ye := cat yw ySm).
           exists ye, xe.
           split.
           ---- unfold xe.
                apply finite_trajectory_cons.
                ----- replace (restr (S m) (Nat.le_succ_diag_r (S m)) (restr (S (S m)) HSSmlen ue)) with (restr (S m) HSmlen ue).
                      apply Hxw.
                      apply functional_extensionality.
                      intros [k p].
                      rewrite -> restr_at.
                      rewrite -> restr_at.
                      rewrite -> restr_at.
                      apply f_equal.
                      apply ord_eq.
                      reflexivity.
                ----- replace (Nat.lt_succ_diag_r m) with HmltSm;
                        [|apply proof_irrelevance].
                      rewrite -> restr_at.
                      replace (ue (ord m _)) with (ue (ord m Hmltn)).
                      exact HxSm.
                      unfold ord. apply ordinal_at. simpl. reflexivity.
           ---- assert (S m <= S m) as HSmleSm. admit.
                assert (m <= S m) as HmleSm. admit.
                assert (S (S m) <= S (S m)) as HSSmleSSm. admit.
                assert (S m <= S (S m)) as HSmleSSm. admit.
                rewrite -> (finite_signal_cons h _ xe) with (p:=HSSmleSSm) (q:=HSmleSSm).
                unfold ye.
                f_equal.
                f_equal.
                rewrite <- Hyw.
                f_equal.
                ----- apply restr_cons.
                ----- apply functional_extensionality.
                      intros [k p].
                      rewrite -> restr_at.
                      rewrite -> restr_at.
                      rewrite -> restr_at.
                      apply ordinal_at.
                      reflexivity.
                ----- unfold ySm.
                      f_equal.
                      unfold xe.
                      apply cat_head.
                      reflexivity.
                      unfold uSm.
                      rewrite -> restr_at.
                      apply ordinal_at.
                      reflexivity.
  - admit.
Admitted.

Proposition finite_input_accepting_implies_input_enabling :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_accepting (@b) -> finite_input_enabling (@b).
Proof.
  unfold finite_input_accepting, finite_input_enabling.
  unfold subset, apply, element.
  intros U Y b Hia.
  intros n u.
  specialize (Hia n u n (Nat.le_refl n)).
  destruct Hia as [[y Hy] _].
  rewrite -> restr_id in Hy.
  exists y.
  exact Hy.
Qed.

Lemma finite_input_accepting_extension :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_accepting (@b) ->
      forall {n} (ue : Wrd (S n) U) (yw : Wrd n Y),
        let p := (Nat.le_succ_diag_r n) in
        element yw (b (restr n p ue)) ->
          exists ye : Wrd (S n) Y,
           restr n p ye = yw /\ element ye (b ue).
Proof.
  unfold finite_input_accepting.
  intros U Y b Hia.
  intros n ue yw Hbyw.
  remember (Nat.le_succ_diag_r n) as p.
  remember (restr n p ue) as uw.
  specialize (Hia (S n) ue n p).
  destruct Hia as [_ Hia].
  rewrite <- Hequw in Hia.
  specialize (Hia yw Hbyw).
  destruct Hia as [ye [Hbye Hyw]].
  exists ye.
  split.
  apply eq_sym.
  exact Hyw.
  exact Hbye.
Qed.


Lemma finite_input_accepting_trajectory :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_accepting (@b) ->
      forall (us : Seq U) {n} (yw : Wrd n Y),
        element yw (b (proj n us)) ->
          exists ys : Seq Y,
           proj n ys = yw /\ forall m (p:n<=m), element (proj m ys) (b (proj m us)).
(*
          exists ys : forall m, n<=m -> Wrd m Y,
            forall m, (p:n<=m), element (ys m p) (b (proj m us)) /\ restr m exists ys : Seq Y, proj n ys = yw /\ forall m, n<=m -> element (proj m ys) (b (proj m us)).
*)
Proof.
  unfold finite_input_accepting.
  intros U Y b Hia.
  intros us n yw Hbyw.
  set (p := Nat.le_succ_diag_r n).
  remember (proj (S n) us) as ue.
  remember (restr n p ue) as uw.
  assert (exists ye : Wrd (S n) Y, restr n p ye = yw /\ element ye (b (S n) (proj (S n) us))) as Hs. {
    specialize (Hia (S n) ue n p).
    destruct Hia as [Hie Hia].

    assert (proj n us = uw) as Huw. {
      rewrite -> Hequw, -> Heque. apply proj_restr. }
    rewrite <- Hequw in Hie, Hia.
    rewrite <- Heque.
    rewrite -> Huw in Hbyw.
    specialize (Hia yw Hbyw).
    destruct Hia as [ye [Hbye Hyw]].
    exists ye.
    split.
    apply eq_sym.
    exact Hyw.
    exact Hbye.
  }
Admitted.


Proposition finite_input_accepting_implies_causal :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_accepting (@b) -> finite_prefix_conform (@b).
Proof.
  unfold finite_input_accepting, finite_prefix_conform.
  unfold subset, apply, element.
  intros U Y b Hia.
(*
  intros n ue y [ye [Hbye Hpye]].
  set (HnleSn := Nat.le_succ_diag_r n).
  remember (restr n HnleSn ue) as u.
  specialize (Hia (S n) ue n HnleSn).
  rewrite <- Hequ in Hia.
  destruct Hia as [Hie Hia].
  destruct Hie as [yw Hyw].

  specialize (Hia yw Hyw).
  destruct Hia as [ywe Hywe].

  rewrite -> Hpye in Hia.
*)
Admitted.

Proposition finite_causal_and_input_enabling_implies_input_accepting :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_prefix_conform (@b) -> finite_input_enabling (@b) -> finite_input_accepting (@b).
Proof.
  unfold finite_input_accepting, finite_input_enabling, finite_prefix_conform.
  unfold subset, apply, element.
  intros U Y b Hc Hie.
  intros n ue m p.
  remember (restr m p ue) as u.
  split.
  - exact (Hie m u).
  - intros y Hbuy.
    specialize (Hc n ue m p y).
    admit.
(*
  set (HnleSn := Nat.le_succ_diag_r n).
  remember (restr n HnleSn ue) as u.
  specialize (Hia (S n) ue n HnleSn).
  rewrite <- Hequ in Hia.
  destruct Hia as [Hie Hia].
  destruct Hie as [yw Hyw].

  specialize (Hia yw Hyw).
  destruct Hia as [ywe Hywe].

  rewrite -> Hpye in Hia.
*)
Admitted.




Definition input_nontrivial {U Y} (b : Seq U -> M (Seq Y)) :=
  exists u, exists y, element y (b u).

Definition input_enabling {U Y} (b : Seq U -> M (Seq Y)) :=
  forall (u : Seq U), exists y, element y (b u).

Definition input_accepting' {U Y} (b : Seq U -> M (Seq Y)) :=
  forall n, forall u1 u2, agree n u1 u2 ->
    forall y1, exists y2, element y2 (b u2) /\ (element y1 (b u1) -> agree n y1 y2).

Definition partial_behaviours {U Y} (b : Seq U -> M (Seq Y)) {n} (uw : Wrd n U) : M (Wrd n Y) :=
  fun yw => exists us ys, proj n us = uw /\ proj n ys = yw /\ element ys (b us).

Definition input_accepting {U Y} (b : Seq U -> M (Seq Y)) :=
  forall u, forall n, let uw := proj n u in
    (exists yw : Wrd n Y, element yw (partial_behaviours b uw))
      /\ forall yw : Wrd n Y,
           element yw (partial_behaviours b uw)
             -> exists y, element y (b u) /\ yw = proj n y.

Proposition input_accepting_implies_input_enabling :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    input_accepting b -> input_enabling b.
Proof.
  unfold input_accepting, input_enabling.
  intros U Y b Hia.
  intro u.
  specialize (Hia u 0).
  destruct Hia as [[yw Hyw] Hy].
  specialize (Hy yw Hyw).
  destruct Hy as [y Hy].
  exists y.
  exact (proj1 Hy).
Qed.

Proposition input_accepting_implies_infinite_causal :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    input_accepting b -> infinite_causal b.
Proof.
  unfold input_accepting, infinite_causal.
  intros U Y b Hia.
  intros n u1 u2 Hu12.
  apply ensemble_equal.
  intro yw1.
  revert Hu12. revert u1 u2.
  assert (forall u1 u2, agree n u1 u2 -> element yw1 (apply (proj n) (b u1)) -> element yw1 (apply (proj n) (b u2))) as H. {
    intros u1 u2 Hu12.
    unfold apply.
    intro Hy1.
    destruct Hy1 as [y1 [Hby1 Hpy1]].
    specialize (Hia u2 n).
    destruct Hia as [_ Hia].
    unfold partial_behaviours in Hia.
    unfold element in *.
    specialize (Hia yw1).
    assert ((exists y2 : Seq Y, b u2 y2 /\ yw1 = proj n y2) -> (exists x : Seq Y, b u2 x /\ proj n x = yw1)) as Hs. {
      intros [y2 Hy2]. exists y2. split. exact (proj1 Hy2). apply (eq_sym). exact (proj2 Hy2).
    }
    apply Hs.
    apply Hia.
    exists u1, y1.
    split; [|split].
    - exact (proj1 (agree_proj n u1 u2) Hu12).
    - exact Hpy1.
    - exact Hby1.
  }
  intros u1 u2 Hu12.
  split.
  - apply H. exact Hu12.
  - apply H. apply agree_sym. exact Hu12.
Qed.

Proposition infinite_causal_and_input_enabling_implies_input_accepting :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    infinite_causal b -> input_enabling b -> input_accepting b.
Proof.
  unfold infinite_causal, input_enabling, input_accepting.
  unfold element, partial_behaviours.
  intros U Y b Hic Hie.
  intros u n.
  split.
  - specialize (Hie u).
    destruct Hie as [y Hy].
    exists (proj n y).
    exists u, y.
    split; [|split].
    -- reflexivity.
    -- reflexivity.
    -- exact Hy.
  - intros yw Hyw.
    destruct Hyw as [us [ys Hyw]].
    destruct Hyw as [Hus [Hys Hbus]].
    specialize (Hic n u us).
    apply agree_proj in Hus.
    apply agree_sym in Hus.
    specialize (Hic Hus).
    unfold apply in Hic.
    apply equal_f with (x:=yw) in Hic.
    assert (exists y : Seq Y, b u y /\ proj n y = yw) as Hy. {
      rewrite -> Hic.
      exists ys.
      split. exact Hbus. exact Hys.
    }
    destruct Hy as [y [Hby Hpy]]. exists y. split. exact Hby. apply eq_sym. exact Hpy.
Qed.

Proposition input_accepting_implies_causal :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    input_accepting b -> infinite_causal b -> causal b.
Proof.
Admitted.

Proposition causal_implies_infinite_causal :
  forall {U Y} (b : Seq U -> M (Seq Y)),
    causal b -> infinite_causal b.
Proof.
Admitted.

(* Show that the behaviour of a system satisfies the weaker definition of causal. *)
Lemma behaviour_causal :
  forall {U X Y : Type}
    (s : @System U X Y),
      causal (behaviour s).
Proof.
(*
  intros UA UD X Y. intro s. unfold mixed_causal.
  intros u u'. intro n.
  intros H0 H1.
  destruct s as (f,h,e).
  unfold behaviour. unfold signal.
  f_equal.
  - induction n.
    + unfold trajectory. reflexivity.
    + assert (forall m0: nat, m0 <= n  -> fst (u m0) = fst (u' m0)) as Hlen. { auto. }
      assert (forall m1: nat, m1 < n  -> snd (u m1) = snd (u' m1)) as Hltn. { auto. }
      assert (fst (u n) = fst (u' n)) as Heqn0. { auto. }
      assert (snd (u n) = snd (u' n)) as Heqn1. { auto. }

      assert (trajectory f e u n = trajectory f e u' n).
      { apply IHn. assumption. assumption. }
      remember (trajectory f e u n) as x eqn:Ex.
      remember (trajectory f e u' n) as x' eqn:Ex'.
      assert (trajectory f e u (S n) = f (trajectory f e u n) (u n)) as Hn.
      { simpl. reflexivity. }
      assert (trajectory f e u' (S n) = f (trajectory f e u' n) (u' n)) as Hn'.
      { simpl. reflexivity. }
      rewrite -> Hn. rewrite <- Ex.
      rewrite -> Hn'. rewrite <- Ex'.
      f_equal.
      * assumption.
      * destruct (u n) as [uan udn].
        destruct (u' n) as [uan' udn'].
        apply pair_qual_spec. split.
        -- apply Heqn0.
        -- apply Heqn1.
  - rewrite <- H0.
    * reflexivity.
    * apply Nat.le_refl.
*)
Admitted.

(* Define the composition of state space models. *)
Definition compose_systems {U X1 X2 Y1 Y2 : Type}
  (s1 : @System U X1 Y1)
  (s2 : @System (U*Y1) X2 Y2)
  : (@System U (X1*X2) (Y1*Y2)) :=
    match s1 with
    | state_space_model f1 h1 e1 =>
      match s2 with
      | state_space_model f2 h2 e2 =>
        let e12 : M (X1*X2) := ensemble_product e1 e2 in
        let h12 : (X1*X2) -> U -> (Y1*Y2) := fun x12 u =>
          (let y1:=h1 (fst x12) u in let y2:=h2 (snd x12) (u,y1) in (y1,y2)) in
        let f12 : (X1*X2) -> U -> M (X1*X2) :=
          (fun x12 u x12' => element (fst x12') (f1 (fst x12) u)
                              /\ element (snd x12') (f2 (snd x12) (u,h1 (fst x12) u))) in
        state_space_model f12 h12 e12
      end
    end
.

Definition is_composed_behaviour {U Y1 Y2}
      (b1 : Seq (U) -> M (Seq Y1))
      (b2 : Seq (U*Y1) -> M (Seq Y2))
      (b12 : Seq U -> M (Seq (Y1*Y2)))
    : Prop :=
  forall (u : Seq U) (y12 : Seq (Y1*Y2)),
    let y1 := fun n => fst (y12 n) in
    let y2 := fun n => snd (y12 n) in
    b12 u y12 <->
      element y1 (b1 (fun n => (u n))) /\ element y2 (b2 (fun n => (u n, y1 n))).


(* Show that the behaviour of the composition of two systems
   is a composition of the behaviours of the components. *)
Theorem composed_system_behaviour {U X1 X2 Y1 Y2 : Type} :
   forall (s1 : @System U X1 Y1)
          (s2 : @System (U*Y1) X2 Y2),
          is_composed_behaviour
            (behaviour s1)
            (behaviour s2)
            (behaviour (compose_systems s1 s2))
.
Proof.
(*
   intros s1 s2.
   remember (compose_systems s1 s2) as s12 eqn:Es12.
   destruct s1 as (f1,h1,e1).
   destruct s2 as (f2,h2,e2).
   destruct s12 as (f12,h12,e12).
   unfold compose_systems in Es12.
   injection (Es12) as Ef12 Eh12 Ee12. clear Es12.
   unfold is_composed_behaviour.
   intros u.
   simpl.

   remember (trajectory f12 e12 u) as x12 eqn:Ex12.
   remember (signal h12 x12 (fun k => fst (u k))) as y12 eqn:Ey12.
   remember (trajectory f1 e1 (fun k =>
      (fst (u k), (snd (u k), snd (y12 k))))) as x1 eqn:Ex1.


   remember (trajectory f2 e2 (fun k =>
      ((fst (u k), fst (y12 k)), snd (u k)))) as x2 eqn:Ex2.
   remember (signal h1 x1) as y1 eqn:Ey1.
   remember (signal h2 x2) as y2 eqn:Ey2.

   assert ( forall n m:nat, m<=n -> x1 m = fst (x12 m) /\ x2 m = snd (x12 m) ) as SHx.
   { induction n.
     - intros m. intros Hmle0.
       assert (m=0) as Hmeq0. { apply Nat.le_0_r. assumption. }
       rewrite -> Hmeq0.
       rewrite -> Ex12. rewrite -> Ex1. rewrite -> Ex2.
       unfold trajectory. rewrite -> Ee12. simpl. split. reflexivity. reflexivity.
     - intro m. rewrite -> Nat.le_succ_r. apply or_ind.
       -- apply IHn.
       -- intro HmeqSn. rewrite -> HmeqSn.

          assert ( x1 (S n) = f1 (x1 n) (fst (u n), (snd (u n), h2 (x2 n) (fst (u n), h1 (x1 n) (fst (u n)))))) as Hx1Sn.
          { rewrite -> Ex1. simpl. f_equal. f_equal.
            rewrite -> Ey12. unfold signal. rewrite -> Eh12. simpl.
            assert ( x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hnx.
            { apply IHn. apply Nat.le_refl. }
            assert (x2 n = snd (x12 n)) as Hx2n. { apply Hnx. }
            rewrite <- Hx2n.
            assert (x1 n = fst (x12 n)) as Hx1n. { apply Hnx. }
            rewrite <- Hx1n.
            f_equal. f_equal. f_equal.
            rewrite -> Ex1. f_equal.
            rewrite -> Ey12. unfold signal. rewrite -> Eh12.
            reflexivity.
          }

          assert ( x2 (S n) = f2 (x2 n) ((fst (u n), h1 (x1 n) (fst (u n))), snd (u n))) as Hx2Sn.
          { rewrite -> Ex2. simpl. f_equal.
            rewrite -> Ey12. unfold signal. rewrite -> Eh12. simpl.
            assert ( x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hnx.
            { apply IHn. apply Nat.le_refl. }
            assert (x1 n = fst (x12 n)) as Hx1n. { apply Hnx. }
            rewrite <- Hx1n. reflexivity.
          }

          assert ( x12 (S n) = f12 (x12 n) (u n) ) as Hx12Sn.
          { rewrite -> Ex12. simpl. reflexivity. }


          assert (  f12 (x12 n) (u n) =
            ( f1 (fst (x12 n)) ((fst (u n)), ((snd (u n)), h2 (snd (x12 n)) ((fst (u n)), h1 (fst (x12 n)) (fst (u n))))),
              f2 (snd (x12 n)) ((fst (u n), h1 (fst (x12 n)) (fst (u n))), snd (u n)
            ))) as Hx12n.
          { rewrite -> Ef12. reflexivity. }

          assert (x1 n = fst (x12 n) /\ x2 n = snd (x12 n)) as Hx1a2n. { apply IHn. apply Nat.le_refl. }
          split.
          --- rewrite -> Hx1Sn. rewrite -> Hx12Sn. rewrite -> Hx12n. simpl. f_equal.
              ---- apply IHn. apply Nat.le_refl.
              ---- assert (x2 n = snd (x12 n)) as Hx2n. { apply Hx1a2n. }
                   rewrite <- Hx2n.
                   assert (x1 n = fst (x12 n)) as Hx1n. { apply Hx1a2n. }
                   rewrite <- Hx1n. reflexivity.
          --- rewrite -> Hx2Sn. rewrite -> Hx12Sn. rewrite -> Hx12n. simpl. f_equal.
              ---- apply IHn. apply Nat.le_refl.
              ---- assert (x1 n = fst (x12 n)) as Hx1n. { apply Hx1a2n. }
                   rewrite <- Hx1n. reflexivity.
   }

   assert ( forall n : nat, n<=n -> x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hnx.
   { intros n. apply SHx. }
   assert ( forall n : nat, x1 n = fst (x12 n) /\ x2 n = snd (x12 n) ) as Hx.
   { intros n. apply Hnx. apply Nat.le_refl. }

   intros n.
   rewrite -> Ey12. rewrite -> Ey1. rewrite -> Ey2.
   unfold signal. rewrite -> Eh12. simpl. split.
   - f_equal. symmetry. apply Hx.
   - f_equal. symmetry. apply Hx.
*)
Admitted.



(* The composed behaviour of two systems should be unique. *)

(* Intermediate step to show how this theorem easily follows from last theorem *)

(* From above Theorem composed_mixed_causal_system_behaviour_unique, get systems involved
   - replace b12' by (behaviour (compose_systems s1 s2)).
   - use (behaviour s1) for b1, (behaviour s2) for b2.
*)

(*
Lemma Hb12eqbehav {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : @system UA (UD*Y2) X1 Y1)
         (s2 : @system (UA*Y1) UD X2 Y2)
         (b12 : (nat->UA*UD)->(nat->Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12 ->
    is_composed_behaviour (behaviour s1) (behaviour s2) (behaviour (compose_systems s1 s2))
      -> forall (u : nat->UA*UD) (n:nat),
        b12 u n = behaviour (compose_systems s1 s2) u n.
Proof.
   intros s1 s2 b12 H0 H1.
   remember (behaviour (compose_systems s1 s2)) as b12' eqn:Eb12'.
   remember (behaviour s1) as b1 eqn:Eb1.
   remember (behaviour s2) as b2 eqn:Eb2.
   intros u n.
   (* Check composed_mixed_causal_system_behaviour_unique. *)
   apply @composed_mixed_causal_behaviour_unique
     with (b1:=b1) (b2:=b2) (b12':=b12').

   - apply X1. (* ? *)
   - apply X2. (* ? *)
   - rewrite Eb1. apply behaviour_mixed_causal.
   - rewrite Eb2. apply behaviour_mixed_causal.
   - exact H0.
   - exact H1.
Qed.
*)

(* The composed behaviour of two systems should be unique. *)
(* One condition can go, because it is already proven to be true *)
(*
Theorem composed_system_behaviour_unique {UA UD X1 X2 Y1 Y2 : Type} :
  forall (s1 : @system UA (UD*Y2) X1 Y1)
         (s2 : @system (UA*Y1) UD X2 Y2)
         (b12 : (nat->UA*UD)->(nat->Y1*Y2)),
    is_composed_behaviour (behaviour s1) (behaviour s2) b12
      -> forall (u : nat->UA*UD) (n:nat),

       b12 u n = behaviour (compose_systems s1 s2) u n.
Proof.
  intros s1 s2 b12 Hb12 u n.
  apply Hb12eqbehav.
  - exact Hb12.
  - apply composed_system_behaviour.
Qed.
*)
