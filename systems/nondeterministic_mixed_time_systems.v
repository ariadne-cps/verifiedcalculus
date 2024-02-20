(******************************************************************************
 *  systems/nondeterministic_mixed_time_systems.v
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
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sets.Ensembles.

Require Import Words.
Require Import EnsembleMonad.

Require Export nondeterministic_system_models.

Search min le.

Section NondeterministicSystems.

  Lemma and_not_impl_not_impl : forall p q, (p /\ ~ q) -> ~ (p -> q).
  Proof. intros p q [Hp Hnq] Hpq. exact (Hnq (Hpq Hp)). Qed.

Notation M := Ensemble.

Notation Nat := nat.

Inductive NatInf : Type :=
  | finite (n:Nat) | infinity
. 
 
Definition lt (m:Nat) (n:NatInf) :=
  match n with | finite n' => Nat.lt m n' | infinity => True end.

Notation "x < y" := (lt x y).

Definition le (m:NatInf) (n:NatInf) :=
  match n with 
  | finite n' => match m with | finite m' => Nat.le m' n' | infinity => False end
  | infinity => True
  end.

Notation "x <= y" := (le x y).

Definition min (m n : NatInf) :=
  match n with 
  | finite n' => match m with | finite m' => finite (Nat.min m' n') | infinity => finite n' end
  | infinity => m
  end.

Lemma le_min_l : forall (m n : NatInf), min m n <= m.
Proof.
  intros m n. unfold min, le.
  destruct m as [m | ].
  - destruct n as [n | ].
    -- exact (Nat.le_min_l m n). -- exact (Nat.le_refl m). 
  - tauto.
Qed.

Lemma le_min_r : forall (m n : NatInf), min m n <= n.
Proof.
  intros m n. unfold min, le.
  destruct n as [n | ].
  - destruct m as [m | ].
    -- exact (Nat.le_min_r m n). -- exact (Nat.le_refl n). 
  - tauto.
Qed.

Lemma lt_le_trans : forall l m n, lt l m -> le m n -> lt l n.
Proof.
  unfold lt, le.
  intros l m n.
  destruct n as [n | ].
  - destruct m as [m | ].
    -- exact (Nat.lt_le_trans l m n). -- contradiction.
  - destruct m as [m | ].
    -- tauto. -- tauto.
Qed.


Record Ordinal (n : NatInf) := {
    val :> nat;
    val_lt : lt val n;
}.

Definition ord {n : NatInf} (m : Nat) (p : m < n) : Ordinal n := {| val:=m; val_lt := p |}.

Definition Seqw (n : NatInf) (X : Type) := (Ordinal n) -> X.

Inductive Seqws {X : Type} := | seqw {n : NatInf} (w : Seqw n X).

Definition lenw {n : NatInf} {X : Type} (w : Seqw n X) : NatInf := n. 
  
Definition len {X : Type} (w : @Seqws X) : NatInf := 
  match w with | @seqw _ n _ => n end. 

Lemma ordinal_eq : forall {n:NatInf} (k1 k2 : Ordinal n),
  k1.(val n) = k2.(val n) -> k1 = k2.
Proof.
  intros n k1 k2. destruct k1 as [k1 p1]. destruct k2 as [k2 p2]. simpl.
  intros H. revert p1 p2. rewrite <- H. intros p1 p2.
  rewrite (proof_irrelevance _ p1 p2). reflexivity.
Qed.

Lemma seq_at_ordinal : forall {X} {n:NatInf} (x : Seqw n X) (k1 k2 : Ordinal n),
  k1.(val n) = k2.(val n) -> x k1 = x k2.
Proof.
  intros X n x k1 k2 H. apply f_equal. exact (ordinal_eq _ _ H).
Qed.

Definition atw' {X : Type} (xs : @Seqws X) (k : Nat) (p : k < len xs) : X.
Proof.
  destruct xs as [n w]. unfold len in p. set (x := w (ord k p)). exact x.
Qed.

Lemma lt_eq_trans : forall l m n, lt l m -> eq m n -> lt l n.
Proof. intros l m n Hlltm Hmeqn. rewrite <- Hmeqn. exact Hlltm. Qed.
 
Definition coerce_ordinal_eq {m : NatInf} (kp : Ordinal m) (n : NatInf) (q : m=n) : Ordinal n :=
  let k := kp.(val m) : Nat in
    let p := kp.(val_lt m) : k < m in
      let r := lt_eq_trans _ _ _ p q in
        {| val:=k; val_lt:=r |}.

Definition coerce_ordinal {m : NatInf} (kp : Ordinal m) (n : NatInf) (q : m <= n) : Ordinal n :=
  let k := kp.(val m) : Nat in
    let p := kp.(val_lt m) : k < m in
      let r := lt_le_trans _ _ _ p q in
        {| val:=k; val_lt:=r |}.

Definition coerce_comparison
  {X : Type} (n : NatInf) (xs : @Seqws X) (x : Seqw n X) (e : xs = seqw x)
  (k : Nat) (p : k < len xs) : (k < n).
Proof.
  unfold len in p. rewrite -> e in p. exact p. 
Qed.

Definition atw {X : Type} (n : NatInf) (x : @Seqw n X) (k : Nat) (p : k < n) : X :=
  x (ord k p).

Definition atws {X : Type} (xs : @Seqws X) (k : Nat) (p : k < len xs) : X :=
  match xs return Seqw (len xs) X with | @seqw _ n w => w end (ord k p). 

Definition Behaviour {U Y : Type} := @Seqws U -> M (@Seqws Y).

Definition nonprescient {U Y : Type} (b : @Behaviour U Y) :=
  forall u, forall y, element y (b u) -> len y <= len u.

(* Project onto a prefix of equal or smaller length. *)
Definition proj {n : NatInf} {X : Type} (m : NatInf) (q : m <= n) (w : Seqw n X) : Seqw m X := 
  fun kp => let q := lt_le_trans _ _ _ (kp.(val_lt m)) q in w (ord kp.(val m) q).

(* Project onto a prefix. 
 * If the required length is greater then the length of the argument,
 * returns the argument unchanged. *)
Definition proje {n : NatInf} {X : Type} (m : NatInf) (w : Seqw n X) : Seqw (min m n) X := 
  fun kp => let r := lt_le_trans _ _ _ (kp.(val_lt (min m n))) (le_min_r m n) in w (ord kp.(val (min m n)) r).

(* Project a word or sequence of unknown length onto a prefix.
 * if the required length is greater than the length of the argument, returns the argument. *)
Definition projs {X : Type} (m : NatInf) (x : @Seqws X) : @Seqws X :=
  match x with | @seqw _ n xn => 
    let mn := min m n in
      let p := le_min_r m n in
        seqw (proj mn p xn)
          end.

Lemma succ_lt : forall (k : Nat) (n : NatInf), finite (S k) = n -> k < n.
Proof.
  intros k n H. destruct n. 
  - injection H. intros He. rewrite <- He. unfold lt. exact (Nat.lt_succ_diag_r k).
  - unfold lt. tauto.
Qed.

Lemma lt_trans : forall (k m : Nat) (n : NatInf), k < finite m -> m < n -> k < n.
Proof.
  intros k m n. unfold lt. destruct n.
  - exact (Nat.lt_trans k m n).
  - tauto.
Qed.

Lemma lt_eq_lt_trans : forall (k m : Nat) (l n : NatInf), k < l -> l = finite m -> m < n -> k < n.
Proof.
  intros k m l n. intros Hkl Hlm Hmn. 
  rewrite -> Hlm in Hkl. rename Hkl into Hkm. exact (lt_trans _ _ _ Hkm Hmn).
Qed.

(* TODO: Simplify definition *)
Definition trajectory' {U X : Type} {nx nu : NatInf}
  (f:X->U->M X) (e:M X) (u:Seqw nu U) (x:Seqw nx X) :=
    nx <= nu /\ (
      forall p0 : 0 < nx,  element (x (ord 0 p0)) e 
        /\ forall (k : Nat), forall pu:k<nu, forall px:k<nx, 
             forall psx:(S k)<nx, element (x (ord (S k) psx)) (f (x (ord k px)) (u (ord k pu)))
        /\ forall (k : Nat) (mx : Nat) (pk : finite (S k) = nx) (pmx : nx = finite mx) (pmu : mx < nu), 
             let pkx := succ_lt k nx pk : k < nx in
               let pku := lt_eq_lt_trans _ _ _ _ pkx pmx pmu : k < nu in
                 empty (f (x (ord k pkx)) (u (ord k pku)))     
         ).

Definition trajectory {U X : Type} 
  (f:X->U->M X) (e:M X) : (@Seqws U) -> M (@Seqws X) :=
    fun u x => match u with | seqw uw => match x with | seqw xw =>
      trajectory' f e uw xw end end.

Definition signal' {X U Y : Type } {nx nu : NatInf}
  (h:X->U->Y) (x:Seqw nx X) (u:Seqw nu U) : Seqw (min nx nu) Y := 
    let ny := min nx nu : NatInf in
      let px := le_min_l nx nu in
        let pu := le_min_r nx nu in
          fun ky : Ordinal ny => 
            let kx := coerce_ordinal ky nx px in
              let ku := coerce_ordinal ky nu pu in
                h (x kx) (u ku).

Definition signal {X U Y : Type }
  (h:X->U->Y) (x:@Seqws X) (u:@Seqws U) : @Seqws Y := 
    match u with | seqw uw => match x with | seqw xw =>
      seqw (signal' h xw uw)
    end end.

Definition behaviour {U X Y : Type}
  (s:@System U X Y) : @Behaviour U Y :=
    match s with
    | state_space_model f h e =>
        fun u => apply (fun x => signal h x u) (trajectory f e u)
    end.




Definition prefix_conform {U Y : Type}
  (b : @Behaviour U Y) :=
    forall (m:NatInf) (u : @Seqws U),
      subset
        (apply (fun u => projs m u) (b u))
        (b (projs m u)).

Definition prefix_conform' {U Y : Type}
  (b : @Behaviour U Y) :=
    forall (n:NatInf) (u : Seqw n U) (m:NatInf) (p:m<=n),
      subset
        (apply (fun u => projs m u) (b (seqw u)))
        (b (seqw (proj m p u))).


Definition strong_causal {U Y : Type}
  (b : @Behaviour U Y) :=
    forall (n n' : NatInf) (u : Seqw n U) (u' : Seqw n' U) (m:NatInf) (p:m<=n) (p':m<=n'),
      proj m p u = proj m p' u' ->
        apply (projs m) (b (seqw u)) = apply (projs m) (b (seqw u')).

Definition weak_causal {U Y : Type}
  (b : @Behaviour U Y) :=
    forall (n:NatInf) (u u' : Seqw n U) (m:NatInf) (p:m<=n),
      proj m p u = proj m p u' ->
        apply (projs m) (b (seqw u)) = apply (projs m) (b (seqw u')).

Notation causal := weak_causal.


Example not_finite_causal_implies_prefix_conform :
  exists U Y (b : @FiniteBehaviour U Y),
    not (finite_causal b -> finite_prefix_conform b).
Proof.
  set (UY := Double).
  exists UY, UY.
  set (b:= fun n (u : Wrd n UY) => match n with | 0 => (fun y => False) | _ => fun y => y=u end).
  exists b.
  apply and_not_impl_not_impl.
  split.
  - unfold finite_causal.
    intros n u u' m p Hu'.
    unfold apply.
    apply functional_extensionality. intro yw.
    revert u u' Hu'.
    assert (forall (u u' : Wrd n UY), (restr m p u = restr m p u')
              -> (exists y, b n u y /\ restr m p y = yw)
              -> (exists y', b n u' y' /\ restr m p y' = yw)) as H. {
      intros u u' Hu'.
      remember (restr m p u) as uw eqn:Hu.
      destruct n.
      unfold b. simpl. 
      intros [_ [Hf _]].
      contradiction.
      unfold b. simpl.
      intros [y [Huy Hy]].
      rewrite -> Huy in Hy.
      rewrite <- Hu in Hy.
      exists u'.
      split.
      reflexivity.
      rewrite <- Hu'.
      exact Hy.
    }
    intros u u' Hu.
    apply propositional_extensionality. split.
    -- apply H. exact Hu.
    -- apply H. symmetry. exact Hu.
  - unfold finite_prefix_conform.
    set (u := (fun _ => second) : Wrd 1 UY). 
    set (uw := (fun _ => second) : Wrd 0 UY).
    set (p := Nat.le_0_1).
    intro H.
    specialize (H 1 u 0 p).
    unfold subset, element, apply in H.
    specialize (H uw).
    unfold b in H. 
    apply H.
    exists u.
    split.
    reflexivity.
    unfold restr.
    apply functional_extensionality. intros u0.
    unfold u, uw.
    reflexivity.
Qed.

Example not_finite_prefix_conform_implies_causal :
  exists U Y (b : @FiniteBehaviour U Y),
    not (finite_prefix_conform b -> finite_causal b).
Proof.
  set (UY := Double).
  set (b := fun n => match n with 
         | 0 => fun (_ : Wrd 0 UY) (_ : Wrd 0 UY) => True 
         | 1 => fun _ _ => True
         | S (S m) => 
           let p0 := (Nat.lt_0_succ (S m)) in 
           let p1 := proj1 (Nat.succ_lt_mono 0 (S m)) (Nat.lt_0_succ m) in 
           fun u y => 
             match u (ord 1 p1) with 
             | first => (y (ord 0 p0) = first)
             | second => True 
             end
         end).
  exists UY, UY, b.
  apply and_not_impl_not_impl.
  split.
  - apply finite_prefix_conform_equivalent.
    unfold finite_prefix_conform'.
    intros n.
    destruct n as [ | [ | n]].
    -- (* Case |u|=1 *)
       intros u y _. unfold element. simpl. tauto. 
    -- (* Case |u|=2 *)
       intros u y _. unfold element. simpl. tauto.
    -- (* Case |u|>=3 *)
       unfold b, subset, element, apply.
       intros u yw Huy.
       destruct Huy as [y Huy].
       set (p0ltSSn := Nat.lt_0_succ (S n)).
       set (p0ltSSSn := Nat.lt_0_succ (S (S n))).
       set (p1ltSSn := proj1 (Nat.succ_lt_mono _ _) (Nat.lt_0_succ n)).
       set (p1ltSSSn:= proj1 (Nat.succ_lt_mono _ _) (Nat.lt_0_succ (S n))).
       remember (u (ord 1 p1ltSSSn)) as u1.
       destruct u1. (* Cases u1 = first and u1 = second *)
       --- rewrite -> (wrd_at_ordinal u _ (ord 1 p1ltSSSn)) in Huy; [|reflexivity].
           rewrite <- Hequ1 in Huy.
           rewrite -> (wrd_at_ordinal y _ (ord 0 p0ltSSSn)) in Huy; [|reflexivity].
           rewrite -> restr_at.
           rewrite -> (wrd_at_ordinal u _ (ord 1 p1ltSSSn)); [|reflexivity].
           rewrite <- Hequ1.
           rewrite <- (proj2 Huy).
           rewrite -> restr_at.
           rewrite -> (wrd_at_ordinal y _ (ord 0 p0ltSSSn)); [|reflexivity].
           exact (proj1 Huy).
       --- rewrite -> restr_at.
           rewrite -> (wrd_at_ordinal u _ (ord _ p1ltSSSn)).
           rewrite <- Hequ1.
           tauto.
           reflexivity.
  - unfold finite_causal, apply.
    intros Hc.
    set (u := proj 2 (fun k => first)).
    set (u' := proj 2 (fun k => match k with | 0 => first | _ => second end)).
    set (p1le2 := proj1 (Nat.succ_le_mono _ _) (Nat.le_0_1)).
    assert (restr 1 p1le2 u = restr 1 p1le2 u') as Hu. {
      unfold u, u'. rewrite <- proj_restr, <- proj_restr. apply agree_proj. unfold agree.
      intros m Hmlt1. replace m with 0. reflexivity. symmetry. exact (proj1 (Nat.lt_1_r m) Hmlt1). }
    specialize (Hc 2 u u' 1 p1le2 Hu).
    assert (forall {X Y} (f1 f2 : X -> Y) (x : X), f1=f2 -> f1 x = f2 x) as Heqf. {
      intros X Y f1 f2 x Hf. rewrite -> Hf. reflexivity. }
    set (yw := proj 1 (fun _ => second)).
    specialize (Heqf _ _ _ _ yw Hc) as Hye.
    simpl in Hye.
    assert (forall p q : Prop, p=q -> (p -> q)) as Hpq. {
      intros p q He Hp. rewrite -> He in Hp. exact Hp. }
    assert (not (exists y, y (ord 0 (Nat.lt_0_succ 1)) = first /\ restr 1 p1le2 y = yw)) as Hy. {
      intros [y [Hyf Hyt]].
      unfold yw in Hyt.
      apply (Heqf _ _ _ _ (ord 0 Nat.lt_0_1)) in Hyt.
      rewrite -> proj_at in Hyt.
      replace (restr 1 p1le2 y (ord 0 (Nat.lt_0_1))) with (y (ord 0 (Nat.lt_0_succ 1))) in Hyt.
      rewrite -> Hyt in Hyf.
      discriminate.
      unfold restr.
      apply wrd_at_ordinal.
      reflexivity.
   }
    assert (exists y : Wrd 2 UY, True /\ restr 1 p1le2 y = yw) as Hy'. {
      set (y := proj 2 (fun _ => second)).
      exists y.
      split.
      tauto.
      unfold y, yw, proj.
      apply wrd_eq.
      intros [k p].
      rewrite -> restr_at.
      reflexivity.
   }
   rewrite <- Hye in Hy'.
   contradiction.
Qed.
(*

Definition causal {U Y : Type}
  (bs : Seq U -> M (Seq Y)) : Prop :=
    exists bw : forall n, Wrd n U -> M (Wrd n Y),
      finite_prefix_conform bw /\ is_infinite_behaviour bw bs.


(* Probably not true, since infinite causal requires infinite_trajectory to exist (non-blocking). *)
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
*)

Definition finite_input_nontrivial {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)) :=
  exists n, exists (u : Wrd n U), exists y, element y (b u).

Definition finite_input_accepting {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)) :=
  forall (n:nat) (u : Wrd n U), exists y, element y (b u).

Definition finite_input_enabling {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)) :=
  forall (n:nat) (u : Wrd n U), forall (m:nat) (p:m<=n), let uw := restr m p u in
    (exists yw : Wrd m Y, element yw (b uw))
      /\ forall yw : Wrd m Y,
           element yw (b uw)
             -> exists y, element y (b u) /\ yw = restr m p y.




(* Issue that finite_behaviour only maps words of length S n. *)
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
         destruct (Compare_dec.le_lt_eq_dec k (S n) (proj1 (Nat.lt_succ_r k (S n)) p)).
         --- unfold ord. apply wrd_at_ordinal. simpl. reflexivity.
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
       --- apply wrd_at_ordinal; simpl; exact Hneqm.
       --- assert (m < S (S n)) as HmltSSn; [exact (Nat.lt_succ_l m (S (S n)) HSmltSSn)|].
           assert (m < S n) as HmltSn; [rewrite <- Hneqm; exact (Nat.lt_succ_diag_r n)|].
           replace (Nat.lt_succ_l m (S (S n)) HSmltSSn) with HmltSSn;  [|apply proof_irrelevance].
           rewrite -> (cat_tail _ _ m HmltSn).
           apply wrd_at_ordinal.
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
    -- rewrite -> restr_at. apply wrd_at_ordinal. unfold ord. reflexivity.
    -- rewrite -> restr_at.
       apply wrd_at_ordinal. unfold ord. reflexivity.
  - rewrite -> cat_head; [|exact Hmeqn].
    f_equal.
    -- apply wrd_at_ordinal. simpl. exact Hmeqn.
    -- apply wrd_at_ordinal. simpl. exact Hmeqn.
Qed.


Example not_finite_prefix_conform_and_causal_and_input_accepting_implies_input_enabling :
  exists (U Y : Type) (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_prefix_conform (@b) /\ finite_causal (@b) /\ finite_input_accepting (@b) /\ not (finite_input_enabling (@b)).
Proof.
Search 0 lt S.
  set (U:=Single). set (Y:=Double).
  set (b:=(let (nn :=n)) in fun n => match n with 
                   | 0 => fun _ _ => True 
                   | S m => fun (u:Wrd n U) (y : Wrd n Y) => y (ord 0 (Nat.lt_0_succ m)) = first 
                   end).
  exists U Y b.
  - admit.
  - admit.
  - admit.
  - set (yw:=proj 1 (fun _ => second)).
Admitted.

Proposition nonblocking_implies_finite_behaviour_input_enabling :
  forall {U X Y} (s : @System U X Y),
    nonblocking s -> finite_input_enabling (@finite_behaviour U X Y s).
Proof.
  unfold finite_behaviour, finite_input_enabling, nonblocking.
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
           apply wrd_at_ordinal.
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
                      unfold ord. apply wrd_at_ordinal. simpl. reflexivity.
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
                      apply wrd_at_ordinal.
                      reflexivity.
                ----- unfold ySm.
                      f_equal.
                      unfold xe.
                      apply cat_head.
                      reflexivity.
                      unfold uSm.
                      rewrite -> restr_at.
                      apply wrd_at_ordinal.
                      reflexivity.
  - admit.
Admitted.

Proposition finite_input_enabling_implies_input_accepting :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_enabling (@b) -> finite_input_accepting (@b).
Proof.
  unfold finite_input_enabling, finite_input_accepting.
  unfold subset, apply, element.
  intros U Y b Hia.
  intros n u.
  specialize (Hia n u n (Nat.le_refl n)).
  destruct Hia as [[y Hy] _].
  rewrite -> restr_id in Hy.
  exists y.
  exact Hy.
Qed.

Lemma finite_input_enabling_extension :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_enabling (@b) ->
      forall {n} (ue : Wrd (S n) U) (yw : Wrd n Y),
        let p := (Nat.le_succ_diag_r n) in
        element yw (b (restr n p ue)) ->
          exists ye : Wrd (S n) Y,
           restr n p ye = yw /\ element ye (b ue).
Proof.
  unfold finite_input_enabling.
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


Lemma finite_input_enabling_trajectory :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_enabling (@b) ->
      forall (us : Seq U) {n} (yw : Wrd n Y),
        element yw (b (proj n us)) ->
          exists ys : Seq Y,
           proj n ys = yw /\ forall m (p:n<=m), element (proj m ys) (b (proj m us)).
(*
          exists ys : forall m, n<=m -> Wrd m Y,
            forall m, (p:n<=m), element (ys m p) (b (proj m us)) /\ restr m exists ys : Seq Y, proj n ys = yw /\ forall m, n<=m -> element (proj m ys) (b (proj m us)).
*)
Proof.
  unfold finite_input_enabling.
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


Proposition finite_input_enabling_implies_causal :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_input_enabling (@b) -> finite_prefix_conform (@b).
Proof.
  unfold finite_input_enabling, finite_prefix_conform.
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

Proposition finite_causal_and_input_accepting_implies_input_enabling :
  forall {U Y} (b : forall {n : nat}, Wrd n U -> M (Wrd n Y)),
    finite_prefix_conform (@b) -> finite_input_accepting (@b) -> finite_input_enabling (@b).
Proof.
  unfold finite_input_enabling, finite_input_accepting, finite_prefix_conform.
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




End NondeterministicSystems.
