(******************************************************************************
 *  utilities/InhabitedEnsembleMonad.v
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
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Logic.ProofIrrelevance.

Require Import Lia.


Require Import Bool.
Require Import List.
Require Import Ensembles.

Require Import Words.
Require Import DependentChoice.

Require Export Monads.
Require Export SubMonads.
Require Export LimitMonads.

Require Export EnsembleMonad.



Section EnsembleMonads.

Record InhabitedEnsemble {A:Type} : Type :=
{
  ensmbl :> Ensemble A;
  ensmbl_inhabited : inhabited ensmbl;
}.

Lemma singleton_inhabited : forall {X : Type} (x : X), inhabited (singleton x).
Proof. intros X x. unfold inhabited, singleton. exists x. reflexivity. Qed.

Lemma image_inhabited : forall {X Y : Type} (fs : X -> Ensemble Y) (xs : Ensemble X),
  (forall x, inhabited (fs x)) -> (inhabited xs) -> inhabited (image fs xs).
Proof.
  intros X Y fs xs Hf Hx.
  unfold inhabited, image in *.
  destruct Hx as [x Hx].
  specialize (Hf x) as Hy.
  destruct Hy as [y Hy].
  exists y.
  exists x.
  split.
  - exact Hx.
  - exact Hy.
Qed.


Definition inhabited_singleton {X : Type} (x : X) : @InhabitedEnsemble X :=
  {| ensmbl := singleton x;
     ensmbl_inhabited := singleton_inhabited x; |}.
Definition inhabited_image {X Y : Type} (fs : X -> @InhabitedEnsemble Y) (xs : @InhabitedEnsemble X) : @InhabitedEnsemble Y :=
  {| ensmbl := image (fun x => ensmbl (fs x)) (ensmbl xs);
     ensmbl_inhabited := image_inhabited (fun x => ensmbl (fs x)) (ensmbl xs) (fun x => ensmbl_inhabited (fs x)) (ensmbl_inhabited xs); |}.


Lemma inhabited_ensemble_eq : forall {X : Type} (s1 s2 : @InhabitedEnsemble X),
  (ensmbl s1) = (ensmbl s2) -> s1 = s2.
Proof.
  intros X s1 s2.
  destruct s1 as [s1 s1ne].
  destruct s2 as [s2 s2ne].
  simpl.
  intros H.
  revert s1ne s2ne.
  rewrite <- H.
  intros s1ne s2ne.
  rewrite (proof_irrelevance _ s1ne s2ne).
  reflexivity.
Qed.


Lemma inhabited_ensemble_left_identity :
  forall {X Y : Type} (f : X -> @InhabitedEnsemble Y) (x : X),
    inhabited_image f (inhabited_singleton x) = f x.
Proof.
  intros A B f a.
  apply inhabited_ensemble_eq.
  simpl.
  rewrite -> ensemble_left_identity.
  reflexivity.
Qed.

Lemma inhabited_ensemble_right_identity :
  forall {X : Type} (xs : @InhabitedEnsemble X),
    inhabited_image (@inhabited_singleton X) xs = xs.
Proof.
  intros A a.
  apply inhabited_ensemble_eq.
  simpl.
  rewrite -> ensemble_right_identity.
  reflexivity.
Qed.

Lemma inhabited_ensemble_associativity :
  forall {X Y Z : Type} (xs : @InhabitedEnsemble X) (fs : X -> @InhabitedEnsemble Y) (gs : Y -> @InhabitedEnsemble Z),
    inhabited_image gs (inhabited_image fs xs) = inhabited_image (fun x => inhabited_image gs (fs x)) xs.
Proof.
  intros A B C x f g.
  apply inhabited_ensemble_eq.
  simpl.
  rewrite -> ensemble_associativity.
  reflexivity.
Qed.


#[export]
Instance InhabitedEnsemble_Monad : Monad (@InhabitedEnsemble) :=
{
   Mpure := @inhabited_singleton;
   Mbind := @inhabited_image;

   Mleft_identity := @inhabited_ensemble_left_identity;
   Mright_identity := @inhabited_ensemble_right_identity;
   Massociativity := @inhabited_ensemble_associativity;
}.

(* Define inhabited subsets as a general subtype. *)
Definition InhabitedSubtype {X : Type} := @Subtype (Ensemble X) (inhabited).

Instance InhabitedSubtype_Monad : Monad (@InhabitedSubtype) :=
  @Subtype_Monad (@Ensemble) (@inhabited) (@Ensemble_Monad)
    (@singleton_inhabited) (@image_inhabited).



Theorem inhabited_ensemble_monad_has_list_infinite_skew_product:
  has_list_infinite_skew_product (@InhabitedEnsemble) (InhabitedEnsemble_Monad).
Proof.
  unfold InhabitedEnsemble_Monad.
  unfold has_list_infinite_skew_product.
  intros X Finhabited.
  set ( F := fun xl => ensmbl (Finhabited xl) ).
  assert (forall xl, inhabited (F xl)) as HF_inhabited. {
    intro xl. exact (Finhabited xl).(ensmbl_inhabited). }
  set ( Finf := (fun xs => forall n, F (proj n xs) (xs n)) : Ensemble (nat -> X) ).
  assert (inhabited Finf) as HFinf_inhabited. {
    apply list_dependent_choice. exact HF_inhabited. }
  set (Finf' := Build_InhabitedEnsemble (nat -> X) Finf HFinf_inhabited).
  exists Finf'.
  unfold is_list_infinite_skew_product.
  split. {
    simpl.
    unfold inhabited_singleton, inhabited_image.
    apply inhabited_ensemble_eq.
    apply functional_extensionality. intro xl.
    apply propositional_extensionality.
    simpl.
    split.
    -- intros [xs [_ Hnil]].
       exact Hnil.
    -- intros Hnil.
       assert (forall {X} (p:X->Prop) (q:Prop), (exists x, p x) /\ q -> exists x, (p x /\ q)) as Hexists. {
         intros X' p q H.
         destruct H as [[x Hp] Hq].
         exists x.
         split. exact Hp. exact Hq.
       }
       unfold image.
       apply Hexists.
       split; [|exact Hnil].
       apply list_dependent_choice.
       unfold is_chosable.
       apply HF_inhabited.
  }
  intros n.
  simpl.
  unfold inhabited_singleton, inhabited_image.
  apply inhabited_ensemble_eq.
  apply functional_extensionality.
  intros xl.
  apply propositional_extensionality.
  simpl.
  split.
  - intros H.
    destruct H as [[xl' xn] H].
    destruct H as [Hp Hc].
    destruct Hp as [xl'' [Hp Hf]].
    destruct Hp as [xs [Hp Hp0]].
    destruct Hf as [xn' [Hf Ht]].
    unfold Mpure in Hp0, Ht, Hc.
    rewrite -> Hp0 in Hf, Ht.
    clear Hp0 xl''.
    injection Ht. intros Hxn' Hxl'.
    rewrite <- Hxn' in *; rewrite -> Hxl' in *.
    clear Hxl' Hxn' xl' xn'.
    clear Ht.
    rewrite -> Hc in *.
    clear Hc.
    clear xl.
    unfold lcons.
    simpl.
    set (xl := cons xn (proj n xs)).
    assert (exists xs' : nat -> X, proj (length xl) xs' = xl /\ forall n', F (proj n' xs') (xs' n')) as Hxs'. {
      apply list_dependent_choice_from.
      - unfold is_chosable.
        apply HF_inhabited.
      - unfold xl.
        apply is_choice_list_cons.
        split.
        -- exact Hf.
        -- apply is_choice_prefix_of_sequence.
           unfold is_choice_sequence.
           exact Hp.
    }
    destruct Hxs' as [xs' [Hpxs' Hcxs']].
    exists xs'.
    split.
    -- unfold Finf.
       unfold element.
       apply Hcxs'.
    -- replace (length xl) with (S n) in Hpxs'.
       rewrite <- proj_succ.
       apply eq_sym.
       exact Hpxs'.
       unfold xl.
       simpl.
       f_equal.
       rewrite -> length_proj.
       reflexivity.
  - unfold singleton, image.
    unfold lcons.
    unfold Finf.
    intros H.
    destruct H as [xs [Hc Hh]].
    exists (proj n xs, xs n).
    split.
    -- exists (proj n xs).
       split.
       --- exists xs.
           split.
           ---- apply Hc.
           ---- reflexivity.
       --- exists (xs n).
           split.
           ---- apply Hc.
           ---- reflexivity.
    -- simpl.
       exact Hh.
Qed.



Definition lt_succ_diag_r := PeanoNat.Nat.lt_succ_diag_r.
Definition le_succ_diag_r := PeanoNat.Nat.le_succ_diag_r.
Definition lt_ge_cases := PeanoNat.Nat.lt_ge_cases.

Lemma restr_wrds_shft : forall {X} {l} (xw : forall n, Wrd (l+n) X)
    (m n1 n2 : nat) (q1 : m<=l+n1) (q2 : m<=l+n2) (e : n1 = n2),
  restr m q1 (xw n1) = restr m q2 (xw n2).
Proof.
  intros X l xw m n1 n2 q1 q2 e.
  generalize q2; clear q2; rewrite <- e; intro q2.
  apply restr_eq.
Qed.

Lemma restr_wrds : forall {X} (xw : forall n, Wrd n X) (m n1 n2 : nat) (q1 : m<=n1) (q2 : m<=n2) (e : n1 = n2),
  restr m q1 (xw n1) = restr m q2 (xw n2).
Proof.
  intros X xw m n1 n2 q1 q2 e.
  generalize q2; clear q2; rewrite <- e; intro q2.
  apply restr_eq.
Qed.

Lemma cast_wrd_pred_id : forall {X} (A : forall n, Wrd n X -> Prop) {m n : nat} (p : m = n) (w : Wrd m X),
  A n (cast_wrd p w) = A m w.
Proof. intros X A m n p w. unfold cast_wrd, cast. rewrite <- p. reflexivity. Qed.

Lemma wrd_seq_eq : forall {X:Type} {n n1 n2 : nat} (f:nat->nat) (e:n1=n2) {e1:f n1=n} {e2:f n2=n}
  (xws : forall n, Wrd (f n) X), cast_wrd e1 (xws n1) = cast_wrd e2 (xws n2).
Proof.
  intros X n n1 n2 f e.
  rewrite <- e.
  intros e1 e2 xws.
  apply cast_wrd_eq.
  intros k p1 p2 kp1 kp2.
  f_equal. apply ord_eq. reflexivity.
Qed.

Lemma wrd_seq_id : forall {X:Type} {n1 n2 : nat} (f:nat->nat) {e:n1=n2} {ef:f n1 = f n2}
  (xws : forall n, Wrd (f n) X), cast_wrd ef (xws n1) = (xws n2).
Proof.
  intros X n1 n2 f e.
  rewrite <- e.
  intros ef xws.
  apply cast_wrd_id'.
Qed.



Lemma elmt_restr_eq : forall {X} (A : forall n, Wrd n X -> Prop) (m1 m2 n : nat) (p1 : m1<=n) (p2:m2<=n) (w : Wrd n X), m1=m2 -> A m1 (restr m1 p1 w) = A m2 (restr m2 p2 w).
Proof.
  intros X A m1 m2 n p1 p2 w e.
  generalize p1 p2 w. clear w p1 p2. rewrite -> e. intros p1 p2 w.
  rewrite <- (restr_eq p2 p1). reflexivity.
Qed.

Lemma elmt_restr_id : forall {X} (A : forall n, Wrd n X -> Prop) (m n : nat) (p : m<=n) (w : Wrd n X), m=n -> A m (restr m p w) = A n w.
Proof.
  intros X A m n p w e.
  generalize p w. clear w p. rewrite -> e. intros p w.
  rewrite -> restr_id. reflexivity.
Qed.

Lemma element_restr_le : forall {X} (A : forall n, Ensemble (Wrd n X)),
  (forall n (xSn : Wrd (S n) X), (A (S n) xSn) -> A n (restr n (le_succ_diag_r n) xSn)) ->
    (forall n (xn : Wrd n X), A n xn -> forall m (p : m<=n), A m (restr m p xn)).
Proof.
  intros X A Hrestr.
  intros n xn HAxn.
  assert (forall k (p : n-k<=n), A (n-k) (restr (n-k) p xn)) as Hrek. {
    induction k.
    - assert (n-0 = n) as Hn0 by lia.
      intro p. rewrite -> elmt_restr_id. exact HAxn. exact Hn0.
    - intro r.
      assert (n-k <= n) as p. lia.
      assert (n-S k <= n - k) as q. lia.
      set (q' := le_succ_diag_r (n - S k)).
      destruct (lt_ge_cases k n) as [Hkltn|Hnlek].
      -- assert (S (n - S k) <= n) as p'. lia.
         assert (S (n - S k) = n - k) as e. lia.
         rewrite <- (restr_restr' _ p' _ q').
         apply (Hrestr _ (restr _ p' xn)).
         rewrite -> (elmt_restr_eq A _ (n-k) n _ p) by lia.
         apply IHk.
      -- rewrite -> (elmt_restr_eq A _ (n-k) n _ p) by lia.
         apply IHk.
  }
  intros m p.
  set (k:=(PeanoNat.Nat.le_exists_sub m n p)).
  destruct k as [k [Hk' _]].
  assert (n - k <= n) as p'. lia.
  rewrite -> (elmt_restr_eq A _ (n-k) _ _ p') by lia.
  apply Hrek.
Qed.

Lemma pred_cases : forall n, PeanoNat.Nat.pred n = n \/ (0<n /\ S (PeanoNat.Nat.pred n) = n).
Proof.
  unfold PeanoNat.Nat.pred.
  destruct n.
  - left. reflexivity.
  - right. split. exact (PeanoNat.Nat.lt_0_succ n). reflexivity.
Qed.


Lemma induction_to : forall (p : nat -> Prop) (n : nat),
  p n -> (forall m, m<n -> p (S m) -> p m) -> forall m, m<=n -> p m.
Proof.
  intros p n Hn Hm.
  assert (forall k, p (n-k)) as Hnk. {
    induction k.
   - replace (n-0) with n by (exact (eq_sym (PeanoNat.Nat.sub_0_r n))). exact Hn.
   - rewrite -> PeanoNat.Nat.sub_succ_r.
     set (Hc := pred_cases (n-k)).
     destruct Hc.
     -- rewrite -> H.  exact IHk.
     -- destruct H as [Hkltn Hs].
        apply Hm.
        apply (PeanoNat.Nat.lt_le_trans _ (n-k) _).
        apply PeanoNat.Nat.lt_pred_l. symmetry. apply PeanoNat.Nat.lt_neq. exact Hkltn.
        exact (PeanoNat.Nat.le_sub_l n k).
        rewrite -> Hs.
        exact IHk.
  }
  intros m Hmlen. 
  set (k:=(PeanoNat.Nat.le_exists_sub m n Hmlen)). 
  destruct k as [k [Hkp _]].
  assert (m=n-k) as Hk. { 
    symmetry. apply PeanoNat.Nat.add_sub_eq_r. symmetry. 
    rewrite -> PeanoNat.Nat.add_comm.  exact Hkp. }
  rewrite -> Hk. exact (Hnk k).
Qed.

Lemma induction_from : forall (p : nat -> Prop) (n : nat),
  p n -> (forall m, n<=m -> p m -> p (S m)) -> forall m, n<=m -> p m.
Proof.
  intros p n Hn Hm.
  assert (forall k, p (n+k)) as Hnk. {
    induction k.
    - replace (n+0) with n by (exact (eq_sym (PeanoNat.Nat.add_0_r n))). exact Hn.
    - replace (n + S k) with (S (n+k)).
      apply (Hm (n+k)).
      exact (PeanoNat.Nat.le_add_r n k).
      exact IHk.
      exact (eq_sym (PeanoNat.Nat.add_succ_r n k)).
  }
  intros m Hmlen. 
  set (k:=(PeanoNat.Nat.le_exists_sub n m Hmlen)). 
  destruct k as [k [Hk _]].
  rewrite -> (PeanoNat.Nat.add_comm) in Hk.
  rewrite -> Hk. exact (Hnk k).
Qed.





Definition diagonal {X} (xws : forall n, Wrd n X) (n : nat) := xws (S n) (ord n (lt_succ_diag_r n)).

Lemma diagonal_eq {X} : forall (xws : forall n, Wrd n X),
  (forall n, restr n (le_succ_diag_r n) (xws (S n)) = xws n) ->
    forall n, projw n (diagonal xws) = xws n.
Proof.
  intros xws Hr.
  assert (forall n k (p:n<=n+k), restr n p (xws (n+k)) = xws n). {
    induction k.
    - replace (n+0) with n by lia. intro p. apply restr_id.
    - intro pSk. set (pk := PeanoNat.Nat.le_add_r n k).
      rewrite <- (IHk pk). rewrite <- (Hr (n+k)).
      rewrite -> restr_restr.
      assert (n + S k = S (n+k)) as e by lia.
      apply restr_eq' with (e:=e).
      rewrite <- e.
      apply cast_wrd_id.
  }
  assert (forall n m (p:n<=m), restr n p (xws m) = xws n) as H'. {
    intros n m p.
    set (Hk := PeanoNat.Nat.le_exists_sub n m p).
    destruct Hk as [k [Hk _]].
    rewrite -> PeanoNat.Nat.add_comm in Hk.
    generalize p; clear p; rewrite -> Hk; intro p.
    apply H.
  }
  intro n.
  apply wrd_eq.
  destruct kp as [k p].
  rewrite -> projw_at.
  unfold diagonal.
  simpl.
  assert (S k <= n) as p' by lia.
  rewrite <- (H' (S k) n p').
  rewrite -> restr_at.
  apply wrd_at.
  unfold ord.
  trivial.
Qed.


Proposition word_sequence_exists :
  forall {X} (A : forall n, Ensemble (Wrd n X)) {m} (xm : Wrd m X),
    (A m xm) ->
    (forall n (xSn : Wrd (S n) X), (A (S n) xSn) -> A n (restr n (le_succ_diag_r n) xSn)) ->
    (forall n (xn : Wrd n X), (A n xn) -> exists xSn, (A (S n) xSn) /\ restr n (le_succ_diag_r n) xSn = xn) -> 
    exists (xs : Seq X), (projw m xs = xm) /\ forall n, A n (projw n xs).
Proof.
  intros X A m xm HAxm Hrestr' Hsucc.
  set (B := sigT (fun n => @sig (Wrd n X) (A n))).
  set (R := fun (x y : B) => let nx := projT1 x in let ny := projT1 y in
         ny = S nx /\ forall (e : ny = S nx), proj1_sig (projT2 x) = restr nx (le_succ_diag_r nx)
          (cast_wrd e (proj1_sig (projT2 y)))).
  assert (forall x, exists y, R x y) as HR. { 
    unfold R. clear R.
    intros x. destruct x as [n [x HAx]].
    specialize (Hsucc n x HAx) as HSxn. destruct HSxn as [y [HAy Hry]]. simpl.
    set (y' := existT (fun n=>sig (A n)) (S n) (exist (A (S n)) y HAy)).
    exists y'. unfold y'. clear y'. simpl.
    split.
    - reflexivity.
    - intro e. rewrite <- Hry. rewrite -> restr_cast_wrd. apply restr_eq.
  }
  set (xm' := existT (fun n => @sig (Wrd n X) (A n)) m (exist _ xm HAxm) : B).
  set (Hfdc := functional_dependent_choice R HR xm'). 
  destruct Hfdc as [xs' [Hxm' Hxs']]. clear HR.
  assert (forall n, projT1 (xs' n) = m+n) as Hxsatn. {
    induction n.
    - rewrite -> Hxm'. trivial.
    - specialize (Hxs' n). unfold R in Hxs'. destruct Hxs' as [Hxs' _].
      rewrite -> Hxs'. rewrite -> IHn. lia.
  }
  set (xmws := fun n => (cast_wrd (Hxsatn n) (proj1_sig (projT2 (xs' n))))).
  assert (forall n, n <= m + (n-m)) as add_sub_ge by lia.
  assert (forall n, m + n <= m + S n) as add_succ_le by lia.
  set (xws := fun n => restr n (add_sub_ge n) (xmws (n-m))).
  set (xs := diagonal xws).
  exists xs.
  unfold R in Hxs'. simpl  in Hxs'.
  assert (forall n p, restr (m+n) p (xmws (S n)) = xmws n) as Hmr. {
    intros n p. unfold xmws. simpl.
    specialize (Hxs' n). unfold R in Hxs'. destruct Hxs' as [_ Hxs'].
    assert (projT1 (xs' (S n)) = S (projT1 (xs' n))) as eSn. {
      rewrite -> (Hxsatn n), -> (Hxsatn (S n)). lia. }
    specialize (Hxs' eSn).
    rewrite -> Hxs'.
    simpl.
    set (x := proj1_sig (projT2 (xs' (S n)))).
    rewrite -> cast_wrd_restr.
    rewrite -> restr_cast_wrd.
    rewrite -> restr_cast_wrd.
    apply restr_eq.
  }
  assert (forall n, restr n (le_succ_diag_r n) (xws (S n)) = xws n) as Hrestrxws. {
    unfold xws.
    intros n.
    assert ( n<m \/ m <= n ) as Hnltgem by (apply PeanoNat.Nat.lt_ge_cases).
    destruct Hnltgem.
    - rewrite -> restr_restr. 
      apply restr_wrds_shft.
      lia.
    - assert (m + (n - m) <= m + S (n - m)) as p' by lia.
    rewrite <- (Hmr (n-m) p').
    rewrite -> restr_restr. 
    rewrite -> restr_restr. 
    apply restr_wrds_shft.
    lia.
  }
  assert (m+0=m) as emp0 by lia.
  assert (cast_wrd emp0 (xmws 0) = xm) as Hxm0. {
    unfold xmws. rewrite -> cast_cast_wrd'. 
    replace xm with (proj1_sig (projT2 xm')).
    apply cast_wrd_id''.
    rewrite -> Hxm'.
    intros k p1 p2 kp1 kp2. 
    f_equal. apply ord_eq. reflexivity.
    unfold xm'. reflexivity.
  }
  assert (forall n (p:n<=m), xws n = restr n p xm) as Hrestrxm. {
    unfold xws. intros n p.
    assert (m+(n-m) = m) as e. lia.
    assert (n-m = 0) as e0. lia.
    apply (restr_eq' e).
    rewrite <- Hxm0.
    apply cast_wrd_eq.
    rewrite -> e0.
    intros k p1 p2 kp1 kp2. f_equal. apply ord_eq. reflexivity.
  }
  assert (forall n (p:n>=m), m+(n-m)=n) as Hmnmeqn by lia.
  assert (forall n, projw n xs = xws n) as Hdiag. { 
    unfold xs.
    apply diagonal_eq.
    exact Hrestrxws.
  }
  assert (forall n (p : n<=m), A n (restr n p xm)) as Hrestr. {
    assert (forall k (p : m-k<=m), A (m-k) (restr (m-k) p xm)) as Hrek. {
      induction k.
      - assert (m-0 =m) as Hm0 by lia.
        intro p. rewrite -> elmt_restr_id. exact HAxm. exact Hm0.
      - intro r.
        assert (m-k <= m) as p by lia.
        assert (m-S k <= m - k) as q by lia.
        set (q' := le_succ_diag_r (m - S k)). 
        destruct (lt_ge_cases k m) as [Hkltm|Hmlek].
        -- assert (S (m - S k) <= m) as p'. lia.
           assert (S (m - S k) = m - k) as e. lia.
           rewrite <- (restr_restr' _ p' _ q').
           apply (Hrestr' _ (restr _ p' xm)).
           rewrite -> (elmt_restr_eq A _ (m-k) m _ p) by lia.
           apply IHk.
        -- rewrite -> (elmt_restr_eq A _ (m-k) m _ p) by lia.
           apply IHk.
    }
    intros n p.
    set (k:=(PeanoNat.Nat.le_exists_sub n m p)). 
    destruct k as [k [Hk' _]].
    assert (m - k <= m) as p' by lia.
    rewrite -> (elmt_restr_eq A _ (m-k) _ _ p') by lia.
    apply Hrek.
  }
  clear Hrestr'.
  rewrite -> Hdiag.
  unfold xws.
  simpl.
  assert (m>=m) as Hmgem by lia.
  clear R Hsucc.
  split.
  - rewrite <- (@restr_id X m (PeanoNat.Nat.le_refl m)).
    assert (m + (m-m) = m) as e by lia.
    apply (restr_eq' e). rewrite <- Hxm0.
    apply wrd_seq_eq. lia.
  - intro n. 
    destruct (lt_ge_cases n m) as [Hnltm|Hmlen].
    -- assert (n<=m) as p by lia.
       unfold xs.
       rewrite -> diagonal_eq.
       rewrite -> (Hrestrxm _ p).
       apply Hrestr.
       apply Hrestrxws.
    -- unfold xs.
       rewrite -> diagonal_eq.
       unfold xws. 
       assert (m+(n-m)=n) as e by lia.
       rewrite -> (restr_cast_wrd_eq e).
       unfold xmws.
       set (Axm := (proj2_sig (projT2 (xs' (n - m))))).
       rewrite -> cast_wrd_pred_id.
       rewrite -> cast_wrd_pred_id.
       exact (proj2_sig (projT2 (xs' (n - m)))).
       apply Hrestrxws.
Qed.

Lemma ensemble_inverse_limits : forall {X} (A : forall n, Ensemble (Wrd n X)) (Ainf : Ensemble (Seq X)),
  (forall n, inhabited (A n)) -> 
  (forall m n (p:m<=n), apply (restr m p) (A n) = A m) ->
  (Ainf = fun (xs : Seq X) => forall n, A n (projw n xs)) ->
    (forall n, apply (projw n) Ainf = A n).
Proof. 
  intros X A Ainf HAi HAr HAinf.
  unfold apply.
  intro n.
  apply functional_extensionality. intro xn.
  apply propositional_extensionality.
  split.
  - rewrite -> HAinf.
    intro Hexs. destruct Hexs as [xs [Hxs Hxn]]. 
    rewrite <- Hxn.
    exact (Hxs n).
  - intro HAxn.
    assert (exists xs, projw n xs = xn /\ forall m, A m (projw m xs)) as Hxs. {
      apply (@word_sequence_exists X A).
      - apply HAxn.
      - clear HAxn xn n.
        intros n xSn HAxSn.
        specialize (HAr n (S n) (le_succ_diag_r n)).  
        unfold apply in HAr.
        rewrite <- HAr.
        exists xSn.
        split.
        exact HAxSn.
        apply restr_eq.
      - clear HAxn xn n. 
        intros n xn HAn.
        specialize (HAr n (S n) (le_succ_diag_r n)).  
        unfold apply in HAr.
        rewrite <- HAr in HAn.
        exact HAn.
    }
    destruct Hxs as [xs [Hpxs HAxs]].
    exists xs.
    split.
    -- rewrite -> HAinf. exact HAxs.
    -- exact Hpxs.
Qed.


Theorem inhabited_ensemble_monad_has_inverse_limits :
  has_inverse_limits (@InhabitedEnsemble) (InhabitedEnsemble_Monad).
Proof.
  unfold InhabitedEnsemble_Monad.
  unfold has_inverse_limits, is_inverse_sequence.
  intros X A' Hinvseq'.
  set ( A := (fun n => ensmbl (A' n))).
  assert ( forall n, inhabited (A n)) as HA. {
    exact (fun n => ensmbl_inhabited (A' n)). }
  assert (forall m n (p : m<=n), apply (@restr X n m p) (A n) = (A m)) as Hinvseq. {
     intros m n p. 
     replace (A m) with (ensmbl (A' m)) by (exact (eq_refl (A m))).
     specialize (Hinvseq' m n p).
     rewrite <- Hinvseq'.
     simpl.
     symmetry.
     apply image_singleton_apply.
  }
  clear Hinvseq'.
  unfold is_inverse_limit.
  unfold Mlift, Mbind, Mpure.
  unfold inhabited_image, inhabited_singleton. simpl.
  set ( Ainf := (fun (xs : nat -> X) => forall n, (A n) (projw n xs)) ).
  assert (inhabited Ainf) as Ainf_inhabited. {
    set (Hp0 := @ensemble_inverse_limits).
    specialize (Hp0 X A Ainf (HA) (Hinvseq) (eq_refl Ainf) 0).
    unfold apply in Hp0.
    destruct (HA 0) as [x0 Hx0]. 
    rewrite <- Hp0 in Hx0.
    destruct Hx0 as [xs [HAxs _]].
    exists xs. exact HAxs.
  }
  set (Ainf' := Build_InhabitedEnsemble (Seq X) Ainf Ainf_inhabited).
  exists Ainf'.
  unfold Ainf'.
  intro n.
  replace (A' n) with (Build_InhabitedEnsemble (Wrd n X) (A n) (HA n)).
  2: unfold A; apply inhabited_ensemble_eq; reflexivity. 
  apply inhabited_ensemble_eq.
  simpl.
  replace (image (fun x => singleton (projw n x)) Ainf) with (apply (projw n) Ainf).
  apply ensemble_inverse_limits.
  exact HA.
  exact Hinvseq.
  exact (eq_refl Ainf).
  symmetry. apply image_singleton_apply.
Qed.

End EnsembleMonads.
