(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export R_addenda.
Require Export Floats.
Require Export PolynomialModels.
Require Import Recdef.
Require Import Lia.


Section Polynomial_Models.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.

(*
Fixpoint Psweep (r : (nat * F) -> bool) (p : Polynomial) : (Polynomial * F) :=
  match p with
  | nil => (nil,Fnull)
  | p0 :: p1 => let (sp1, e1) := (Psweep r p1) in 
                  if (r p0) then (rp1, Fadd up (Fabs (snd p0)) e1) else (p0 :: sp1, e1)
  end
.
*)

Fixpoint Psweep (r : (nat * F) -> bool) (p : Polynomial) : (Polynomial * F) :=
  match p with
  | nil => (nil,Fnull)
  | p0 :: p1 => if (r p0) 
                  then (fst (Psweep r p1), Fadd up (Fabs (snd p0)) (snd (Psweep r p1))) 
                  else (p0 :: fst (Psweep r p1), snd (Psweep r p1))
  end
.

Fixpoint Psweep_ax_error (r : (nat * F) -> bool) (p : Polynomial) : R :=
  match p with
  | nil => 0%R
  | p0::p1 => (if (r p0) then Rabs (FinjR (snd p0)) else 0%R) + Psweep_ax_error r p1
  end.
  
Lemma Psweep_ax_error_true : forall r a0 p1, (true = r a0) -> 
  Psweep_ax_error r (a0::p1) = Rabs (FinjR (snd a0)) + Psweep_ax_error r p1.
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Lemma Psweep_ax_error_false : forall r a0 p1, (false = r a0) -> 
  Psweep_ax_error r (a0::p1) = Psweep_ax_error r p1.
Proof.
  intros. simpl. rewrite <- H. simpl. apply Rplus_0_l.
Qed.


Lemma list_head_some : forall {X} (l : list X) (l0 : X), (head l = Some l0) -> (exists l1, l=l0::l1).
Proof.
  intros X l l0 H.
  destruct l.
  - inversion H.
  - unfold hd_error in H. inversion H. simpl. exists l. reflexivity.
Qed.

Lemma Psweep_true : forall r a0 p1, (true = r a0) -> fst (Psweep r (a0::p1)) = fst (Psweep r p1).
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Lemma Psweep_false : forall r a0 p1, (false = r a0) -> fst (Psweep r (a0::p1)) = a0 :: fst (Psweep r p1).
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Lemma Psweep_error_true : forall r a0 p1, (true = r a0) -> 
  snd (Psweep r (a0::p1)) = Fadd up (Fabs (snd a0)) (snd (Psweep r p1)).
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Lemma Psweep_error_false : forall r a0 p1, (false = r a0) -> 
  snd (Psweep r (a0::p1)) = snd (Psweep r p1).
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

 
Lemma Psweep_head_true : forall r a0 p1, (true = r a0) -> head (fst (Psweep r (a0::p1))) = head (fst (Psweep r p1)).
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Lemma Psweep_head_false : forall r a0 p1, (false = r a0) -> head (fst (Psweep r (a0::p1))) = Some a0.
Proof.
  intros. simpl. rewrite <- H. simpl. reflexivity.
Qed.

Lemma Psweep_head_leq : forall (r:nat*F->bool) (p:list (nat*F)), (is_sorted_fst p) ->  
  match (head p, head (fst (Psweep r p))) with
    | (Some a0,Some sa0) => ((fst a0) <= (fst sa0))%nat
    | (_,_) => True
  end.
Proof.
  intros r p Hsrtp.
  induction p as [|a0 p1]. 
  - simpl. trivial.
  - simpl.
    remember (r a0) as ra0.
    destruct ra0.
    -- (* Case (r a0) = true : drop a0 *)
       remember (fst (Psweep r p1)) as swp1.
       assert (is_sorted_fst p1) as Hsrtp1. { apply (is_sorted_fst_cons_inv a0). exact Hsrtp. }
       apply IHp1 in Hsrtp1 as IHp1'.
       destruct p1 as [|a1 p2].
       --- simpl in Heqswp1. rewrite -> Heqswp1. simpl. trivial.
       --- simpl in IHp1'. 
           destruct swp1 as [|swa1 swp2]. simpl. trivial.
           assert ((fst a1 <= fst swa1)%nat) as Ha1. { apply IHp1'. }
           assert ((fst a0 < fst a1)%nat) as Ha0. { apply (is_sorted_fst_cons_lt a0 a1 p2). exact Hsrtp. }
           apply (Nat.le_trans _ (fst a1)).  apply Nat.lt_le_incl. exact Ha0. exact Ha1.
    -- (* Case (r a0) = true : keep a0 *)
       simpl. apply Nat.eq_le_incl. reflexivity.
Qed.


Proposition Psweep_sorted : forall r p, is_sorted_fst p -> is_sorted_fst (fst (Psweep r p)).
Proof.
  intros r p Hsrtp.
  
  induction p as [|a0 p1 IHp1].
  - simpl. trivial.
  - assert (is_sorted_fst p1) as Hsrtp1. {
      apply (is_sorted_fst_cons_inv a0). 
      exact Hsrtp.
    }
    assert (is_sorted_fst (fst (Psweep r p1))) as Hsrtswp1. {
      apply IHp1. 
      exact Hsrtp1. 
    }
    apply (Psweep_head_leq r p1) in Hsrtp1 as Hswa1.
    remember (r a0) as ra0.
    destruct ra0.  
    -- (* Case drop term a0. *)
       rewrite -> Psweep_true by (exact Heqra0).
       exact Hsrtswp1.
    -- (* Case keep term a0. *)
       rewrite -> Psweep_false by (exact Heqra0).
       remember (fst (Psweep r p1)) as swp1.
       destruct swp1 as [|swa1 swp2].
       exact (is_sorted_fst_one a0).
       apply (is_sorted_fst_cons a0 (swa1::swp2) swa1).
       --- trivial.
       --- destruct p1 as [|a1 p2].
           ---- unfold Psweep in Heqswp1. simpl. inversion Heqswp1.
           ---- apply (Nat.lt_le_trans _ (fst a1)).
                ----- apply (is_sorted_fst_cons_lt _ _ p2). exact Hsrtp.
                ----- apply Hswa1.
       --- exact Hsrtswp1.
Qed.




Lemma Psweep_head_leq' : forall r p, (is_sorted_fst p) -> (fst (Psweep r p)) <> nil -> (exists a sa, (head p = Some a /\ head (fst (Psweep r p)) = Some sa /\ (fst a <= fst sa)%nat)).
Proof.
   intros r p.
   induction p.
   - simpl. contradiction.
   - intros Hsrtp Hnil.
     rename p into p1, a into a0.
     exists a0.
     remember (r a0) as ra0.
     destruct ra0.
     -- simpl. 
        rewrite <- Heqra0.
        simpl.
        assert (is_sorted_fst p1) as Hsrtp1. { 
          apply (is_sorted_fst_cons_inv a0 p1). exact Hsrtp. }
        assert (fst (Psweep r p1) <> nil) as Hnilp1. {
          rewrite <- (Psweep_true r a0) by (exact Heqra0). exact Hnil. 
        }
        apply IHp in Hsrtp1 as IHp'.
        destruct IHp' as [a1 IHp']. destruct IHp' as [sa1 IHp'].
        destruct IHp' as [Ha1 IHp'].
        destruct IHp' as [Hswp1  Ha1lesa1].
        exists sa1.
        split.
          reflexivity.
        split.
          exact Hswp1.
          apply (Nat.le_trans _ (fst a1) _).
          apply Nat.lt_le_incl.
          apply (is_sorted_fst_cons_lt _ _ (tl p1)).
          assert (p1 = a1::tl p1) as Hp1. { 
            apply hd_error_tl_repr. split. exact Ha1. reflexivity. 
          }
          rewrite <- Hp1. apply Hsrtp. exact Ha1lesa1.
          exact Hnilp1.
     -- simpl.
        rewrite <- Heqra0.
        simpl.
        exists a0.
        split. trivial. split. trivial. apply Nat.eq_le_incl. reflexivity.
Qed.
  
  
  

Proposition Psweep_sorted' : forall r p, is_sorted_fst p -> is_sorted_fst (fst (Psweep r p)).
Proof.
  intros r p Hsrtp.
  
  induction p as [|a0 p1 IHp1].
  - simpl. trivial.
  - assert (is_sorted_fst p1) as Hsrtp1. {
      apply (is_sorted_fst_cons_inv a0). 
      exact Hsrtp.
    }
    assert (is_sorted_fst (fst (Psweep r p1))) as Hsrtswp1. {
      apply IHp1. 
      exact Hsrtp1. 
    }
    remember (r a0) as ra0.
    destruct ra0.  
    -- (* Case drop term a0. *)
       rewrite -> Psweep_true by (exact Heqra0).
       exact Hsrtswp1.
    -- (* Case keep term a0. *)
       rewrite -> Psweep_false by (exact Heqra0).
       remember (fst (Psweep r p1)) as swp1.
       destruct swp1 as [|swa1 swp2].
       exact (is_sorted_fst_one a0).
       apply (is_sorted_fst_cons a0 (swa1::swp2) swa1).
       --- trivial.
       --- destruct p1 as [|a1 p2].
           ---- unfold Psweep in Heqswp1. simpl. inversion Heqswp1.
           ---- apply (Nat.lt_le_trans _ (fst a1)).
                apply (is_sorted_fst_cons_lt _ _ p2). exact Hsrtp.
                remember (a1::p2) as p1.
                assert (exists a1' sa1', (head p1 = Some a1' /\ head (fst (Psweep r p1)) = Some sa1' /\ (fst a1' <= fst sa1')%nat)) as H. {
                  apply Psweep_head_leq'. 
                    exact Hsrtp1.
                    rewrite <- Heqswp1. discriminate.
                }
                destruct H as [a1' H]. destruct H as [swa1' H].
                destruct H as [Ha1 H]. destruct H as [Hswa1 H].
                rewrite -> Heqp1 in Ha1. simpl in Ha1. injection Ha1 as Ha1. 
                rewrite <- Heqswp1 in Hswa1. simpl in Hswa1. injection Hswa1 as Hswa1.
                rewrite <- Ha1 in H.
                rewrite <- Hswa1 in H.
                exact H.
       --- exact Hsrtswp1.
Qed.



Definition PMsweep (r : (nat * F) -> bool) (t : PolynomialModel) : PolynomialModel :=
  match t with
  | {| polynom:=p; polynom_sorted:= H_p; error :=e |} =>
        {| polynom:=fst (Psweep r p); polynom_sorted := Psweep_sorted r p H_p; error := Fadd up e (snd (Psweep r p)) |}
  end.  

Definition Pmodels p f e := forall x, -1<=x<=1 -> Rabs (Pax_eval p x - f x) <= e.

Theorem Psweep_pre_correct : forall r p f e, 
  Pmodels p f e -> Pmodels (fst (Psweep r p)) f (Psweep_ax_error r p + e).
Proof.
  intros r p f e.
  intro H.
  intros x Hx.
  specialize (H x Hx).
  revert e f H.
  
  induction p as [|a0 p1].
  - intros e f. 
    simpl.
    rewrite -> Rplus_0_l.
    tauto.
  - intros e f. 
    remember (fun x => (f x - FinjR (snd a0) * x ^ (fst a0))) as f1.
    remember (f x - FinjR (snd a0) * x ^ (fst a0)) as f1x.
    remember (r a0) as ra0.
    destruct ra0.
    -- (* Case r a0 = true : drop term *)
       simpl; rewrite <- Heqra0; simpl.
       remember (Rabs (FinjR (snd a0)) + e) as e1.
       specialize (IHp1 e f1). 
       assert (Pax_eval (a0::p1) x - f x = Pax_eval p1 x - f1 x) as Hf1. {
         rewrite -> Heqf1. simpl. ring. }
       rewrite <- Pax_eval_eq_1. rewrite -> Hf1.
       intros Hp1x.
       apply IHp1 in Hp1x as IHp1x.
       assert (Rabs (Pax_eval (fst (Psweep r p1)) x - f x) <=
         Rabs (Pax_eval (fst (Psweep r p1)) x - f1 x) + Rabs (f1 x - f x)) as Hd;
           [apply Rabs_dist_triang|].
       assert (f1 x - f x = - (FinjR (snd a0) * x ^ (fst a0))) as Hy0. {
         rewrite -> Heqf1. ring. }
       apply (Rle_trans _ _ _ Hd).
       apply Rle_trans with ((Psweep_ax_error r p1 + e) + Rabs (f1 x - f x)).
       --- apply Rplus_le_compat_r. exact IHp1x.
       --- rewrite -> Hy0.
           rewrite -> Rabs_Ropp.
           assert (Rabs (FinjR (snd a0) * x^(fst a0)) <= Rabs (FinjR (snd a0))) as Ha0. {
             rewrite -> Rabs_mult.
             stepr (Rabs (FinjR (snd a0))*1). 
               apply Rmult_le_compat_l.
               apply Rabs_pos.
               apply Rabs_pow_le_1. apply Rabs_le_1; [apply Hx|apply Hx].
               apply Rmult_1_r.
           }
           apply Rle_trans with ((Psweep_ax_error r p1 + e) + Rabs(FinjR (snd a0))). {
             apply Rplus_le_compat_l. exact Ha0. }
           remember (Psweep_ax_error r p1) as swe1.
           remember (Rabs (FinjR (snd a0))) as e0.
           assert (swe1 + e + e0 = e0 + swe1 + e) as Heq by  (ring).
           right. exact Heq.
    -- (* Case r a0 = true : keep term *)
       simpl; rewrite <- Heqra0; simpl. 
       specialize (IHp1 e f1). 
       intro Hp0.
       replace (FinjR (snd a0)*x^(fst a0)+Pax_eval (fst (Psweep r p1)) x - f x)
         with (Pax_eval (fst (Psweep r p1)) x - f1 x); [|rewrite -> Heqf1; ring].  
       rewrite -> Rplus_0_l.
       apply IHp1.
       rewrite -> Heqf1. 
       replace (Pax_eval p1 x - (f x - FinjR (snd a0)*x^(fst a0)))
          with (FinjR (snd a0)*x^(fst a0) + Pax_eval p1 x - f x).
       exact Hp0.
       ring.
Qed.

Theorem PMsweep_correct : forall r t f, PMmodels t f -> PMmodels (PMsweep r t) f.
Proof.
  intros r t f.
  intro H.
  intros x Hx.
  destruct t as [p Hp e].
  unfold PMmodels in H.
  simpl in H. simpl.
  apply Rle_trans with ((Psweep_ax_error r p) + (FinjR e)).
  - assert (Pmodels (fst (Psweep r p)) f (Psweep_ax_error r p + (FinjR e)) ) as Hm. {
      apply Psweep_pre_correct. unfold Pmodels. exact H. }
    unfold Pmodels in Hm.
    apply Hm. apply Hx.
  - clear H.
    revert e.
    induction p as [|a0 p1].
    -- intro e. simpl. rewrite -> Rplus_comm. 
       replace 0 with (FinjR (NinjF 0%nat)) by (apply flt_ninjr).
       apply flt_add_up_le.
    -- assert (is_sorted_fst p1) as Hsrtp1. { apply (is_sorted_fst_cons_inv a0). exact Hp. }
       specialize (IHp1 Hsrtp1).
       intro e.
       remember (r a0) as ra0.
       destruct ra0.
       --- rewrite -> Psweep_ax_error_true by (exact Heqra0).
           rewrite -> Psweep_error_true by (exact Heqra0).
           (* Take e:=Fabs (snd a0) in IHp1. 
              This is not the original intention of the induction,
                but handles the second Fadd up. *)
              rewrite <- flt_abs_exact in *.
              apply Rle_trans with (FinjR (Fadd up (Fabs (snd a0)) (snd (Psweep r p1)))+FinjR e).
              ---- apply Rplus_le_compat_r. rewrite -> Rplus_comm. apply IHp1.
              ---- rewrite -> Rplus_comm. apply flt_add_up_le.
       --- rewrite -> Psweep_ax_error_false by (exact Heqra0).
           rewrite -> Psweep_error_false by (exact Heqra0).
           apply IHp1.
Qed.

Close Scope R_scope.

End Polynomial_Models.
