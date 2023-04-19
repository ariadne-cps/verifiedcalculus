(************************************************************************)
(* Copyright 2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModels.
Require Export PolynomialModelsSum.

Section Polynomial_Models_Difference.

Open Scope R_scope.

Context `{F : Type} `{FltF : Float F}.


Fixpoint Pnegate (p : list (nat * F)) : list (nat * F) :=
  match p with 
  | nil => nil
  | (m0,c0) :: p1 => (m0, Fneg c0) :: (Pnegate p1)
  end.

Lemma Pnegate_eq_nil : Pnegate nil = nil.
Proof.
  intros. trivial.
Qed.
 
Lemma Pnegate_eq_cons : forall a0 p1, 
  Pnegate (a0::p1) = (fst a0, Fneg (snd a0)) :: Pnegate p1.
Proof.
  intros. destruct a0. trivial.
Qed.
 
Proposition is_sorted_polynomial_negate : forall p,
  is_sorted_fst p -> is_sorted_fst (Pnegate p).
Proof.
  intros p.
  induction p as [|a0 p1].
  - simpl. tauto.
  - destruct a0 as [m0 c0].
    destruct p1 as [|a1 p2].
    -- intros Hs. simpl. apply is_sorted_fst_one.
    -- destruct a1 as [m1 c1].
       intros Hs.
       simpl.
       apply (is_sorted_fst_cons _ _ (m1,Fneg c1)).
       --- trivial.
       --- simpl.
           apply (is_sorted_fst_cons_lt _ _ _ Hs).
       --- set (a1 := (m1,c1)).
           replace (m1, Fneg c1) with (fst a1, Fneg (snd a1)) by trivial.
           rewrite <- Pnegate_eq_cons.
           apply IHp1.
           apply (is_sorted_fst_cons_inv (m0,c0)). 
           exact Hs.
Qed.
  
 
Definition PMneg (t : PolynomialModel) : PolynomialModel :=
  {| polynomial := Pnegate t.(polynomial);
     sorted := is_sorted_polynomial_negate t.(polynomial) t.(sorted);
     error := t.(error) |}.
     
Theorem PMneg_correct : forall t f,
  PMmodels t f -> PMmodels (PMneg t) (fun x => - f x).
Proof.
  intros t.
  destruct t as [p Hs e].
  induction p as [|a0 p1].
  - unfold PMneg, PMmodels. simpl.
    intros f H x Hx.
    specialize (H x Hx).
    rewrite -> Rminus_0_l in *.
    rewrite -> Rabs_Ropp.
    exact H.
  - assert (is_sorted_fst p1) as Hs1. { apply (is_sorted_fst_cons_inv a0). exact Hs. }
    specialize (IHp1 Hs1).
    destruct a0 as [m0 c0].
    intros f H x Hx.
    set (f1 := fun x => f x - (FinjR c0) * x^m0).
    assert (f x = (FinjR c0) * x^m0 + f1 x) as Hf1 by (unfold f1; field).
    specialize (IHp1 f1).
    unfold PMneg, PMmodels in *.
    simpl in *.
    replace (FinjR (Fneg c0) * x ^ m0 + 
              Pax_eval (Pnegate p1) x - - f x)
      with (Pax_eval (Pnegate p1) x - - f1 x)
      by (rewrite -> Hf1; rewrite -> flt_neg_exact; field). 
      apply IHp1; [|exact Hx].
      intros x' Hx'.
      replace (Pax_eval p1 x' - f1 x') with (FinjR (snd (m0, c0)) * x' ^ fst (m0, c0) + Pax_eval p1 x' - f x').
      apply H; exact Hx'.
      unfold f1; simpl; field.
Qed.
    

 
Definition PMsub t1 t2 := PMadd t1 (PMneg t2).

Theorem PMsub_correct : forall t1 t2 f1 f2, 
  PMmodels t1 f1 -> PMmodels t2 f2 -> PMmodels (PMsub t1 t2) (fun x => f1 x - f2 x).
Proof.
  intros t1 t2 f1 f2 H1 H2.
  unfold PMsub, Rminus.
  apply PMadd_correct. exact H1.
  set ( f2s := fun x => - f2 x ).
  apply PMneg_correct. exact H2.
Qed.



Close Scope R_scope.

End Polynomial_Models_Difference.
