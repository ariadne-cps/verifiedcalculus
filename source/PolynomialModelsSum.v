(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export PolynomialModels.
Require Import Recdef.
Require Import Lia.
Require Import Ring.


Section Polynomial_Models_Sum.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Function pre_merge (p1p2 : list (nat*F) * list (nat*F))   
    {measure (fun l1l2=> (length (fst l1l2) + length (snd l1l2)))%nat p1p2} : list (nat*F) :=
  match p1p2 with
  | (nil, nil) => nil
  | (nil, fn2 :: p2') => fn2 :: p2'
  | (fn1 :: p1', nil) => fn1 :: p1'
  | (fn1 :: p1' , fn2 :: p2') =>
    match lt_eq_lt_dec (fst fn1) (fst fn2) with
    | inleft (left _) => (fst fn1 , snd fn1) :: pre_merge (p1',(fn2 :: p2'))
    | inleft (right _) => (fst fn1, Fadd_near (snd fn1) (snd fn2)) :: pre_merge (p1',p2')
    | inright _ => (fst fn2 , snd fn2) :: pre_merge  ((fn1 :: p1'),p2')
    end
  end.
Proof.
 intros; simpl; lia.
 intros; simpl; lia.
 intros; simpl; lia.
Time Qed.


Lemma pre_merge_eq_nil_nil: pre_merge (nil,nil) = nil.
Proof.
 intros; rewrite pre_merge_equation; trivial.
Qed.

Lemma pre_merge_eq_nil_cons: forall fn2 p2, pre_merge (nil,fn2 :: p2) = fn2 :: p2.
Proof.
 intros fn2 p2; rewrite pre_merge_equation; trivial.
Qed.

Lemma pre_merge_eq_cons_nil: forall fn1 p1, pre_merge (fn1 :: p1, nil) = fn1 :: p1.
Proof.
 intros fn1 p1; rewrite pre_merge_equation; trivial.
Qed.

Lemma pre_merge_eq_cons_cons: forall fn1 p1 fn2 p2,
  pre_merge (fn1 :: p1, fn2 :: p2) =
                 match lt_eq_lt_dec (fst fn1) (fst fn2) with
                 | inleft (left _) => (fst fn1 , snd fn1) :: pre_merge (p1,(fn2 :: p2))
                 | inleft (right _) => (fst fn1, Fadd_near (snd fn1) (snd fn2)) :: pre_merge (p1,p2)
                 | inright _ => (fst fn2 , snd fn2) :: pre_merge ((fn1 :: p1),p2)
                 end.
Proof.
 intros fn1 p1 fn2 p2; rewrite pre_merge_equation; trivial.
Qed.

Hint Resolve pre_merge_eq_nil_nil pre_merge_eq_nil_cons pre_merge_eq_cons_nil pre_merge_eq_cons_cons.

Lemma pre_merge_eq_1: forall p, pre_merge (p,nil) = p.
Proof.
 intros [|fn p']; auto.
Qed.

Lemma pre_merge_eq_2: forall p, pre_merge (nil,p) = p.
Proof.
 intros [|fn p']; auto.
Qed.

Ltac local_tactic_prove_pre_merge_equation :=
 intros fn1 p1 fn2 p2 H; rewrite pre_merge_eq_cons_cons;
 destruct (lt_eq_lt_dec (fst fn1) (fst fn2)) as [[H_ | H_f] | H_f];
 trivial; contradict H; lia.


Lemma pre_merge_eq_3: forall fn1 p1 fn2 p2, (fst fn1 < fst fn2) %nat ->
 pre_merge (fn1 :: p1, fn2 :: p2) = (fst fn1 , snd fn1) :: pre_merge (p1,(fn2 :: p2)).
Proof.
 local_tactic_prove_pre_merge_equation.
Qed.

Lemma pre_merge_eq_4: forall fn1 p1 fn2 p2, (fst fn1 = fst fn2) %nat ->
 pre_merge (fn1 :: p1, fn2 :: p2) = (fst fn1, Fadd_near (snd fn1) (snd fn2)) :: pre_merge (p1,p2).
Proof.
 local_tactic_prove_pre_merge_equation.
Qed.

Lemma pre_merge_eq_5: forall fn1 p1 fn2 p2, (fst fn2 < fst fn1) %nat ->
 pre_merge (fn1 :: p1, fn2 :: p2) = (fst fn2 , snd fn2) :: pre_merge ((fn1 :: p1),p2).
Proof.
 local_tactic_prove_pre_merge_equation.
Qed.

Lemma pre_merge_sorted: forall p1 p2, is_sorted p1 -> is_sorted p2 -> is_sorted (pre_merge (p1,p2)).
Proof.
 induction p1 as [|a1 p].
  (* nil , _ *)
  intros p2 H_ap1 H_ap2; rewrite pre_merge_eq_2; assumption.
  (* a1 :: p , _ *)
  induction p2 as [|b1 q]; intros H_ap H_bq.
   (* a1 :: p , nil *)
   rewrite pre_merge_eq_1; assumption.
   (* a1 :: p , b1 : q *)
   assert (H_p:is_sorted p); [apply is_sorted_cons_inv with (fst a1) (snd a1); rewrite <- (surjective_pairing); exact H_ap|].
   assert (H_q:is_sorted q); [apply is_sorted_cons_inv with (fst b1) (snd b1); rewrite <- (surjective_pairing); exact H_bq|].
   rewrite pre_merge_eq_cons_cons.
   destruct (lt_eq_lt_dec (fst a1) (fst b1)) as [[Hlt | Heq] | Hlt].
    (* 1 *)
    assert (hyp:is_sorted (pre_merge (p, b1 :: q))); [apply IHp; assumption|].
    destruct p as  [|a2 p'].
     (* a1 :: nil , b1 :: q *)
     rewrite pre_merge_eq_2; apply (is_sorted_cons (fst a1) (snd a1) (b1 :: q) b1); trivial.
     (* a1 :: a2 :: p1' , b1 :: q *)
     assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
     revert hyp.
     rewrite pre_merge_eq_cons_cons.
     destruct (lt_eq_lt_dec (fst a2) (fst b1)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
      apply (is_sorted_cons (fst a1) (snd a1)
                  ((fst a2, snd a2) :: pre_merge (p', b1 :: q))
                  (fst a2, snd a2) ); simpl; trivial...
      apply (is_sorted_cons (fst a1) (snd a1)
                      ((fst a2, Fadd_near (snd a2) (snd b1)):: pre_merge (p', q))
                      (fst a2, Fadd_near (snd a2) (snd b1))); simpl; trivial.
      apply (is_sorted_cons (fst a1) (snd a1)
                      ((fst b1, snd b1) :: pre_merge (a2 :: p', q))
                      (fst b1, snd b1)); simpl; trivial.
    (* 2 *)
    assert (hyp:is_sorted (pre_merge (p, q))); [apply IHp; assumption|].
    destruct p as  [|a2 p']; destruct q as [|b2 q'].
     (* a1 :: nil , b1 :: nil *)
     rewrite pre_merge_eq_nil_nil; apply is_sorted_one.
     (* a1 :: nil , b1 :: b2 :: q' *)
     assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
     assert (H_a1_b2: (fst a1<fst b2)%nat); [rewrite Heq; assumption|].
     rewrite pre_merge_eq_2; apply (is_sorted_cons (fst a1) (Fadd_near (snd a1) (snd b1)) (b2 :: q') b2); trivial.
     (* a1 :: a2 :: p' , b1 :: nil *)
     assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
     rewrite pre_merge_eq_1; apply (is_sorted_cons (fst a1) (Fadd_near (snd a1) (snd b1)) (a2 :: p') a2); trivial.
     (* a1 :: a2 :: p' , b1 :: b2 :: q' *)
     assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
     assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
     assert (H_a1_b2: (fst a1<fst b2)%nat); [rewrite Heq; assumption|].
     revert hyp.
     rewrite pre_merge_eq_cons_cons.
     destruct (lt_eq_lt_dec (fst a2) (fst b2)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
      apply (is_sorted_cons (fst a1) (Fadd_near (snd a1) (snd b1))
                  ((fst a2, snd a2) :: pre_merge (p', b2 :: q'))
                  (fst a2, snd a2) ); simpl; trivial...
      apply (is_sorted_cons (fst a1) (Fadd_near (snd a1) (snd b1))
                      ((fst a2, Fadd_near (snd a2) (snd b2)):: pre_merge (p', q'))
                      (fst a2, Fadd_near (snd a2) (snd b2))); simpl; trivial.
      apply (is_sorted_cons (fst a1) (Fadd_near (snd a1) (snd b1))
                      ((fst b2, snd b2) :: pre_merge (a2 :: p', q'))
                      (fst b2, snd b2)); simpl; trivial.
    (* 3 *)
    assert (hyp:is_sorted (pre_merge (a1 :: p, q))); [apply IHq; assumption|].
    destruct q as  [|b2 q'].
     (* a1 :: p , b1 :: nil *)
     rewrite pre_merge_eq_1; apply (is_sorted_cons (fst b1) (snd b1) (a1 :: p) a1); trivial.
     (* a1 :: p , b1 :: b2 :: q' *)
     assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
     revert hyp.
     rewrite pre_merge_eq_cons_cons.
     destruct (lt_eq_lt_dec (fst a1) (fst b2)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
      apply (is_sorted_cons (fst b1) (snd b1)
                  ((fst a1, snd a1) :: pre_merge (p, b2 :: q'))
                  (fst a1, snd a1) ); simpl; trivial...
      apply (is_sorted_cons (fst b1) (snd b1)
                      ((fst a1, Fadd_near (snd a1) (snd b2)):: pre_merge (p, q'))
                      (fst a1, Fadd_near (snd a1) (snd b2))); simpl; trivial.
      apply (is_sorted_cons (fst b1) (snd b1)
                      ((fst b2, snd b2) :: pre_merge (a1 :: p, q'))
                      (fst b2, snd b2)); simpl; trivial.
Qed.


Function pre_merge_error (p1p2: Polynomial * Polynomial)
   {measure (fun l1l2=> (length (fst l1l2) + length (snd l1l2)))%nat} : list (nat*F) :=
         match p1p2 with
         | (nil, nil) => nil
         | (nil, fn2 :: p2') => nil
         | (fn1 :: p1', nil) => nil
         | (fn1 :: p1' , fn2 :: p2') =>
                 match lt_eq_lt_dec (fst fn1) (fst fn2) with
                 | inleft (left _) => pre_merge_error (p1',(fn2 :: p2'))
                 | inleft (right _) => (fst fn1, Fdiv2_up (Fsub_up (Fadd_up (snd fn1) (snd fn2)) (Fadd_down (snd fn1) (snd fn2)))) :: pre_merge_error (p1',p2')
                 | inright _ => pre_merge_error ((fn1 :: p1'),p2')
                 end
         end.
Proof.
 intros; simpl; lia.
 intros; simpl; lia.
 intros; simpl; lia.
Time Qed.

Lemma pre_merge_error_eq_nil_nil : pre_merge_error  (nil,nil) = nil.
Proof.
 intros ; rewrite pre_merge_error_equation; trivial.
Qed.

Lemma pre_merge_error_eq_nil_cons : forall fn p, pre_merge_error  (nil,fn :: p) = nil.
Proof.
 intros fn p; rewrite pre_merge_error_equation; trivial.
Qed.

Lemma pre_merge_error_eq_cons_nil : forall fn p, pre_merge_error  (fn :: p, nil) = nil.
Proof.
 intros fn p; rewrite pre_merge_error_equation; trivial.
Qed.

Lemma pre_merge_error_eq_cons_cons : forall fn1 p1 fn2 p2,
  pre_merge_error (fn1 :: p1, fn2 :: p2) =
                    match lt_eq_lt_dec (fst fn1) (fst fn2) with
                    | inleft (left _) => pre_merge_error  (p1,(fn2 :: p2))
                    | inleft (right _) => (fst fn1, Fdiv2_up (Fsub_up (Fadd_up (snd fn1) (snd fn2)) (Fadd_down (snd fn1) (snd fn2)) )) :: pre_merge_error  (p1,p2)
                    | inright _ => pre_merge_error  ((fn1 :: p1),p2)
                    end.
Proof.
 intros  fn1 p1 fn2 p2; rewrite pre_merge_error_equation; trivial.
Qed.

Hint Resolve pre_merge_error_eq_nil_nil pre_merge_error_eq_nil_cons pre_merge_error_eq_cons_nil pre_merge_error_eq_cons_cons.

Lemma pre_merge_error_eq_1 : forall  p, pre_merge_error  (p,nil) = nil.
Proof.
 intros  [|fn p']; auto.
Qed.

Lemma pre_merge_error_eq_2 : forall  p, pre_merge_error  (nil,p) = nil.
Proof.
 intros  [|fn p']; auto.
Qed.

Ltac local_tactic_prove_pre_merge_error_equation :=
 intros  fn1 p1 fn2 p2 H; rewrite pre_merge_error_eq_cons_cons;
 destruct (lt_eq_lt_dec (fst fn1) (fst fn2)) as [[H_ | H_f] | H_f]; trivial; contradict H; lia.


Lemma pre_merge_error_eq_3 : forall  fn1 p1 fn2 p2, (fst fn1 < fst fn2) %nat ->
 pre_merge_error  (fn1 :: p1, fn2 :: p2) = pre_merge_error  (p1,(fn2 :: p2)).
Proof.
 local_tactic_prove_pre_merge_error_equation.
Qed.

Lemma pre_merge_error_eq_4 : forall  fn1 p1 fn2 p2, (fst fn1 = fst fn2) %nat ->
 pre_merge_error  (fn1 :: p1, fn2 :: p2) = (fst fn1, Fdiv2_up (Fsub_up (Fadd_up (snd fn1) (snd fn2)) (Fadd_down (snd fn1) (snd fn2)))) :: pre_merge_error  (p1,p2).
Proof.
 local_tactic_prove_pre_merge_error_equation.
Qed.

Lemma pre_merge_error_eq_5 : forall  fn1 p1 fn2 p2, (fst fn2 < fst fn1) %nat ->
 pre_merge_error  (fn1 :: p1, fn2 :: p2) = pre_merge_error  ((fn1 :: p1),p2).
Proof.
 local_tactic_prove_pre_merge_error_equation.
Qed.

Definition pre_merge_add_error p1 p2 : Polynomial := pre_merge_error (p1,p2).

Definition error_add t1 t2 : F := Fadd_up t1.(error) (Fadd_up t2.(error) (Fsum_snd_add up (pre_merge_add_error t1.(spolynom) t2.(spolynom)))).

Definition pre_merge_add_spolynom p1 p2 : list (nat*F) := pre_merge (p1,p2).

Definition merge_add_near sp1 sp2 : SparsePolynomial :=
       match sp1, sp2 with
       | {| polynom:=p1;polynom_sorted:= H1 |}, {| polynom:=p2; polynom_sorted:= H2 |} =>
               {| polynom:=pre_merge_add_spolynom p1 p2; polynom_sorted:=@pre_merge_sorted p1 p2 H1 H2 |}
       end.

Definition PMadd (t1 t2 : PolynomialModel) : PolynomialModel :=
 {| spolynom:= merge_add_near t1.(spolynom) t2.(spolynom); error:=error_add t1 t2 |}.

Lemma sum_add_up_nonneg:forall (t1 t2: PolynomialModel), 0<= FinjR ( Fsum_snd_add up (pre_merge_add_error (spolynom t1) (spolynom t2))).
Proof.
 intros [[p1 H1] e1].
 induction p1; intros [[p2 H2] e2].
  (* nil, _ *)
  simpl; unfold pre_merge_add_error; rewrite pre_merge_error_eq_2; simpl; rewrite flt_null; auto with real.

  (* a :: p1, _  *)
  induction p2.
   (* a::p1, nil *)
   simpl; unfold pre_merge_add_error; rewrite pre_merge_error_eq_1; simpl; rewrite flt_null; auto with real.
   (* a::p1, a0::p2 *)
   assert (H_p1:is_sorted p1); [apply is_sorted_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H1|].
   assert (H_p2:is_sorted p2); [apply is_sorted_cons_inv with (fst a0) (snd a0); rewrite <- (surjective_pairing); exact H2|].
   simpl in *.
   unfold pre_merge_add_error.
   rewrite pre_merge_error_eq_cons_cons.
   destruct (lt_eq_lt_dec (fst a) (fst a0)) as [[Hlt | Heq] | Hlt].

    apply (IHp1 H_p1 (Build_PolynomialModel (Build_SparsePolynomial (a0 :: p2) H2) e2)).
    apply Rle_trans with (FinjR (Fdiv2_up (Fsub_up (Fadd_up (snd a) (snd a0)) (Fadd_down (snd a) (snd a0)))) +
                          FinjR (Fsum_snd_add up (pre_merge_error (p1,p2)))); [|apply Rge_le; apply flt_add_up].
    apply Rplus_le_le_0_compat.
     (*    0 <= FinjR (div2_up (Fsub_up (add_up x y) (add_down x y))) *)
     generalize (snd a) (snd a0); intros x y.
     apply Rle_trans with (Rabs ( (FinjR  (Fadd_near x y))- ((FinjR x)+(FinjR y)) )).
       apply Rabs_pos.
       unfold Fadd_near, Fadd_up, Fadd_down.
       replace Fadd with (Fapply Add); [|trivial]. replace Rplus with (Rapply Add); [|trivial].
       apply flt_op_near_up_down_sub_hlf_up.
     apply (IHp1 H_p1 (Build_PolynomialModel (Build_SparsePolynomial p2 H_p2) e2)).

    apply IHp2; assumption.
Qed.


Lemma sum_add_up_property : forall (sp1 sp2:SparsePolynomial) x,  -1 <= x <= 1 ->
   Rabs (SPax_eval sp1 x + SPax_eval sp2 x - SPax_eval (merge_add_near sp1 sp2) x) <=
        FinjR (Fsum_snd_add up (pre_merge_add_error sp1 sp2)).
Proof.
 intros [p1 H1].
 induction p1; intros [p2 H2].
  intros  x _; simpl; unfold merge_add_near, pre_merge_add_spolynom, pre_merge_add_error in *.
  rewrite pre_merge_eq_2, pre_merge_error_eq_2; simpl.
  stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

  induction p2.
   intros x _; simpl; unfold merge_add_near, pre_merge_add_spolynom, pre_merge_add_error in *.
   rewrite pre_merge_eq_1, pre_merge_error_eq_1; simpl.
   stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

   intros x Hx.
   unfold merge_add_near, pre_merge_add_spolynom, pre_merge_add_error.
   assert (H_p1:is_sorted p1); [apply is_sorted_cons_inv with (fst a) (snd a); rewrite <- (surjective_pairing); exact H1|].
   assert (H_p2:is_sorted p2); [apply is_sorted_cons_inv with (fst a0) (snd a0); rewrite <- (surjective_pairing); exact H2|].
   assert (H_p1_a0_p2:=@pre_merge_sorted p1 (a0 :: p2)  H_p1 H2).

   unfold SPax_eval at 3.
   unfold polynom.
   rewrite pre_merge_eq_cons_cons, pre_merge_error_eq_cons_cons.
   destruct (lt_eq_lt_dec (fst a) (fst a0)) as [[Hlt | Hlt] | Hlt].
    (* 1 *)
    rewrite (SPax_eval_eq_1) with (H2:=H_p1).
    set (sp1:=Build_SparsePolynomial p1 H_p1).
    set (sp2:=Build_SparsePolynomial (a0 :: p2) H2).
    replace (Pax_eval ((fst a, snd a) :: pre_merge (p1, a0 :: p2)) x) with
            (FinjR (snd a) *(pow x (fst a)) + (SPax_eval (merge_add_near sp1 sp2) x)); [|trivial].
    replace (pre_merge_error (p1, a0 :: p2)) with
            (pre_merge_add_error sp1 sp2); [|trivial].
    stepl (Rabs (Pax_eval sp1 x +
                 Pax_eval sp2 x -
                 Pax_eval (merge_add_near sp1 sp2) x)).
      apply (IHp1 H_p1 sp2). exact Hx.
      remember (merge_add_near sp1 sp2) as sp12.
      f_equal; destruct sp12; simpl; ring.

    (* 2 *)

    simpl.
    apply Rle_trans with (  (FinjR(Fdiv2_up (Fsub_up (Fadd_up (snd a) (snd a0)) (Fadd_down (snd a) (snd a0)))) +
                                    FinjR(Fsum_snd_add up (pre_merge_add_error (Build_SparsePolynomial p1 H_p1) (Build_SparsePolynomial p2 H_p2))))).
    2: apply Rge_le. 2: apply flt_add_up.

    rewrite <- Hlt.
    set (sp1:=Build_SparsePolynomial p1 H_p1).
    set (sp2:=Build_SparsePolynomial p2 H_p2).
    stepl (Rabs ( ( (FinjR (snd a) + FinjR (snd a0)) * (pow x (fst a)) -
                     FinjR (Fadd_near (snd a) (snd a0)) * (pow x (fst a))
                   ) +
                  (SPax_eval sp1 x + SPax_eval sp2 x - SPax_eval (merge_add_near sp1 sp2) x)
                ) ).
    2:f_equal; simpl; unfold merge_add_near, pre_merge_add_spolynom; ring.
    apply Rle_trans with (Rabs ( FinjR (Fadd_near (snd a) (snd a0)) -
                                  (FinjR (snd a) + FinjR (snd a0))
                               ) * Rabs (pow x (fst a)) +
                         Rabs (SPax_eval sp1 x + SPax_eval sp2 x - SPax_eval (merge_add_near sp1 sp2) x) );
    [ rewrite <- Rabs_mult;
      replace ((FinjR (Fadd_near (snd a) (snd a0)) - (FinjR (snd a) + FinjR (snd a0))) * (pow x (fst a))) with
      (FinjR (Fadd_near (snd a) (snd a0))*(pow x (fst a)) - (FinjR (snd a) + FinjR (snd a0))*(pow x (fst a)));[|ring];
      rewrite Rabs_minus_sym; apply Rabs_triang; rewrite Rabs_minus_sym; apply Rabs_triang
    |].
    apply Rplus_le_compat; [| apply (IHp1 _ _ _ Hx)].
    apply Rle_trans with (Rabs(FinjR (Fadd_near (snd a) (snd a0)) - (FinjR (snd a) + FinjR (snd a0)))).
     assert (H_xn_l:-1 <= (pow x (fst a)) );[apply pow_Rle_l_1; elim Hx; trivial|].
     assert (H_xn_r:(pow x (fst a))<= 1 );[apply pow_Rle_r_1; elim Hx; trivial|].
     assert (H_xn_abs:Rabs (pow x (fst a))<=1). { apply Rabs_Rle_1. split. exact H_xn_l. exact H_xn_r. }
     stepr (Rabs (FinjR (Fadd_near (snd a) (snd a0)) - (FinjR (snd a) + FinjR (snd a0))) * 1); [|ring].
     apply Rmult_le_compat_l; trivial; apply Rabs_pos.

     unfold Fadd_near, Fadd_up, Fadd_down.
     replace Fadd with (Fapply Add); [|trivial].
     replace Rplus with (Rapply Add); [|trivial].
     apply flt_op_near_up_down_sub_hlf_up.

    (* 3 *)
    rewrite (SPax_eval_eq_1) with (H2:=H_p2).
    set (sp1:=Build_SparsePolynomial (a :: p1) H1).
    set (sp2:=Build_SparsePolynomial p2 H_p2).
    replace (Pax_eval ((fst a0, snd a0) :: pre_merge (a :: p1, p2)) x) with
            (FinjR (snd a0) *(pow x (fst a0)) + (SPax_eval (merge_add_near sp1 sp2) x)); [|trivial].
    replace (pre_merge_error (a :: p1, p2)) with
            (pre_merge_add_error sp1 sp2); [|trivial].
    stepl (Rabs (SPax_eval sp1 x +
                 SPax_eval sp2 x -
                 SPax_eval (merge_add_near sp1 sp2) x)) ;[|f_equal; ring].
    apply IHp2; assumption.
Qed.

Theorem PMadd_correct : forall (t1 t2: PolynomialModel) (f1 f2:R -> R),
  PMmodels t1 f1 -> PMmodels t2 f2 -> PMmodels (PMadd t1 t2) (fun x=> f1(x)+ f2(x)).
Proof.
 intros t1 t2 f1 f2 H1 H2 x hyp_x.
 specialize (H1 x hyp_x); specialize (H2 x hyp_x).
 assert (H_sum_err_nonneg:= sum_add_up_nonneg t1 t2).
 apply Rle_trans with (FinjR (error t1)+ FinjR (error t2) + FinjR (Fsum_snd_add up (pre_merge_add_error (spolynom t1) (spolynom t2)))).

  2:apply Rle_trans with (FinjR (error t1)+ FinjR (error t2) + FinjR (Fsum_snd_add up (pre_merge_add_error (spolynom t1) (spolynom t2))));
     [ apply Rplus_le_compat_l;
       generalize (FinjR (Fsum_snd_add up (pre_merge_add_error (spolynom t1) (spolynom t2)))) H_sum_err_nonneg; intros r H_r; lra
     | apply Rle_trans with (FinjR (error t1)+ FinjR (Fadd_up (error t2) (Fsum_snd_add up (pre_merge_add_error (spolynom t1) (spolynom t2)))));
       [(stepl (FinjR (error t1)+ (FinjR (error t2) + FinjR (Fsum_snd_add up (pre_merge_add_error (spolynom t1) (spolynom t2))))) by ring) ;
       apply Rplus_le_compat_l |] ; apply Rge_le; apply flt_add_up
     ].
 destruct t1 as [sp1 e1]; destruct t2 as [sp2 e2].
 simpl in *.
 set (p1_x:= SPax_eval sp1 x).
 set (p2_x:= SPax_eval sp2 x).
 set (pp_x:= SPax_eval (merge_add_near sp1 sp2) x).
 rewrite Rabs_minus_sym.
 stepl ( Rabs ( (f1(x) - p1_x) + (f2(x) - p2_x) + ( (p1_x + p2_x) - pp_x) ) ); [|f_equal; ring].
 apply Rle_trans with ( Rabs ( (f1(x) - p1_x) + (f2(x) - p2_x) ) + Rabs ( (p1_x + p2_x) - pp_x) ); [apply Rabs_triang |].
 apply Rplus_le_compat.
  apply Rle_trans with ( Rabs(f1(x) - p1_x) + Rabs (f2(x) - p2_x) );
  [ apply Rabs_triang
  | apply Rplus_le_compat; rewrite Rabs_minus_sym; assumption
  ].
 apply sum_add_up_property; assumption.
Qed.

Close Scope R_scope.

End Polynomial_Models_Sum.
