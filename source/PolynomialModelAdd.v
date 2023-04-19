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


Section Polynomial_Model_Add.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Definition Fadd_err_up x1 x2 := Fdiv2 up (Fsub up (Fadd up x1 x2) (Fadd down x1 x2)).


Function Padd (p1p2 : list (nat*F) * list (nat*F))   
    {measure (fun l1l2=> (length (fst l1l2) + length (snd l1l2)))%nat p1p2} : list (nat*F) :=
  match p1p2 with
  | (nil, nil) => nil
  | (nil, a2::p2') => a2 :: p2'
  | (a1::p1', nil) => a1 :: p1'
  | (a1::p1', a2::p2') =>
    match lt_eq_lt_dec (fst a1) (fst a2) with
    | inleft (left _) => (fst a1, snd a1) :: Padd (p1',a2 :: p2')
    | inleft (right _) => (fst a1, Fadd_near (snd a1) (snd a2)) :: Padd (p1',p2')
    | inright _ => (fst a2, snd a2) :: Padd (a1::p1',p2') 
    end
  end.
Proof.
 intros; simpl; lia.
 intros; simpl; lia.
 intros; simpl; lia.
Time Qed.


Lemma Padd_eq_nil_nil: Padd (nil,nil) = nil.
Proof.
  intros; rewrite Padd_equation; trivial.
Qed.

Lemma Padd_eq_nil_cons: forall fn2 p2, Padd (nil,fn2 :: p2) = fn2 :: p2.
Proof.
  intros fn2 p2; rewrite Padd_equation; trivial.
Qed.

Lemma Padd_eq_cons_nil: forall fn1 p1, Padd (fn1 :: p1, nil) = fn1 :: p1.
Proof.
  intros fn1 p1; rewrite Padd_equation; trivial.
Qed.

Lemma Padd_eq_cons_cons: forall a1 p1 a2 p2,
  Padd (a1 :: p1, a2 :: p2) =
    match lt_eq_lt_dec (fst a1) (fst a2) with
    | inleft (left _) => (fst a1, snd a1) :: Padd (p1,a2 :: p2)
    | inleft (right _) => (fst a1, Fadd_near (snd a1) (snd a2)) :: Padd (p1,p2)
    | inright _ => (fst a2, snd a2) :: Padd (a1::p1,p2) 
    end.
Proof.
 intros fn1 p1 fn2 p2; rewrite Padd_equation; trivial.
Qed.

Hint Resolve Padd_eq_nil_nil Padd_eq_nil_cons Padd_eq_cons_nil Padd_eq_cons_cons.

Lemma Padd_eq_nil_r: forall p, Padd (p,nil) = p.
Proof.
 intros [|fn p']; auto.
Qed.

Lemma Padd_eq_nil_l: forall p, Padd (nil,p) = p.
Proof.
 intros [|fn p']; auto.
Qed.

Ltac local_tactic_prove_Padd_equation :=
 intros fn1 p1 fn2 p2 H; rewrite Padd_eq_cons_cons;
 destruct (lt_eq_lt_dec (fst fn1) (fst fn2)) as [[H_ | H_f] | H_f];
 trivial; contradict H; lia.


Lemma Padd_eq_lt: forall fn1 p1 fn2 p2, (fst fn1 < fst fn2) %nat ->
 Padd (fn1 :: p1, fn2 :: p2) = (fst fn1 , snd fn1) :: Padd (p1,(fn2 :: p2)).
Proof.
 local_tactic_prove_Padd_equation.
Qed.

Lemma Padd_eq_eq: forall fn1 p1 fn2 p2, (fst fn1 = fst fn2) %nat ->
 Padd (fn1 :: p1, fn2 :: p2) = (fst fn1, Fadd_near (snd fn1) (snd fn2)) :: Padd (p1,p2).
Proof.
 local_tactic_prove_Padd_equation.
Qed.

Lemma Padd_eq_gt: forall fn1 p1 fn2 p2, (fst fn2 < fst fn1) %nat ->
 Padd (fn1 :: p1, fn2 :: p2) = (fst fn2 , snd fn2) :: Padd ((fn1 :: p1),p2).
Proof.
 local_tactic_prove_Padd_equation.
Qed.

(*
Definition pre_sum (p1 p2 : list (nat * F)) : list (nat*F) * F := Padd' (p1,p2).

Definition pre_sum_polynom p1 p2 := fst (pre_sum p1 p2).
Definition pre_sum_error p1 p2 := snd (pre_sum p1 p2).

Lemma pre_sum_eq_nil_nil: pre_sum nil nil = (nil,Fnull).
Proof. intros; unfold pre_sum; rewrite Padd'_equation; trivial. Qed.

Lemma pre_sum_eq_nil_cons: forall a2 p2, pre_sum nil (a2::p2) = (a2::p2,Fnull).
Proof. intros a2 p2; unfold pre_sum; rewrite Padd'_equation; trivial. Qed.

Lemma pre_sum_eq_cons_nil: forall a1 p1, pre_sum (a1::p1) nil = (a1::p1,Fnull).
Proof. intros a1 p1; unfold pre_sum; rewrite Padd'_equation; trivial. Qed.

Lemma pre_sum_eq_cons_cons: forall a1 p1 a2 p2,
  pre_sum (a1 :: p1) (a2 :: p2) =
    match lt_eq_lt_dec (fst a1) (fst a2) with
    | inleft (left _) => ( a1 :: fst (pre_sum p1 (a2::p2)), 
                           snd (pre_sum p1 (a2::p2)) )
    | inleft (right _) => ( (fst a1, Fadd_near (snd a1) (snd a2)) :: fst (pre_sum p1 p2),
                            Fadd up (Fadd_err_up (snd a1) (snd a2)) (snd (pre_sum p1 p2)) )
    | inright _ => ( a2 :: fst (pre_sum (a1::p1) p2), 
                           snd (pre_sum (a1::p1) p2) )
    end.
Proof. intros a1 p1 a2 p2; unfold pre_sum. rewrite Padd'_equation. trivial. Qed.

Lemma pre_sum_correct : forall (p1 p2 : list (nat*F)) x,  -1 <= x <= 1 ->
   Rabs (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (pre_sum_polynom p1 p2) x) <=
        FinjR (pre_sum_error p1 p2).
Proof.
  unfold pre_sum_polynom, pre_sum_error.
  
  intros p1;
  induction p1 as [|a1 p1].
    intros p2;
    induction p2 as [|a2 p2].

      intros x _; rewrite -> pre_sum_eq_nil_nil; simpl.
      stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

       intros x _; rewrite -> pre_sum_eq_nil_cons; simpl.
       stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

    induction p2 as [|a2 p2].
      intros x _; rewrite -> pre_sum_eq_cons_nil; simpl.
      stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

      intros x Hx.
      rewrite pre_sum_eq_cons_cons.
      destruct (lt_eq_lt_dec (fst a1) (fst a2)) as [[Hlt | Heq] | Hgt].
        (* 1: m1 <m2 *)
        - rewrite (Pax_eval_eq_nil_r). set (sp2:=a2::p2). simpl.
          stepl (Rabs (Pax_eval p1 x + Pax_eval sp2 x - Pax_eval (pre_sum_polynom p1 sp2) x)).
          apply (IHp1 sp2). exact Hx.
          f_equal. unfold pre_sum_polynom. simpl. ring.

        (* 2: m1=m2 *)
        - simpl. rewrite <- Heq;
          set (m:=fst a1); set (c1:=snd a1); set (c2:=snd a2).
          
          apply Rle_trans with ( FinjR (Fadd_err_up c1 c2) + FinjR (pre_sum_error p1 p2) ).
          2: apply Rge_le. 2: apply flt_add_up.

          stepl (Rabs ( ( (FinjR c1 + FinjR c2) * (pow x m) -
                           FinjR (Fadd_near c1 c2) * (pow x m)
                         ) +
                        (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (pre_sum_polynom p1 p2) x)
                      ) ).
          2: f_equal; unfold pre_sum_polynom; simpl; simpl; ring.
          apply Rle_trans with (Rabs ( FinjR (Fadd_near c1 c2) - (FinjR c1 + FinjR c2) ) * Rabs (pow x m) +
                                Rabs (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (pre_sum_polynom  p1 p2) x) );
          [ rewrite <- Rabs_mult;
            replace ((FinjR (Fadd_near c1 c2) - (FinjR c1 + FinjR c2)) * (pow x m)) with
            (FinjR (Fadd_near c1 c2)*(pow x m) - (FinjR c1 + FinjR c2)*(pow x m));[|ring];
            rewrite Rabs_minus_sym; apply Rabs_triang; rewrite Rabs_minus_sym; apply Rabs_triang
          |].
          apply Rplus_le_compat; [| apply (IHp1 _ _ Hx)].

           apply Rle_trans with (Rabs(FinjR (Fadd_near c1 c2) - (FinjR c1 + FinjR c2))).
           assert (H_xn_l:-1 <= (pow x m) );[apply pow_Rle_l_1; elim Hx; trivial|].
           assert (H_xn_r:(pow x m)<= 1 );[apply pow_Rle_r_1; elim Hx; trivial|].
           assert (H_xn_abs:Rabs (pow x m)<=1). { apply Rabs_Rle_1. split. exact H_xn_l. exact H_xn_r. }
           stepr (Rabs (FinjR (Fadd_near c1 c2) - (FinjR c1 + FinjR c2)) * 1); [|ring].
           apply Rmult_le_compat_l. trivial; apply Rabs_pos. exact H_xn_abs.

           assert (forall r1 r2, Rabs (r1-r2) = Rdist r1 r2) as Hdist. { unfold Rdist. trivial. }
           
           rewrite -> Hdist.
           unfold Fadd_near, Fadd_up, Fadd_down.
           replace Fadd with (Fapply Add); [|trivial].
           replace Rplus with (Rapply Add); [|trivial].
           unfold Fadd_err_up.
           apply (flt_op_near_up_down_sub_hlf_up Add c1 c2).
         
        (* 3 *)
        - rewrite (Pax_eval_eq_nil_r). set (sp1:=a1::p1). simpl.
          stepl (Rabs (Pax_eval sp1 x + Pax_eval p2 x - Pax_eval (pre_sum_polynom sp1 p2) x)).
            apply IHp2. exact Hx.
            f_equal. unfold pre_sum_polynom. simpl. ring.
Qed.
*)
  
Lemma Padd_sorted: forall p1 p2, is_sorted_fst p1 -> is_sorted_fst p2 -> is_sorted_fst (Padd (p1,p2)).
  induction p1 as [|a1 p].
  (* nil , _ *)
  intros p2 H_ap1 H_ap2; rewrite Padd_eq_nil_l; assumption.
  (* a1 :: p , _ *)
  induction p2 as [|b1 q]; intros H_ap H_bq.
   (* a1 :: p , nil *)
   rewrite Padd_eq_nil_r; assumption.
   (* a1 :: p , b1 : q *)
   assert (H_p:is_sorted_fst p); [apply is_sorted_fst_cons_inv with a1; exact H_ap|].
   assert (H_q:is_sorted_fst q); [apply is_sorted_fst_cons_inv with b1; exact H_bq|].
   rewrite Padd_eq_cons_cons.
   destruct (lt_eq_lt_dec (fst a1) (fst b1)) as [[Hlt | Heq] | Hlt].
    (* 1 *)
    assert (hyp:is_sorted_fst (Padd (p, b1 :: q))); [apply IHp; assumption|].
    destruct p as  [|a2 p'].
     (* a1 :: nil , b1 :: q *)
     rewrite Padd_eq_nil_l; apply (is_sorted_fst_cons (fst a1,snd a1) (b1 :: q) b1); trivial.
     (* a1 :: a2 :: p1' , b1 :: q *)
     assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
     revert hyp.
     rewrite Padd_eq_cons_cons.
     destruct (lt_eq_lt_dec (fst a2) (fst b1)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
      apply (is_sorted_fst_cons (fst a1,snd a1)
                  ((fst a2, snd a2) :: Padd (p', b1 :: q))
                  (fst a2, snd a2) ); simpl; trivial...
      apply (is_sorted_fst_cons (fst a1,snd a1)
                      ((fst a2, Fadd_near (snd a2) (snd b1)):: Padd (p', q))
                      (fst a2, Fadd_near (snd a2) (snd b1))); simpl; trivial.
      apply (is_sorted_fst_cons (fst a1,snd a1)
                      ((fst b1, snd b1) :: Padd (a2 :: p', q))
                      (fst b1, snd b1)); simpl; trivial.
    (* 2 *)
    assert (hyp:is_sorted_fst (Padd (p, q))); [apply IHp; assumption|].
    destruct p as  [|a2 p']; destruct q as [|b2 q'].
     (* a1 :: nil , b1 :: nil *)
     rewrite Padd_eq_nil_nil; apply is_sorted_fst_one.
     (* a1 :: nil , b1 :: b2 :: q' *)
     assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
     assert (H_a1_b2: (fst a1<fst b2)%nat); [rewrite Heq; assumption|].
     rewrite Padd_eq_nil_l; apply (is_sorted_fst_cons (fst a1, Fadd_near (snd a1) (snd b1)) (b2 :: q') b2); trivial.
     (* a1 :: a2 :: p' , b1 :: nil *)
     assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
     rewrite Padd_eq_nil_r; apply (is_sorted_fst_cons (fst a1,Fadd_near (snd a1) (snd b1)) (a2 :: p') a2); trivial.
     (* a1 :: a2 :: p' , b1 :: b2 :: q' *)
     assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
     assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
     assert (H_a1_b2: (fst a1<fst b2)%nat); [rewrite Heq; assumption|].
     revert hyp.
     rewrite Padd_eq_cons_cons.
     destruct (lt_eq_lt_dec (fst a2) (fst b2)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
      apply (is_sorted_fst_cons (fst a1,Fadd_near (snd a1) (snd b1))
                  ((fst a2, snd a2) :: Padd (p', b2 :: q'))
                  (fst a2, snd a2) ); simpl; trivial...
      apply (is_sorted_fst_cons (fst a1,Fadd_near (snd a1) (snd b1))
                      ((fst a2, Fadd_near (snd a2) (snd b2)):: Padd (p', q'))
                      (fst a2, Fadd_near (snd a2) (snd b2))); simpl; trivial.
      apply (is_sorted_fst_cons (fst a1, Fadd_near (snd a1) (snd b1))
                      ((fst b2, snd b2) :: Padd (a2 :: p', q'))
                      (fst b2, snd b2)); simpl; trivial.
    (* 3 *)
    assert (hyp:is_sorted_fst (Padd (a1 :: p, q))); [apply IHq; assumption|].
    destruct q as  [|b2 q'].
     (* a1 :: p , b1 :: nil *)
     rewrite Padd_eq_nil_r; apply (is_sorted_fst_cons (fst b1,snd b1) (a1 :: p) a1); trivial.
     (* a1 :: p , b1 :: b2 :: q' *)
     assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
     revert hyp.
     rewrite Padd_eq_cons_cons.
     destruct (lt_eq_lt_dec (fst a1) (fst b2)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
      apply (is_sorted_fst_cons (fst b1,snd b1)
                  ((fst a1, snd a1) :: Padd (p, b2 :: q'))
                  (fst a1, snd a1) ); simpl; trivial...
      apply (is_sorted_fst_cons (fst b1,snd b1)
                      ((fst a1, Fadd_near (snd a1) (snd b2)):: Padd (p, q'))
                      (fst a1, Fadd_near (snd a1) (snd b2))); simpl; trivial.
      apply (is_sorted_fst_cons (fst b1,snd b1)
                      ((fst b2, snd b2) :: Padd (a1 :: p, q'))
                      (fst b2, snd b2)); simpl; trivial.
Qed.


Function Padd_error_sum (p1p2: Polynomial * Polynomial)
   {measure (fun l1l2=> (length (fst l1l2) + length (snd l1l2)))%nat} : list (nat*F) :=
         match p1p2 with
         | (nil, nil) => nil
         | (nil, fn2 :: p2') => nil
         | (fn1 :: p1', nil) => nil
         | (fn1 :: p1' , fn2 :: p2') =>
                 match lt_eq_lt_dec (fst fn1) (fst fn2) with
                 | inleft (left _) => Padd_error_sum (p1',(fn2 :: p2'))
                 | inleft (right _) => (fst fn1, Fdiv2_up (Fsub_up (Fadd_up (snd fn1) (snd fn2)) (Fadd_down (snd fn1) (snd fn2)))) :: Padd_error_sum (p1',p2')
                 | inright _ => Padd_error_sum ((fn1 :: p1'),p2')
                 end
         end.
Proof.
 intros; simpl; lia.
 intros; simpl; lia.
 intros; simpl; lia.
Time Qed.

Lemma Padd_error_sum_eq_nil_nil : Padd_error_sum  (nil,nil) = nil.
Proof.
 intros ; rewrite Padd_error_sum_equation; trivial.
Qed.

Lemma Padd_error_sum_eq_nil_cons : forall fn p, Padd_error_sum  (nil,fn :: p) = nil.
Proof.
 intros fn p; rewrite Padd_error_sum_equation; trivial.
Qed.

Lemma Padd_error_sum_eq_cons_nil : forall fn p, Padd_error_sum  (fn :: p, nil) = nil.
Proof.
 intros fn p; rewrite Padd_error_sum_equation; trivial.
Qed.

Lemma Padd_error_sum_eq_cons_cons : forall fn1 p1 fn2 p2,
  Padd_error_sum (fn1 :: p1, fn2 :: p2) =
                    match lt_eq_lt_dec (fst fn1) (fst fn2) with
                    | inleft (left _) => Padd_error_sum  (p1,(fn2 :: p2))
                    | inleft (right _) => (fst fn1, Fdiv2_up (Fsub_up (Fadd_up (snd fn1) (snd fn2)) (Fadd_down (snd fn1) (snd fn2)) )) :: Padd_error_sum  (p1,p2)
                    | inright _ => Padd_error_sum  ((fn1 :: p1),p2)
                    end.
Proof.
 intros  fn1 p1 fn2 p2; rewrite Padd_error_sum_equation; trivial.
Qed.

Hint Resolve Padd_error_sum_eq_nil_nil Padd_error_sum_eq_nil_cons Padd_error_sum_eq_cons_nil Padd_error_sum_eq_cons_cons.

Lemma Padd_error_sum_eq_nil_r : forall  p, Padd_error_sum  (p,nil) = nil.
Proof.
 intros  [|fn p']; auto.
Qed.

Lemma Padd_error_sum_eq_nil_l : forall  p, Padd_error_sum  (nil,p) = nil.
Proof.
 intros  [|fn p']; auto.
Qed.

Ltac local_tactic_prove_Padd_error_sum_equation :=
 intros  fn1 p1 fn2 p2 H; rewrite Padd_error_sum_eq_cons_cons;
 destruct (lt_eq_lt_dec (fst fn1) (fst fn2)) as [[H_ | H_f] | H_f]; trivial; contradict H; lia.


Lemma Padd_error_sum_eq_lt : forall  fn1 p1 fn2 p2, (fst fn1 < fst fn2) %nat ->
 Padd_error_sum  (fn1 :: p1, fn2 :: p2) = Padd_error_sum  (p1,(fn2 :: p2)).
Proof.
 local_tactic_prove_Padd_error_sum_equation.
Qed.

Lemma Padd_error_sum_eq_eq : forall  fn1 p1 fn2 p2, (fst fn1 = fst fn2) %nat ->
 Padd_error_sum  (fn1 :: p1, fn2 :: p2) = (fst fn1, Fdiv2_up (Fsub_up (Fadd_up (snd fn1) (snd fn2)) (Fadd_down (snd fn1) (snd fn2)))) :: Padd_error_sum  (p1,p2).
Proof.
 local_tactic_prove_Padd_error_sum_equation.
Qed.

Lemma Padd_error_sum_eq_gt : forall  fn1 p1 fn2 p2, (fst fn2 < fst fn1) %nat ->
 Padd_error_sum  (fn1 :: p1, fn2 :: p2) = Padd_error_sum  ((fn1 :: p1),p2).
Proof.
 local_tactic_prove_Padd_error_sum_equation.
Qed.


Definition Padd_polynomial p1 p2 : list (nat*F) := Padd (p1,p2).

Definition Padd_error p1 p2 : Polynomial := Padd_error_sum (p1,p2).

Definition PMadd_error t1 t2 : F := Fadd_up t1.(error) (Fadd_up t2.(error) (Fsum_snd_add up (Padd_error t1.(polynomial) t2.(polynomial)))).




Definition PMadd (t1 t2 : PolynomialModel) : PolynomialModel :=
 {| polynomial:= Padd_polynomial t1.(polynomial) t2.(polynomial); 
    error:=PMadd_error t1 t2 |}.

Lemma sum_add_up_nonneg : forall (t1 t2: PolynomialModel), 0<= FinjR ( Fsum_snd_add up (Padd_error (polynomial t1) (polynomial t2))).
Proof.
 intros [p1 e1].
 induction p1; intros [p2 e2].
  (* nil, _ *)
  simpl; unfold Padd_error; rewrite Padd_error_sum_eq_nil_l; simpl; rewrite flt_null; auto with real.

  (* a :: p1, _  *)
  induction p2.
   (* a::p1, nil *)
   simpl; unfold Padd_error; rewrite Padd_error_sum_eq_nil_r; simpl; rewrite flt_null; auto with real.
   (* a::p1, a0::p2 *)
   simpl in *.
   unfold Padd_error.
   rewrite Padd_error_sum_eq_cons_cons.
   destruct (lt_eq_lt_dec (fst a) (fst a0)) as [[Hlt | Heq] | Hlt].

    apply (IHp1 (Build_PolynomialModel (a0 :: p2) e2)).
    apply Rle_trans with (FinjR (Fdiv2_up (Fsub_up (Fadd_up (snd a) (snd a0)) (Fadd_down (snd a) (snd a0)))) +
                          FinjR (Fsum_snd_add up (Padd_error_sum (p1,p2)))); [|apply Rge_le; apply flt_add_up].
    apply Rplus_le_le_0_compat.
     (*    0 <= FinjR (div2_up (Fsub_up (add_up x y) (add_down x y))) *)
     generalize (snd a) (snd a0); intros x y.
     apply Rle_trans with (Rabs ( (FinjR  (Fadd_near x y))- ((FinjR x)+(FinjR y)) )).
       apply Rabs_pos.
       unfold Fadd_near, Fadd_up, Fadd_down.
       replace Fadd with (Fapply Add); [|trivial]. replace Rplus with (Rapply Add); [|trivial].
       apply flt_op_near_up_down_sub_hlf_up.
     apply (IHp1 (Build_PolynomialModel p2 e2)).

    apply IHp2; assumption.
Qed.


Lemma sum_add_up_property : forall (p1 p2:Polynomial) x,  -1 <= x <= 1 ->
   Rabs (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (Padd_polynomial p1 p2) x) <=
        FinjR (Fsum_snd_add up (Padd_error p1 p2)).
Proof.
  intros p1.
(*
  unfold Pax_eval in *.
*)
  induction p1; intros p2.
    intros  x _; simpl; unfold Padd_polynomial, Padd_error in *.
    rewrite Padd_eq_nil_l, Padd_error_sum_eq_nil_l; simpl.
    stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

    induction p2.
      intros x _; simpl; unfold Padd_polynomial, Padd_error in *.
      rewrite Padd_eq_nil_r, Padd_error_sum_eq_nil_r; simpl.
      stepl 0; [ rewrite flt_null; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

      intros x Hx.
      unfold Padd_polynomial, Padd_error.

      rewrite Padd_eq_cons_cons, Padd_error_sum_eq_cons_cons.
      destruct (lt_eq_lt_dec (fst a) (fst a0)) as [[Hlt | Hlt] | Hlt].
        (* 1 *)
        rewrite (Pax_eval_eq).
        set (p02:=(a0 :: p2)).
        replace (Pax_eval ((fst a, snd a) :: Padd (p1, a0 :: p2)) x) with
                (FinjR (snd a) *(pow x (fst a)) + (Pax_eval (Padd_polynomial p1 (a0::p2)) x)); [|trivial].
        replace (Padd_error_sum (p1, a0 :: p2)) with
                (Padd_error p1 (a0::p2)); [|trivial].
        stepl (Rabs (Pax_eval p1 x +
                     Pax_eval (a0::p2) x -
                     Pax_eval (Padd_polynomial p1 (a0::p2)) x)).
          apply (IHp1 (a0::p2)). exact Hx.
          remember (Padd_polynomial p1 (a0::p2)) as p12.
          f_equal. unfold Pax_eval. simpl. ring.

        (* 2 *)

        simpl.
        apply Rle_trans with (  (FinjR(Fdiv2_up (Fsub_up (Fadd_up (snd a) (snd a0)) (Fadd_down (snd a) (snd a0)))) +
                                        FinjR(Fsum_snd_add up (Padd_error p1 p2)))).
        2: apply Rge_le. 2: apply flt_add_up.

        rewrite <- Hlt.
        stepl (Rabs ( ( (FinjR (snd a) + FinjR (snd a0)) * (pow x (fst a)) -
                         FinjR (Fadd_near (snd a) (snd a0)) * (pow x (fst a))
                       ) +
                      (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (Padd_polynomial p1 p2) x)
                    ) ).
        2:f_equal; simpl; unfold Padd_polynomial; simpl; ring.
        apply Rle_trans with (Rabs ( FinjR (Fadd_near (snd a) (snd a0)) -
                                      (FinjR (snd a) + FinjR (snd a0))
                                   ) * Rabs (pow x (fst a)) +
                             Rabs (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (Padd_polynomial p1 p2) x) );
        [ rewrite <- Rabs_mult;
          replace ((FinjR (Fadd_near (snd a) (snd a0)) - (FinjR (snd a) + FinjR (snd a0))) * (pow x (fst a))) with
          (FinjR (Fadd_near (snd a) (snd a0))*(pow x (fst a)) - (FinjR (snd a) + FinjR (snd a0))*(pow x (fst a)));[|ring];
          rewrite Rabs_minus_sym; apply Rabs_triang; rewrite Rabs_minus_sym; apply Rabs_triang
        |].
        apply Rplus_le_compat; [| apply (IHp1 _ _ Hx)].

         apply Rle_trans with (Rabs(FinjR (Fadd_near (snd a) (snd a0)) - (FinjR (snd a) + FinjR (snd a0)))).
         assert (H_xn_l:-1 <= (pow x (fst a)) );[apply pow_Rle_l_1; elim Hx; trivial|].
         assert (H_xn_r:(pow x (fst a))<= 1 );[apply pow_Rle_r_1; elim Hx; trivial|].
         assert (H_xn_abs:Rabs (pow x (fst a))<=1). { apply Rabs_Rle_1. split. exact H_xn_l. exact H_xn_r. }
         stepr (Rabs (FinjR (Fadd_near (snd a) (snd a0)) - (FinjR (snd a) + FinjR (snd a0))) * 1); [|ring].
         apply Rmult_le_compat_l. trivial; apply Rabs_pos. exact H_xn_abs.

         unfold Fadd_near, Fadd_up, Fadd_down.
         replace Fadd with (Fapply Add); [|trivial].
         replace Rplus with (Rapply Add); [|trivial].
         apply flt_op_near_up_down_sub_hlf_up.
         
        (* 3 *)
        rewrite (Pax_eval_eq).
        set (sp1:=(a :: p1)).
        set (sp2:=p2).
        replace (Pax_eval ((fst a0, snd a0) :: Padd (a :: p1, p2)) x) with
                (FinjR (snd a0) *(pow x (fst a0)) + (Pax_eval (Padd_polynomial sp1 sp2) x)); [|trivial].
        replace (Padd_error_sum (a :: p1, p2)) with
                (Padd_error sp1 sp2); [|trivial].
        stepl (Rabs (Pax_eval sp1 x +
                     Pax_eval sp2 x -
                     Pax_eval (Padd_polynomial sp1 sp2) x)).
          apply IHp2. exact Hx.
          remember (Padd_polynomial sp1 sp2) as sp12.
          f_equal. simpl. ring.
Qed.

Theorem PMadd_correct : forall (t1 t2: PolynomialModel) (f1 f2:R -> R),
   PMmodels t1 f1 -> PMmodels t2 f2 -> PMmodels (PMadd t1 t2) (fun x=> f1(x)+ f2(x)).
Proof.
 intros t1 t2 f1 f2 H1 H2 x hyp_x.
 specialize (H1 x hyp_x); specialize (H2 x hyp_x).
 assert (H_sum_err_nonneg:= sum_add_up_nonneg t1 t2).
 apply Rle_trans with (FinjR (error t1)+ FinjR (error t2) + FinjR (Fsum_snd_add up (Padd_error (polynomial t1) (polynomial t2)))).

  2:apply Rle_trans with (FinjR (error t1)+ FinjR (error t2) + FinjR (Fsum_snd_add up (Padd_error (polynomial t1) (polynomial t2))));
     [ apply Rplus_le_compat_l;
       generalize (FinjR (Fsum_snd_add up (Padd_error (polynomial t1) (polynomial t2)))) H_sum_err_nonneg; intros r H_r; lra
     | apply Rle_trans with (FinjR (error t1)+ FinjR (Fadd_up (error t2) (Fsum_snd_add up (Padd_error (polynomial t1) (polynomial t2)))));
       [(stepl (FinjR (error t1)+ (FinjR (error t2) + FinjR (Fsum_snd_add up (Padd_error (polynomial t1) (polynomial t2))))) by ring) ;
       apply Rplus_le_compat_l |] ; apply Rge_le; apply flt_add_up
     ].
 destruct t1 as [p1 e1]; destruct t2 as [p2 e2].
 simpl in *.
 set (p1_x:= Pax_eval p1 x).
 set (p2_x:= Pax_eval p2 x).
 set (pp_x:= Pax_eval (Padd_polynomial p1 p2) x).
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

End Polynomial_Model_Add.
