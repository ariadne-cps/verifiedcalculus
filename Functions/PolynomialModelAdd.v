(******************************************************************************
 *  Functions/PolynomialModelsAdd.v
 *
 *  Copyright 2010 Milad Niqui
 *            2023 Pieter Collins
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


From Stdlib Require Import Recdef.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import Ring.
From Stdlib Require Import Arith.Compare_dec.

Require Export PolynomialModels.


Section Polynomial_Model_Add.

Context `{F : Type} `{FltF : Float F}.

Open Scope R_scope.


Definition Fadd_err_up x1 x2 := F.div2 up (F.sub up (F.add up x1 x2) (F.add down x1 x2)).


Function Padd_approx' (p1p2 : list (nat*F) * list (nat*F))
    {measure (fun l1l2=> (length (fst l1l2) + length (snd l1l2)))%nat p1p2} : list (nat*F) :=
  match p1p2 with
  | (nil, nil) => nil
  | (nil, a2::p2') => a2 :: p2'
  | (a1::p1', nil) => a1 :: p1'
  | (a1::p1', a2::p2') =>
    match lt_eq_lt_dec (fst a1) (fst a2) with
    | inleft (left _) => (fst a1, snd a1) :: Padd_approx' (p1', a2::p2')
    | inleft (right _) => (fst a1, F.add_near (snd a1) (snd a2)) :: Padd_approx' (p1', p2')
    | inright _ => (fst a2, snd a2) :: Padd_approx' (a1::p1', p2')
    end
  end.
Proof.
  intros; simpl; lia.
  intros; simpl; lia.
  intros; simpl; lia.
Qed.

Definition Padd_approx p1 p2 : list (nat*F) := Padd_approx' (p1,p2).


Lemma Padd_approx_eq_nil_l : forall p2, Padd_approx nil p2 = p2.
Proof.
  intros p2; unfold Padd_approx; rewrite Padd_approx'_equation; destruct p2; trivial.
Qed.

Lemma Padd_approx_eq_nil_r: forall p1, Padd_approx p1 nil = p1.
Proof.
  intros p1; unfold Padd_approx; rewrite Padd_approx'_equation; destruct p1; trivial.
Qed.

Lemma Padd_approx_eq_cons_cons: forall a1 p1 a2 p2,
  Padd_approx (a1::p1) (a2::p2) =
    match lt_eq_lt_dec (fst a1) (fst a2) with
    | inleft (left _) => (fst a1, snd a1) :: Padd_approx p1 (a2::p2)
    | inleft (right _) => (fst a1, F.add_near (snd a1) (snd a2)) :: Padd_approx p1 p2
    | inright _ => (fst a2, snd a2) :: Padd_approx (a1::p1) p2
    end.
Proof.
  intros a1 p1 a2 p2; unfold Padd_approx; rewrite Padd_approx'_equation; trivial.
Qed.



Lemma Padd_sorted: forall p1 p2,
  is_sorted_fst p1 -> is_sorted_fst p2 -> is_sorted_fst (Padd_approx p1 p2).
Proof.
  induction p1 as [|a1 p].
    (* nil , _ *)
    intros p2 H_ap1 H_ap2; rewrite Padd_approx_eq_nil_l; assumption.
    (* a1 :: p , _ *)
    induction p2 as [|b1 q]; intros H_ap H_bq.
      (* a1 :: p , nil *)
      rewrite Padd_approx_eq_nil_r; assumption.
      (* a1 :: p , b1 : q *)
      assert (H_p:is_sorted_fst p); [apply is_sorted_fst_cons_inv with a1; exact H_ap|].
      assert (H_q:is_sorted_fst q); [apply is_sorted_fst_cons_inv with b1; exact H_bq|].
      rewrite Padd_approx_eq_cons_cons.
      destruct (lt_eq_lt_dec (fst a1) (fst b1)) as [[Hlt | Heq] | Hlt].
        (* 1 *)
        assert (hyp:is_sorted_fst (Padd_approx p (b1 :: q))); [apply IHp; assumption|].
        destruct p as  [|a2 p'].
          (* a1 :: nil , b1 :: q *)
          rewrite Padd_approx_eq_nil_l; apply (is_sorted_fst_cons (fst a1,snd a1) (b1 :: q) b1); trivial.
          (* a1 :: a2 :: p1' , b1 :: q *)
          assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
          revert hyp.
          rewrite Padd_approx_eq_cons_cons.
          destruct (lt_eq_lt_dec (fst a2) (fst b1)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
            apply (is_sorted_fst_cons (fst a1,snd a1)
                        ((fst a2, snd a2) :: Padd_approx p' (b1 :: q))
                        (fst a2, snd a2) ); simpl; trivial...
            apply (is_sorted_fst_cons (fst a1,snd a1)
                            ((fst a2, F.add_near (snd a2) (snd b1)):: Padd_approx p' q)
                            (fst a2, F.add_near (snd a2) (snd b1))); simpl; trivial.
            apply (is_sorted_fst_cons (fst a1,snd a1)
                            ((fst b1, snd b1) :: Padd_approx (a2 :: p') q)
                            (fst b1, snd b1)); simpl; trivial.
        (* 2 *)
        assert (hyp:is_sorted_fst (Padd_approx p q)); [apply IHp; assumption|].
        destruct p as  [|a2 p']; destruct q as [|b2 q'].
          (* a1 :: nil , b1 :: nil *)
          rewrite Padd_approx_eq_nil_l; apply is_sorted_fst_one.
          (* a1 :: nil , b1 :: b2 :: q' *)
          assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
          assert (H_a1_b2: (fst a1<fst b2)%nat); [rewrite Heq; assumption|].
          rewrite Padd_approx_eq_nil_l; apply (is_sorted_fst_cons (fst a1, F.add_near (snd a1) (snd b1)) (b2 :: q') b2); trivial.
          (* a1 :: a2 :: p' , b1 :: nil *)
          assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
          rewrite Padd_approx_eq_nil_r; apply (is_sorted_fst_cons (fst a1,F.add_near (snd a1) (snd b1)) (a2 :: p') a2); trivial.
          (* a1 :: a2 :: p' , b1 :: b2 :: q' *)
          assert (H_a12: (fst a1<fst a2)%nat); [inversion H_ap; injection H1; intros H_tmp; subst a2; assumption|].
          assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
          assert (H_a1_b2: (fst a1<fst b2)%nat); [rewrite Heq; assumption|].
          revert hyp.
          rewrite Padd_approx_eq_cons_cons.
          destruct (lt_eq_lt_dec (fst a2) (fst b2)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
            apply (is_sorted_fst_cons (fst a1,F.add_near (snd a1) (snd b1))
                        ((fst a2, snd a2) :: Padd_approx p' (b2 :: q'))
                        (fst a2, snd a2) ); simpl; trivial...
            apply (is_sorted_fst_cons (fst a1,F.add_near (snd a1) (snd b1))
                            ((fst a2, F.add_near (snd a2) (snd b2)):: Padd_approx p' q')
                            (fst a2, F.add_near (snd a2) (snd b2))); simpl; trivial.
            apply (is_sorted_fst_cons (fst a1, F.add_near (snd a1) (snd b1))
                            ((fst b2, snd b2) :: Padd_approx (a2 :: p') q')
                            (fst b2, snd b2)); simpl; trivial.
        (* 3 *)
        assert (hyp:is_sorted_fst (Padd_approx (a1 :: p) q)); [apply IHq; assumption|].
        destruct q as  [|b2 q'].
          (* a1 :: p , b1 :: nil *)
          rewrite Padd_approx_eq_nil_r; apply (is_sorted_fst_cons (fst b1,snd b1) (a1 :: p) a1); trivial.
          (* a1 :: p , b1 :: b2 :: q' *)
          assert (H_b12: (fst b1<fst b2)%nat); [inversion H_bq; injection H1; intros H_tmp; subst b2; assumption|].
          revert hyp.
          rewrite Padd_approx_eq_cons_cons.
          destruct (lt_eq_lt_dec (fst a1) (fst b2)) as [[Hlt' | Heq'] | Hlt']; intros hyp.
            apply (is_sorted_fst_cons (fst b1,snd b1)
                        ((fst a1, snd a1) :: Padd_approx p (b2 :: q'))
                        (fst a1, snd a1) ); simpl; trivial...
            apply (is_sorted_fst_cons (fst b1,snd b1)
                            ((fst a1, F.add_near (snd a1) (snd b2)):: Padd_approx p q')
                            (fst a1, F.add_near (snd a1) (snd b2))); simpl; trivial.
            apply (is_sorted_fst_cons (fst b1,snd b1)
                            ((fst b2, snd b2) :: Padd_approx (a1 :: p) q')
                            (fst b2, snd b2)); simpl; trivial.
Qed.


Definition Padd_error_term (a1 a2 : nat * F) :=
  F.div2_up (F.sub_up (F.add_up (snd a1) (snd a2)) (F.add_down (snd a1) (snd a2))).

Function Padd_error' (p1p2 : list (nat*F) * list (nat*F))
   {measure (fun l1l2 => (length (fst l1l2) + length (snd l1l2)))%nat} : F :=
         match p1p2 with
         | (nil, nil) => F.null
         | (nil, a2 :: p2') => F.null
         | (a1 :: p1', nil) => F.null
         | (a1 :: p1' , a2 :: p2') =>
                 match lt_eq_lt_dec (fst a1) (fst a2) with
                 | inleft (left _) => Padd_error' (p1', a2::p2')
                 | inleft (right _) => F.add up (Padd_error_term a1 a2) (Padd_error' (p1',p2'))
                 | inright _ => Padd_error' (a1::p1', p2')
                 end
         end.
Proof.
  intros; simpl; lia.
  intros; simpl; lia.
  intros; simpl; lia.
Qed.

Definition Padd_error p1 p2 : F := Padd_error' (p1,p2).

Lemma Padd_error_eq_nil_l : forall (p : list (nat*F)), Padd_error nil p = F.null.
Proof.
  intros; unfold Padd_error; rewrite Padd_error'_equation; destruct p; trivial.
Qed.

Lemma Padd_error_eq_nil_r : forall (p : list (nat*F)), Padd_error p nil = F.null.
Proof.
  intros; unfold Padd_error; rewrite Padd_error'_equation; destruct p; trivial.
Qed.

Lemma Padd_error_eq_cons_cons : forall a1 p1 a2 p2,
  Padd_error (a1::p1) (a2::p2) =
    match lt_eq_lt_dec (fst a1) (fst a2) with
    | inleft (left _) => Padd_error p1 (a2::p2)
    | inleft (right _) => F.add up (Padd_error_term a1 a2) (Padd_error p1 p2)
    | inright _ => Padd_error (a1::p1) p2
    end.
Proof.
  intros a1 p1 a2 p2; unfold Padd_error; rewrite Padd_error'_equation; trivial.
Qed.


Definition PMadd_error t1 t2 : F := F.add_up (F.add_up t1.(error) t2.(error)) (Padd_error t1.(polynomial) t2.(polynomial)).


Definition PMadd (t1 t2 : PolynomialModel F) : PolynomialModel F :=
  {| polynomial:= Padd_approx t1.(polynomial) t2.(polynomial);
     error:=PMadd_error t1 t2 |}.


Lemma Padd_correct : forall (p1 p2:Polynomial F) x,  -1 <= x <= 1 ->
  Rabs (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (Padd_approx p1 p2) x) <=
    F.injR (Padd_error p1 p2).
Proof.
  intros p1.
  induction p1 as [|a1 p1]; intros p2.

  (* nil, p2 *)
  intros  x _; simpl.
  rewrite Padd_approx_eq_nil_l. rewrite Padd_error_eq_nil_l. simpl.
  stepl 0; [ rewrite F.null_spec; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

  (* a1::p1, p2 *)
  induction p2 as [|a2 p2].

  (* a1::p1, nil *)
  intros x _; simpl.
  rewrite Padd_approx_eq_nil_r, Padd_error_eq_nil_r; simpl.
  stepl 0; [ rewrite F.null_spec; lra | symmetry; stepl (Rabs 0); [apply Rabs_R0|f_equal; ring]].

  (* a1::p1, a2::p2 *)
  intros x Hx.
  rewrite Padd_approx_eq_cons_cons, Padd_error_eq_cons_cons.
  destruct (lt_eq_lt_dec (fst a1) (fst a2)) as [[Hlt | Heq] | Hgt].
  - (* m1 < m2 *)
    rewrite (Pax_eval_eq).
    replace (Pax_eval ((fst a1, snd a1) :: Padd_approx p1 (a2::p2)) x) with
            (F.injR (snd a1) *(pow x (fst a1)) + (Pax_eval (Padd_approx p1 (a2::p2)) x)); [|trivial].
    stepl (Rabs (Pax_eval p1 x + Pax_eval (a2::p2) x - Pax_eval (Padd_approx p1 (a2::p2)) x)).
      apply (IHp1 (a2::p2)). exact Hx.
      f_equal. unfold Pax_eval. simpl. ring.

  - (* m1 = m2 *)
    simpl.
    apply Rle_trans with ( F.injR (Padd_error_term a1 a2) + F.injR (Padd_error p1 p2) ).
    2: apply F.add_up_le_spec.

    rewrite <- Heq; set (m:=fst a1).
    unfold Padd_error_term.
    set (c1:=snd a1); set (c2:=snd a2).
    stepl (Rabs ( ( (F.injR c1 + F.injR c2) * (pow x m) - F.injR (F.add_near c1 c2) * (pow x m) )
                      + (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (Padd_approx p1 p2) x) ) ).
    2: f_equal; simpl; unfold Padd_approx; simpl; ring.
    apply Rle_trans with (Rabs ( F.injR (F.add_near c1 c2) - (F.injR c1 + F.injR c2) )
                              * Rabs (pow x m)
                            + Rabs (Pax_eval p1 x + Pax_eval p2 x - Pax_eval (Padd_approx p1 p2) x) ).
    -- rewrite <- Rabs_mult.
       replace ((F.injR (F.add_near c1 c2) - (F.injR c1 + F.injR c2)) * (pow x m)) with
         (F.injR (F.add_near c1 c2)*(pow x m) - (F.injR c1 + F.injR c2)*(pow x m)); [|ring].
       rewrite Rabs_minus_sym; apply Rabs_triang; rewrite Rabs_minus_sym; apply Rabs_triang.
    -- apply Rplus_le_compat; [| apply (IHp1 _ _ Hx)].
       apply Rle_trans with (Rabs (F.injR (F.add_near c1 c2) - (F.injR c1 + F.injR c2))).
       --- stepr ( (Rabs (F.injR (F.add_near c1 c2) - (F.injR c1 + F.injR c2))) * 1); [|ring].
          apply Rmult_le_compat_l; [apply Rabs_pos|].
          apply Rabs_pow_le_1; apply Rabs_le; exact Hx.
       --- unfold F.add_near, F.add_up, F.add_down.
           replace F.add with (F.apply Add); [|trivial].
           replace Rplus with (Rapply Add); [|trivial].
           unfold Padd_error_term.
           apply F.op_near_up_down_sub_hlf_up_spec.

  - (* 3 *)
    rewrite (Pax_eval_eq).
    replace (Pax_eval ((fst a2, snd a2) :: Padd_approx (a1::p1) p2) x) with
            (F.injR (snd a2) * (pow x (fst a2)) + (Pax_eval (Padd_approx (a1::p1) p2) x)); [|trivial].
    stepl (Rabs (Pax_eval (a1::p1) x + Pax_eval p2 x - Pax_eval (Padd_approx (a1::p1) p2) x)).
      apply IHp2. exact Hx.
      f_equal. unfold Pax_eval. simpl. ring.
Qed.


Theorem PMadd_correct : forall (t1 t2: PolynomialModel F) (f1 f2:R -> R),
   PMmodels t1 f1 -> PMmodels t2 f2 -> PMmodels (PMadd t1 t2) (fun x=> f1(x)+ f2(x)).
Proof.
  intros t1 t2 f1 f2 H1 H2 x Hx.
  specialize (H1 x Hx); specialize (H2 x Hx).
  destruct t1 as [p1 e1]; destruct t2 as [p2 e2].
  unfold PMadd_error.
  simpl in *.

  apply Rle_trans with (F.injR e1 + F.injR e2 + F.injR (Padd_error p1 p2)).
  - set (pp1:= Pax_eval p1).
    set (pp2:= Pax_eval p2).
    set (pp12:= Pax_eval (Padd_approx p1 p2)).
    rewrite Rabs_minus_sym.
    stepl ( Rabs ( (f1 x - pp1 x) + (f2 x - pp2 x) + ( (pp1 x + pp2 x) - pp12 x) ) ); [|f_equal; ring].
    apply Rle_trans with ( Rabs ( (f1 x - pp1 x) + (f2 x - pp2 x) ) + Rabs ( (pp1 x + pp2 x) - pp12 x) ); [apply Rabs_triang |].
    apply Rplus_le_compat.
    apply Rle_trans with ( Rabs (f1 x - pp1 x) + Rabs (f2 x - pp2 x) );
      [ apply Rabs_triang
      | apply Rplus_le_compat; rewrite Rabs_minus_sym; assumption
      ].
    apply Padd_correct; assumption.
  - apply Rle_trans with (F.injR (F.add up e1 e2) + F.injR (Padd_error p1 p2) ).
    -- apply Rplus_le_compat_r. apply F.add_up_le_spec.
    -- apply F.add_up_le_spec.
Qed.

Close Scope R_scope.

End Polynomial_Model_Add.
