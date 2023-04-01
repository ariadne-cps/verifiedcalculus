(************************************************************************)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Import Floats.


Require Export QArith.
Require Export QArith.Qabs.
Require Export QArith.Qminmax.
Require Export QArith.Qreals.

Open Scope Q_scope.


(*
Nat2Z.inj_add: forall n m : nat, Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%Z
Qinv_plus_distr: forall (a b : Z) (c : positive), (a # c) + (b # c) == a + b # c 
*)


Lemma Qleb : forall q1 q2 : Q, Qle_bool q1 q2 = true <-> Rle (Q2R q1) (Q2R q2). 
Proof.
  intros q1 q2.
  apply iff_trans with (B:=(Qle q1 q2)).
  - apply Qle_bool_iff.
  - split. apply Qle_Rle. apply Rle_Qle.
Qed.


Definition INQ := fun n => Qmake (Z.of_nat n) 1.

Lemma plus_INQ : forall n1 n2 : nat, (INQ n1) + (INQ n2) == INQ (n1 + n2).
Proof.
  intros n1 n2.
  unfold INQ.
  assert (Zplus (Z.of_nat n1) (Z.of_nat n2) = Z.of_nat (n1 + n2)) as Hn. {
    apply eq_sym. apply Nat2Z.inj_add.
  }
  rewrite <- Hn. 
  apply Qinv_plus_distr.
Qed.

Lemma mult_INQ : forall n1 n2 : nat, (INQ n1) * (INQ n2) == INQ (n1 * n2).
Proof.
  intros n1 n2.
  unfold INQ.
  assert (Zmult (Z.of_nat n1) (Z.of_nat n2) = Z.of_nat (n1 * n2)) as Hn. {
    apply eq_sym. apply Nat2Z.inj_mul.
  }
  rewrite <- Hn.
  unfold Qmult. unfold Qeq.
  unfold Qnum. unfold Qden. 
  f_equal.
Qed.

(*
plus_INR: forall n m : nat, INR (n + m) = (INR n + INR m)%R
Q2R_plus : forall x y : Q, Q2R (x + y) = (Q2R x + Q2R y)%R
*)

Lemma INQ_0 : INQ 0%nat == 0%Q.
Proof.
  rewrite <- (Qplus_0_r (INQ 0)).
  rewrite <- (Qplus_opp_r (INQ 0)).
  rewrite -> Qplus_assoc.
  rewrite -> Qplus_opp_r.
  rewrite -> plus_INQ.
  rewrite -> Nat.add_0_r.
  rewrite -> Qplus_opp_r.
  reflexivity.
Qed.

Lemma INQ_1 : INQ 1%nat == 1%Q.
Proof.
  assert (~ 1%Q == 0%Q) as H1ne0. { discriminate. }
  rewrite <- (Qmult_1_r (INQ 1)).
  rewrite <- (Qmult_inv_r (INQ 1)) by (apply H1ne0).
  rewrite -> Qmult_assoc.
  rewrite -> mult_INQ.
  rewrite -> Nat.mul_1_r.
  reflexivity.
Qed.
  
Definition Q2R_0 := RMicromega.Q2R_0.
Definition Q2R_1 := RMicromega.Q2R_1.


Lemma Qnijnr : forall n : nat, Q2R (INQ n) = INR n.
Proof. 
  intro n.
  induction n.
  - rewrite -> INQ_0. apply Q2R_0.
  - replace (S n) with (n + 1)%nat by (apply Nat.add_1_r).
    rewrite <- plus_INQ.
    rewrite -> Q2R_plus.
    rewrite -> IHn.
    rewrite -> INQ_1.
    rewrite -> Q2R_1.
    rewrite -> plus_INR.
    rewrite -> INR_1.
    reflexivity.
Qed.

(*
Rabs_pos_eq : forall x : R, Rle 0 x -> Rabs x = x.
Rabs_neg_eq : forall x : R, Rle x 0 -> Rabs x = Ropp x.
Qabs_pos: forall x : Q, 0 <= x -> Qabs x == x
Qabs_neg: forall x : Q, x <= 0 -> Qabs x == - x
*)

(*
Qeq_sym : forall x y : Q, x == y -> y == x
Q.OT.lt_total: forall x y : Q, x < y \/ x == y \/ y < x
Qlt_le_weak: forall x y : Q, x < y -> x <= y
Qle_lt_or_eq: forall x y : Q, x <= y -> x < y \/ x == y
Qle_lteq: forall x y : Q, x <= y <-> x < y \/ x == y
Qle_Rle : forall x y : Q, x <= y -> (Q2R x <= Q2R y)%R
Q2R_opp : forall x : Q, forall x : Q, Q2R (- x) = (- Q2R x)%R
*)


Lemma Qle_total : forall q1 q2 : Q, q1 <= q2 \/ q2 <= q1.
Proof.
  intros q1 q2.
  apply or_impl_compat with (p1:=q1<q2) (p2:=q1==q2\/q2<q1).
  - apply Qlt_le_weak.
  - (* For some reason, can't apply Qeq_sym directly *)   
    intros H. apply Qle_lteq. destruct H. 
    -- right. apply Qeq_sym. exact H. 
    -- left. exact H. 
  -  apply Q.OT.lt_total.
Qed.    

Lemma Qabs_Rabs : forall q : Q, Q2R (Qabs q) = Rabs (Q2R q).
Proof. 
  intro q.
  apply or_ind with (A:=0<=q) (B:=q<=0).
  - intro Hq. 
    assert (Rle 0 (Q2R q)) as Hr. { rewrite <- RMicromega.Q2R_0. apply (Qle_Rle). exact Hq. }
    rewrite Qabs_pos by (exact Hq). rewrite Rabs_pos_eq by (exact Hr). reflexivity.
  - intro Hq. 
    assert (Rle (Q2R q) 0) as Hr. { rewrite <- RMicromega.Q2R_0. apply (Qle_Rle). exact Hq. }
    rewrite Qabs_neg by (exact Hq). { rewrite Rabs_neg_eq by (exact Hr). apply Q2R_opp. }
  - apply Qle_total.
Qed.

Lemma Qhlf_Rhlf : forall q : Q, Q2R (Qdiv q 2) = Rdiv (Q2R q) 2.
Proof. 
  assert (~ 2%Q == 0%Q) as H2ne0. {
    discriminate.
  }  
  intro q.
  replace 2%R with (Q2R 2%Q).
  apply Q2R_div. { apply H2ne0. }
  unfold Q2R. unfold Qnum. unfold Qden.
  rewrite -> Rinv_1.
  apply Rmult_1_r.
Qed.


(*
Q.max_l: forall x y : Q, y <= x -> Qmax x y == x
Q.max_r: forall x y : Q, x <= y -> Qmax x y == y
Rmax_right: forall x y : R, (x <= y)%R -> Rmax x y = y
Rmax_left: forall x y : R, (y <= x)%R -> Rmax x y = x
*)

Lemma Qmax_Rmax : forall q1 q2 : Q, Q2R (Qmax q1 q2) = Rmax (Q2R q1) (Q2R q2).
Proof. 
  intros q1 q2.
  apply or_ind with (A:=q1<=q2) (B:=q2<=q1).
  - intro Hq. 
    assert (Rle (Q2R q1) (Q2R q2)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.max_r by (exact Hq). rewrite Rmax_right by (exact Hr). reflexivity.
  - intro Hq. 
    assert (Rle (Q2R q2) (Q2R q1)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.max_l by (exact Hq). { rewrite Rmax_left by (exact Hr). reflexivity. }
  - apply Qle_total.
Qed.
  
Lemma Qmin_Rmin : forall q1 q2 : Q, Q2R (Qmin q1 q2) = Rmin (Q2R q1) (Q2R q2).
Proof. 
  intros q1 q2.
  apply or_ind with (A:=q1<=q2) (B:=q2<=q1).
  - intro Hq. 
    assert (Rle (Q2R q1) (Q2R q2)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.min_l by (exact Hq). rewrite Rmin_left by (exact Hr). reflexivity.
  - intro Hq. 
    assert (Rle (Q2R q2) (Q2R q1)) as Hr. { apply Qle_Rle. exact Hq. }
    rewrite Q.min_r by (exact Hq). { rewrite Rmin_right by (exact Hr). reflexivity. }
  - apply Qle_total.
Qed.
  
  

#[refine]
Instance Rational_Float : Float Q :=
{
  NinjF := (fun n => Qmake (Z.of_nat n) 1);
  FinjR := (fun q => Q2R q);
  Fneg := Qopp;
  Fhlf := (fun q => Qdiv q 2);
  Fabs := Qabs;
  
  Fadd := (fun (r:Rounding) q1 q2 => Qplus q1 q2);
  Fsub := (fun (r:Rounding) q1 q2 => Qminus q1 q2);
  Fmul := (fun (r:Rounding) q1 q2 => Qmult q1 q2);
  Fdiv := (fun (r:Rounding) q1 q2 => Qdiv q1 q2);

  Frec := (fun (r:Rounding) q => Qinv q);

  Fmin := Qmin;
  Fmax := Qmax;
  
  Fleb := Qle_bool;
  
  flt_ninjr := Qnijnr;

  flt_leb := Qleb;
  
  flt_neg_exact := Q2R_opp;
  flt_hlf_exact := Qhlf_Rhlf;
  flt_abs_exact := Qabs_Rabs;
  flt_min_exact := Qmin_Rmin;
  flt_max_exact := Qmax_Rmax;
}.
Proof.
  - intros op x y. destruct op.
    -- rewrite <- Q2R_plus. apply Req_ge. reflexivity.
    -- rewrite <- Q2R_minus. apply Req_ge. reflexivity.
    -- rewrite <- Q2R_mult. apply Req_ge. reflexivity.
  - intros op x y. destruct op.
    -- rewrite <- Q2R_plus. apply Req_le. reflexivity.
    -- rewrite <- Q2R_minus. apply Req_le. reflexivity.
    -- rewrite <- Q2R_mult. apply Req_le. reflexivity.
  - intros op x y z. 
    assert (forall u v : R, Rle (Rabs (Rminus u u)) (Rabs v)) as H. {
      intros u v. rewrite -> Rminus_eq_0. rewrite -> Rabs_R0. apply Rabs_pos.  
    }
    destruct op.
    -- rewrite <- Q2R_plus. apply H.
    -- rewrite <- Q2R_minus. apply H.
    -- rewrite <- Q2R_mult. apply H.
  - (* div up *)
    intros x y H.
    rewrite <- Q2R_div. apply Req_ge. reflexivity.
    intro Hfls.
    assert (Q2R y = Q2R 0) as H0. { apply Qeq_eqR. exact Hfls. } 
    rewrite -> Q2R_0 in H0. apply H. exact H0.
  - (* div down *)
    intros x y H.
    rewrite <- Q2R_div. apply Req_ge. reflexivity.
    intro Hfls.
    assert (Q2R y = Q2R 0) as H0. { apply Qeq_eqR. exact Hfls. } 
    rewrite -> Q2R_0 in H0. apply H. exact H0.
 - (* rec up *) 
    intros x H.
    rewrite <- Q2R_inv. apply Req_ge. reflexivity.
    intro Hfls.
    assert (Q2R x = Q2R 0) as H0. { apply Qeq_eqR. exact Hfls. } 
    rewrite -> Q2R_0 in H0. apply H. exact H0.
 - (* rec down *) 
    intros x H.
    rewrite <- Q2R_inv. apply Req_ge. reflexivity.
    intro Hfls.
    assert (Q2R x = Q2R 0) as H0. { apply Qeq_eqR. exact Hfls. } 
    rewrite -> Q2R_0 in H0. apply H. exact H0.
Qed.  
      
Close Scope Q_scope.
