(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export Reals.
Require Export R_addenda.
Require Export Lra.
Require Export List.


Open Scope R_scope.

Coercion INR : nat >-> R.

Record Float : Type :=
{
  crr :> Set;
  f0 : crr;
  f1 : crr;
  inj_R : crr -> R;
  add_up : crr -> crr -> crr;
  add_down : crr -> crr -> crr;
  add_near : crr -> crr -> crr;
  neg_exact : crr -> crr;
  minus_up := fun x y=> add_up x (neg_exact y);
  abs_exact : crr -> crr;
  mult_up : crr -> crr -> crr;
  mult_down : crr -> crr -> crr;
  mult_near : crr -> crr -> crr;
  ndiv_up : crr -> nat -> crr;
  ndiv_down : crr -> nat -> crr;
  ndiv_near : crr -> nat -> crr;
  div2_up := fun x=> ndiv_up x 2;
  flt_null: inj_R f0 = 0;
  flt_unit: inj_R f1 = 1;
  flt_neg: forall x, inj_R (neg_exact x) = - inj_R x;
  flt_abs: forall x, inj_R (abs_exact x) = Rabs (inj_R x);
  flt_add_n : forall x y z, Rabs (  (inj_R (add_near x y)) - ((inj_R x) + (inj_R y))) <= Rabs (inj_R (z) - ((inj_R x) + (inj_R y)));
  flt_add_u: forall x y,  (inj_R x) + (inj_R y) <= (inj_R (add_up x y));
  flt_add_d: forall x y,  inj_R (add_down x y) <= (inj_R x) + (inj_R y);
  flt_mul_n : forall x y z, Rabs (  (inj_R (mult_near x y)) - ((inj_R x) * (inj_R y))) <= Rabs (inj_R (z) - ((inj_R x) * (inj_R y)));
  flt_mul_u: forall x y,  (inj_R x) * (inj_R y) <= (inj_R (mult_up x y));
  flt_mul_d: forall x y,  inj_R (mult_down x y) <= (inj_R x) * (inj_R y);
  flt_ndiv_n : forall x m z, (0<m)%nat -> Rabs (  (inj_R (ndiv_near x m)) - ((inj_R x) / m) ) <= Rabs (inj_R (z) - ((inj_R x) / m));
  flt_ndiv_u: forall x m, (0<m)%nat -> (inj_R x) / m <= (inj_R (ndiv_up x m));
  flt_ndiv_d: forall x m,  (0<m)%nat -> inj_R (ndiv_down x m) <= (inj_R x) / m;
}.

Arguments add_up {f}.
Arguments add_down {f}.
Arguments add_near {f}.
Arguments neg_exact {f}.
Arguments minus_up {f}.
Arguments inj_R {f}.
Arguments f0 {f}.
Arguments f1 {f}.
Arguments abs_exact {f}.
Arguments mult_up {f}.
Arguments mult_down {f}.
Arguments mult_near {f}.
Arguments ndiv_up {f}.
Arguments ndiv_down {f}.
Arguments ndiv_near {f}.
Arguments div2_up {f}.

Check Float.

Definition minus_down {F:Float} (x y:crr F) := add_down x (neg_exact y).
Definition minus_near {F:Float} (x y:crr F) := add_near x (neg_exact y).

Definition div2_down {F:Float} (x:crr F) := ndiv_down x 2.
Definition div2_near {F:Float} (x:crr F) := ndiv_near x 2.

Fixpoint pow_up {F:Float} (x:crr F) (n:nat) :=
    match n with
    | O => f1
    | S n' => mult_up x (pow_up x n')
    end.

Definition sum_add_up {F:Float} : list (nat * F) -> F := fold_right (fun nf=> @add_up F (snd nf)) f0.

Lemma flt_add_n_u_abs: forall {F:Float} x y, Rabs ( (@inj_R F (add_near x y)) - ((inj_R x) + (inj_R y))) <= Rabs ((inj_R (add_up x y)) - ((inj_R x) + (inj_R y))).
Proof.
 intros F x y; apply flt_add_n.
Qed.

Lemma flt_add_n_d_abs: forall {F:Float} x y, Rabs ( (@inj_R F (add_near x y)) - ((inj_R x) + (inj_R y))) <= Rabs((inj_R x) + (inj_R y) - (inj_R (add_down x y))).
Proof.
 intros F x y;
 stepr (Rabs ((inj_R (add_down x y)) - ((inj_R x) + (inj_R y)))); [apply flt_add_n|apply Rabs_minus_sym].
Qed.

Lemma flt_mul_n_u_abs: forall {F:Float} x y, Rabs ( (@inj_R F (mult_near x y)) - ((inj_R x) * (inj_R y))) <= Rabs ((inj_R (mult_up x y)) - ((inj_R x) * (inj_R y))).
Proof.
 intros F x y; apply flt_mul_n.
Qed.

Lemma flt_mul_n_d_abs: forall {F:Float} x y, Rabs ( (@inj_R F (mult_near x y)) - ((inj_R x) * (inj_R y))) <= Rabs((inj_R x) * (inj_R y) - (inj_R (mult_down x y))).
Proof.
 intros F x y;
 stepr (Rabs ((inj_R (mult_down x y)) - ((inj_R x) * (inj_R y)))); [apply flt_mul_n|apply Rabs_minus_sym].
Qed.

Lemma flt_add_n_u: forall {F:Float} x y, Rabs ( (@inj_R F (add_near x y)) - ((inj_R x) + (inj_R y))) <= (inj_R (add_up x y)) - ((inj_R x) + (inj_R y)).
Proof.
 intros F x y.
 stepr (Rabs ((inj_R (add_up x y)) - ((inj_R x) + (inj_R y))));
 [ apply flt_add_n_u_abs
 | apply Rabs_pos_eq; apply Rle_Rminus_zero; apply flt_add_u].
Qed.

Lemma flt_add_n_d: forall {F:Float} x y, Rabs ( (@inj_R F (add_near x y)) - ((inj_R x) + (inj_R y))) <= (inj_R x) + (inj_R y) - (inj_R (add_down x y)).
Proof.
 intros F x y.
 stepr (Rabs (((inj_R x) + (inj_R y)) - (inj_R (add_down x y)) ));
 [ apply flt_add_n_d_abs
 | apply Rabs_pos_eq; apply Rle_Rminus_zero; apply flt_add_d].
Qed.

Lemma flt_add_n_u_d_R: forall {F:Float} x y, Rabs ( (@inj_R F (add_near x y))- ((inj_R x)+(inj_R y)) ) <= (1/2)*((inj_R (add_up x y))-(inj_R (add_down x y))).
Proof.
 intros F x y.
 apply Rmult_le_reg_l with 2; try lra.
 stepr ((inj_R (add_up x y) - ((inj_R x) + (inj_R y))) + ((inj_R x) + (inj_R y) - inj_R (add_down x y))) by field.
 stepl (Rabs ( (inj_R (add_near x y)) - (inj_R x + inj_R y) )+ Rabs ((inj_R (add_near x y)) - (inj_R x + inj_R y))) by ring.
 apply Rplus_le_compat;
 [ apply flt_add_n_u
 | apply flt_add_n_d
 ].
Qed.


Lemma flt_add_n_u_d: forall {F:Float} x y, Rabs ( (@inj_R  F (add_near x y))- ((inj_R x)+(inj_R y)) ) <= (1/2)* inj_R (minus_up (add_up x y) (add_down x y)).
Proof.
 intros F x y.
 apply Rle_trans with ((1/2)*((inj_R (add_up x y))-(inj_R (add_down x y)))); [apply flt_add_n_u_d_R|].
 apply Rmult_le_compat_l; try lra.
 apply Rle_trans with ((inj_R (add_up x y)) + (inj_R (neg_exact (add_down x y)))).
  rewrite flt_neg; apply Rle_refl.
  apply flt_add_u.
Qed.

Lemma flt_add_n_u_d_div2: forall {F:Float} x y, Rabs ( (@inj_R  F (add_near x y))- ((inj_R x)+(inj_R y)) ) <=  inj_R (div2_up (minus_up (add_up x y) (add_down x y))).
Proof.
 intros F x y.
 apply Rle_trans with ((1/2)* inj_R (minus_up (add_up x y) (add_down x y)));[apply flt_add_n_u_d|].
 apply Rle_trans with ((inj_R (minus_up (add_up x y) (add_down x y)))/(2%nat)); [|apply flt_ndiv_u; auto].
 simpl; rewrite Rmult_comm; assert (H_rw:1 / 2 = Rinv 2); [field|]; rewrite H_rw.
 apply Rle_refl.
Qed.


Lemma flt_mul_n_u: forall {F:Float} x y, Rabs ( (@inj_R F (mult_near x y)) - ((inj_R x) * (inj_R y))) <= (inj_R (mult_up x y)) - ((inj_R x) * (inj_R y)).
Proof.
 intros F x y.
 stepr (Rabs ((inj_R (mult_up x y)) - ((inj_R x) * (inj_R y))));
 [ apply flt_mul_n_u_abs
 | apply Rabs_pos_eq; apply Rle_Rminus_zero; apply flt_mul_u].
Qed.

Lemma flt_mul_n_d: forall {F:Float} x y, Rabs ( (@inj_R F (mult_near x y)) - ((inj_R x) * (inj_R y))) <= (inj_R x) * (inj_R y) - (inj_R (mult_down x y)).
Proof.
 intros F x y.
 stepr (Rabs (((inj_R x) * (inj_R y)) - (inj_R (mult_down x y)) ));
 [ apply flt_mul_n_d_abs
 | apply Rabs_pos_eq; apply Rle_Rminus_zero; apply flt_mul_d].
Qed.


Lemma flt_mul_n_u_d_R: forall {F:Float} x y, Rabs ( (@inj_R F (mult_near x y))- ((inj_R x)*(inj_R y)) ) <= (1/2)*((inj_R (mult_up x y))-(inj_R (mult_down x y))).
Proof.
 intros F x y.
 apply Rmult_le_reg_l with 2; try lra.
 stepr ((inj_R (mult_up x y) - ((inj_R x) * (inj_R y))) + ((inj_R x) * (inj_R y) - inj_R (mult_down x y))) by field.
 stepl (Rabs ( (inj_R (mult_near x y)) - (inj_R x * inj_R y) )+ Rabs ((inj_R (mult_near x y)) - (inj_R x * inj_R y))) by ring.
 try lra.
 apply Rplus_le_compat;
 [ apply flt_mul_n_u
 | apply flt_mul_n_d
 ].
Qed.


Lemma flt_mul_n_u_d: forall {F:Float} x y, Rabs ( (@inj_R  F (mult_near x y))- ((inj_R x)*(inj_R y)) ) <= (1/2)* inj_R (minus_up (mult_up x y) (mult_down x y)).
Proof.
 intros F x y.
 apply Rle_trans with ((1/2)*((inj_R (mult_up x y))-(inj_R (mult_down x y)))); [apply flt_mul_n_u_d_R|].
 apply Rmult_le_compat_l;
 try lra.
 apply Rle_trans with ((inj_R (mult_up x y)) + (inj_R (neg_exact (mult_down x y)))).
 try lra.
 rewrite flt_neg; apply Rle_refl.
 apply flt_add_u.
Qed.

Lemma flt_mul_n_u_d_div2: forall {F:Float} x y, Rabs ( (@inj_R  F (mult_near x y))- ((inj_R x)*(inj_R y)) ) <=  inj_R (div2_up (minus_up (mult_up x y) (mult_down x y))).
Proof.
 intros F x y.
 apply Rle_trans with ((1/2)* inj_R (minus_up (mult_up x y) (mult_down x y)));[apply flt_mul_n_u_d|].
 apply Rle_trans with ((inj_R (minus_up (mult_up x y) (mult_down x y)))/(2%nat)); [|apply flt_ndiv_u; auto].
 simpl; rewrite Rmult_comm; assert (H_rw:1 / 2 = Rinv 2); [field|]; rewrite H_rw.
 apply Rle_refl.
Qed.
