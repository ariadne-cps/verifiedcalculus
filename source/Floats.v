(************************************************************************)
(* Copyright 2010 Milad Niqui                                           *)
(*           2023 Pieter Collins                                        *)
(* This file is distributed under the terms of the                      *)
(* GNU General Public License Version 2                                 *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export Reals.
Require Export Reals.Rbase.
Require Export Reals.Rfunctions.
Require Export Reals.Rbasic_fun.
Require Export Reals.Rbasic_fun.
Require Export Reals.Rdefinitions.

Require Export Lra.
Require Export List.

Require Export R_addenda.

(* 
Module Floats.
*)



Open Scope R_scope.


Lemma or_impl_compat : forall p1 p2 p3 p4 : Prop, 
  (p1 -> p3) -> (p2 -> p4) -> (p1 \/ p2) -> (p3 \/ p4).
Proof.
  intros p1 p2 p3 p4 Hp13 Hp24 Hor.
  apply or_ind with (A:=p1) (B:=p2).
  - left. apply Hp13. exact H.
  - right. apply Hp24. exact H.
  - exact Hor.
Qed.


(*
INR_eq: forall n m : nat, INR n = INR m -> n = m
not_O_S_INR: forall n : nat, INR (S n) <> 0
plus_INR: forall n m : nat, INR (n + m) = INR n + INR m
not_0_INR: forall n : nat, n <> 0%nat -> INR n <> 0
INR_not_0: forall n : nat, INR n <> 0 -> n <> 0%nat
S_O_plus_INR: forall n : nat, INR (1 + n) = INR 1 + INR n
S_INR: forall n : nat, INR (S n) = INR n + 1
minus_INR: forall n m : nat, (m <= n)%nat -> INR (n - m) = INR n - INR m
*)

Lemma INR_0 : INR 0%nat = 0%R.
Proof.
  unfold INR. reflexivity.
Qed.

Lemma INR_1 : INR 1%nat = 1%R.
Proof.
  unfold INR. reflexivity.
Qed.
  
Lemma Rabs_neg_eq : forall x : R, Rle x 0 -> Rabs x = Ropp x.
Proof.
  intro x. intro H. 
  rewrite <- Rabs_pos_eq.
  apply eq_sym. apply Rabs_Ropp.
  apply Ropp_0_le_contravar; exact H.
Qed.








Coercion INR : nat >-> R.


Inductive Rounding := up | down | near.


Inductive BinOp := Add | Sub | Mul.
(* Inductive BinOp := Add | Sub | Mul | Div. *)


Definition Rapply (op:BinOp) : R -> R -> R :=
  match op with
    | Add => Rplus | Sub => Rminus | Mul => Rmult (* | Div => Rdiv *)
  end
.


Class Float (F : Type) :=
{
  NinjF : nat -> F;
  FinjR : F -> R;

  Fnull := NinjF 0;
  Funit := NinjF 1;

  F0 := Fnull;
  F1 := Funit;
  
  Fneg : F -> F;
  Fhlf : F -> F;
  Fabs : F -> F;

  Fadd : Rounding -> F -> F -> F;
  Fsub : Rounding -> F -> F -> F;
  Fmul : Rounding -> F -> F -> F;
  Fdiv : Rounding -> F -> F -> F;

  Frec : Rounding -> F -> F;

  Fdiv_flt_nat : Rounding -> F -> nat -> F := fun r x n => Fdiv r x (NinjF n);

  Fmin : F -> F -> F;
  Fmax : F -> F -> F;
  
  Fleb : F -> F -> bool;




  flt_ninjr : forall n : nat, FinjR (NinjF n) = INR n;
  
  flt_leb : forall (x1 x2 : F), (Fleb x1 x2 = true) <-> (FinjR x1) <= (FinjR x2);
   
  flt_neg_exact : forall x : F, FinjR (Fneg x) = Ropp (FinjR x);
  flt_hlf_exact : forall x : F, FinjR (Fhlf x) = (FinjR x) / 2;
  flt_abs_exact : forall x : F, FinjR (Fabs x) = Rabs (FinjR x);

  flt_min_exact : forall x1 x2 : F, FinjR (Fmin x1 x2) = Rmin (FinjR x1) (FinjR x2);
  flt_max_exact : forall x1 x2 : F, FinjR (Fmax x1 x2) = Rmax (FinjR x1) (FinjR x2);

  Fneg_exact := Fneg; 
  Fabs_exact := Fabs; 
  
  Fadd_up := Fadd up;  
  Fadd_down := Fadd down;  
  Fadd_near := Fadd near;

  Fsub_up := Fsub up;  
  Fsub_down := Fsub down;  
  Fsub_near := Fsub near;

  Fmul_up := Fmul up;  
  Fmul_down := Fmul down;  
  Fmul_near := Fmul near;

(*
  flt_uop_exact (opF : F -> F) (opR : R -> R):
     forall x : F, FinjR (opF x) = opR (FinjR x);

  flt_op_exact (opF : F -> F -> F) (opR : R -> R -> R) :
     forall x1 x2 : F, FinjR (opF x1 x2)  = opR (FinjR x1) (FinjR x2);
*)

(*
  flt_op_near (opF : Rounding -> F -> F -> F) (opR : R -> R -> R) :
    forall x y z: F, Rabs ( (FinjR (opF near x y)) - (opR (FinjR x) (FinjR y)) )
                         <= Rabs ( (FinjR z) - (opR (FinjR x) (FinjR y)) );
*)
  
  
(*
  Fapply (op : BinOp) : Rounding -> F -> F -> F :=
    match op with | Add => Fadd | Sub => Fsub | Mul => Fmul | Div => Fdiv end;
*)
  Fapply (op : BinOp) : Rounding -> F -> F -> F :=
    match op with | Add => Fadd | Sub => Fsub | Mul => Fmul end;

  flt_op_up : forall (op : BinOp) (x y : F),
    (FinjR (Fapply op up x y)) >= (Rapply op (FinjR x) (FinjR y));
  flt_op_down : forall (op : BinOp) (x y : F),
    (FinjR (Fapply op down x y)) <= (Rapply op (FinjR x) (FinjR y));
  flt_op_near : forall (op : BinOp) (x y z : F), 
    Rabs ( (FinjR (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)) )
      <= Rabs ( (FinjR z) - (Rapply op (FinjR x) (FinjR y)) );

(*
  flt_neg_exact := flt_uop_exact Fneg Ropp;
  flt_abs_exact := flt_uop_exact Fabs Rabs;
  flt_min_exact := flt_op_exact Fmin Rmin;
  flt_max_exact := flt_op_exact Fmax Rmax;
*)

  flt_add_near := flt_op_near Add;
  flt_add_up := flt_op_up Add;
  flt_add_down := flt_op_down Add;

  flt_sub_near := flt_op_near Sub;
  flt_sub_up := flt_op_up Sub;
  flt_sub_down := flt_op_down Sub;

  flt_mul_near := flt_op_near Mul;
  flt_mul_up := flt_op_up Mul;
  flt_mul_down := flt_op_down Mul;

  flt_div_up : forall (x y : F),
    (FinjR y <> 0%R) -> (FinjR (Fdiv up x y)) >= (Rdiv (FinjR x) (FinjR y));
  flt_div_down : forall (x y : F),
    (FinjR y <> 0%R) -> (FinjR (Fdiv down x y)) <= (Rdiv (FinjR x) (FinjR y));

  flt_rec_up : forall (x : F),
    (FinjR x <> 0%R) -> (FinjR (Frec up x)) >= (Rinv (FinjR x));
  flt_rec_down : forall (x : F),
    (FinjR x <> 0%R) -> (FinjR (Frec down x)) <= (Rinv (FinjR x));
(*
  flt_div_near := flt_op_near Div;
  flt_div_up := flt_op_up Div;
  flt_div_down := flt_op_down Div;
*)
}.

(* Coercion (forall F : Float F), FinjR : F >-> R. *)






Section Float_defs.

Context `{F : Type} `{FltF : Float F}.


Definition Fdiv2 {F} {Flt : Float F} (r : Rounding) (x:F) := Fdiv r x (NinjF 2).

Definition Fdiv2_up {F} {Flt : Float F} := Fdiv2 up.

Fixpoint Fsum {F} {Flt : Float F} (r : Rounding) (xs : list F) :=
  match xs with | nil => Fnull | hd::tl => Fadd r hd (Fsum r tl) end.
  
Definition Fsum_snd_add {I} {F} {Flt : Float F} (r : Rounding) : list (I * F) -> F
  := fold_right (fun nf=> @Fadd F Flt r (snd nf)) Fnull.

Fixpoint Fpow_up {F} {Flt : Float F} (x:F) (n:nat) :=
    match n with
    | O => Funit
    | S n' => Fmul up x (@Fpow_up F Flt x n')
    end.

Lemma flt_null : FinjR (Fnull) = 0%R.
Proof.
  unfold Fnull. apply flt_ninjr.
Qed.

Lemma flt_add_up_le : forall (x y:F),
  (FinjR x) + (FinjR y) <= FinjR (Fadd up x y).
Proof.
  intros x y.
  apply Rge_le; apply flt_add_up.
Qed.

Lemma flt_mul_up_le : forall (x y:F),
  (FinjR x) * (FinjR y) <= FinjR (Fmul up x y).
Proof.
  intros x y.
  apply Rge_le; apply flt_mul_up.
Qed.

Lemma flt_op_near_up_abs : forall op x y, 
  Rabs ( (FinjR (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)) )
    <= Rabs ( (FinjR (Fapply op up x y)) - (Rapply op (FinjR x) (FinjR y)) ).
Proof.
 intros op x y.
 apply (flt_op_near op) with (z:=Fapply op up x y).
Qed.

Lemma flt_op_near_down_abs : forall op x y, 
  Rabs ( (FinjR (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)))
    <= Rabs ((FinjR (Fapply op down x y)) - (Rapply op (FinjR x) (FinjR y))).
Proof.
 intros op x y.
 apply (flt_op_near op) with (z:=Fapply op down x y).
Qed.

Lemma flt_op_near_up : forall op x y, 
  Rabs ( (FinjR (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)))
    <= (FinjR (Fapply op up x y)) - (Rapply op (FinjR x) (FinjR y)).
Proof.
 intros op x y.
 apply Rle_trans with (r2 := Rabs ( (FinjR (Fapply op up x y)) - (Rapply op (FinjR x) (FinjR y)))).
 - exact (flt_op_near_up_abs op x y).
 - rewrite -> Rabs_pos_eq.
   -- apply Rle_refl.
   -- apply Rge_le. apply Rge_minus. apply flt_op_up.
Qed.

Lemma flt_op_near_down : forall op x y, 
  Rabs ( (FinjR (Fapply op near x  y)) - (Rapply op (FinjR x) (FinjR y))) 
    <= (Rapply op (FinjR x) (FinjR y)) - (FinjR (Fapply op down x y)).
Proof.
 intros op x y.
 apply Rle_trans with (r2 := Rabs ( (FinjR (Fapply op down x y)) - (Rapply op (FinjR x) (FinjR y)))).
 - apply flt_op_near_down_abs.
 - rewrite -> Rabs_minus_sym. rewrite Rabs_pos_eq.
   -- apply Rle_refl.
   -- apply Rge_le. apply Rge_minus. apply Rle_ge. apply flt_op_down.
Qed.


Lemma flt_op_near_up_down : forall op x y, 
  Rabs ( (FinjR (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)) )
    <= ( (FinjR (Fapply op  up x y)) - (FinjR (Fapply op  down x y)) ) / 2.
Proof.
  intros op x y.
  apply Rmult_le_reg_l with 2. lra.
  stepr ((FinjR (Fapply op up x y) - (Rapply op (FinjR x) (FinjR y))) + (Rapply op (FinjR x) (FinjR y) - FinjR (Fapply op down x y))) by field.
  - stepl (Rabs ( (FinjR (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)) ) + Rabs ((FinjR (Fapply op near x y)) - Rapply op (FinjR x) (FinjR y))) by ring.
    apply Rplus_le_compat.
    -- apply flt_op_near_up.
    -- apply flt_op_near_down.
Qed.

Lemma flt_op_near_up_down_sub_up : forall op x y, 
  Rabs ( (FinjR (Fapply op near x y))- (Rapply op (FinjR x) (FinjR y)) )
    <= (FinjR (Fsub up (Fapply op up x y) (Fapply op down x y))) / 2.
Proof.
  intros op x y.
  apply Rle_trans with (((FinjR (Fapply op up x y))-(FinjR (Fapply op down x y)))/2);
    [apply flt_op_near_up_down|].
  apply Rmult_le_compat_r; [lra|].
  apply Rge_le. apply flt_sub_up.
Qed.

Lemma flt_op_near_up_down_sub_hlf_up : forall op x y, 
    Rabs ( (FinjR  (Fapply op near x y)) - (Rapply op (FinjR x) (FinjR y)) )
      <=  FinjR (Fdiv2 up (Fsub up (Fapply op up x y) (Fapply op down x y))).
Proof.
  intros op x y.
  apply Rle_trans with ((FinjR (Fsub up (Fapply op up x y) (Fapply op down x y)))/2);
    [apply flt_op_near_up_down_sub_up|].
  remember (Fsub up (Fapply op up x y) (Fapply op down x y)) as z.
  stepl ((FinjR z)/(FinjR (NinjF 2))).
  - assert (FinjR (NinjF 2%nat) <> 0%R) as H2ne0. {
      rewrite -> flt_ninjr. apply not_O_S_INR.
    }
    apply Rge_le; unfold Fdiv2; apply flt_div_up. apply H2ne0.
  - rewrite -> flt_ninjr; reflexivity.
Qed. 

(*
Lemma flt_mul_near_up: forall {F:Type} {FltF:Float F} x y,
  Rabs ( (FinjR (Fmul near x y)) - ((FinjR x) * (FinjR y))) <= (FinjR (Fmul up x y)) - ((FinjR x) * (FinjR y)).
Proof.
  intros. apply (@flt_op_near_up F FltF Mul).
Qed.
*)

End Float_defs.

(*
End Floats.
*)
