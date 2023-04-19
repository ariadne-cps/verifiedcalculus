Require Extraction.
(*
Extraction Language OCaml.
*)
Extraction Language C++.

Require Import QArith.

(* Require ExtrOCamlBasic. *)

Require Import R_addenda.
Require Import Floats.
Require Import Bounds.
Require Import RationalFloat.

Extract Inductive bool => "bool" [ "true" "false" ].

About Q.

(*
Extract Inductive QArith_base.Q => "Rational" [ "Rational" ].
*)

Extract Inductive Q => "Rational" [ "Rational" ].

(*
Extract Instance Rational_Float => "RationalFloat".
*)

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

Definition next n := S n.

(*
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
*)

(* From LF Require Import ImpCEvalFun. *)

Extraction "verifiedcalculus.ml" nat next.

(*
Extraction "verifiedcalculus.ml" Q next.
*)














