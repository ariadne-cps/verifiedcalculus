(******************************************************************************
 *  utilities/extract.v
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














