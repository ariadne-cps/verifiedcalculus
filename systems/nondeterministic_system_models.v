(******************************************************************************
 *  systems/nondeterministic_system_models.v
 *
 *  Copyright 2023 Sacha L. Sindorf
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


Require Import Coq.Sets.Ensembles.
Require Import EnsembleMonad.

Section NondeterministicSystems.

Notation M := Ensemble.

(*
Inductive system {UA UD X Y : Type} : Type :=
  | state_space_model (f:X->UA*UD->M X) (h:X->UA->Y) (e:M X)
.
*)

Inductive System {U X Y : Type} : Type :=
  | state_space_model (f:X->U->M X) (h:X->U->Y) (e:M X)
.

Definition nonblocking {U X Y} (s : @System U X Y) :=
  match s with | state_space_model f _ e => inhabited e /\ forall x u, inhabited (f x u) end.


(* Useful types for constructing examples. *)
Inductive Single := | only.
Inductive Double := | first | second.


End NondeterministicSystems.
