Require Import Sierpinskian.
Require Import Kleenean.

Definition st : Sierpinski.Sierpinskian := Sierpinski.true.
Definition si : Sierpinski.Sierpinskian := Sierpinski.indeterminate.

Definition sr := Sierpinski.and (Sierpinski.or st si) si.

Definition sf2 := Sierpinski.true_from 2.

Definition ss := fun n => Sierpinski.true_from n.

Definition sd := Sierpinski.disj ss.

