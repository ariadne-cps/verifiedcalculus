Require Sierpinskian.
Require Kleenean.


Check true.
Require Import Sierpinskian.
Check true.
Require Import Kleenean.
Check true.

Definition st : Sierpinskian := Sierpinskian.true.
Definition si : Sierpinskian := Sierpinskian.indeterminate.

Definition sr := Sierpinskian.and (Sierpinskian.or st si) si.

Definition sf2 := Sierpinskian.true_from 2.

Definition ss := fun n => Sierpinskian.true_from n.

Definition sd := Sierpinskian.disj ss.

