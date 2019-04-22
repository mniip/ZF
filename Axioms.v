Require Export ZF.Logic.

Axiom set : Type.
Bind Scope sets with set.
Open Scope sets.

Axiom elem : set -> set -> Prop.
Notation "x 'in' y" := (elem x y) (at level 60) : sets.

Axiom set_ext : forall x y, (forall z, z in x <-> z in y) -> x = y.
Definition nonempty x := exists y, y in x.
Definition empty x := ~nonempty x.
Axiom set_reg : forall x, nonempty x -> exists y, y in x /\ ~(exists z, z in y /\ z in x).
Axiom c_specif : set -> (set -> Prop) -> set.
Axiom set_specif : forall x P y, y in c_specif x P <-> y in x /\ P y.
Axiom nothing : set.
Notation "{ }" := nothing : sets.
Axiom set_nothing : empty nothing.
Axiom c_pairing : set -> set -> set.
Axiom set_pairing : forall x y, x in c_pairing x y /\ y in c_pairing x y.
Definition pairing x y := c_specif (c_pairing x y) (fun z => x = z \/ y = z).
Notation "{ x , y }" := (pairing x y) : sets.
Axiom c_union : set -> set.
Axiom set_union : forall x y z, x in y -> y in z -> x in c_union z.
Definition union x := c_specif (c_union x) (fun z => exists y, z in y /\ y in x).
Axiom c_repl : set -> (set -> set) -> set.
Axiom set_repl : forall x F z, z in c_repl x F <-> exists y, y in x /\ z = F y.
Definition singleton x := {x, x}.
Notation "{ x , }" := (singleton x) : sets.
Definition cup x y := union {x, y}.
Definition succ x := cup x {x,}.
Axiom c_inductive : set.
Axiom set_infty : nothing in c_inductive /\ forall x, x in c_inductive -> succ x in c_inductive.
Definition subset x y := forall z, z in x -> z in y.
Notation "x 'sub' y" := (subset x y) (at level 60).
Axiom c_power : set -> set.
Axiom set_power : forall x z, z sub x -> z in c_power x.
Definition power x := c_specif (c_power x) (fun z => z sub x).
Definition cap x y := c_specif x (fun z => z in y).

Definition dep_repl x (F : forall y, y in x -> set) := c_repl x (fun y => match classic (y in x) with
  | left p => F y p
  | right _ => nothing
  end).

Definition dep_specif x (P : forall y, y in x -> Prop) := c_specif x (fun y => exists (p : y in x), P y p).
