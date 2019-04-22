Require Export ZF.Axioms.
Require Import ZF.Tactics.

Theorem singleton_not_empty x : nonempty {x,}.
Proof. unfold nonempty. unsettle. exists x. auto. Qed.

Theorem empty_nexists x : ~(exists z, z in x) <-> x = nothing.
Proof.
  split.
  - intros u.
    apply set_ext. intuition.
    * destruct u. firstorder.
    * unsettle. contradiction.
  - intros -> [z]. unsettle. auto.
Qed.

Theorem subset_nexists x y : ~(exists z, z in x /\ ~(z in y)) <-> x sub y.
Proof.
  split.
  - intros nex z ?.
    destruct (classic (z in y)); auto.
    destruct nex. exists z. auto.
  - intros ? [? []]. auto.
Qed.

Theorem subset_ext x y : (x sub y /\ y sub x) <-> x = y.
Proof.
  split.
  - intros []. apply set_ext. intuition.
  - intros <-. unsettle. intuition.
Qed.

Theorem pair_not_empty x y : nonempty {x, y}.
Proof. unfold nonempty. unsettle. exists x. auto. Qed.

Definition ordpair x y := {{x,}, {x, y}}.
Notation "( x , y )" := (ordpair x y) : sets.

Theorem pair_ext1 x y z w : {x, y} = {z, w} -> x = z \/ x = w.
Proof. intros u. ext u. unsettle. firstorder. Qed.

Theorem pair_ext2 x y z w : {x, y} = {z, w} -> y = z \/ y = w.
Proof. intros u. ext u. unsettle. firstorder. Qed.

Theorem ordpair_ext1 x y z w : (x, y) = (z, w) -> x = z.
Proof.
  intros u.
  destruct (pair_ext1 _ _ _ _ u) as [i | i].
  all:symmetry in i.
  all:destruct (pair_ext1 _ _ _ _ i).
  all:auto.
Qed.

Theorem ordpair_ext2 x y z w : (x, y) = (z, w) -> y = w.
Proof.
  intros u.
  rewrite <- (ordpair_ext1 _ _ _ _ u) in u.
  assert (x = y -> y = w). {
    intros <-.
    symmetry in u.
    destruct (pair_ext2 _ _ _ _ u) as [i | i].
    all:destruct (pair_ext2 _ _ _ _ i).
    all:auto.
  }
  destruct (pair_ext2 _ _ _ _ u) as [i | i].
  all:destruct (pair_ext2 _ _ _ _ i).
  all:auto.
Qed.

Theorem repl_distr_cup x y F : c_repl (cup x y) F = cup (c_repl x F) (c_repl y F).
Proof. apply set_ext. unsettle. firstorder. Qed.

Theorem repl_distr_singleton x F : c_repl {x,} F = {F x,}.
Proof. apply set_ext. unsettle. firstorder. subst. auto. Qed.