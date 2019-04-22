Require Import ZF.Constructions.
Require Import ZF.Tactics.
Require Import ZF.Regularity.
Require Import ZF.Omega.

Record is_ordinal a : Prop := {
  ordinal_transitive : forall x y, x in a -> y in x -> y in a;
  ordinal_total : forall x y, x in a -> y in a -> (x in y \/ x = y \/ y in x);
}.

Hint Resolve ordinal_transitive : ordinal.
Hint Resolve ordinal_total : ordinal.

Theorem ordinals_transitive : forall a b, is_ordinal a -> b in a -> is_ordinal b.
Proof.
  intros a b ? ?.
  split.
  + intros x y ? ?.
    assert (x in a); eauto with ordinal.
    assert (y in a); eauto with ordinal.
    destruct (ordinal_total a ?? b y) as [ | [<- | ]]; auto.
    - destruct (not_in_triple x b y); auto.
    - destruct (not_in_eachother x b); auto.
  + intros x y ? ?.
    eauto with ordinal.
Qed.

Hint Resolve ordinals_transitive : ordinal.

Theorem ordinals_total : forall a, is_ordinal a -> forall b, is_ordinal b -> (a in b \/ a = b \/ b in a).
Proof. 
  intros a ?.
  induction a as [a aH] using set_ind.
  intros b ?.
  induction b as [b bH] using set_ind.
  destruct (classic (exists x, x in a /\ ~(x in b))) as [[x []] | nex].
  + edestruct (aH x) as [ | [ | ]]; eauto with ordinal.
    - contradiction.
    - subst. auto.
  + destruct (classic (exists y, y in b /\ ~(y in a))) as [[y []] | ney].
    - edestruct (bH y) as [ | [ | ]]; eauto with ordinal.
      * subst. auto.
      * contradiction.
    - right; left.
      apply subset_ext.
      split; apply subset_nexists; auto.
Qed.

Theorem finite_ordinal : forall x, x in omega -> is_ordinal x.
Proof.
  apply omega_ind.
  + split; unsettle; intuition.
  + split; unfold succ; unsettle.
    all:intuition eauto with ordinal.
    all:subst.
    all:intuition.
Qed.

Hint Resolve finite_ordinal : ordinal.

Theorem omega_ordinal : is_ordinal omega.
Proof.
  split; intros.
  + apply (omega_transitive x); auto.
  + apply ordinals_total;
    apply finite_ordinal; auto.
Qed.

Fixpoint fin n := match n with
  | 0 => nothing
  | S n => succ (fin n)
  end.

Theorem fin_in_omega n : fin n in omega.
Proof. induction n; simpl; eauto with omega. Qed.


Definition plus_acc a b := (fix pl b (acc : Acc elem b) := match acc with
  Acc_intro _ h => cup a (dep_repl b (fun d i => pl d (h d i)))
  end) b.

Definition plus a b := plus_acc a b (in_accessible b).
Notation "a + b" := (plus a b) : sets.

Theorem plus_sub a b : a sub a + b.
Proof.
  intros z.
  unfold plus, plus_acc.
  set (acc := in_accessible _). destruct acc.
  unsettle. intuition.
Qed.

Theorem plus_nothing_r a : a + nothing = a.
Proof.
  unfold plus, plus_acc.
  set (acc := in_accessible _). destruct acc.
  apply set_ext.
  unsettle.
  firstorder.
  set x0. unsettle. intuition.
Qed.

Theorem plus_nothing_l a : nothing + a = a.
Proof.
  unfold plus.
  pattern a.
  apply set_ind.
  intros x IH.
  set (acc := in_accessible x).
  destruct acc as [acc].
  replace acc with (fun y (p : y in x) => in_accessible y). 2:{ apply uip. }
  apply set_ext. intros z.
  simpl. unsettle. firstorder.
  + rewrite IH in H; subst; auto.
  + right. exists z. firstorder.
Qed.
