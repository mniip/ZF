Require Import ZF.Axioms.
Require Import ZF.Constructions.
Require Import ZF.Tactics.
Require Import ZF.Omega.

Theorem not_in_self x : ~(x in x).
Proof.
  intros ?.
  destruct (set_reg {x,}) as [? []]. { apply singleton_not_empty. }
  unsettle. subst. firstorder.
Qed.

Theorem not_in_eachother x y: ~(x in y /\ y in x).
Proof.
  intros ?.
  destruct (set_reg {x, y}) as [? []]. { apply pair_not_empty. }
  unsettle. intuition; subst; firstorder.
Qed.

Theorem not_in_triple x y z : ~(x in y /\ y in z /\ z in x).
Proof.
  intros ?.
  destruct (set_reg (cup {x, y} {y, z})) as [w [i d]]. { exists x. unsettle. auto. }
  unsettle. intuition; subst; firstorder.
Qed.

Theorem in_well_founded s : nonempty s -> exists m, m in s /\ forall w, w in s -> ~(w in m).
Proof. 
  intros e.
  destruct (set_reg _ e) as [x [? H]].
  exists x. intuition.
  destruct H. exists w. auto.
Qed.

Definition transitive_closure a := union (c_repl omega (recurse a union)).

Theorem transitive_closure_transitive a b c: b in c -> c in transitive_closure a -> b in transitive_closure a.
Proof.
  intros ? i.
  unfold transitive_closure in *.
  unsettle.
  destruct i as [l [? [n]]].
  exists (union l).
  unsettle. split.
  + exists c. auto.
  + exists (succ n).
    intuition. subst.
    rewrite recurse_s; auto.
Qed.

Theorem set_ind (P : set -> Prop) : (forall x, (forall y, y in x -> P y) -> P x) -> forall z, P z.
Proof.
  intros I a.
  destruct (classic (P a)) as [ | na]; auto.
  destruct (in_well_founded (c_specif (transitive_closure {a,}) (fun z => ~P z))) as [m [i min]]. {
    exists a. unfold transitive_closure. unsettle. intuition.
    exists {a,}. unsettle. intuition.
    exists nothing.
    intuition.
    auto using recurse_z.
  }
  unsettle.
  destruct i as [? u].
  destruct u.
  apply I.
  intros y ?.
  destruct (classic (P y)); auto.
  destruct (min y); intuition.
  eauto using transitive_closure_transitive.
Qed.

Print set_ind.

Theorem in_accessible x : Acc elem x.
Proof. induction x using set_ind. constructor. auto. Qed.

(*
Section wf_recursion.
Variable S : forall x, (forall y, y in x -> set) -> set.

Local Record is_wf_recursive i F : Prop := {
  is_wf_rec_pairs : forall p, p in F -> exists s x, s in i /\ p = (k, x);
  is_wf_rec_functional : forall s, s in i -> exists! x, (k, x) in F;
  is_wf_rec_s : forall s, s in i -> (forall (k, x) in F -> (succ k, S x) in F;
}.

*)


