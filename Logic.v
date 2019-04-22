Axiom classic : forall (P : Prop), {P} + {~P}.

Axiom uip : forall {P : Prop} (p q : P), p = q.

Theorem not_not_elim P : ~~P -> P.
Proof. destruct (classic P); intuition. Qed.

Definition definite {T} (V : T -> Prop) := exists! y, V y.
Axiom definite_description : forall {T} (V : T -> Prop), definite V -> sig V.
Definition the {T} (V : T -> Prop) {p : definite V} := proj1_sig (definite_description V p).

Theorem definite_compat {T} (V P : T -> Prop) : definite V -> (exists x, V x /\ P x) <-> (forall x, V x -> P x).
Proof.
  intros [y [? eq]].
  split.
  + intros [x []] z ?.
    replace x with y in *; auto.
    replace z with y in *; auto.
  + intros ?. exists y. auto.
Qed.