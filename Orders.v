Require Import ZF.Logic.
Require Import ZF.Tactics.
Require Import ZF.Constructions.

Section order.

Variable X : set.
Variable R : set -> set -> Prop.

Definition reflexive := forall a, a in X -> R a a.
Definition transitive := forall a b c, a in X -> b in X -> c in X -> R a b -> R b c -> R a c.
Definition antisymmetric := forall a b, a in X -> b in X -> R a b -> R b a -> a = b.
Definition connex := forall a b, a in X -> b in X -> R a b \/ R b a.

Record pre_ord := {
    pre_refl : reflexive;
    pre_trans : transitive;
  }.
Record part_ord := {
    po_refl : reflexive;
    po_trans : transitive;
    po_antisym : antisymmetric;
  }.
Record total_ord := {
    tot_trans : transitive;
    tot_antisym : antisymmetric;
    tot_connex : connex;
  }.

Definition irreflexive := forall a, a in X -> ~(R a a).
Definition asymmetric := forall a b, a in X -> b in X -> R a b -> ~(R b a).
Definition comparable := forall a b c, a in X -> b in X -> c in X -> R a c -> R a b \/ R b c.
Definition connected := forall a b, a in X -> b in X -> ~(R a b) -> ~(R b a) -> a = b.

Record strict_part_ord := {
    spo_irrefl : irreflexive;
    spo_trans : transitive;
  }.

Record linear_ord := {
    lin_comp : comparable;
    lin_conn : connected;
    lin_asym : asymmetric;
  }.

Theorem connex_reflexive : connex -> reflexive.
Proof. intros u a ?. destruct (u a a); auto. Qed.
Theorem asymmetric_irreflexive : asymmetric -> irreflexive.
Proof. intros u a ? ?. apply (u a a); auto. Qed.
Theorem asymmetric_comparable_transitive : asymmetric -> comparable -> transitive.
Proof. intros u v a b c. specialize (u b c). specialize (v a c b). intuition. Qed.
Theorem connex_transitive_comparable : connex -> transitive -> comparable.
Proof. intros u v a b c. specialize (u a b). specialize (v b a c). intuition. Qed.
Theorem irreflexive_transitive_asymmetric : irreflexive -> transitive -> asymmetric.
Proof. intros u v a b. specialize (u a). specialize (v a b a). intuition. Qed.
Theorem reflexive_comparable_connex : reflexive -> comparable -> connex.
Proof. intros u v a b. specialize (u a). specialize (v a b a). intuition. Qed.

Theorem total_part_ord : total_ord -> part_ord.
Proof. intros []. constructor; auto using connex_reflexive. Qed.
Theorem part_pre_ord : part_ord -> pre_ord.
Proof. intros []. constructor; auto. Qed.
Theorem total_pre_ord : total_ord -> pre_ord.
Proof. intros []. constructor; auto using connex_reflexive. Qed.
Theorem strict_linear_part_ord : linear_ord -> strict_part_ord.
Proof. intros []. constructor; auto using asymmetric_irreflexive, asymmetric_comparable_transitive. Qed.
Theorem linear_trans : linear_ord -> transitive.
Proof. intros []. auto using asymmetric_comparable_transitive. Qed.
Theorem total_comp : total_ord -> comparable.
Proof. intros []. auto using connex_transitive_comparable. Qed.

Definition well_ord := forall W, W sub X -> (exists w, w in W) -> exists m, m in W /\ forall x, x in W -> R m x.
Definition strict_well_ord := forall W, W sub X -> (exists w, w in W) -> exists m, m in W /\ forall x, x in W -> ~(R x m).

End order.

Definition backwards (R : set -> set -> Prop) b a := R a b.

Theorem backwards_refl X R : reflexive X R -> reflexive X (backwards R).
Proof. auto. Qed.
Theorem backwards_trans X R : transitive X R -> transitive X (backwards R).
Proof. intros u a b c. specialize (u c b a). intuition. Qed.
Theorem backwards_antisym X R : antisymmetric X R -> antisymmetric X (backwards R).
Proof. unfold antisymmetric. auto. Qed.
Theorem backwards_connex X R : connex X R -> connex X (backwards R).
Proof. unfold connex, backwards. auto. Qed.
Theorem backwards_irrefl X R : irreflexive X R -> irreflexive X (backwards R).
Proof. auto. Qed.
Theorem backwards_asym X R : asymmetric X R -> asymmetric X (backwards R).
Proof. unfold asymmetric, backwards. auto. Qed.
Theorem backwards_comp X R : comparable X R -> comparable X (backwards R).
Proof. intros u a b c. specialize (u c b a). intuition. Qed.
Theorem backwards_conn X R : connected X R -> connected X (backwards R).
Proof. unfold connected. auto. Qed.

Theorem backwards_pre_ord X R : pre_ord X R -> pre_ord X (backwards R).
Proof. intros []. constructor; auto using backwards_trans. Qed.
Theorem backwards_part_ord X R : part_ord X R -> part_ord X (backwards R).
Proof. intros []. constructor; auto using backwards_trans, backwards_antisym. Qed.
Theorem backwards_total_ord X R : total_ord X R -> total_ord X (backwards R).
Proof. intros []. constructor; auto using backwards_trans, backwards_antisym, backwards_connex. Qed.
Theorem backwards_strict_part_ord X R : strict_part_ord X R -> strict_part_ord X (backwards R).
Proof. intros []. constructor; auto using backwards_trans. Qed.
Theorem backwards_linear_ord X R : linear_ord X R -> linear_ord X (backwards R).
Proof. intros []. constructor; auto using backwards_comp, backwards_conn, backwards_asym. Qed.

Definition dual (R : set -> set -> Prop) b a := ~(R a b).
Theorem dual_refl X R : irreflexive X R -> reflexive X (dual R).
Proof. auto. Qed.
Theorem dual_trans X R : comparable X R -> transitive X (dual R).
Proof. intros u a b c. specialize (u c b a). unfold dual. intuition. Qed.
Theorem dual_antisym X R : connected X R -> antisymmetric X (dual R).
Proof. unfold connected, antisymmetric. auto. Qed.
Theorem dual_connex X R : asymmetric X R -> connex X (dual R).
Proof. intros u a b. specialize (u a b). unfold dual. apply not_not_elim. intuition. Qed.
Theorem dual_irrefl X R : reflexive X R -> irreflexive X (dual R).
Proof. unfold reflexive, irreflexive. intuition. Qed.
Theorem dual_asym X R : connex X R -> asymmetric X (dual R).
Proof. intros u a b. specialize (u a b). intuition. Qed.
Theorem dual_comp X R : transitive X R -> comparable X (dual R).
Proof. intros u a b c. specialize (u c b a). unfold dual. apply not_not_elim. intuition. Qed.
Theorem dual_conn X R : antisymmetric X R -> connected X (dual R).
Proof. unfold connected, antisymmetric. unfold dual. intuition. apply not_not_elim. intuition. Qed.

Theorem dual_well_ord X R : strict_well_ord X R -> well_ord X (dual R).
Proof. intros u W ? ?. destruct (u W) as [M []]; auto. Qed.
Theorem dual_strict_well_ord X R : well_ord X R -> strict_well_ord X (dual R).
Proof. intros u W ? ?. destruct (u W) as [M []]; auto. exists M. auto. Qed.

Theorem dual_total_ord X R : linear_ord X R -> total_ord X (dual R).
Proof. intros []. constructor; auto using dual_trans, dual_antisym, dual_connex. Qed.
Theorem dual_linear_ord X R : total_ord X R -> linear_ord X (dual R).
Proof. intros []. constructor; auto using dual_comp, dual_conn, dual_asym. Qed.

Section mapping.

Variable X : set.
Variables P Q : set -> set -> Prop.

Local Notation "P => Q" := (forall a b, a in X -> b in X -> P a b -> Q a b) (at level 50, only parsing).
Local Notation "P <=> Q" := (forall a b, a in X -> b in X -> P a b <-> Q a b) (at level 50, only parsing).

Theorem map_refl : (P => Q) -> reflexive X P -> reflexive X Q.
Proof. intros ? ? ?. intuition. Qed.
Theorem map_trans : (P <=> Q) -> transitive X P -> transitive X Q.
Proof. intros m u a b c. specialize (u a b c). pose (m a c). pose (m a b). pose (m b c). intuition. Qed.
Theorem map_antisym : (Q => P) -> antisymmetric X P -> antisymmetric X Q.
Proof. intros ? ? ? ?. intuition. Qed.
Theorem map_connex : (P => Q) -> connex X P -> connex X Q.
Proof. intros ? u a b. specialize (u a b). intuition. Qed.
Theorem map_irrefl : (Q => P) -> irreflexive X P -> irreflexive X Q.
Proof. intros ? u a. specialize (u a). intuition. Qed.
Theorem map_asym : (Q => P) -> asymmetric X P -> asymmetric X Q.
Proof. intros ? u a b. specialize (u a b). intuition. Qed.
Theorem map_comp : (P <=> Q) -> comparable X P -> comparable X Q.
Proof. intros m u a b c. specialize (u a b c). pose (m a c). pose (m a b). pose (m b c). intuition. Qed.
Theorem map_conn : (P => Q) -> connected X P -> connected X Q.
Proof. intros ? u a b. specialize (u a b). intuition. Qed.

Theorem map_pre_ord : (P <=> Q) -> pre_ord X P -> pre_ord X Q.
Proof.
  intros m [].
  constructor.
  + eapply map_refl. apply m. auto.
  + eapply map_trans; auto.
Qed.

Theorem map_part_ord : (P <=> Q) -> part_ord X P -> part_ord X Q.
Proof.
  intros m [].
  constructor.
  + eapply map_refl. apply m. auto.
  + eapply map_trans; auto.
  + eapply map_antisym. apply m. auto.
Qed.

Theorem map_total_ord : (P <=> Q) -> total_ord X P -> total_ord X Q.
Proof.
  intros m [].
  constructor.
  + eapply map_trans; auto.
  + eapply map_antisym. apply m. auto.
  + eapply map_connex. apply m. auto.
Qed.

Theorem map_strict_part_ord : (P <=> Q) -> strict_part_ord X P -> strict_part_ord X Q.
Proof.
  intros m [].
  constructor.
  + eapply map_irrefl. apply m. auto.
  + eapply map_trans; auto.
Qed.

Theorem map_linear_ord : (P <=> Q) -> linear_ord X P -> linear_ord X Q.
Proof.
  intros m [].
  constructor.
  + eapply map_comp; auto.
  + eapply map_conn. apply m. auto.
  + eapply map_asym. apply m. auto.
Qed.

Theorem map_well_ord : (P => Q) -> well_ord X P -> well_ord X Q.
Proof. intros m u W ? ?. destruct (u W) as [M []]; auto. exists M. auto. Qed.
Theorem map_strict_well_ord : (Q => P) -> strict_well_ord X P -> strict_well_ord X Q.
Proof. intros m u W ? ?. destruct (u W) as [M []]; auto. exists M. intuition. eauto. Qed.

End mapping.

Theorem well_ord_connex X R : well_ord X R -> connex X R.
Proof.
  intros u a b ? ?.
  destruct (u {a, b}) as [? []].
  + unsettle. intros ? [<- | <-]; auto.
  + exists a. unsettle. auto.
  + unsettle. intuition; subst; auto.
Qed.

Theorem subset_part_ord U : part_ord U subset.
Proof.
  constructor.
  + intros ? ? ?. auto.
  + intros ? ? ? ? ? ? ? ? ?. auto.
  + intros ? ? ? ? ? ?. apply subset_ext. auto.
Qed.