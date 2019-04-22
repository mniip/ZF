Require Import ZF.Axioms.

Notation "??" := (ltac:(assumption)) (only parsing).

Local Lemma and_map_l (B C A : Prop) : (A -> B) -> A /\ C -> B /\ C. Proof. intuition. Qed.
Local Lemma and_map_r (C B A : Prop) : (A -> B) -> C /\ A -> C /\ B. Proof. intuition. Qed.
Local Lemma or_map_l (B C A : Prop) : (A -> B) -> A \/ C -> B \/ C. Proof. intuition. Qed.
Local Lemma or_map_r (C B A : Prop) : (A -> B) -> C \/ A -> C \/ B. Proof. intuition. Qed.
Local Lemma forall_map A (P Q : A -> Prop) : (forall a, P a -> Q a) -> (forall a, P a) -> (forall a, Q a). Proof. intuition. Qed.

Local Lemma nothing_ft e : e in nothing <-> False.
Proof. intuition. apply set_nothing. exists e. auto. Qed.

Local Lemma union_ft e x : e in union x <-> exists y, e in y /\ y in x.
Proof.
  split.
  + apply set_specif.
  + intros [y []].
    apply set_specif.
    split.
    - apply (set_union _ y); auto.
    - exists y; auto.
Qed.

Local Lemma pairing_ft e x y : e in {x, y} <-> e = x \/ e = y.
Proof.
  split; intros p.
  + apply set_specif in p. intuition.
  + apply set_specif.
    intuition; subst;
    apply set_pairing.
Qed.

Local Lemma singleton_ft e x : e in {x,} <-> e = x. Proof. pose (pairing_ft e x x). intuition. Qed.

Local Lemma cup_ft e x y : e in cup x y <-> e in x \/ e in y.
Proof.
  split; intros p.
  + apply union_ft in p as [? [? p]].
    apply pairing_ft in p.
    intuition; subst; auto.
  + apply union_ft.
    destruct p;
    exists x + exists y; intuition; apply pairing_ft; progress intuition.
Qed.

Local Lemma power_ft e x : e in power x <-> e sub x.
Proof.
  split; intros p.
  + apply (set_specif (c_power x) (fun z => z sub x)). auto.
  + apply set_specif.
    split; auto.
    apply set_power. auto.
Qed.

Local Lemma dep_repl_ft e x (F : forall y, y in x -> set) : e in dep_repl x F <-> exists y, exists p, e = F y p.
Proof.
  split; intros p.
  + apply set_repl in p as [y [q i]].
    exists y. exists q.
    set (s := classic (y in x)) in i. destruct s; try contradiction.
    erewrite (uip q). eauto.
  + destruct p as [y [q i]]. 
    apply set_repl.
    exists y. split; auto.
    set (s := classic (y in x)). destruct s; try contradiction.
    erewrite (uip q) in i. eauto.
Qed.

Ltac inclusion_goal := lazymatch goal with
  | |- _ <-> _ => unfold iff; inclusion_goal
  | |- _ sub _ => unfold subset
  | |- not _ => unfold not; inclusion_goal
  | |- ?p -> ?q => let v := fresh in intros v; inclusion_goal + inclusion_hyp v; revert v
  | |- forall v, ?p => let v := fresh v in intros v; inclusion_goal; revert v
  | |- ?p /\ ?q => (eapply (and_map_l p q); [ let v := fresh in intros v; inclusion_goal; exact v | ])
                || (eapply (and_map_r p q); [ let v := fresh in intros v; inclusion_goal; exact v | ])
  | |- ?p \/ ?q => (eapply (or_map_l p q); [ let v := fresh in intros v; inclusion_goal; exact v | ])
                || (eapply (or_map_r p q); [ let v := fresh in intros v; inclusion_goal; exact v | ])
  | |- exists v, ?p => let A := fresh in let Q := fresh in
                       evar (A : Type); evar (Q : A -> Prop);
                       cut (exists v, Q v);
                       [ let v := fresh in let w := fresh in intros [w v]; exists w; inclusion_goal; exact v | ];
                       subst A Q; cbn
  | |- ?e in c_specif ?x ?P => apply (set_specif x P e)
  | |- ?e in nothing => apply (nothing_ft e)
  | |- ?e in {?x, ?y} => apply (pairing_ft e x y)
  | |- ?e in union ?x => apply (union_ft e x)
  | |- ?e in c_repl ?x ?F => apply (set_repl x F e)
  | |- ?e in dep_repl ?x ?F => apply (dep_repl_ft e x F)
  | |- ?e in {?x,} => apply (singleton_ft e x)
  | |- ?e in cup ?x ?y => apply (cup_ft e x y)
  | |- ?e in cap ?x ?y => apply (set_specif x (fun z => z in y) e)
  | |- ?e in power ?x => apply (power_ft e x)
  end
with inclusion_hyp H := lazymatch type of H with
  | _ <-> _ => unfold iff in H; inclusion_hyp H
  | _ sub _ => unfold subset in H
  | not _ => unfold not in H; inclusion_hyp H
  | ?p -> ?q => let r := fresh in let H' := fresh in evar (r : Prop);
                ( assert (H' : p -> r);
                  [ let v := fresh in intros v; let v' := fresh in pose (v' := H v); inclusion_hyp v'; exact v' | ]
                ) || ( assert (H' : r -> q);
                  [ let v := fresh in intros v; refine (H _); inclusion_goal; exact v | ]
                );
                clear H; rename H' into H; subst r
  | forall v, ?p => let A := fresh in let Q := fresh in
                    evar (A : Type); evar (Q : A -> Prop);
                    cut (forall v, Q v);
                    [ | let v := fresh in intros v; specialize H with v; inclusion_hyp H; exact H ];
                    clear H; intros H; subst A Q; cbn in H
  | ?p /\ ?q => (eapply (and_map_l _ q p) in H; [ | let v := fresh in intros v; inclusion_hyp v; exact v ])
             || (eapply (and_map_r p _ q) in H; [ | let v := fresh in intros v; inclusion_hyp v; exact v ])
  | ?p \/ ?q => (eapply (or_map_l _ q p) in H; [ | let v := fresh in intros v; inclusion_hyp v; exact v ])
             || (eapply (or_map_r p _ q) in H; [ | let v := fresh in intros v; inclusion_hyp v; exact v ])
  | exists v, ?p => let A := fresh in let P := fresh in
                    evar (A : Type); evar (P : A -> Prop);
                    cut (exists v, P v);
                    [ | let v := fresh in let w := fresh in destruct H as [w v]; exists w; inclusion_hyp v; exact v ];
                    clear H; intros H; subst A P; cbn in H
  | ?e in c_specif ?x ?P => apply (set_specif x P e) in H
  | ?e in nothing => apply (nothing_ft e) in H
  | ?e in {?x, ?y} => apply (pairing_ft e x y) in H
  | ?e in union ?x => apply (union_ft e x) in H
  | ?e in c_repl ?x ?F => apply (set_repl x F e) in H
  | ?e in dep_repl ?x ?F => apply (dep_repl_ft e x F) in H
  | ?e in {?x,} => apply (singleton_ft e x) in H
  | ?e in cup ?x ?y => apply (cup_ft e x y) in H
  | ?e in cap ?x ?y => apply (set_specif x (fun z => z in y) e) in H
  | ?e in power ?x => apply (power_ft e x) in H
  end.

Ltac inclusion := inclusion_goal + match goal with H : _ |- _ => inclusion_hyp H end.
Global Ltac unsettle := repeat inclusion.

Global Ltac ext H := lazymatch type of H with
  | ?x = ?y => let H' := fresh in assert (H' : forall z, z in x <-> z in y);
               [ intros ?; split; intros ?; [ rewrite <- H | rewrite H ]; assumption | ];
               clear H; rename H' into H
  end.