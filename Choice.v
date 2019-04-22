Require Import ZF.Axioms.
Require Import ZF.Tactics.
Require Import ZF.Constructions.
Require Import ZF.Orders.

Definition Choice := forall A, (forall X, X in A -> exists x, x in X) -> exists F, forall X, X in A -> F X in X.

Definition Zorn := forall X R, part_ord X R -> (forall C, C sub X -> total_ord C R -> exists b, b in X /\ forall c, c in C -> R c b) -> exists m, m in X /\ forall x, x in X -> R m x -> m = x.

Definition StrictZorn := forall X R, strict_part_ord X R -> (forall C, C sub X -> linear_ord C R -> exists b, b in X /\ forall c, c in C -> R c b \/ c = b) -> exists m, m in X /\ forall x, x in X -> ~(R m x).

Definition StrictWellOrdering := forall X, exists R, linear_ord X R /\ strict_well_ord X R.

Definition WellOrdering := forall X, exists R, total_ord X R /\ well_ord X R.

Section zorn_well_ordering.

Local Definition step_for S x Y := ~(x in Y) /\ Y in S /\ cup Y {x,} in S.

Local Record ascend X S := {
  asc_sub : forall A, A in S -> A sub X;
  asc_linear : connex S subset;
  asc_pinned : nothing in S;
  asc_step : forall x, x in union S -> exists Y, step_for S x Y;
  asc_min : forall W, W sub union S -> (exists w, w in W) -> exists x Y, x in W /\ step_for S x Y /\ cap Y W = nothing;
}.

Local Theorem step_unique X S x Y Y' : ascend X S -> step_for S x Y -> step_for S x Y' -> Y = Y'.
Proof.
  intros ? [? []] [? []].
  destruct (classic (exists y, y in Y /\ ~(y in Y'))) as [[y []] | ].
  + destruct (asc_linear X S ?? Y (cup Y' {x,})) as [u | u]; auto.
    - unsettle.
      destruct (u y) as [ | <-]; auto; contradiction.
    - unsettle.
      assert (x in Y). { apply u. auto. }
      contradiction.
  + destruct (classic (exists y, y in Y' /\ ~(y in Y))) as [[y []] | ].
    - destruct (asc_linear X S ?? Y' (cup Y {x,})) as [u | u]; auto.
      * unsettle.
        destruct (u y) as [ | <-]; auto; contradiction.
      * unsettle.
        assert (x in Y'). { apply u. auto. }
        contradiction.
    - apply subset_ext.
      split; apply subset_nexists; auto.
Qed.

Local Definition ascend_bound C := cup {nothing,} (union C).

Local Theorem ascend_bound_ascend X C : total_ord C subset -> (forall S, S in C -> ascend X S) -> ascend X (ascend_bound C).
Proof.
  intros asc. split; unfold ascend_bound, connex; unsettle.
  + intros A [-> | [S []]].
    - unsettle; intuition.
    - apply (asc_sub X S); auto.
  + intros A B [-> | [S1 []]] [-> | [S2 []]]; unsettle; intuition.
    destruct (tot_connex C subset ?? S1 S2); auto.
    - assert (ascend X S2). { auto. }
      destruct (asc_linear X S2 ?? A B); auto.
    - assert (ascend X S1). { auto. }
      destruct (asc_linear X S1 ?? A B); auto.
  + auto.
  + intros x [B [? [-> | [S []]]]].
    - unsettle. contradiction.
    - assert (ascend X S). { auto. }
      assert (S sub (ascend_bound C)). {
        unfold ascend_bound. unsettle.
        intros ? ?. right. exists S. auto.
      }
      destruct (asc_step X S ?? x) as [Y [? []]]. { unsettle. exists B. auto. }
      exists Y.
      split; try split; auto.
  + intros W ? [w].
    assert (w in union (ascend_bound C)) as u. { unfold ascend_bound. unsettle. auto. }
    unfold ascend_bound in *. unsettle.
    destruct u as [B [? [-> | [S []]]]].
    - unsettle. contradiction.
    - assert (ascend X S). { auto. }
      assert (S sub (ascend_bound C)). {
        unfold ascend_bound. unsettle.
        intros ? ?. right. exists S. auto.
      }
      destruct (asc_min X S ?? (cap W (union S))) as [x [Y [? [[? []] u%empty_nexists]]]].
      { unsettle. intuition. }
      { unsettle. exists w. split; auto. exists B. auto. }
      exists x. exists Y.
      split; try split; try split; auto.
      * unsettle. intuition.
      * apply empty_nexists.
        unsettle. intros [z []]. apply u.
        exists z. intuition.
        exists Y. auto.
Qed.

Local Definition ascend_succ S x := cup S {union S, cup (union S) {x,}}.

Local Theorem ascend_succ_ascend X S y : y in X -> ~(y in union S) -> ascend X S -> ascend X (ascend_succ S y).
Proof.
  intros ? d ?. split; unfold ascend_succ, connex; unsettle.
  + intros A [ | [-> | ->]].
    - apply (asc_sub X S ?? A). auto.
    - unsettle. intros x [A []].
      apply (asc_sub X S ?? A); auto.
    - unsettle. intros x [[A []] | <-]; auto.
      apply (asc_sub X S ?? A); auto.
  + assert (forall A, A in S -> A sub (union S)). { unsettle. intuition. exists A. auto. }
    assert (forall A, A in S -> A sub (cup (union S) {y,})). { unsettle. left. eauto. }
    assert (forall A, A sub A). { intros ? ?. auto. }
    unsettle.
    intros A B [ | [-> | ->]] [ | [-> | ->]]; eauto.
    - apply (asc_linear X S ?? A B); auto.
    - left. unsettle. auto.
    - right. unsettle. auto.
  + left. apply (asc_pinned X S). auto.
  + assert (forall x B, x in B -> B in S -> exists Y, step_for (ascend_succ S y) x Y) as ss. {
      intros x B ? ?.
      destruct (asc_step X S ?? x) as [Y [? []]]. { unsettle. exists B. auto. }
      unfold ascend_succ.
      exists Y. split; try split; unsettle; auto.
    }
    intros x [B [u [ | [-> | ->]]]].
    - eauto. 
    - unsettle. destruct u as [B []]. eauto.
    - unsettle. destruct u as [[B []] | ->]; eauto.
      exists (union S).
      split; try split; unsettle; auto.
  + intros W u [w].
    destruct (classic (exists v, v in W /\ v <> y)) as [[v []] | nex].
    - destruct (asc_min X S ?? (c_specif W (fun v => v <> y))) as [x [Y [? [[? []] i%empty_nexists]]]]. {
        unsettle. intros z [].
        destruct (u z) as [B [? [ | [-> | ->]]]]; unsettle; intuition.
        exists B. auto.
      }
      { exists v. unsettle. auto. }
      exists x. exists Y. split; try split; try split; unsettle; auto.
      * unsettle. intuition.
      * apply empty_nexists. unsettle.
        intros [z []]. apply i. exists z. intuition.
        apply d. exists Y. subst. auto.
    - exists y. exists (union S). split; try split; try split; unsettle; auto.
      * replace y with w; auto.
        apply not_not_elim. intros ?.
        destruct nex. exists w. auto.
      * apply empty_nexists. unsettle. intros [z [[B []]]].
        apply nex. exists z. intuition. subst.
        apply d. exists B. auto.
Qed.

Theorem zorn_well_ordering : Zorn -> StrictWellOrdering.
Proof.
  intros Zorn X.
  pose (J := c_specif (power (power X)) (ascend X)).
  destruct (Zorn J _ (subset_part_ord _)) as [M [? max]]. {
    intros C u ?.
    exists (ascend_bound C). unfold J in *. unsettle.
    split; try split.
    + unfold ascend_bound. unsettle.
      intros B [-> | [S []]].
      - unsettle. intuition.
      - assert (ascend X S). { apply u. auto. }
        apply (asc_sub X S ?? B). auto.
    + apply ascend_bound_ascend; auto. apply u.
    + unfold ascend_bound. unsettle. intros S ? z ?.
      right. exists S. auto.
  }
  assert (ascend X M). { unfold J in *. unsettle. intuition. }
  assert (X sub union M) as top. {
    apply subset_nexists.
    intros [y [? u]].
    pose (S := ascend_succ M y).
    apply u. rewrite (max S).
    + unfold ascend_succ in *. subst S. unsettle.
      exists (cup (union M) {y, }). unsettle. intuition.
    + unfold J. unsettle. split.
      - assert (forall A, A in M -> A sub X). { intros A. apply (asc_sub X M ?? A). }
        unfold S, ascend_succ. unsettle.
        intros B [ | [-> | ->]]; eauto.
        * unsettle. intros ? [? []]. eauto.
        * unsettle. intros ? [[? []] | <-]; eauto.
      - apply ascend_succ_ascend; unsettle; auto.
    + unfold S, ascend_succ. unsettle. auto.
  }
  exists (fun x y => exists Y, x in Y /\ step_for M y Y).
  split; try split.
  + intros a b c ? ? ? [Yc [? sc]].
    destruct (asc_step X M ?? a) as [Ya sa]; auto.
    destruct (asc_step X M ?? b) as [Yb sb]; auto.
    unfold step_for in *.
    destruct (asc_linear X M ?? (cup Yb {b,}) Yc) as [u | i]; unsettle.
    1,2:intuition.
    - right. exists Yc. intuition.
    - destruct (i a) as [ | ->]; auto.
      * left. exists Yb. intuition.
      * right. exists Yc. intuition.
  + intros a b ? ? na nb. 
    destruct (asc_step X M ?? a) as [Ya sa]; auto.
    destruct (asc_step X M ?? b) as [Yb sb]; auto.
    unfold step_for in *.
    destruct (asc_linear X M ?? (cup Ya {a,}) (cup Yb {b,})) as [u | u]; unsettle.
    1,2:intuition.
    - destruct (u a); auto.
      destruct na. exists Yb. intuition.
    - destruct (u b); auto.
      destruct nb. exists Ya. intuition.
  + intros a b ? ? [Ya sa] [Yb sb].
    unfold step_for in *.
    destruct (asc_linear X M ?? Ya Yb); intuition.
  + intros W ? [w].
    destruct (asc_min X M ?? W) as [m [Ym [? [? u%empty_nexists]]]]. { intros ?. auto. } { exists w. auto. }
    exists m. split; try split; auto.
    intros x ? [Y []].
    destruct u. exists x. unsettle.
    rewrite (step_unique X M m Ym Y); auto.
Qed.

End zorn_well_ordering.

Theorem strict_well_ordering : WellOrdering <-> StrictWellOrdering.
Proof.
  split.
  + intros wo X. destruct (wo X) as [R []].
    exists (dual R). auto using dual_linear_ord, dual_strict_well_ord.
  + intros swo X. destruct (swo X) as [R []].
    exists (dual R). auto using dual_total_ord, dual_well_ord.
Qed.

Theorem strict_zorn : Zorn <-> StrictZorn.
Proof.
  split.
  + intros z X R ? u.
    destruct (z X (fun x y => R x y \/ x = y)) as [m [? e]].
    - constructor.
      * intros ?. auto.
      * intros a b c ? ? ? [ | <-] [ | <-]; auto.
        left. apply (spo_trans X R ?? a b c); auto.
      * intros a b ? ? [] []; auto.
        destruct (spo_irrefl X R ?? a); auto.
        apply (spo_trans X R ?? a b a); auto.
    - intros C ? to.
      destruct (u C) as [b [? j]]; auto.
      * apply (map_linear_ord C (dual (fun x y => R x y \/ x = y)) R). {
          unfold dual. intuition.
          - apply not_not_elim. intros ?.
            destruct (tot_connex C _ to a b); intuition.
          - apply (spo_irrefl X R ?? a); auto.
            apply (spo_trans X R ?? a b a); auto.
          - subst. apply (spo_irrefl X R ?? a); auto.
        }
        apply dual_linear_ord. auto.
      * exists b. intuition.
    - exists m. intuition.
      replace x with m in *; auto.
      apply (spo_irrefl X R ?? m); auto.
  + intros sz X R ? u.
    destruct (sz X (fun x y => R x y /\ x <> y)) as [m [? e]].
    - constructor.
      * intros ?. intuition.
      * intros a b c ? ? ? [] []. split.
        ** apply (po_trans X R ?? a b c); auto.
        ** intros <-. replace a with b in *; intuition. apply (po_antisym X R ?? b a); auto.
    - intros C ? lo.
      destruct (u C) as [b [? j]]; auto.
      * apply (map_total_ord C (dual (fun x y => R x y /\ x <> y)) R). {
          split.
          - intros j. unfold dual in j.
            apply not_not_elim. intros ?.
            destruct (lin_conn C _ lo b a); auto. { intros []. contradiction. }
            pose (po_refl X R ?? b). intuition.
          - intros ? [].
            replace a with b in *; auto.
            apply (po_antisym X R ?? b a); auto.
        }
        apply dual_total_ord. auto.
      * exists b. intuition.
        destruct (classic (c = b)); auto.
    - exists m. intuition.
      apply not_not_elim. intros ?.
      apply (e x); auto.
Qed.

Section well_ordering_choice.

Local Theorem function_comprehension (P : set -> set -> Prop) : (forall x, exists! y, P x y) -> sig (fun f => forall x, P x (f x)).
Proof.
  intros u.
  exists (fun x => @the _ (fun y => P x y) (u x)).
  intros x. unfold the.
  set (t := definite_description _ _).
  destruct t. auto.
Qed.

Theorem well_ordering_choice : WellOrdering -> Choice.
Proof.
  intros wo A ex.
  destruct (wo (union A)) as [R [? w]].
  assert (forall X, exists! m, if classic (X in A) then m in X /\ forall x, x in X -> R m x else nothing = m) as u. {
    intros X. set (s := classic (X in A)). destruct s.
    + destruct (w X) as [m []].
      - intros x ?. unsettle. exists X. auto.
      - destruct (ex X); auto.
      - exists m. split; try split; auto.
        intros y []. apply (tot_antisym (union A) R ?? m y); auto.
        * unsettle. exists X. auto.
        * unsettle. exists X. auto.
    + exists nothing. split; auto.
  }
  destruct (function_comprehension _ u) as [F pF].
  exists F. intros X ?. specialize (pF X).
  set (s := classic (X in A)) in *. destruct s; intuition.
Qed.

End well_ordering_choice.
