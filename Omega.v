Require Import ZF.Constructions.
Require Import ZF.Tactics.

Definition omega := c_specif c_inductive (fun y => forall x, nothing in x -> (forall y, y in x -> succ y in x) -> y in x).

Theorem induction x : x sub omega -> nothing in x -> (forall y, y in x -> succ y in x) -> x = omega.
Proof.
  intros ? ? ?.
  apply set_ext. intros z. split; auto.
  unfold omega.
  unsettle. intuition.
Qed.

Theorem omega_nothing : nothing in omega.
Proof. unfold omega. unsettle. intuition. apply set_infty. Qed.

Theorem omega_succ x : x in omega -> succ x in omega.
Proof. unfold omega. unsettle. intuition. apply set_infty. auto. Qed.

Hint Resolve omega_nothing : omega.
Hint Resolve omega_succ : omega.
Hint Resolve (ltac:(unfold succ; unsettle; auto) : forall x, x in succ x) : omega.

Theorem omega_ind (P : set -> Prop) : P nothing -> (forall y, y in omega -> P y -> P (succ y)) -> forall z, z in omega -> P z.
Proof.
  intros ? ?.
  assert (c_specif omega P = omega) as h. {
    apply induction.
    all:unfold omega; unsettle; intuition.
    all:apply set_infty; auto.
  }
  rewrite <- h.
  unsettle. intuition.
Qed.

Theorem omega_strong_ind (P : set -> Prop) : (forall y, y in omega -> (forall z, z in y -> P z) -> P y) -> forall w, w in omega -> P w.
Proof.
  intros step.
  assert (forall z, z in omega -> forall w, w in z -> P w) as ind. {
    apply (omega_ind (fun z => forall w, w in z -> P w)).
    + unsettle. intuition.
    + unfold succ. unsettle. intuition. subst. auto.
  }
  intros w ?.
  specialize (ind (succ w)). intuition.
Qed.

Theorem omega_transitive : forall x, x in omega -> forall y, y in x -> y in omega.
Proof.
  intros x ?.
  pattern x. apply omega_ind; auto.
  + unsettle. intuition.
  + unfold succ. unsettle. intuition. subst. auto.
Qed.

Theorem omega_transitives : forall x, x in omega -> forall y z, z in y -> y in x -> z in x.
Proof.
  apply (omega_ind (fun x => forall y z, z in y -> y in x -> z in x)).
  + unsettle. intuition.
  + unfold succ. unsettle.
    intros x ? ? y z ? [ | <-]; eauto.
Qed.

Theorem omega_not_in_self : forall x, x in omega -> ~(x in x).
Proof.
  apply omega_strong_ind.
  intros x ? IH ?.
  apply (IH x); auto.
Qed.

Theorem omega_not_in_eachother : forall x y, x in omega -> y in omega -> ~(x in y /\ y in x).
Proof.
  intros x y ? ? [].
  apply (omega_not_in_self x); auto.
  apply (omega_transitives x ?? y x); auto.
Qed.

Theorem omega_pred x y : y in omega -> succ x in succ y -> x in y.
Proof.
  intros ?.
  pattern y. apply omega_ind; auto.
  all:unfold succ in *.
  all:unsettle.
  all:intuition.
  + ext H1.
    unsettle.
    apply (H1 x). auto.
  + ext H3.
    unsettle.
    apply (H3 x). auto.
Qed.

Section recursion.
Variable Z : set.
Variable S : set -> set.

Local Record is_recursive n F : Prop := {
  is_rec_pairs : forall p, p in F -> exists k x, k in succ n /\ p = (k, x);
  is_rec_functional : forall k, k in succ n -> exists! x, (k, x) in F;
  is_rec_z : (nothing, Z) in F;
  is_rec_s : forall k x, k in n -> (k, x) in F -> (succ k, S x) in F;
}.

Local Lemma is_recursive_ext n F0 F1 z : n in omega -> z in omega -> is_recursive n F0 -> is_recursive n F1 -> forall w, (z, w) in F0 -> (z, w) in F1.
Proof.
  intros ? ? [] [].
  pattern z.
  apply omega_ind; auto.
  + intros w ?.
    replace w with Z; auto.
    destruct (is_rec_functional0 nothing) as [? [? eq]].
    - destruct (is_rec_pairs0 ({}, w)) as [? [? [? u]]]; auto.
      apply ordpair_ext1 in u. subst. auto.
    - rewrite <- (eq Z); auto.
  + intros y ? h w ?.
    assert (y in n). {
      apply omega_pred; auto.
      destruct (is_rec_pairs0 (succ y, w)) as [? [? [? u]]]; auto.
      apply ordpair_ext1 in u as <-. auto.
    }
    destruct (is_rec_functional0 y) as [pw []]. { unfold succ. unsettle. auto. }
    assert (w = S pw). {
      assert ((succ y, S pw) in F0) as l. { apply (is_rec_s0 y pw); auto. }
      destruct (is_rec_functional0 (succ y)) as [? [? eq]].
      - destruct (is_rec_pairs0 (succ y, w)) as [? [? [? u]]]; auto.
        apply ordpair_ext1 in u as <-. auto.
      - rewrite <- (eq w); auto.
    }
    subst.
    apply (is_rec_s1 y pw); auto.
Qed.

Local Definition recursive_zero := {(nothing, Z),}.

Local Lemma is_recursive_z : is_recursive nothing recursive_zero.
Proof.
  unfold recursive_zero.
  split; try split; unsettle; intuition.
  + firstorder.
  + unfold unique, succ in *.
    unsettle.
    intuition.
    subst.
    exists Z.
    intuition.
    eauto using ordpair_ext2.
Qed.

Local Definition recursive_succ F n w := cup F {(succ n, w),}.

Local Lemma is_recursive_s n F w : n in omega -> is_recursive n F -> (n, w) in F -> is_recursive (succ n) (recursive_succ F n (S w)).
Proof.
  intros ? [] ?.
  split.
  + unfold recursive_succ, unique, succ in *.
    unsettle.
    intuition.
    - destruct (is_rec_pairs0 p); auto.
      destruct (is_rec_pairs0 p) as [k [y]]; auto.
      exists k. exists y. intuition.
    - exists (succ n). exists (S w). intuition.
  + unfold recursive_succ, unique, succ in *.
    unsettle.
    intros k [ | ->].
    - destruct (is_rec_functional0 k) as [x]; auto.
      exists x.
      intuition.
      * apply ordpair_ext1 in H1 as ->.
        destruct (omega_not_in_eachother n (succ n)); eauto with omega.
      * apply ordpair_ext1 in H1 as ->.
        destruct (omega_not_in_self (succ n)); eauto with omega.
        unfold succ. unsettle. auto.
    - exists (S w).
      intuition.
      * destruct (is_rec_pairs0 (succ n, x')); intuition.
        destruct H2.
        intuition.
        ** apply ordpair_ext1 in H4 as <-.
           destruct (omega_not_in_eachother n (succ n)); eauto with omega.
        ** apply ordpair_ext1 in H4 as <-.
           destruct (omega_not_in_self (succ n)); eauto with omega.
           unfold succ. unsettle. auto.
      * eapply ordpair_ext2. eauto.
  + unfold recursive_succ. unsettle. intuition.
  + unfold recursive_succ, succ in *.
    unsettle.
    intuition.
    * apply ordpair_ext1 in H1 as ->.
      destruct (omega_not_in_eachother n (succ n)); eauto with omega.
    * subst.
      replace x with w; auto.
      destruct (is_rec_functional0 n) as [? [? eq]]; auto.
      rewrite <- (eq x); eauto.
      erewrite eq; auto.
    * subst.
      apply ordpair_ext1 in H1.
      destruct (omega_not_in_self (succ n)); eauto with omega.
      unfold succ. unsettle. auto.
Qed.

Local Lemma is_recursive_ext_s n F0 F1 z : n in omega -> z in omega -> is_recursive n F0 -> is_recursive (succ n) F1 -> forall w, (z, w) in F0 -> (z, w) in F1.
Proof.
  intros ? ? h ? ? ?.
  destruct (is_rec_functional _ _ h n) as [w' []]. { unfold succ. unsettle. auto. }
  assert ((z, w) in recursive_succ F0 n (S w')). { unfold recursive_succ. unsettle. auto. }
  apply (is_recursive_ext (succ n) (recursive_succ F0 n (S w'))); eauto with omega.
  apply is_recursive_s; auto.
Qed.

Local Definition recurse' n w := exists F, is_recursive n F /\ (n, w) in F.

Local Lemma recurse'_definite : forall n, n in omega -> definite (recurse' n).
Proof.
  apply omega_ind.
  + exists Z.
    split.
    - exists recursive_zero.
      unfold recursive_zero.
      unsettle.
      eauto using is_recursive_z.
    - intros w [F []].
      edestruct (is_rec_functional nothing F) as [? [? eq]]; auto.
      * unfold succ. unsettle. eauto.
      * rewrite <- (eq Z); auto.
        apply (is_rec_z nothing).
        auto.
  + intros n ? [w [[F []]]].
    exists (S w).
    assert (is_recursive (succ n) (recursive_succ F n (S w))). {
      apply (is_recursive_s _ _ w); auto.
    }
    split.
    - exists (recursive_succ F n (S w)).
      unfold recursive_succ.
      unsettle. intuition.
    - intros w' [F' []].
      assert ((succ n, S w) in F'). {
        apply (is_recursive_ext (succ n) (recursive_succ F n (S w)) F'); eauto with omega.
        unfold recursive_succ.
        unsettle. auto.
      }
      edestruct (is_rec_functional (succ n) F') as [? [? eq]]; eauto with omega.
      rewrite <- (eq (S w)); auto.
Qed.

Local Lemma recurse'_z : recurse' nothing Z.
Proof.
  + intros.
    exists recursive_zero.
    split.
    - apply is_recursive_z.
    - unfold recursive_zero. unsettle. auto.
Qed.

Local Lemma recurse'_s n w : n in omega -> recurse' n w -> recurse' (succ n) (S w).
Proof.
  intros i.
  + intros h.
    destruct (recurse'_definite n) as [? [[F []] eq]]; auto.
    exists (recursive_succ F n (S w)).
    split.
    - apply (is_recursive_s _ _ w); auto.
      rewrite <- (eq w); auto.
    - unfold recursive_succ. unsettle. auto.
Qed.

Local Definition recurse'' n w := if classic (n in omega) then recurse' n w else w = nothing.

Local Lemma recurse''_definite n : definite (recurse'' n).
Proof.
  unfold recurse''.
  set (i := classic (n in omega)).
  destruct i.
  2:try (exists nothing; split; auto).
  apply recurse'_definite.
  auto.
Qed.

Definition recurse n := @the _ (recurse'' n) ltac:(apply recurse''_definite).

Theorem recurse_z : recurse nothing = Z.
Proof.
  unfold recurse.
  unfold the.
  set (d := definite_description _ _).
  destruct d as [x].
  replace Z with x; auto.
  destruct (recurse''_definite nothing) as [? [? eq]].
  rewrite <- (eq x); auto.
  rewrite (eq Z); auto.
  unfold recurse''.
  set (e := classic (nothing in omega)).
  destruct e as [ | ne].
  2:destruct ne; apply omega_nothing.
  apply recurse'_z.
Qed.

Theorem recurse_s n : n in omega -> recurse (succ n) = S (recurse n).
Proof.
  unfold recurse.
  unfold the.
  set (d := definite_description _ _).
  destruct d as [w'].
  set (d := definite_description _ _).
  destruct d as [w u].
  intros.
  cbn.
  assert (recurse'' (succ n) (S w)). {
    unfold recurse''.
    set (e' := classic (succ n in omega)).
    destruct e' as [ e' | ne'].
    2:destruct ne'; apply omega_succ; auto.
    apply recurse'_s; auto.
    unfold recurse'' in u.
    set (e := classic (n in omega)) in u.
    destruct e as [ | ne].
    2:destruct ne; auto.
    auto.
  }
  destruct (recurse''_definite (succ n)) as [? [? eq]].
  rewrite <- (eq (S w)); auto.
  rewrite (eq w'); auto.
Qed.

End recursion.

Hint Rewrite recurse_z : recurse.
Hint Rewrite recurse_s : recurse.

Theorem recurse_sz Z S n : n in omega -> recurse Z S (succ n) = recurse (S Z) S n.
Proof.
  intros ?.
  pattern n.
  apply omega_ind; auto.
  + autorewrite with recurse;
    eauto with omega.
  + intros ? ? IH.
    autorewrite with recurse in *;
    eauto with omega.
    rewrite IH.
    auto.
Qed.