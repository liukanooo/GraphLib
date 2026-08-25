Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From ListLib Require Import General.Length General.NoDup.
From MaxMinLib Require Import MaxMin Interface.

Import SetsNotation.

Local Open Scope sets.
Local Open Scope Z.

Section list_enumeration.

Variable A: Type.

Fixpoint lists_of_length (n: nat) (xs: list A): list (list A) :=
  match n with
  | O => nil :: nil
  | S n' =>
      flat_map (fun x => map (cons x) (lists_of_length n' xs)) xs
  end.

Fixpoint lists_upto (n: nat) (xs: list A): list (list A) :=
  match n with
  | O => lists_of_length O xs
  | S n' => lists_upto n' xs ++ lists_of_length (S n') xs
  end.

Lemma lists_of_length_complete:
  forall n xs ys,
    length ys = n ->
    Forall (fun x => In x xs) ys ->
    In ys (lists_of_length n xs).
Proof.
  induction n as [|n IH]; intros xs ys Hlen Hfor.
  - destruct ys; simpl in *; [left; reflexivity | lia].
  - destruct ys as [|y ys]; simpl in Hlen; [lia |].
    inversion Hfor as [|? ? Hy Hys]; subst.
    simpl.
    apply in_flat_map.
    exists y; split; auto.
    apply in_map.
    apply IH; auto.
Qed.

Lemma lists_upto_complete:
  forall n xs ys,
    (length ys <= n)%nat ->
    Forall (fun x => In x xs) ys ->
    In ys (lists_upto n xs).
Proof.
  induction n as [|n IH]; intros xs ys Hlen Hfor.
  - simpl.
    destruct ys; simpl in *; [left; reflexivity | lia].
  - simpl.
    apply in_app_iff.
    destruct (Nat.eq_dec (length ys) (S n)) as [Heq | Hneq].
    + right.
      change (In ys (lists_of_length (S n) xs)).
      apply lists_of_length_complete; auto.
    + left.
      apply IH; auto.
      lia.
Qed.

Lemma Forall_incl:
  forall (P: A -> Prop) xs,
    (forall x, In x xs -> P x) ->
    Forall P xs.
Proof.
  intros P xs Hincl.
  induction xs as [|x xs IH].
  - constructor.
  - constructor.
    + apply Hincl. simpl; auto.
    + apply IH. intros y Hy. apply Hincl. simpl; auto.
Qed.

End list_enumeration.

Section bellmanford_graph_facts.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {step_valid: StepValid G V E}
        {step_unique: StepUniqueDirected G V E}
        {elist_bijective: EListBijective G V E}
        (g: G)
        {g_valid: gvalid g}.

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Context {no_negative_closed_path: nonnegative_closed_path g}.

Lemma valid_epath_edge_bound_snoc_or_short:
  forall u k v p,
    (0 <= k)%Z ->
    valid_epath g u p v ->
    (Zlength p <= k + 1)%Z ->
    (Zlength p <= k)%Z \/
    exists w e p0,
      evalid g e /\
      step_aux g e w v /\
      valid_epath g u p0 w /\
      p = p0 ++ e :: nil /\
      (Zlength p0 <= k)%Z.
Proof.
  intros u k v p Hk Hpath Hlen.
  destruct (Z_le_gt_dec (Zlength p) k) as [Hshort | Hlong].
  - left; exact Hshort.
  - right.
    apply valid_epath_inv_n1 in Hpath as [[Heq Hnil] | [p0 [w [e [Hp [Hpvalid Hstep]]]]]].
    + subst p. rewrite Zlength_nil in Hlong. lia.
    + subst p.
      exists w, e, p0.
      repeat split; auto.
      * eapply step_evalid; eauto.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
        lia.
Qed.

Lemma valid_epath_edges_in_bijective_list:
  forall u p v,
    valid_epath g u p v ->
    incl p (bijective_listE g).
Proof.
  intros u p v Hpath x Hx.
  revert u v Hpath x Hx.
  induction p as [|e p IH]; intros u v Hpath x Hx.
  - contradiction.
  - apply valid_epath_cons_inv in Hpath as [w [Hstep Hrest]].
    simpl in Hx.
    destruct Hx as [Hx | Hx].
    + subst x.
      apply bijective_edges; auto.
      eapply step_evalid; eauto.
    + eapply IH; eauto.
Qed.

Lemma valid_epath_edge_num_bound:
  forall u p v,
    valid_epath g u p v ->
    NoDup p ->
    (Zlength p <= edge_num g)%Z.
Proof.
  intros u p v Hpath Hnodup.
  unfold edge_num.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_le.
  eapply NoDup_incl_length; eauto.
  eapply valid_epath_edges_in_bijective_list; eauto.
Qed.

Lemma valid_epath_shorten_repeated_edge_nonnegative:
  forall u v l1 e l2 l3,
    valid_epath g u (l1 ++ e :: l2 ++ e :: l3) v ->
    exists q,
      valid_epath g u q v /\
      (length q < length (l1 ++ e :: l2 ++ e :: l3))%nat /\
      Z_op_le (epath_weight g q)
              (epath_weight g (l1 ++ e :: l2 ++ e :: l3)).
Proof.
  intros u v l1 e l2 l3 Hpath.
  apply valid_epath_app_inv in Hpath as [u1 [Hl1 Hrest1]].
  apply valid_epath_cons_inv in Hrest1 as [v1 [He1 Hrest2]].
  apply valid_epath_app_inv in Hrest2 as [u2 [Hl2 Hrest3]].
  apply valid_epath_cons_inv in Hrest3 as [v2 [He2 Hl3]].
  pose proof (step_aux_unique g e u1 v1 u2 v2 g_valid He1 He2) as [Hu Hv].
  subst u2 v2.
  exists (l1 ++ e :: l3).
  split; [|split].
  - eapply valid_epath_app; eauto.
    eapply valid_epath_cons; eauto.
  - repeat rewrite app_length.
    simpl.
    rewrite app_length.
    simpl.
    lia.
  - assert (Hcycle: valid_epath g v1 (l2 ++ e :: nil) v1).
    { eapply valid_epath_snoc; eauto. }
    specialize (no_negative_closed_path (l2 ++ e :: nil) v1 Hcycle) as Hnonneg.
    replace (l1 ++ e :: l3) with ((l1 ++ e :: nil) ++ l3)
      by (rewrite <- app_assoc; reflexivity).
    replace (l1 ++ e :: l2 ++ e :: l3)
      with ((l1 ++ e :: nil) ++ ((l2 ++ e :: nil) ++ l3))
      by (rewrite <- !app_assoc; reflexivity).
    rewrite !epath_weight_app_assoc.
    apply Z_op_plus_mono; [apply Z_op_le_refl|].
    assert (Hnonneg':
      Z_op_le (Some 0)
              (Z_op_plus (epath_weight g l2) (epath_weight g (e :: nil)))).
    { rewrite <- epath_weight_app_assoc. exact Hnonneg. }
    replace (epath_weight g l3)
      with (Z_op_plus (Some 0) (epath_weight g l3)) at 1
      by (rewrite Z_op_plus_O_l; reflexivity).
    apply Z_op_plus_mono; [exact Hnonneg'|apply Z_op_le_refl].
Qed.

Lemma valid_epath_nonnegative_edge_simple:
  forall u p v,
    valid_epath g u p v ->
    exists q,
      valid_epath g u q v /\
      NoDup q /\
      Z_op_le (epath_weight g q) (epath_weight g p).
Proof.
  intros u p v Hpath.
  remember (length p) as n eqn:Hn.
  revert u p v Hpath Hn.
  induction n using lt_wf_ind; intros u p v Hpath Hn.
  destruct (classic (NoDup p)) as [Hnodup | Hdup].
  - exists p.
    repeat split; auto.
    apply Z_op_le_refl.
  - apply Nodup_exists_repetition in Hdup.
    destruct Hdup as [e [l1 [l2 [l3 Hp]]]].
    subst p.
    destruct (valid_epath_shorten_repeated_edge_nonnegative
                u v l1 e l2 l3 Hpath)
      as [q [Hqpath [Hqlen Hqle]]].
    destruct (H (length q) ltac:(lia) u q v Hqpath eq_refl)
      as [r [Hrpath [Hrnodup Hrle]]].
    exists r.
    repeat split; auto.
    eapply Z_op_le_trans; eauto.
Qed.

Lemma bounded_epath_candidates_complete:
  forall u p v,
    valid_epath g u p v ->
    (Zlength p <= edge_num g)%Z ->
    In p (lists_upto E (length (bijective_listE g)) (bijective_listE g)).
Proof.
  intros u p v Hpath Hlen.
  apply lists_upto_complete.
  - unfold edge_num in Hlen.
    rewrite !Zlength_correct in Hlen.
    lia.
  - apply Forall_incl.
    eapply valid_epath_edges_in_bijective_list; eauto.
Qed.

Theorem reachable_min_object_epath_edge_num_bound:
  forall u v,
    reachable g u v ->
    exists p,
      min_object_weight_epath g u v p /\
      (Zlength p <= edge_num g)%Z.
Proof.
  intros u v Hreach.
  destruct (reachable_valid_epath g u v Hreach) as [p0 Hp0].
  destruct (valid_epath_nonnegative_edge_simple u p0 v Hp0)
    as [p1 [Hp1 [Hp1nodup Hp1le]]].
  pose proof (valid_epath_edge_num_bound u p1 v Hp1 Hp1nodup) as Hp1bound.
  set (candidates := lists_upto E (length (bijective_listE g)) (bijective_listE g)).
  assert (Hp1in: In p1 candidates).
  {
    unfold candidates.
    eapply bounded_epath_candidates_complete; eauto.
  }
  set (bounded_path := fun p => valid_epath g u p v /\ (Zlength p <= edge_num g)%Z).
  destruct (Z_op_finite_min
              (epath_weight g)
              bounded_path
              candidates
              p1)
    as [m [Hmbounded Hmmin]].
  - exact Hp1in.
  - split; auto.
  - intros y [Hyvalid Hybound].
    unfold candidates.
    eapply bounded_epath_candidates_complete; eauto.
  - exists m.
    split.
    + unfold min_object_weight_epath, min_object_of_subset.
      destruct Hmbounded as [Hmvalid Hmbound].
      split; auto.
      intros q Hqvalid.
      destruct (valid_epath_nonnegative_edge_simple u q v Hqvalid)
        as [q' [Hq'valid [Hq'nodup Hq'le]]].
      pose proof (valid_epath_edge_num_bound u q' v Hq'valid Hq'nodup)
        as Hq'bound.
      assert (Hq'bounded: bounded_path q') by (split; auto).
      eapply Z_op_le_trans.
      * apply Hmmin. exact Hq'bounded.
      * exact Hq'le.
    + destruct Hmbounded as [_ Hmbound].
      exact Hmbound.
Qed.

End bellmanford_graph_facts.
