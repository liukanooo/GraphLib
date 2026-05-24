Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Export Coq.Classes.EquivDec.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted subgraph path path_basic vpath epath Zweight tree.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import General.NoDup General.Forall.

Import ListNotations.

Local Open Scope sets.
Local Open Scope Z.

Section prim.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}
        {addEdge2Exist: addEdge2Exist G V E}. (*要求原图的加边存在性*)
Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.
Context (g: G)
        {g_valid: gvalid g}
        {g_tree: tree g}.

Context (r: G)
        {r_valid: gvalid r}
        {ew: EdgeWeight G E}.

Lemma addEdge2_vvalid_iff:
  forall i h u v e x,
    addEdge2 i h u v e ->
    vvalid h x <-> vvalid i x.
Proof.
  intros i h u v e x Hadd.
  destruct Hadd as [[Hu [Hv He]] Hvvalid _ _].
  rewrite Hvvalid.
  split; subst; auto. 
  intros [Hx | Hx]; subst; auto. 
Qed.

Lemma addEdge2_evalid_iff:
  forall i h u v e a,
    addEdge2 i h u v e ->
    evalid h a <-> evalid i a \/ a = e.
Proof.
  intros i h u v e a Hadd.
  destruct Hadd as [_ _ Hevalid _].
  apply Hevalid.
Qed.

Lemma addEdge2_old_step:
  forall i h u v e x y a,
    addEdge2 i h u v e ->
    step_aux i a x y ->
    step_aux h a x y.
Proof.
  intros i h u v e x y a Hadd Hstep.
  destruct Hadd as [_ _ _ Hstep_aux].
  apply Hstep_aux; left; auto.
Qed.

Lemma addEdge2_new_step_uv:
  forall i h u v e,
    addEdge2 i h u v e ->
    step_aux h e u v.
Proof.
  intros i h u v e Hadd.
  destruct Hadd as [_ _ _ Hstep_aux].
  apply Hstep_aux; right; split; [reflexivity | left; split; reflexivity].
Qed.

Lemma addEdge2_new_step_vu:
  forall i h u v e,
    addEdge2 i h u v e ->
    step_aux h e v u.
Proof.
  intros i h u v e Hadd.
  destruct Hadd as [_ _ _ Hstep_aux].
  apply Hstep_aux; right; split; [reflexivity | right; split; reflexivity].
Qed.

Lemma addEdge2_keep_step:
  forall i h u v e x y a,
    addEdge2 i h u v e ->
    step_aux h a x y ->
    a <> e ->
    step_aux i a x y.
Proof.
  intros i h u v e x y a Hadd Hstep Hneq.
  destruct Hadd as [_ _ _ Hstep_aux].
  apply Hstep_aux in Hstep as [Hold | [Heq _]]; auto.
  contradiction.
Qed.

Lemma addEdge2_vlist_permutation:
  forall i h u v e,
    gvalid i ->
    gvalid h ->
    addEdge2 i h u v e ->
    Permutation (bijective_listV h) (bijective_listV i).
Proof.
  intros i h u v e Hvalid_i Hvalid_h Hadd. 
  apply NoDup_Permutation.
  - apply bijective_listV_NoDup; auto.
  - apply bijective_listV_NoDup; auto.
  - intros x.
    rewrite !bijective_vertices; auto.
    apply addEdge2_vvalid_iff with (u := u) (v := v) (e := e); auto.
Qed.

Lemma addEdge2_elist_permutation:
  forall i h u v e,
    gvalid i ->
    gvalid h ->
    addEdge2 i h u v e ->
    Permutation (bijective_listE h) (e :: bijective_listE i).
Proof.
  intros i h u v e Hvalid_i Hvalid_h Hadd.
  destruct Hadd as [[Hu [Hv He]] Hvvalid Hevalid Hstep_aux].
  apply NoDup_Permutation.
  - apply bijective_listE_NoDup; auto.
  - constructor.
    + intro Hin.
      apply He.
      apply bijective_edges; auto.
    + apply bijective_listE_NoDup; auto.
  - intros a; split; intros Hin.
    + apply bijective_edges in Hin; auto.
      apply Hevalid in Hin as [Hin | Hin].
      * right; apply bijective_edges; auto.
      * subst; left; auto.
    + apply bijective_edges; auto.
      simpl in Hin.
      apply Hevalid.
      destruct Hin as [Hin | Hin]; [right | left]; auto.
      apply bijective_edges; auto.
Qed.

Lemma addEdge2_valid_epath: 
  forall i h u v e p, 
    addEdge2 i h u v e ->
    forall x y, 
      valid_epath i x p y ->
      valid_epath h x p y.
Proof.
  intros i h u v e p Hadd2. 
  induction p as [|a p IHp]; intros.
  - apply valid_epath_nil_inv in H; subst.
    apply valid_epath_empty.
  - apply valid_epath_cons_inv in H as [z [Hstep Hrest]].
    eapply valid_epath_cons with (v:=z); eauto.
    destruct Hadd2 as [[Hu [Hv He]] _ _ Hstep_aux]. 
    apply Hstep_aux; left; auto. 
Qed.

Lemma tree_addEdge_have_circuit: 
  forall i h u v e, 
    gvalid i ->
    tree i ->
    addEdge2 i h u v e -> 
    exists p, is_simple_epath h u p u /\ In e p /\ p <> nil.
Proof. 
  intros i h u v e Hvalid Htree Hadd. 
  pose proof Hadd as [[Hu [Hv He]] Hvvalid Hevalid Hstep_aux]. 
  pose proof tree_connected i Htree u v Hu Hv.
  apply reachable_valid_epath in H as [p Hpath]. 
  eapply valid_epath_simple in Hpath.
  2:{ intros; eapply step_aux_unique_undirected; try apply Hvalid; eauto. }
  destruct Hpath as [q [Hqsimple Hqnodup]]. 
  exists (q ++ [e]); split; [|split];
  [split | apply in_app_iff; right; simpl; auto | symmetry; apply app_cons_not_nil].
  * eapply valid_epath_snoc with (v:=v); eauto.
    + eapply addEdge2_valid_epath; eauto.
    + apply Hstep_aux; right; split; auto. 
  * apply Nodup_app_comm. 
    simpl; constructor; auto. 
    assert (forall a, In a q -> evalid i a). {
      intros a Hin. 
      apply in_split in Hin as [l1 [l2 Hp]]; subst. 
      apply valid_epath_app_inv in Hqsimple as [b [Hl1 Hrest]].
      apply valid_epath_cons_inv in Hrest as [c [Hstep Hl2]].
      eapply step_evalid; eauto.
    }
    unfold not; intros; apply He; auto. 
Qed.

Lemma circuit_have_pair_cross_edge: 
  forall i h u v e p, 
    gvalid h ->
    vvalid i u -> ~ vvalid i v -> step_aux h e u v -> 
    In e p -> 
    is_simple_epath h u p u ->
    exists x y a, vvalid i x /\ ~ vvalid i y /\ step_aux h a x y /\ In a p /\ a <> e.
Proof.
  intros i h u v e p Hvalid_h Hu Hv Hstep_e Hin [Hpath Hnodup].
  apply in_split in Hin as [p1 [p2 Hp]].
  subst p.
  apply valid_epath_app_inv in Hpath as [z [Hpre Hrest]].
  apply valid_epath_cons_inv in Hrest as [w [Hstep_in Hpost]]. 
  eapply step_aux_unique_undirected in Hstep_e as [[Hzu Hwv] | [Hwu Hzv]]; eauto; subst.
  - pose proof (valid_epath_rev h v p2 u Hpost) as Hrev. 
    eapply valid_epath_cross with (P := vvalid i) in Hrev
    as [x [y [a [Hx [Hy [Hstep Hina]]]]]]; eauto.
    exists x, y, a; repeat split; auto.
    + rewrite in_app_iff; right; simpl; right; apply in_rev; auto. 
    + destruct (Nodup_split_constructors p1 p2 e Hnodup) as [_ Hnotin].
      intro Heq; subst; apply Hnotin; apply in_rev; auto. 
  - eapply valid_epath_cross with (P := vvalid i) in Hpre
    as [x [y [a [Hx [Hy [Hstep Hina]]]]]]; eauto.
    exists x, y, a; repeat split; auto.
    + rewrite in_app_iff; left; auto.
    + destruct (Nodup_split_constructors p1 p2 e Hnodup) as [Hnotin _].
      intro Heq; subst; contradiction.
Qed.

Lemma addEdge2_valid_epath_new_to_old:
  forall i h u v e p x y,
    addEdge2 i h u v e ->
    valid_epath h x p y ->
    ~ In e p ->
    valid_epath i x p y.
Proof.
  intros i h u v e p.
  induction p as [|a p IHp]; intros x y Hadd Hpath Hnotin.
  - apply valid_epath_nil_inv in Hpath; subst.
    apply valid_epath_empty.
  - simpl in Hnotin.
    apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    eapply valid_epath_cons with (v:=z).
    + eapply addEdge2_keep_step; eauto.
    + eapply IHp; eauto.
Qed.

Lemma addEdge2_edge_not_in_old_path:
  forall i h u v e p x y,
    addEdge2 i h u v e ->
    valid_epath i x p y ->
    ~ In e p.
Proof.
  intros i h u v e p.
  induction p as [|a p IHp]; intros x y Hadd Hpath Hin; simpl in Hin; [contradiction|].
  apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
  pose proof Hadd as [[_ [_ Hnewe]] _ _ _].
  destruct Hin as [Hin | Hin].
  - subst a. apply Hnewe. eapply step_evalid; eauto.
  - eapply IHp; eauto.
Qed.

Lemma addEdge2_cycle_without_new_edge_simple:
  forall i h u v e z p,
    gvalid h ->
    addEdge2 i h u v e ->
    is_simple_epath h z p z ->
    In e p ->
    exists q,
      is_simple_epath i u q v /\
      (forall a, In a q <-> In a p /\ a <> e).
Proof.
  intros i h u v e z p Hvalid_h Hadd [Hpath Hnodup] Hin.
  apply in_split in Hin as [p1 [p2 Hp]].
  subst p.
  apply valid_epath_app_inv in Hpath as [s [Hpre Hrest]].
  apply valid_epath_cons_inv in Hrest as [t [Hstep_e Hpost]].
  pose proof (addEdge2_new_step_uv _ _ _ _ _ Hadd) as Huv.
  eapply step_aux_unique_undirected in Hstep_e as [[Hsu Htv] | [Hsv Htu]]; eauto; subst.
  - exists (rev (p2 ++ p1)); split; [split|].
    + apply valid_epath_rev.
      eapply addEdge2_valid_epath_new_to_old; eauto; 
      [eapply valid_epath_app; eauto|].
      intros Hin; rewrite in_app_iff in Hin.
      destruct (Nodup_split_constructors _ _ _ Hnodup); tauto.
    + apply NoDup_rev.
      apply Nodup_app_comm. 
      eapply NoDup_remove_1; eauto.
    + intros a.
      rewrite <- in_rev, in_app_iff.
      split; [intros [|]; split|intros].
      * rewrite in_app_iff; right; simpl; right; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff; left; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff in H.
        destruct H as [[|[|]]]; subst; try tauto.
  - exists (p2 ++ p1); split; [split|].
    + eapply addEdge2_valid_epath_new_to_old; eauto; 
      [eapply valid_epath_app; eauto|].
      intros Hin; rewrite in_app_iff in Hin.
      destruct (Nodup_split_constructors _ _ _ Hnodup); tauto.
    + apply Nodup_app_comm.
      eapply NoDup_remove_1; eauto.
    + intros a.
      rewrite in_app_iff; split; [intros [|]; split|intros].
      * rewrite in_app_iff; right; simpl; right; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff; left; auto.
      * intro Heq; subst.
        destruct (Nodup_split_constructors _ _ _ Hnodup); contradiction.
      * rewrite in_app_iff in H.
        destruct H as [[|[|]]]; subst; try tauto.
Qed.

Lemma addEdge2_replace_edge_connected:
  forall y1 h i u v e x y a p,
    gvalid y1 ->
    gvalid h ->
    tree y1 ->
    addEdge2 y1 h u v e ->
    addEdge2 i h x y a ->
    is_simple_epath h u p u ->
    In a p ->
    connected i.
Proof.
  intros y1 h i u v e x y a p Hvalid_y1 Hvalid_h Htree_y1 Hadd2 Hi Hp Hina s t Hs Ht.
  assert (Hs_y1 : vvalid y1 s) by (rewrite <- addEdge2_vvalid_iff; [rewrite addEdge2_vvalid_iff|]; eauto).
  assert (Ht_y1 : vvalid y1 t) by (rewrite <- addEdge2_vvalid_iff; [rewrite addEdge2_vvalid_iff|]; eauto).

  destruct (reachable_valid_epath _ _ _ (tree_connected _ Htree_y1 _ _ Hs_y1 Ht_y1)) as [q Hqpath].
  eapply valid_epath_simple in Hqpath as [q' [Hq'path Hq'nodup]].
  2:{ intros; eapply step_aux_unique_undirected; try apply Hvalid_y1; eauto. }

  destruct (classic (In a q')) as [Hinaq | Hnotinaq].
  - apply in_split in Hinaq as [q1 [q2]]; subst.
    apply valid_epath_app_inv in Hq'path as [z [Hpre Hrest]].
    apply valid_epath_cons_inv in Hrest as [w [Hstep_a Hpost]].
    pose proof (addEdge2_old_step _ _ _ _ _ _ _ _ Hadd2 Hstep_a) as Hstep_a_h.
    pose proof (addEdge2_new_step_uv _ _ _ _ _ Hi) as Hstep_a_new.
    eapply step_aux_unique_undirected in Hstep_a_h as [[]|[]]; eauto; subst z w.
    + destruct (addEdge2_cycle_without_new_edge_simple i h x y a u p Hvalid_h Hi Hp Hina)
        as [alt [[Halt_path _] _]].
      eapply valid_epath_reachable.
      eapply valid_epath_app; [|eapply valid_epath_app].
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (i:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [Hnotin1 _]; contradiction.
      * exact Halt_path.
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (i:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [_ Hnotin2]; contradiction.
    + destruct (addEdge2_cycle_without_new_edge_simple i h x y a u p Hvalid_h Hi Hp Hina)
        as [alt [[Halt_path _] _]].
      eapply valid_epath_reachable.
      eapply valid_epath_app; [|eapply valid_epath_app].
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (i:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [Hnotin1 _]; contradiction.
      * apply valid_epath_rev. exact Halt_path.
      * eapply addEdge2_valid_epath_new_to_old; [exact Hi|eapply addEdge2_valid_epath with (i:=y1); eauto|].
        intros ?; destruct (Nodup_split_constructors q1 q2 a Hq'nodup) as [_ Hnotin2]; contradiction.
  - eapply valid_epath_reachable.
    eapply addEdge2_valid_epath_new_to_old; [exact Hi| |exact Hnotinaq].
    eapply addEdge2_valid_epath with (i:= y1); eauto.
Qed.

Lemma addEdge2_delete_circuit_no_circuit:
  forall y1 h i u v e x y a p,
    gvalid y1 ->
    gvalid h ->
    tree y1 ->
    addEdge2 y1 h u v e ->
    addEdge2 i h x y a ->
    is_simple_epath h u p u ->
    In e p ->
    In a p ->
    a <> e ->
    ~ exists z q, q <> nil /\ is_simple_epath i z q z.
Proof.
  intros y1 h i u v e x y a p Hvalid_y1 Hvalid_h Htree_y1 Hadd2 Hi Hp Hein Hina Hane [z [q [Hqne Hq]]].
  assert (Hq_h : is_simple_epath h z q z) by (destruct Hq as [Hqpath Hqnodup]; split; auto; eapply addEdge2_valid_epath; eauto).
  destruct (classic (In e q)) as [Heinq | Hnotinq].
  - destruct (addEdge2_cycle_without_new_edge_simple y1 h u v e u p Hvalid_h Hadd2 Hp Hein) as [p_old [Hp_old Hp_mem]].
    destruct (addEdge2_cycle_without_new_edge_simple y1 h u v e z q Hvalid_h Hadd2 Hq_h Heinq) as [q_old [Hq_old Hq_mem]].
    assert (Hpq : p_old = q_old) by (eapply tree_one_simple_epath with (g:= y1); eauto).
    assert (Hain_pold : In a p_old) by (apply Hp_mem; split; auto).
    assert (Hnotin_q : ~ In a q) by (eapply addEdge2_edge_not_in_old_path; eauto; apply Hq).
    assert (Hnotin_qold : ~ In a q_old) by (intro Hain; apply Hq_mem in Hain as [Hainq _]; contradiction).
    subst q_old. contradiction.
  - eapply tree_no_curcuit; eauto.
    exists z, q; split; auto.
    destruct Hq as [Hqpath Hqnodup].
    split; auto.
    eapply addEdge2_valid_epath_new_to_old ; eauto. 
    apply Hq_h.
Qed.

Lemma addEdge2_delete_circuit_tree:
  forall y1 h i u v e x y a p,
    gvalid y1 ->
    gvalid h ->
    tree y1 ->
    addEdge2 y1 h u v e ->
    addEdge2 i h x y a ->
    is_simple_epath h u p u ->
    In e p ->
    In a p ->
    a <> e ->
    tree i.
Proof.
  intros.
  apply tree_decide.
  - eapply addEdge2_replace_edge_connected with (y1:=y1); eauto.
  - eapply addEdge2_delete_circuit_no_circuit with (y1:=y1); eauto.
Qed.


Theorem prim_step: 
  forall g1 g2 u v e, 
    gvalid g1 /\ tree g1 /\ (exists y1, is_mst r y1 /\ subgraph2 g1 y1) -> 
    step_aux r e u v ->
    addEdge g1 g2 u v e -> 
    min_object_of_subset Z_op_le (fun e => exists u v, vvalid g1 u /\ ~ vvalid g1 v /\ step_aux r e u v) (weight r) e ->
    tree g2 /\ (exists y2, is_mst r y2 /\ subgraph2 g2 y2). 
Proof. 
  intros g1 g2 u v e [Hgvalid1 [Htree [y1 [Hmst Hsubgraph]]]] Hrstep Hadd Hmin. 
  split; [eapply addEdge_tree; eauto|].
  destruct (classic (evalid y1 e)).
  - exists y1; split; auto. 
    split. 
    { 
      intros x Hx. 
      apply Hadd in Hx as []; subst. 
      + apply Hsubgraph; auto. 
      + apply Hmst. 
        eapply step_vvalid2; eauto.  
    } 
    {
      intros x y a Hstep.
      destruct Hadd as [[Hu [Hv He]] Hvvalid Hevalid Hstep_aux].
      apply Hstep_aux in Hstep as [Hold | [Heq [[Hx Hy] | [Hx Hy]]]]; subst.
      + apply Hsubgraph; auto.
      + eapply mst_edge_step with (r:=r); eauto.
      + apply step_sym. eapply mst_edge_step with (r:=r); eauto.
    }
  - (* 当新增加的边e不在原来的被包含在的最小生成树中时 *)
    (* 将这条边e增加到最小生成树y1中去，y1 + e = h *)
    assert (exists h, gvalid h /\ addEdge2 y1 h u v e) as [h [Hvalid Hadd2]].
    {
      apply addEdge2_valid; auto; [apply Hmst| |]. 
      * destruct Hmst as [[_ [_ Hsubeq]]]. 
        eapply subgraph_vertex; eauto. 
        eapply step_vvalid1; eauto.
      * destruct Hmst as [[_ [_ Hsubeq]]]. 
        eapply subgraph_vertex; eauto.
        eapply step_vvalid2; eauto.
    } 
    (* 则 h 中有一个简单回路 p ，包含跨边e *)
    assert (exists p, is_simple_epath h u p u /\ In e p /\ p <> nil) as [p [Hp [Heinp Hpne]]]. 
    {
      eapply tree_addEdge_have_circuit; try apply Hadd2; apply Hmst.
    } 
    (* p 中包含另外一条跨边 a *)
    assert (exists x y a, vvalid g1 x /\ ~ vvalid g1 y /\ step_aux h a x y /\ In a p /\ a <> e) as [x [y [a [Hx [Hy [Hstep Hin]]]]]].
    {
      eapply circuit_have_pair_cross_edge with (v := v); eauto; 
      try (try destruct Hadd; tauto). 
      destruct Hadd2 as [_ _ _ Hstep_aux]. 
      apply Hstep_aux; right; auto.
    }
    (* 将 a 从 h 中删除，y1 + e - a = i *)
    assert (exists i, gvalid i /\ addEdge2 i h x y a) as [i [Hvalidi Hi]]. {
      apply addEdge2_valid_inv; auto. 
      * eapply step_vvalid1; eauto.
      * eapply step_vvalid2; eauto.
      * eapply step_evalid; eauto.
    }



    
    (* i 是新的满足条件的最小生成树 *)
    exists i; split; [split; [split; [|split]|]|]. 

    (* i gvalid *)
    + apply Hvalidi. 


    (* i 是 树 *)
    + eapply addEdge2_delete_circuit_tree. 
      5: apply Hi.
      4: apply Hadd2.
      4: apply Hp. 
      all: try tauto. 
      all: apply Hmst.

    (* i 是 原图的子图 *)
    + destruct Hmst as [Hy1_legal Hy1_min].
      destruct Hy1_legal as [_ [_ Hsubeq_y1]].
      destruct Hsubeq_y1 as [Hy1_vertex Hy1_step].
      split.
      * intros z.
        rewrite <- Hy1_vertex.
        rewrite <- (addEdge2_vvalid_iff i h x y a z Hi).
        apply addEdge2_vvalid_iff with (u := u) (v := v) (e := e); auto.
      * intros z w b Hstep_i.
        pose proof (addEdge2_old_step _ _ _ _ _ _ _ _ Hi Hstep_i) as Hstep_h.
        destruct Hadd2 as [_ _ _ Hstep_h_iff].
        apply Hstep_h_iff in Hstep_h as [Hstep_y1 | [Hb [[] | []]]]; subst; auto.
        apply step_sym; auto. 

    (* i 的权值小于等于 y1 的权值 *)
    + intros b Hb.
      eapply Z_op_le_trans with (y:= total_weight r y1); 
      [|apply Hmst; auto]. 
      pose proof Hadd2 as Hadd2'. 
      pose proof Hi as Hi'. 

      apply addEdge2_elist_permutation in Hadd2; auto. 
      2:{ apply Hmst. } 

      apply addEdge2_elist_permutation in Hi; auto.

      set (sumE := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight r) l)).
      assert (Hperm_sum : forall l1 l2, Permutation l1 l2 -> sumE l1 = sumE l2).
      {
        intros l1 l2 Hperm.
        induction Hperm; subst sumE; simpl; auto.
        - rewrite IHHperm; auto.
        - rewrite !Z_op_plus_assoc.
          rewrite (Z_op_plus_comm (weight r x0) (weight r y0)).
          reflexivity.
        - rewrite IHHperm1, IHHperm2; auto.
      }
      assert (Hh_y1 : total_weight r h = Z_op_plus (weight r e) (total_weight r y1)).
      {
        unfold total_weight. 
        pose proof (Hperm_sum _ _ Hadd2). 
        unfold sumE in H0. 
        rewrite H0.
        simpl; reflexivity.
      }
      assert (Hh_i : total_weight r h = Z_op_plus (weight r a) (total_weight r i)).
      {
        unfold total_weight.
        pose proof (Hperm_sum _ _ Hi). 
        unfold sumE in H0. 
        rewrite H0.
        simpl; reflexivity.
      }
      destruct Hmst as [[Hy1_valid [_ Hsubeq_y1]] _].
      destruct Hsubeq_y1 as [_ Hy1_step].
      assert (Hstep_y1 : step_aux y1 a x y) by (eapply addEdge2_keep_step; eauto; tauto).
      assert (Hin_a_y1 : In a (bijective_listE y1)).
      { apply bijective_edges; auto. eapply step_evalid; eauto. }
      assert (Hwea : Z_op_le (weight r e) (weight r a)).
      {
        destruct Hmin as [_ Hmin_sound].
        apply Hmin_sound.
        exists x, y.
        repeat split; auto.
      }
      assert (Hnone_in_sum :
        forall l, In a l -> weight r a = None -> sumE l = None).
      {
        intros l.
        induction l as [|c l IH]; intros Hinc Hwa; simpl in *; [contradiction|].
        destruct Hinc as [Hc | Hinc].
        - subst. unfold sumE; simpl. rewrite Hwa. reflexivity.
        - apply IH in Hwa; auto. unfold sumE; simpl. 
          unfold sumE in Hwa; simpl in Hwa. 
          rewrite Hwa. apply Z_op_plus_none_r.
      }
      destruct (weight r a) as [wa|] eqn:Hwa.
      * destruct (weight r e) as [we|] eqn:Hwe; simpl in Hwea; [|contradiction].
        rewrite Hh_y1 in Hh_i.
        destruct (total_weight r i) as [wi|] eqn:Hwi;
        destruct (total_weight r y1) as [wy|] eqn:Hwy;
        simpl in *; try discriminate; auto.
        inversion Hh_i; subst; lia.
      * assert (Hy1_none : total_weight r y1 = None).
        {
          unfold total_weight.
          apply Hnone_in_sum; auto.
        }
        rewrite Hy1_none.
        apply Z_op_le_none_r.

    (* g2 是 i 的子图 *)
    + split.
      {
        intros z Hz. 
        apply Hadd in Hz as []; subst.
        + apply Hsubgraph in H0.
          destruct Hadd2 as [[Hu [Hv He]] Hvvalid _ _] . 
          assert (vvalid h z) by (eapply Hvvalid; auto). 
          apply Hi in H1 as []; auto; subst. 
          apply Hi.
        + destruct Hadd2 as [[Hu [Hv He]] Hvvalid _ _] . 
          assert (vvalid h v) by (eapply Hvvalid; auto). 
          apply Hi in H0 as []; auto; subst. 
          apply Hi.
      }
      {
        intros z w b Hstep_g2.
        destruct Hadd as [[Hu [Hv He]] _ _ Hstep_g2_iff].
        apply Hstep_g2_iff in Hstep_g2 as [Hstep_g1 | [Hb [[Hz Hw] | [Hz Hw]]]].
        * assert (Hstep_y1 : step_aux y1 b z w) by (apply Hsubgraph; auto).
          assert (Hstep_h : step_aux h b z w) by (eapply addEdge2_old_step with (i:=y1); eauto).
          destruct (classic (b = a)) as [Hba | Hba]; 
          [|eapply addEdge2_keep_step; eauto].
          subst; exfalso.
          eapply step_aux_unique_undirected in Hstep as [[] | []]; eauto; subst; 
          apply Hy; [eapply step_vvalid2; eauto | eapply step_vvalid1; eauto].
        * subst b z w.
          assert (Hstep_h : step_aux h e u v) by (eapply addEdge2_new_step_uv; eauto).
          eapply addEdge2_keep_step; eauto; symmetry; tauto.
        * subst b z w.
          assert (Hstep_h : step_aux h e v u) by (eapply addEdge2_new_step_vu; eauto).
          eapply addEdge2_keep_step; eauto.
          intro Heq; subst; apply Hin; auto. 
      }
Qed.


End prim.


Section SPANNING_TREE.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}.
Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}.
Context (g: G)
        {g_valid: gvalid g}
        {g_connected: connected g}.

Context {fg: FiniteGraph G V E}
        {addEdge2Exist: addEdge2Exist G V E}.  

Definition connected_subgraph_eq (h: G) : Prop := 
  gvalid h /\ connected h /\ subgraph_vertex_eq h g. 

Lemma connected_subgraph_eq_refl: 
  connected_subgraph_eq g. 
Proof. 
  repeat split; auto. 
Qed. 

Lemma connected_subgraph_eq_edge_num_lt_bounded: 
  forall h, connected_subgraph_eq h ->  
  (edge_num h <= edge_num g)%Z. 
Proof. 
  intros h [Hvalid [Hconnected Hsub]]. 
  unfold edge_num. 
  pose proof (bijective_listE_NoDup g g_valid) as elist_nodup_g.
  pose proof (bijective_edges g g_valid) as elist_iff_g.
  pose proof (bijective_listE_NoDup h Hvalid) as elist_nodup_h.
  pose proof (bijective_edges h Hvalid) as elist_iff_h.

  assert (forall e, In e (bijective_listE h) -> In e (bijective_listE g)). {
    intros e Heh. 
    rewrite elist_iff_h in Heh. 
    apply no_empty_edge in Heh as [x [y Hstep]]; auto. 
    rewrite elist_iff_g. 
    eapply step_evalid; eauto. 
    apply Hsub; eauto. 
  }
  rewrite ! Zlength_correct.
  apply NoDup_incl_length in H; auto. 
  lia.
Qed. 

Lemma connected_subgraph_eq_edge_num_gt_bounded: 
  forall h, connected_subgraph_eq h ->  
  (edge_num h >= 0)%Z. 
Proof. 
  intros. 
  unfold edge_num. 
  rewrite ! Zlength_correct.
  lia.
Qed. 

Lemma connected_subgraph_eq_exist: 
  exists h, 
    min_object_of_subset Z.le connected_subgraph_eq edge_num h.
Proof.
  set (Q := fun n => exists h, connected_subgraph_eq h /\ edge_num h = n).
  assert (Hexists: exists n, (0 <= n <= edge_num g)%Z /\ Q n).
  { exists (edge_num g)%Z. split.
    + split; unfold edge_num; 
      rewrite ! Zlength_correct; lia. 
    + exists g; repeat split; auto. 
  }
  destruct (min_n_in_range Q (edge_num g)) as [m [Hm [Hlow Hhigh]]]; auto. 
  { unfold edge_num; rewrite ! Zlength_correct; lia. }
  destruct Hm as [h [Hconnected_subgraph_eq Hedge_num]].
  exists h; split; auto. 
  intros; rewrite Hedge_num; apply Hhigh; auto. 
  split; [unfold edge_num; rewrite ! Zlength_correct; lia|
  apply connected_subgraph_eq_edge_num_lt_bounded; auto]. 
  exists b; split; auto. 
Qed.

Lemma spanningtree_exist: 
  exists h, 
    gvalid h /\ tree h /\ subgraph_vertex_eq h g.
Proof.
  destruct connected_subgraph_eq_exist as [h [[Hvalid [Hconnected Hsub]] Hmin]].
  exists h; split; [|split]; auto. 
  apply tree_decide; auto. 
  intros [u [p [Hpne Hsimple]]]. 
  destruct p; [auto|clear Hpne]. 
  pose proof Hsimple as [Hpath Hnodup]. 
  apply valid_epath_cons_inv in Hpath as [v [Hstep Hrest]]. 
  pose proof Hvalid as Hh.
  eapply addEdge2_valid_inv in Hvalid as [i [Hvalidi Hadd]]; 
  [|eapply step_vvalid1; eauto|eapply step_vvalid2; eauto|eapply step_evalid; eauto]. 
  assert (connected_subgraph_eq i). {
    split; [|split]; auto. 
    + intros x y Hx Hy. 
      assert (Hhx:vvalid h x) by (eapply Hadd; auto). 
      assert (Hhy:vvalid h y) by (eapply Hadd; auto). 
      pose proof Hconnected x y Hhx Hhy. 
      apply reachable_valid_epath in H as [q Hqpath]. 
      apply valid_epath_simple in Hqpath as [q' [Hqpath Hqnodup]].
      2:{ intros; eapply step_aux_unique_undirected with (g:=h); try apply Hh; eauto. } 
      clear q; rename q' into q. 
      destruct (classic (In e q)) as [Hin | Hnotin]; [|].
      * apply in_split in Hin as [q1 [q2 Hp]]; subst.
        apply valid_epath_app_inv in Hqpath as [a [Hqpre Hqrest]].
        apply valid_epath_cons_inv in Hqrest as [b [Hqstep Hqpost]].
        eapply step_aux_unique_undirected in Hstep as [[]|[]]; eauto; subst a b.
        - eapply valid_epath_reachable. 
          instantiate (1:= q1 ++ (rev p) ++ q2).
          eapply addEdge2_valid_epath_new_to_old; eauto. 
          { 
            eapply valid_epath_app; eauto. 
            eapply valid_epath_app; eauto. 
            apply valid_epath_rev; auto. 
          }
          {
            rewrite ! in_app_iff; intros ?. 
            apply NoDup_remove_2 in Hqnodup; rewrite in_app_iff in Hqnodup.
            inversion Hnodup; subst. 
            rewrite <- in_rev in H. 
            tauto. 
          } 
        - eapply valid_epath_reachable.
          instantiate (1:= q1 ++ p ++ q2).
          eapply addEdge2_valid_epath_new_to_old; eauto. 
          { 
            eapply valid_epath_app; eauto. 
            eapply valid_epath_app; eauto. 
          }
          {
            rewrite ! in_app_iff; intros ?. 
            apply NoDup_remove_2 in Hqnodup; rewrite in_app_iff in Hqnodup.
            inversion Hnodup; subst. 
            tauto. 
          } 
      * eapply valid_epath_reachable.
        eapply addEdge2_valid_epath_new_to_old; eauto. 
    + split. 
      * intros; split; intros. 
        - apply Hsub. 
          apply Hadd. 
          left; auto. 
        - apply Hsub in H.  
          apply Hadd in H as []; auto; subst. 
          apply Hadd. 
      * intros. 
        apply Hsub. 
        apply Hadd; left; auto. 
  }
  apply addEdge2_elist_permutation in Hadd; auto. 
  apply Permutation_length in Hadd. 
  apply Hmin in H; unfold edge_num in H. 
  rewrite ! Zlength_correct in H. 
  simpl in Hadd. 
  lia. 
Qed. 

Context {ew: EdgeWeight G E}.

Theorem connected_have_mst: 
  exists h, is_mst g h. 
Proof. 
  set (edge_weight_sum := fun l => fold_right Z_op_plus (Some 0%Z) (map (weight g) l)).
  set (legal := fun h => gvalid h /\ tree h /\ subgraph_vertex_eq h g).
  assert (edge_weight_sum_perm:
    forall l1 l2, Permutation l1 l2 -> edge_weight_sum l1 = edge_weight_sum l2).
  {
    intros l1 l2 Hperm. 
    induction Hperm; unfold edge_weight_sum in *; simpl; auto.
    - rewrite IHHperm; auto.
    - destruct (weight g x), (weight g y), (fold_right Z_op_plus (Some 0) (map (weight g) l)); simpl; auto; f_equal; lia.
    - congruence.
  }
  destruct (Nodup_all_sublists (bijective_listE g) (bijective_listE_NoDup g g_valid))
    as [edge_sets [Hedge_sets_sound Hedge_sets_complete]].
  set (represented := fun l =>
    In l edge_sets /\ exists h, legal h /\ Permutation l (bijective_listE h)).

  assert (legal_edges_in_g:
    forall h, legal h -> incl (bijective_listE h) (bijective_listE g)).
  {
    intros h [Hvalid [_ Hsub]] e Hin.
    apply bijective_edges in Hin; auto.
    apply no_empty_edge in Hin as [u [v Hstep]]; auto.
    apply bijective_edges; auto.
    eapply step_evalid; eauto. 
    apply Hsub; eauto.
  }
  destruct spanningtree_exist as [h0 Hh0].
  assert (represented_exists : exists l, In l edge_sets /\ represented l).
  {
    destruct (Hedge_sets_complete (bijective_listE h0)) as [l0 [Hl0 Hperm0]].
    - apply bijective_listE_NoDup; tauto.
    - apply legal_edges_in_g; auto.
    - exists l0; split; auto.
      split; auto; exists h0; split; auto.
  }
  destruct represented_exists as [l0 [Hl0 Hrepr0]].
  destruct (Z_op_finite_min edge_weight_sum represented edge_sets l0 Hl0 Hrepr0
    ltac:(intros y Hy; exact (proj1 Hy))) as [lm [Hreprm Hminm]].
  destruct Hreprm as [_ [hm [Hlegalm Hpermm]]].
  exists hm.
  split; auto.
  intros h Hlegalh.
  destruct (Hedge_sets_complete (bijective_listE h)) as [lh [Hlh Hpermh]].
  - apply bijective_listE_NoDup; try tauto. 
    apply Hlegalh.
  - apply legal_edges_in_g; auto.
  - assert (Hreprh : represented lh) by (split; auto; exists h; split; auto).
    specialize (Hminm lh Hreprh).
    pose proof (edge_weight_sum_perm lm (bijective_listE hm) Hpermm).
    unfold edge_weight_sum in H. 
    unfold total_weight.
    rewrite <- H.
    rewrite (edge_weight_sum_perm lh (bijective_listE h) Hpermh) in Hminm.
    exact Hminm.
Qed. 

End SPANNING_TREE.
