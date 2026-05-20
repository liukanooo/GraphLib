Require Import SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From MaxMinLib Require Import MaxMin Interface. 
From ListLib Require Import Base.Inductive General.NoDup General.Length.
From GraphLib Require Import graph_basic reachable_basic reachable_restricted path path_basic epath subgraph Syntax Zweight.
Local Open Scope list.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.

(* 树的基本定义：包含树的性质和树的判定 *)

Class Tree 
    (G V E: Type) 
    {pg: Graph G V E} 
    {gv: GValid G} 
    (P: Type) 
    {path: Path G V E P}:=
{
  tree: G -> Prop;
  tree_connected: forall g, tree g -> connected g;
  tree_no_curcuit: forall g, tree g -> 
  ~ exists u p, ( p <> nil /\ is_simple_epath g u p u); 
  tree_decide: forall g, connected g -> (~ exists x p, p <> nil /\ is_simple_epath g x p x) -> tree g;
}.

(* 关于AddEdge前后都是树的证明和顶点边列表关系 *)
Section ADD_EDGE_TREE.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}. (*存在一个tree的谓词 *)
(* 两个图之间的关系 *)
Context {g1 g2: G}
        {g_valid1: gvalid g1}
        {g_valid2: gvalid g2}
        {u v: V}
        {e: E}
        (Hadd: addEdge g1 g2 u v e). 

Lemma addEdge_subgraph: 
  subgraph g1 g2.
Proof.
  unfold subgraph.
  intros. 
  apply Hadd; left; auto.
Qed.

Lemma addEdge_new_step_aux:
  forall x y a,
    step_aux g2 a x y ->
    a <> e ->
    step_aux g1 a x y.
Proof.
  intros x y a Hstep Hneq.
  destruct Hadd as [_ _ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq _]]; auto.
  contradiction.
Qed.

Lemma addEdge_new_step_uv:
  step_aux g2 e u v.
Proof.
  destruct Hadd as [_ _ _ Hstep_add].
  apply Hstep_add.
  right; split; [reflexivity | left; split; reflexivity].
Qed.

Lemma addEdge_new_step_vu:
  step_aux g2 e v u.
Proof.
  apply step_sym.
  apply addEdge_new_step_uv.
Qed.

Lemma addEdge_new_vertex_is_leaf:
  exists ! x, exists a, step_aux g2 a x v.
Proof.
  exists u.
  split.
  - exists e; apply addEdge_new_step_uv.
  - intros x [a Hstep].
    destruct Hadd as [[Hu [Hv He]] _ _ Hstep_add].
    apply Hstep_add in Hstep as [Hold | [Heq [[Hx Hy] | [Hx Hy]]]].
    + exfalso.
      apply Hv.
      eapply step_vvalid2; eauto.
    + subst; reflexivity.
    + subst; auto.
Qed.

Lemma addEdge_vlist_permutation:
  forall (vlist1 vlist2: list V),
    NoDup vlist1 ->
    (forall x, In x vlist1 <-> vvalid g1 x) ->
    NoDup vlist2 ->
    (forall x, In x vlist2 <-> vvalid g2 x) ->
    Permutation vlist2 (v :: vlist1).
Proof.
  intros vlist1 vlist2 Hnodup1 Hviff1 Hnodup2 Hviff2. 
  destruct Hadd as [[Hu [Hv He]] _ _ Hstep_add].
  apply NoDup_Permutation; auto.
  - constructor; auto.
    intro Hin.
    apply Hv.
    apply Hviff1; auto.
  - intros x; split; intros Hin.
    + apply Hviff2 in Hin.
      destruct Hadd as [_ Hadd_vvalid _].
      apply Hadd_vvalid in Hin as [Hin | Hin]; simpl; auto. 
      right; apply Hviff1; auto.
    + apply Hviff2.
      destruct Hadd as [_ Hadd_vvalid _].
      apply Hadd_vvalid.
      destruct Hin; [right|left]; auto. 
      apply Hviff1; auto.
Qed.

Lemma addEdge_elist_permutation:
  forall (elist1 elist2: list E),
    NoDup elist1 ->
    (forall a, In a elist1 <-> evalid g1 a) ->
    NoDup elist2 ->
    (forall a, In a elist2 <-> evalid g2 a) ->
    Permutation elist2 (e :: elist1).
Proof.
  intros elist1 elist2 Hnodup1 Heiff1 Hnodup2 Heiff2.
  destruct Hadd as [[Hv He] _ _ Hstep_add].
  apply NoDup_Permutation; auto.
  - constructor; auto.
    intro Hin.
    apply He.
    apply Heiff1; auto.
  - intros a; split; intros Hin.
    + apply Heiff2 in Hin.
      destruct Hadd as [_ _ Hadd_evalid].
      apply Hadd_evalid in Hin as [Hin | Hin]; simpl; auto. 
      right; apply Heiff1; auto.
    + apply Heiff2.
      destruct Hadd as [_ _ Hadd_evalid].
      apply Hadd_evalid.
      destruct Hin; [right|left]; auto. 
      apply Heiff1; auto.
Qed.


Lemma addEdge_valid_epath_old_to_new:
  forall x p y, valid_epath g1 x p y -> valid_epath g2 x p y.
Proof.
  intros x p.
  revert x.
  induction p as [|a p IHp]; intros x y Hpath.
  - apply valid_epath_nil_inv in Hpath; subst.
    apply valid_epath_empty.
  - apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    eapply valid_epath_cons.
    + apply addEdge_subgraph; exact Hstep.
    + apply IHp; exact Hrest.
Qed.

Lemma addEdge_valid_epath_new_to_old:
  forall x p y,
    valid_epath g2 x p y ->
    ~ In e p ->
    valid_epath g1 x p y.
Proof.
  intros x p.
  revert x.
  induction p as [|a p IHp]; intros x y Hpath Hfor.
  - apply valid_epath_nil_inv in Hpath; subst.
    apply valid_epath_empty.
  - simpl in Hfor.
    apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    eapply valid_epath_cons.
    + eapply addEdge_new_step_aux; eauto.
    + apply IHp; auto.
Qed.

Lemma addEdge_no_epath_from_new_without_edge:
  forall p x,
    valid_epath g2 v p x ->
    ~ In e p ->
    x = v.
Proof.

  intros p.
  induction p as [|a p IHp]; intros x Hpath Hfor.
  - apply valid_epath_nil_inv in Hpath; auto.
  - simpl in Hfor.
    apply valid_epath_cons_inv in Hpath as [z [Hstep Hrest]].
    destruct Hadd as [[Hu [Hv He]] _ _ Hstep_add].
    apply Hstep_add in Hstep as [Hold | [Heq _]].
    + exfalso.
      apply Hv.
      eapply step_vvalid1; eauto.
    + destruct Hfor; subst; left; auto.
Qed.

Lemma addEdge_no_epath_to_new_without_edge:
  forall x p,
    valid_epath g2 x p v ->
    ~ In e p ->
    x = v.
Proof.
  intros x p Hpath Hfor. 
  rewrite in_rev in Hfor.
  pose proof (valid_epath_rev g2 x p v Hpath) as Hrev.
  eapply addEdge_no_epath_from_new_without_edge; eauto.
Qed. 

Lemma addEdge_simple_epath_old_endpoints_not_in_new_edge:
  forall x p y,
    x <> v ->
    y <> v ->
    is_simple_epath g2 x p y ->
    ~ In e p.
Proof.
  intros x p y Hxv Hyv [Hpath Hnodup] Hin.
  apply in_split in Hin as [l1 [l2 Hp]].
  subst p.
  apply valid_epath_app_inv in Hpath as [a [Hl1 Hrest]].
  apply valid_epath_cons_inv in Hrest as [b [Hstep Hl2]]. 
  apply NoDup_remove_2 in Hnodup. 
  rewrite in_app_iff in Hnodup.
  pose proof Hadd as Hadd'.
  destruct Hadd' as [[Hu [Hv He]] _ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq [[Ha Hb] | [Ha Hb]]]]; subst.
  * apply He.
    eapply step_evalid; eauto.
  * assert (y = v) by (eapply addEdge_no_epath_from_new_without_edge; eauto).
    contradiction.
  * assert (x = v) by (eapply addEdge_no_epath_to_new_without_edge; eauto).
    contradiction.
Qed.

Lemma addEdge_simple_cycle_not_in_new_edge:
  forall x p,
    is_simple_epath g2 x p x ->
    ~ In e p.
Proof.
  intros x p [Hpath Hnodup] Hin.
  apply in_split in Hin as [l1 [l2 Hp]]; subst.
  apply valid_epath_app_inv in Hpath as [a [Hl1 Hrest]].
  apply valid_epath_cons_inv in Hrest as [b [Hstep Hl2]].
  apply NoDup_remove_2 in Hnodup. 
  rewrite in_app_iff in Hnodup.
  pose proof Hadd as Hadd'.
  destruct Hadd' as [[Hu [Hv He]] _ _ Hstep_add].
  apply Hstep_add in Hstep as [Hold | [Heq [[Ha Hb] | [Ha Hb]]]]; subst.
  * apply He; eapply step_evalid; eauto.
  * assert (x = v) by (eapply addEdge_no_epath_from_new_without_edge; eauto); subst.
    assert (u = v) by (eapply addEdge_no_epath_from_new_without_edge; eauto); subst. 
    auto.
  * assert (x = v) by (eapply addEdge_no_epath_to_new_without_edge; eauto); subst.
    assert (u = v) by (eapply addEdge_no_epath_to_new_without_edge; eauto); subst.
    auto.
Qed.

Lemma addEdge_tree_connected:
  tree g1 -> 
  connected g2.
Proof.
  intros tr1 x y Hx Hy.
  pose proof Hadd as Hadd'.
  destruct Hadd' as [[Hu [Hv He]] Hvx _ Hstep_add].
  apply Hvx in Hx as [Hx | Hx]; apply Hvx in Hy as [Hy | Hy]; subst.
  * eapply (sub_reachable g1 g2); 
    [apply addEdge_subgraph|apply tree_connected; auto].
  * transitivity u.
    + eapply (sub_reachable g1 g2); 
      [apply addEdge_subgraph|apply tree_connected; auto].
    + apply step_rt; exists e; apply addEdge_new_step_uv.
  * transitivity u.
    + apply step_rt; exists e; apply addEdge_new_step_vu.
    + eapply (sub_reachable g1 g2); 
      [apply addEdge_subgraph|apply tree_connected; auto].
  * reflexivity. 
  Unshelve. all: auto.
Qed.

Lemma addEdge_tree_no_curcuit:
  tree g1 -> 
  (~ exists x p, p <> nil /\ is_simple_epath g2 x p x).
Proof.
  intros tr1 [x [p [Hpne Hsimple]]].
  destruct (classic (In e p)) as [Hin | Hnotin].
  * eapply addEdge_simple_cycle_not_in_new_edge; eauto.
  * eapply tree_no_curcuit; eauto.
    exists x, p; split; auto.
    destruct Hsimple as [Hpath Hnodup].
    split; auto.
    eapply addEdge_valid_epath_new_to_old; eauto.
Qed. 

Theorem addEdge_tree: 
  tree g1 -> tree g2. 
Proof.
  intros tr1.
  apply tree_decide; auto.
  apply addEdge_tree_connected; auto.
  apply addEdge_tree_no_curcuit; auto.
Qed.

Lemma deleteLeaf_tree_connected:
  tree g2 -> 
  connected g1.
Proof.
  intros tr2 x y Hx Hy.
  assert (Hxv: x <> v) by (intros Heq; subst; destruct Hadd as [[? []] _ _]; contradiction).
  assert (Hyv: y <> v) by (intros Heq; subst; destruct Hadd as [[? []] _ _]; contradiction).
  pose proof Hadd as Hadd'.
  destruct Hadd' as [[Hu [Hv He]] Hvertex _ _].
  assert (Hx2: vvalid g2 x) by (apply Hvertex; left; auto).
  assert (Hy2: vvalid g2 y) by (apply Hvertex; left; auto).
  destruct (reachable_valid_epath g2 x y (tree_connected g2 tr2 x y Hx2 Hy2))
    as [p Hpath].
  eapply valid_epath_simple_directed in Hpath as [q Hsimple]; eauto.
  assert (Hnotin: ~ In e q) by (eapply addEdge_simple_epath_old_endpoints_not_in_new_edge; try eapply Hsimple; eauto).
  eapply valid_epath_reachable.
  eapply addEdge_valid_epath_new_to_old; eauto.
  apply Hsimple.
Qed.

Lemma deleteLeaf_tree_no_curcuit:
  tree g2 -> 
  (~ exists x p, p <> nil /\ is_simple_epath g1 x p x).
Proof.
  intros tr2 [x [p [Hpne [Hpath Hnodup]]]].
  eapply tree_no_curcuit; eauto.
  exists x, p; split; auto.
  split; auto.
  apply addEdge_valid_epath_old_to_new; auto.
Qed.

Theorem deleteLeaf_tree:
  tree g2 -> tree g1.
Proof.
  intros tr2.
  apply tree_decide; auto.
  apply deleteLeaf_tree_connected; auto.
  apply deleteLeaf_tree_no_curcuit; auto.
Qed.

End ADD_EDGE_TREE.

(* 树本身的一些性质。可能需要用到树操作来进行证明 *)

Section TREE.
Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E} (*这里要求原图是simple graph是一个很明显的疑惑点*)
        {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}
        (g: G)
        {g_valid: gvalid g}
        {g_tree: tree g}.

Lemma no_self_loop: forall u e,
  ~ step_aux g e u u.
Proof.
  intros. intros Hstep. 
  eapply tree_no_curcuit; eauto. 
  exists u, (e :: nil); split; [unfold not; intros; inversion H|split]. 
  * apply valid_epath_single; auto.
  * repeat constructor; auto.
Qed.

Lemma no_multiple_edge: forall u v e1 e2,
  step_aux g e1 u v -> step_aux g e2 u v -> e1 = e2.
Proof.
  intros.
  destruct (classic (e1 = e2)); auto.
  exfalso. 
  eapply tree_no_curcuit; eauto. 
  exists u, (e1 :: e2 :: nil); split; [symmetry; apply nil_cons|split]. 
  * eapply valid_epath_cons; eauto. 
    apply valid_epath_single; auto. 
    apply step_sym; auto. 
  * repeat constructor; auto. 
    simpl; unfold not; intros [|]; auto. 
Qed.


Lemma tree_edge_is_bridge: forall u v e,
  step_aux g e u v ->
  ~ reachable_without g e u v.
Proof.
  intros u v e Hstep Hrw.
  apply reachable_without_valid_epath in Hrw as [p [Hvalid_epath Hnot_in]].
  assert (Hfor : Forall (fun x => x <> e) p) by (rewrite Forall_forall; intros ? ? ?; subst; auto). 
  pose proof Hvalid_epath as Hp. 
  eapply valid_epath_simple_Forall in Hvalid_epath as [q [[Hqvalid Hqnodup] Hqfor]]; eauto.
  2:{ intros; eapply step_aux_unique_undirected; eauto. }
  eapply tree_no_curcuit; eauto.
  exists u, (e :: rev q); split; [symmetry; apply nil_cons|split].
  * eapply valid_epath_cons; eauto.
    eapply valid_epath_rev; eauto. 
  * constructor.
    + rewrite <- in_rev.
      rewrite Forall_forall in Hqfor.
      intros Hin.
      pose proof (Hqfor e Hin) as Hneq.
      contradiction.
    + apply NoDup_rev; auto.
Qed.

Theorem tree_one_simple_epath: 
  forall u v p1 p2,
  is_simple_epath g u p1 v ->
  is_simple_epath g u p2 v ->
  p1 = p2.
Proof.
  intros u v p1; revert u v. 
  induction p1 as [|e1 q1 IHp1]; intros u v p2 Hp1 Hp2.
  - unfold is_simple_epath in *.
    destruct Hp1 as [Hp1 _], Hp2 as [Hp2 Hnodup2].
    apply valid_epath_nil_inv in Hp1; subst u.
    destruct p2 as [|e2 q2].
    + reflexivity.
    + exfalso.
      eapply tree_no_curcuit; eauto.
      exists v, (e2 :: q2); split; [symmetry; apply nil_cons|split; auto].
  - unfold is_simple_epath in *.
    destruct Hp1 as [Hpath1 Hnodup1], Hp2 as [Hpath2 Hnodup2].
    apply valid_epath_cons_inv in Hpath1 as [w1 [Hstep1 Htail1]].
    inversion Hnodup1 as [|? ? Hnotin1 Hnodup_tail1]; subst.
    assert (Hin_e1_p2 : In e1 p2).
    {
      destruct (classic (In e1 p2)); auto.
      exfalso.
      eapply tree_edge_is_bridge; eauto.
      eapply valid_epath_reachable_without.
      + eapply valid_epath_app; [apply Hpath2|apply valid_epath_rev; eauto].
      + rewrite in_app_iff.
        intros [|]; [contradiction|apply Hnotin1; apply in_rev; auto].
    }
    destruct (in_split _ _ Hin_e1_p2) as [l1 [l2 Hp2eq]].
    subst p2.
    apply valid_epath_app_inv in Hpath2 as [x [Hpre Hsuf]].
    apply valid_epath_cons_inv in Hsuf as [y [Hstep2 Htail2]]. 
    eapply step_aux_unique_undirected in Hstep1 as [[]|[]]; eauto; subst.
    + destruct l1 as [|a l1'].
      * simpl. f_equal.
        eapply IHp1; eauto. 
        split; auto.
        inversion Hnodup2; auto.
      * exfalso.
        eapply tree_no_curcuit; eauto.
        exists u, (a :: l1'); split; [symmetry; apply nil_cons|split; auto].
        apply NoDup_app_remove_r in Hnodup2; auto.
    + destruct l1 as [|a l1'].
      * apply valid_epath_nil_inv in Hpre; subst; exfalso.
        eapply no_self_loop; eauto.
      * exfalso. 
        eapply tree_no_curcuit; eauto. 
        exists w1, (e1 :: a :: l1'); split; [symmetry; apply nil_cons|split]. 
        eapply valid_epath_cons; eauto.
        constructor; [|apply NoDup_app_remove_r in Hnodup2; auto]. 
        apply NoDup_remove in Hnodup2 as []. 
        unfold not; intros; apply H0. 
        apply in_or_app; left; auto.
Qed.

(* 树中任意两点间有且仅有一个 simple_epath *)
Lemma tree_unique_simple_epath: forall u v,
  vvalid g u -> vvalid g v ->
  exists! p, is_simple_epath g u p v.
Proof.
  intros.
  pose proof (reachable_valid_epath g u v (tree_connected g g_tree u v H H0)) as [p Hpath].
  eapply valid_epath_simple in Hpath as [q Hsimple]; eauto.
  exists q. split; auto.
  intros q' Hsimple'.
  eapply tree_one_simple_epath; eauto. 
  intros; eapply step_aux_unique_undirected; eauto.
Qed.

Section TREEINDUCTION.

Context {fg: FiniteGraph G V E}. 

#[export]Instance vlist_bijective: VListBijective G V E.
Proof. apply finite_graph_vlist_bijective; auto. Qed.

#[export]Instance elist_bijective: EListBijective G V E.
Proof. 
  apply finite_egraph_elist_bijective; auto.
  apply finite_graph_finite_egraph; auto. 
  
Qed.


Definition is_leaf (v: V): Prop := 
  exists ! u, (exists e, step_aux g e u v). 

Lemma in_epath_evalid: 
  forall u v p e,
    valid_epath g u p v ->
    In e p ->
    evalid g e.
Proof.
  intros. 
  revert u H. 
  induction p; intros. 
  + contradiction. 
  + inversion H0; subst. 
    * apply valid_epath_cons_inv in H as [w [Hstep Hrest]]. 
      eapply step_evalid; eauto. 
    * apply valid_epath_cons_inv in H as [w [Hstep Hrest]]. 
      eapply IHp; eauto. 
Qed.

Lemma simple_epath_length_bounded : forall u v p,
  is_simple_epath g u p v ->
  (Zlength p <= edge_num g)%Z.
Proof.
  intros; unfold edge_num.
  destruct H as [Hvalid Hnodup].
  assert (incl p (bijective_listE g)) by 
  (intros e Hin; apply bijective_edges; auto; eapply in_epath_evalid; eauto).
  rewrite ! Zlength_correct. 
  apply inj_le.
  apply NoDup_incl_length; auto. 
Qed.

Lemma max_n_in_range: forall (Q: Z -> Prop) (K: Z),
  (0 <= K)%Z ->
  (exists n, (0 <= n <= K)%Z /\ Q n) ->
  exists m, Q m /\ (0 <= m <= K)%Z /\ (forall k, (0 <= k <= K)%Z -> Q k -> k <= m)%Z.
Proof.
  intros Q K HK Hexists.
  remember (Z.to_nat K) as n.
  revert K Heqn Hexists HK.
  induction n; intros.
  - assert (K = 0)%Z by lia. subst.
    destruct Hexists as [x [[Hlow Hhigh] HP]].
    assert (x = 0)%Z by lia. subst.
    exists 0%Z. repeat split; auto; intros; lia.
  - destruct (classic (Q K)) as [HPK | HNPK].
    + exists K. repeat split; auto; intros; lia.
    + assert (Hexists': exists n, (0 <= n <= K - 1)%Z /\ Q n).
      { destruct Hexists as [x [[Hlx Hhx] HPx]].
        exists x. split; auto. 
        destruct (classic (x = K)); subst; [contradiction|lia]. }
      specialize (IHn (K - 1)%Z). 
      destruct IHn as [m [HPm [[Hlm Hhm] Hmax]]]; 
      [lia|auto|lia|].
      exists m. repeat split; auto; [lia |].
      intros k Hrange HPk.
      assert (k < K)%Z by (destruct (Z.eq_dec k K); [subst; contradiction | lia]).
      apply Hmax; [lia | auto].
Qed.

Lemma min_n_in_range: forall (Q: Z -> Prop) (K: Z),
  (0 <= K)%Z ->
  (exists n, (0 <= n <= K)%Z /\ Q n) ->
  exists m, Q m /\ (0 <= m <= K)%Z /\ (forall k, (0 <= k <= K)%Z -> Q k -> m <= k)%Z.
Proof.
  intros Q K HK Hexists.
  remember (Z.to_nat K) as n.
  revert Q K Heqn Hexists HK.
  induction n; intros.
  - assert (K = 0)%Z by lia. subst.
    destruct Hexists as [x [[Hlow Hhigh] HP]].
    assert (x = 0)%Z by lia. subst.
    exists 0%Z. repeat split; auto; intros; try lia.
  - destruct (classic (Q 0%Z)) as [Q0 | NotQ0].
    + exists 0%Z. split; [|split]; auto; intros; lia.
    + assert (Hexists': exists n, (0 <= n <= K - 1)%Z /\ (fun x => Q (x + 1)%Z) n).
      { destruct Hexists as [x [[Hlx Hhx] Qx]].
        assert (x > 0)%Z by (destruct (Z.eq_dec x 0); [subst; contradiction|lia]).
        exists (x - 1)%Z. split; [lia|].
        replace (x - 1 + 1)%Z with x by lia; auto. }
      specialize (IHn (fun x => Q (x + 1)%Z) (K - 1)%Z).
      destruct IHn as [m [Qm [[Hlm Hhm] Hmin]]]; [lia|auto|lia|].
      exists (m + 1)%Z. split; [|split]; auto; [lia|].
      intros k Hrange Qk.
      assert (k > 0)%Z by (destruct (Z.eq_dec k 0); [subst; contradiction|lia]).
      pose proof Hmin (k - 1)%Z ltac:(lia) ltac:(replace (k - 1 + 1)%Z with k by lia; auto) as Hle. 
      lia.
Qed.

Theorem longest_simple_epath_exists :
  (exists v, vvalid g v) -> 
  exists p, max_object_of_subset Z.le (fun x => exists u v, is_simple_epath g u x v) (@Zlength E) p.
Proof.
  intros [v0 Hv0].
  set (Q := fun n => exists u v p, is_simple_epath g u p v /\ Zlength p = n).
  set (K := Zlength (bijective_listE g)).

  assert (Hexists: exists n, (0 <= n <= K)%Z /\ Q n).
  { exists 0%Z. split. 
    + split; [lia | apply Zlength_nonneg]. 
    + exists v0, v0, nil. split.
      * split; [apply valid_epath_empty | constructor].
      * apply Zlength_nil. }

  destruct (max_n_in_range Q K) as [max_n [HPmax [[Hlow Hhigh] Hmax]]];
  [apply Zlength_nonneg|auto|].

  destruct HPmax as [u_max [v_max [p_max [Hsimple_max Hlen_max]]]].
  exists p_max. split.
  + exists u_max, v_max; auto.
  + intros p [u [v Hsimple']]. 
    rewrite Hlen_max.
    apply Hmax.
    * split; [apply Zlength_nonneg|eapply simple_epath_length_bounded; eauto].
    * exists u, v, p; split; auto.
Qed.

Theorem at_least_one_leaf: 
  (exists e, evalid g e) -> (* 至少有一条边 *)
  exists v, is_leaf v.
Proof.
  intros [a Ha].

  assert (Hexists_v: exists v, vvalid g v).
  { destruct (no_empty_edge g a g_valid Ha) as [x [y Hstep]].
    exists x. eapply step_vvalid1; eauto. }
  pose proof (longest_simple_epath_exists Hexists_v) as [p [Hpsimple Hmax]].
  destruct Hpsimple as [u [v Hpsimple]].

  assert (Hp_not_nil: p <> nil).
  { intros Heq; subst p.
    destruct (no_empty_edge g a g_valid Ha) as [x [y Hstep]].
    assert (is_simple_epath g x (a :: nil) y).
    { split.
      - apply valid_epath_single; auto.
      - constructor; [simpl; auto | constructor]. }
    pose proof (Hmax (a :: nil) (ex_intro _ x (ex_intro _ y H))) as Hlen_le.
    rewrite Zlength_nil in Hlen_le.
    rewrite Zlength_cons, Zlength_nil in Hlen_le.
    lia. } 
  destruct (list_snoc_destruct p) as [|[e [q Hpq]]]; [contradiction|subst].  
  destruct Hpsimple as [Hpvalid Hpnodup]. 
  pose proof Hpvalid as Hp. 
  apply valid_epath_snoc_inv in Hpvalid as [w [Hpre Hstep]].
  exists v, w. split.
  - exists e; auto. 
  - intros x [e' Hstep']. 
    destruct (classic (e' = e)) as [|Hneq1]; [subst|exfalso].
    { eapply step_aux_unique_undirected in Hstep as [[]|]; subst; eauto. 
      destruct H; subst; auto. } 
    destruct (classic (In e' q)). 
    { apply in_split in H as [l1 [l2 H]]. 
      rewrite H in Hpre. 
      apply valid_epath_app_inv in Hpre as [y [Hl1 Hel2]]. 
      apply valid_epath_cons_inv in Hel2 as [z [He' Hl2]]. 
      eapply step_aux_unique_undirected in He' as [[]|[]]; eauto; subst y z. 
      * eapply tree_no_curcuit; eauto. 
        exists v, (l2 ++ e :: nil); split; [symmetry; apply app_cons_not_nil|split]. 
        + eapply valid_epath_snoc; eauto. 
        + subst. 
          rewrite <- app_assoc in Hpnodup.
          apply NoDup_app_remove_l in Hpnodup. 
          rewrite <- app_comm_cons in Hpnodup. 
          inversion Hpnodup; auto. 
      * eapply tree_no_curcuit; eauto. 
        exists v, (e' :: l2 ++ e :: nil); split; [symmetry; apply nil_cons|split]. 
        + eapply valid_epath_cons with (v:=x); eauto;
          [eapply step_sym; eauto|].
          eapply valid_epath_snoc; eauto.
        + subst. 
          rewrite <- app_assoc in Hpnodup.
          apply NoDup_app_remove_l in Hpnodup. 
          auto. 
    }
    assert (is_simple_epath g u ((q ++ [e]) ++ [e']) x). {
      split.
      - eapply valid_epath_snoc; eauto. 
        eapply step_sym; eauto.
      - apply Nodup_app_comm. 
        constructor; auto. 
        rewrite in_app_iff in *.
        intros [Hin | Hin]; auto; inversion Hin; auto.
    }
    pose proof Hmax ((q ++ [e]) ++ [e']) ltac:(exists u, x; auto). 
    rewrite Zlength_app, Zlength_cons, Zlength_nil in H1.  
    lia.
Qed.

(* 最长的路径的两个端点都是叶子 *)

Definition parent_edge_rel (r x: V) (e: E) : Prop :=
  exists p w, is_simple_epath g r (p ++ e :: nil) x /\ step_aux g e w x.

Lemma path_to_endpoint_uses_incident_edge_last :
  forall r x y p e,
    is_simple_epath g r p x ->
    In e p ->
    step_aux g e y x ->
    exists p', p = p' ++ e :: nil.
Proof.
  intros r x y p e [Hpath Hnodup] Hin Hstep_yx.
  destruct (in_split _ _ Hin) as [l1 [l2 Hp]].
  subst p.
  destruct l2 as [|a l2'].
  - exists l1; reflexivity.
  - apply valid_epath_app_inv in Hpath as [m [Hpre Hsuf]].
    apply valid_epath_cons_inv in Hsuf as [z [Hstep1 Hrest]].
    eapply step_aux_unique_undirected in Hstep1 as [[Hz1 Hz2]|[Hz1 Hz2]]; eauto.
    + subst z y.
      exfalso.
      eapply tree_no_curcuit; eauto.
      exists x, (a :: l2'); split; [discriminate|].
      split.
      * exact Hrest.
      * apply NoDup_app_remove_l in Hnodup.
        inversion Hnodup; subst; auto.
    + subst z m.
      exfalso.
      eapply tree_no_curcuit; eauto.
      exists x, (e :: a :: l2'); split; [discriminate|].
      split.
      * eapply valid_epath_cons; eauto.
        eapply step_sym; eauto.
      * apply NoDup_app_remove_l in Hnodup.
        exact Hnodup.
Qed.

Lemma edge_of_vertex_exists :
  forall r x,
    vvalid g r ->
    vvalid g x ->
    x <> r ->
    exists e, parent_edge_rel r x e.
Proof.
  intros r x Hr Hx Hneq.
  destruct (tree_unique_simple_epath r x Hr Hx) as [q [Hsimple _]].
  destruct (valid_epath_inv_n1 g r q x (proj1 Hsimple))
    as [[Heq Hnil]|[p [w [e [Hq [Hpre Hstep]]]]]].
  - subst. contradiction.
  - exists e. exists p, w. split.
    + subst q. destruct Hsimple; split; auto.
    + exact Hstep.
Qed.

Lemma parent_edge_rel_right_unique :
  forall r x e1 e2,
    parent_edge_rel r x e1 ->
    parent_edge_rel r x e2 ->
    e1 = e2.
Proof.
  intros r x e1 e2 [p1 [w1 [H1 Hstep1]]] [p2 [w2 [H2 Hstep2]]].
  assert (Hp : p1 ++ e1 :: nil = p2 ++ e2 :: nil).
  { eapply tree_one_simple_epath; eauto. }
  apply app_inj_tail_iff in Hp; tauto.
Qed.

Lemma parent_edge_prefix_simple :
  forall r x y p e,
    is_simple_epath g r (p ++ e :: nil) y ->
    step_aux g e x y ->
    is_simple_epath g r p x.
Proof.
  intros r x y p e [Hvalid Hnodup] Hstep.
  apply valid_epath_snoc_inv in Hvalid as [z [Hpre Hlast]].
  assert (Hzx: z = x).
  {
    eapply step_aux_unique_undirected in Hlast as [[]|]; eauto; subst.
    destruct H; subst; auto.
  }
  subst z.
  split; auto.
  apply NoDup_app_remove_r in Hnodup; auto.
Qed.

Lemma parent_edge_rel_left_unique :
  forall r x y e,
    parent_edge_rel r x e ->
    parent_edge_rel r y e ->
    x = y.
Proof.
  intros r x y e [px [wx [Hsx Hstepx]]] [py [wy [Hsy Hstepy]]].
  eapply step_aux_unique_undirected in Hstepx as [[Hwx Hxy]|]; eauto.
  destruct H; subst.
  assert (Hpyx : is_simple_epath g r py x).
  { eapply parent_edge_prefix_simple; eauto. }
  assert (Heq : px ++ e :: nil = py).
  { eapply tree_one_simple_epath; eauto. }
  subst py.
  destruct Hsy as [_ Hnodup].
  apply NoDup_remove_2 in Hnodup.
  rewrite in_app_iff in Hnodup.
  exfalso; apply Hnodup; left.
  rewrite in_app_iff; right; left; reflexivity.
Qed.

Lemma parent_edge_rel_of_vertex_in_list :
  forall r xs es x e,
    Forall2 (parent_edge_rel r) xs es ->
    In x xs ->
    parent_edge_rel r x e ->
    In e es.
Proof.
  intros r xs es x e Hfor.
  induction Hfor; intros Hin Hrel.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Hx|Hin].
    + subst x. simpl.
      left. eapply parent_edge_rel_right_unique; eauto.
    + simpl. right. eapply IHHfor; eauto.
Qed.

Lemma parent_edge_rel_of_edge_in_list :
  forall r xs es e,
    Forall2 (parent_edge_rel r) xs es ->
    In e es ->
    exists x, In x xs /\ parent_edge_rel r x e.
Proof.
  intros r xs es e Hfor.
  induction Hfor; intros Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [He|Hin].
    + exists x. split; [left; reflexivity|].
      subst e. exact H.
    + destruct (IHHfor Hin) as [z [Hyin Hyrel]].
      exists z. split; [right; exact Hyin|exact Hyrel].
Qed.

Lemma edge_has_parent_vertex :
  forall r e,
    vvalid g r ->
    evalid g e ->
    exists x, x <> r /\ vvalid g x /\ parent_edge_rel r x e.
Proof.
  intros r e Hr He.
  destruct (no_empty_edge g e g_valid He) as [u [v Hstep]].
  pose proof (step_vvalid1 _ _ _ _ Hstep) as Hu.
  pose proof (step_vvalid2 _ _ _ _ Hstep) as Hv.
  destruct (tree_unique_simple_epath r u Hr Hu) as [pu [Hpu _]].
  destruct (tree_unique_simple_epath r v Hr Hv) as [pv [Hpv _]].
  destruct (classic (In e pu)) as [Hin_u|Hnin_u].
  - destruct (path_to_endpoint_uses_incident_edge_last r u v pu e Hpu Hin_u (step_sym _ _ _ _ Hstep)) as [p' Hp'].
    exists u; repeat split.
    + intro Heq; subst u.
      eapply tree_no_curcuit; eauto.
      exists r, (p' ++ e :: nil); split.
      * destruct p'; discriminate.
      * subst; auto.
    + auto.
    + exists p', v; split; [subst|apply step_sym]; auto.
  - destruct (classic (In e pv)) as [Hin_v|Hnin_v].
    { 
      destruct (path_to_endpoint_uses_incident_edge_last r v u pv e Hpv Hin_v Hstep) as [p' Hp'].
      exists v; repeat split.
      + intro Heq; subst v.
        eapply tree_no_curcuit; eauto.
        exists r, (p' ++ e :: nil); split.
        * destruct p'; discriminate.
        * subst; auto.
      + auto.
      + exists p', u; split; [subst|]; auto. 
    }
    { 
      exfalso.
      eapply tree_edge_is_bridge; eauto.
      eapply valid_epath_reachable_without.
      + eapply valid_epath_app.
        * eapply valid_epath_rev; apply Hpu.
        * apply Hpv.
      + rewrite in_app_iff.
        intros [Hin|]; [apply in_rev in Hin|]; auto. 
    }
Qed.

(* 每个顶点列表都存在对应的父亲边列表 *)
Lemma parent_edges_for_vertices :
  forall r xs,
    vvalid g r ->
    NoDup (r :: xs) ->
    (forall x, In x xs -> vvalid g x) ->
    exists es, Forall2 (parent_edge_rel r) xs es /\ NoDup es /\ Zlength es = Zlength xs.
Proof.
  intros r xs Hr Hnodup Hvalids.
  inversion Hnodup as [|? ? Hnotin_r Hnodup_xs]; subst.
  induction xs as [|x xs IH]; intros.
  - exists nil; repeat split; constructor.
  - inversion Hnodup_xs as [|? ? Hnotin_x Hnodup_tail]; subst.
    assert (Hx : vvalid g x) by (apply Hvalids; left; reflexivity).
    assert (Hxr : x <> r) by (intro Heq; subst; apply Hnotin_r; simpl; auto).
    destruct (edge_of_vertex_exists r x Hr Hx Hxr) as [e Hrel].
    assert (Htail_valid : forall y, In y xs -> vvalid g y) by (intros y Hy; apply Hvalids; right; exact Hy).
    assert (Htail_nodup : NoDup (r :: xs)) by (constructor; auto; intro Hin; apply Hnotin_r; simpl; auto). 
    inversion Htail_nodup; subst.
    destruct (IH Htail_nodup Htail_valid H1 H2) as [es [Hfor [Hesnodup Hlen]]].
    exists (e :: es). repeat split.
    + constructor; auto.
    + constructor; auto.
      intro Hin.
      destruct (parent_edge_rel_of_edge_in_list r xs es e Hfor Hin)
      as [y [Hyin Hyrel]].
      assert (x = y) by (eapply parent_edge_rel_left_unique; eauto).
      subst y. contradiction.
    + simpl. rewrite ! Zlength_cons; now rewrite Hlen.
Qed.

Theorem tree_size_formula0: 
  (vertex_num g > 0)%Z ->
  (vertex_num g - 1 = edge_num g)%Z.
Proof.
  unfold vertex_num, edge_num.
  intros Hpos. 
  destruct (bijective_listV g) as [|r vs] eqn:Hvlist.
  - rewrite Zlength_nil in Hpos; lia.
  - assert (Hr : vvalid g r) by (apply bijective_vertices; auto; rewrite Hvlist; simpl; eauto).
    assert (Hvs_valid : forall x, In x vs -> vvalid g x) by (intros x Hin; apply bijective_vertices; auto; rewrite Hvlist; simpl; auto). 
    pose proof (bijective_listV_NoDup g g_valid) as vlist_nodup. 
    pose proof (bijective_vertices g g_valid) as vlist_iff. 
    pose proof (bijective_listE_NoDup g g_valid) as elist_nodup.
    pose proof (bijective_edges g g_valid) as elist_iff.
    
    pose proof parent_edges_for_vertices r vs Hr ltac:(rewrite <- Hvlist; auto) Hvs_valid 
    as [es [Hfor [Hesnodup Hlen]]]; subst. 

    rewrite Hvlist in vlist_nodup, vlist_iff.

    assert (Hall1 : forall e, In e es -> In e (bijective_listE g)).
    {
      intros e Hin; apply bijective_edges; auto.
      destruct (parent_edge_rel_of_edge_in_list r vs es e Hfor Hin)
      as [x [_ [p [w [_ Hstep]]]]].
      eapply step_evalid; eauto.
    }
    assert (Hall2 : forall e, In e (bijective_listE g) -> In e es).
    {
      intros e Hin; apply elist_iff in Hin as He; auto.
      destruct (edge_has_parent_vertex r e Hr He) as [x [Hxneq [Hxvalid Hrel]]].
      assert (Hinx : In x vs) by (apply vlist_iff in Hxvalid as [|]; [subst; contradiction|auto]).
      eapply parent_edge_rel_of_vertex_in_list; eauto.
    }
    assert (Hperm : Permutation es (bijective_listE g)) by (apply NoDup_Permutation; auto; intros; split; auto).
    rewrite Zlength_cons; simpl.
    rewrite <- Hlen. 
    rewrite ! Zlength_correct.
    rewrite (Permutation_length Hperm).
    lia.
Qed. 

End TREEINDUCTION.


End TREE.

Class addEdgeExist (G V E: Type) {pg: Graph G V E} {gv: GValid G} := {
  addEdge_valid: forall g u v e, 
    gvalid g ->
    step_aux g e u v -> 
    (forall w, (exists a, step_aux g a w v) -> u = w) ->
    exists h, gvalid h /\ addEdge h g u v e;
}.

Section TREE_OPERATION.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {noemptyedge: NoEmptyEdge G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {finitegraph: FiniteGraph G V E}
        {simplegraph: SimpleGraph G V E}
        {addEdgeExist: addEdgeExist G V E}(*要求原图的加边存在性*)
        {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}
        {tr: Tree G V E P}
        (g: G)
        {g_valid: gvalid g}
        {g_tree: tree g}.

Context {fg: FiniteGraph G V E}. 

Theorem tree_size_formula: 
  (vertex_num g > 0)%Z ->
  (vertex_num g - 1 = edge_num g)%Z.
Proof.
  unfold vertex_num, edge_num.
  intros. 
  assert (forall n, Zlength (bijective_listE g) = Z.of_nat n + 1 -> Zlength (bijective_listV g) - 1 = Zlength (bijective_listE g))%Z.  
  {
    clear H. intros n.
    revert g g_valid g_tree.
    induction n. 
    * intros. 
      simpl in H. 
  
      pose proof (bijective_vertices g g_valid) as vlist_iff.
      pose proof (bijective_listV_NoDup g g_valid) as vlist_nodup.
      pose proof (bijective_edges g g_valid) as elist_iff.
      pose proof (bijective_listE_NoDup g g_valid) as elist_nodup.

      destruct (bijective_listE g); [discriminate|rewrite Zlength_cons in H]. 
      destruct l; [|rewrite Zlength_cons in H; pose proof Zlength_nonneg l; lia]. 
      clear H. 
      assert (In e [e]) by (left; auto). 
      eapply elist_iff in H; eauto. 
      apply no_empty_edge in H as [u [v Hstep]]; auto. 

      assert (Huneqv: u <> v) by (intros ?; subst; eapply no_self_loop; eauto).
      (* assert (Huneqv: u <> v) by (exfalso; apply test_point). *)

      assert (Hu: In u (bijective_listV g)) by (apply vlist_iff; eapply step_vvalid1; eauto).
      assert (Hv: In v (bijective_listV g)) by (apply vlist_iff; eapply step_vvalid2; eauto).
      assert (Hw: ~ exists w, w <> u /\ w <> v /\ In w (bijective_listV g)). 
      {
        unfold not; intros [w [Hwnequ [Hwneqv Hw]]]. 
        apply vlist_iff in Hw. 
        pose proof (tree_connected g g_tree v w ltac:(eapply step_vvalid2; eauto) Hw) as Hreachable.
        destruct (reachable_valid_epath g v w Hreachable) as [p Hpath].
        eapply valid_epath_simple_directed in Hpath as [q [Hqpath Hqnodup]]; eauto.
        destruct q as [|a q].
        - apply valid_epath_nil_inv in Hqpath; auto. 
        - assert (Ha_valid : evalid g a).
          { apply valid_epath_cons_inv in Hqpath as [y [Ha_step _]].
            eapply step_evalid; eauto. }
          assert (Ha_eq : a = e).
          { apply elist_iff in Ha_valid as [Ha_eq | []]; auto. }
          subst a.
          destruct q as [|a q].
          + apply valid_epath_single_inv in Hqpath.
            eapply step_aux_unique_undirected in Hqpath as [[]|]; eauto.
            destruct H; subst; auto.
          + inversion Hqnodup as [|? ? Hnotin _]; subst. 
            assert (He_valid : evalid g a).
            { apply valid_epath_cons_inv in Hqpath as [y [He_step Hrest]].
              apply valid_epath_cons_inv in Hrest as [z [Ha_step _]].
              eapply step_evalid; eauto. }
            assert (Ha_eq : a = e).
            { apply elist_iff in He_valid as [Ha_eq | []]; auto. }
            subst a. apply Hnotin; simpl; auto.
      }
      assert (Hperm : Permutation (bijective_listV g) [u; v]).
      {
        apply NoDup_Permutation; auto.
        - constructor.
          + simpl. intros [Hu_eq | []]. subst. contradiction.
          + constructor; auto; apply NoDup_nil.
        - intros x; split; intros Hin.
          + destruct (classic (x = u)) as [Hx|Hx]; [subst; simpl; auto|].
            destruct (classic (x = v)) as [Hxv|Hxv]; [subst; simpl; auto|].
            exfalso. apply Hw. exists x; repeat split; auto.
          + simpl in Hin. destruct Hin as [Hin|[Hin|[]]]; subst; auto.
      }
      rewrite !Zlength_correct.
      rewrite (Permutation_length Hperm).
      simpl. lia.
    * intros. 
      assert (Hleaf: exists v, is_leaf g v). 
      { 
        apply at_least_one_leaf; auto. 
        destruct (bijective_listE g) eqn: Hel; [rewrite Zlength_nil in H; lia|].
        exists e; apply bijective_edges; auto; subst; rewrite Hel; left; auto.
        (* exfalso; apply test_point. *)
      } destruct Hleaf as [v [u [[e Hstep] Hleaf]]]. 
      apply addEdge_valid in Hstep as [h [Hvalid Hadd]]; auto.

      assert (Hv: ~ vvalid h v) by (destruct Hadd; tauto). 
      assert (He: ~ evalid h e) by (destruct Hadd; tauto). 
      assert (tree h) by (eapply deleteLeaf_tree; eauto). 
      assert (HpermV : Permutation (bijective_listV g) (v :: bijective_listV h)).
      {
        eapply addEdge_vlist_permutation; eauto.
        + apply bijective_listV_NoDup; auto.
        + apply bijective_vertices; auto.
        + apply bijective_listV_NoDup; auto.
        + apply bijective_vertices; auto.
      }
      assert (HpermE : Permutation (bijective_listE g) (e :: bijective_listE h)).
      {
        eapply addEdge_elist_permutation; eauto.
        + apply bijective_listE_NoDup; auto.
        + apply bijective_edges; auto.
        + apply bijective_listE_NoDup; auto.
        + apply bijective_edges; auto.
      }
      apply Permutation_length in HpermV, HpermE. 
      simpl in HpermV, HpermE. 
      pose proof IHn h Hvalid H0. 
      rewrite ! Zlength_correct in *.
      lia.  
      Unshelve. auto. 
  }
  destruct (bijective_listE g) eqn: Hel. 
  {
    rewrite Zlength_nil.
    assert (Zlength (bijective_listV g) = 1)%Z.
    { 
      pose proof (bijective_vertices g g_valid) as vlist_iff.
      pose proof (bijective_listV_NoDup g g_valid) as vlist_nodup.
      pose proof (bijective_edges g g_valid) as elist_iff.
      destruct (bijective_listV g) as [|r [|x xs]].
      - rewrite Zlength_nil in H; lia.
      - rewrite Zlength_cons, Zlength_nil; lia.
      - assert (Hr : vvalid g r) by (apply vlist_iff; simpl; auto).
        assert (Hx : vvalid g x) by (apply vlist_iff; simpl; auto).
        assert (Hrx : r <> x).
        { intro Heq; subst.
          simpl in vlist_nodup.
          inversion vlist_nodup; subst.
          apply H3; simpl; auto. }
        destruct (reachable_valid_epath g r x (tree_connected g g_tree r x Hr Hx))
          as [p Hpath].
        destruct p as [|a p].
        + apply valid_epath_nil_inv in Hpath; contradiction.
        + apply valid_epath_cons_inv in Hpath as [y [Hstep _]].
          assert (Ha_valid : evalid g a) by (eapply step_evalid; eauto).
          apply elist_iff in Ha_valid. 
          rewrite Hel in Ha_valid; contradiction.
    }
    lia.
  } 
  apply H0 with (n := Z.to_nat (Zlength l)). 
  rewrite ! Zlength_cons; simpl. 
  rewrite Zlength_correct; lia.
Qed.


Context (r: G)
        {r_valid: gvalid r}
        {ew: EdgeWeight G E}.

Definition total_weight : G -> option Z :=
  fun g => fold_right Z_op_plus (Some 0%Z) (map (weight r) (bijective_listE g)).

Definition is_mst : G -> Prop := 
  fun g => min_object_of_subset Z_op_le 
          (fun g => gvalid g /\ tree g /\ subgraph_vertex_eq g r)          
          (total_weight) g. 


Lemma is_mst_legal:
  forall y, is_mst y -> gvalid y /\ tree y /\ subgraph_vertex_eq y r.
Proof.
  intros y Hmst.
  unfold is_mst, min_object_of_subset in Hmst.
  tauto.
Qed.

Lemma mst_edge_step:
  forall y u v e,
    is_mst y ->
    evalid y e ->
    step_aux r e u v ->
    step_aux y e u v.
Proof.
  intros y u v e Hmst Hevalid Hstep_r.
  pose proof (is_mst_legal y Hmst) as [Hyvalid [_ Hsub]].
  destruct (no_empty_edge y e Hyvalid Hevalid) as [x [z Hstep_y]].
  destruct Hsub as [_ Hsub_step].
  pose proof (Hsub_step x z e Hstep_y) as Hstep_r'.
  eapply step_aux_unique_undirected in Hstep_r as [[] | []]; eauto; subst.
  - subst; exact Hstep_y.
  - subst; apply step_sym; exact Hstep_y.
Qed.

End TREE_OPERATION.
