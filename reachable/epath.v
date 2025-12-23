Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic Zweight.
From MaxMinLib Require Import MaxMin Interface.
From ListLib Require Import Base.Inductive Base.Positional General.NoDup.

Import SetsNotation.

Local Open Scope sets.

Section EPATH.

Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {P: Type}
        {path: @Path G V E pg gv P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

(* 基于原始Type Class destruct1n的导出定义valid_epath在list E上的归纳法 *)

(* epath: 存在一个P，使得P的edgeList等于它 *)
Definition valid_epath: 
  G -> V -> list E -> V -> Prop := 
  fun g u p v => exists P: P, 
    path_valid g P /\ 
    edge_in_path P = p /\ 
    hd_error (vertex_in_path P) = Some u /\ 
    tl_error (vertex_in_path P)= Some v.


(* empty_path能构造出平凡的epath *)
Lemma valid_epath_empty: forall g v,
  valid_epath g v nil v.
Proof.
  intros.
  unfold valid_epath.
  exists (empty_path v).
  assert (path_valid g (empty_path v)) by (apply empty_path_valid).
  split; [auto|].
  split.
  - apply (empty_path_edge g).
  - rewrite empty_path_vertex. simpl. auto.
Qed.

(* nil的epath对应 (empty_path v) *)
Lemma valid_epath_nil_inv:
  forall g u v,
  valid_epath g u nil v ->
  u = v.
Proof.
  intros.
  destruct H as [path_obj [H_pval [H_edges [H_hd H_tl]]]].
  pose proof (vpath_iff_epath g path_obj H_pval) as [Hlen _].
  rewrite H_edges in Hlen. simpl in Hlen.
  destruct (vertex_in_path path_obj) as [| x [| y l]].
  - simpl in Hlen; lia.
  - simpl in H_hd; injection H_hd as Hu; subst.
    simpl in H_tl; injection H_tl as Hv; subst.
    reflexivity.
  - simpl in Hlen; lia.
Qed.

(* single_path能构造出单步的epath *)
Lemma valid_epath_single: forall g u v e,
  step_aux g e u v ->
  valid_epath g u (e :: nil) v.
Proof.
  intros.
  unfold valid_epath.
  exists (single_path u v e). split; [apply single_path_valid; auto|].
  split; [apply single_path_edge|].
  split; [rewrite single_path_vertex; simpl; auto|].
  rewrite single_path_vertex; simpl; auto.
Qed.

(* epath的singleton对应一个step关系 *)
Lemma valid_epath_single_inv:
  forall g u v e,
  valid_epath g u (e :: nil) v ->
  step_aux g e u v.
Proof.
  intros. 
  destruct H as [p [Hp [Hedge [Hhd Htl]]]]. 
  pose proof (vpath_iff_epath g p Hp) as [Hlen Hstep]. 
  rewrite Hedge in Hlen; simpl in Hlen. 
  rewrite <- nth_error_O in Hhd. 
  unfold tl_error in Htl; rewrite Hlen in Htl.  
  pose proof Hstep g 0%nat u v e ltac:(rewrite Hedge; simpl; lia)
  ltac:(rewrite Hedge; simpl; auto) Hhd Htl. 
  apply H.
Qed.



(* epath的++也是epath *)
Lemma valid_epath_app:
  forall g u p1 v p2 w,
    valid_epath g u p1 v ->
    valid_epath g v p2 w ->
    valid_epath g u (p1 ++ p2) w.
Proof.
  intros.
  destruct H as [P1 [Hp1 [Hedge1 [Hhd1 Htl1]]]].
  destruct H0 as [P2 [Hp2 [Hedge2 [Hhd2 Htl2]]]].
  
  exists (concat_path P1 P2).
  
  assert (Hconnect: tail P1 = head P2).
  { 
    apply Some_inversion.
    erewrite tail_valid by eauto.
    erewrite head_valid by eauto.
    rewrite Htl1, Hhd2. reflexivity. 
  } 
  assert (Hvalid: path_valid g (concat_path P1 P2)) by (apply concat_path_valid; auto).
  split; [|split; [|split]]; auto.
  - rewrite concat_path_edge. rewrite Hedge1, Hedge2. reflexivity.
  - rewrite concat_path_vertex.
    destruct (vertex_in_path P1); [discriminate|simpl; auto].
  - rewrite concat_path_vertex.
    destruct (vertex_in_path P2); [discriminate|simpl in *; auto].
    destruct (list_snoc_destruct l); [subst; simpl in *|].
    * unfold tl_error in Htl2; simpl in Htl2. 
      inversion Hhd2 ; inversion Htl2; subst. 
      rewrite app_nil_r; auto. 
    * destruct H as [? []]; subst. 
      rewrite! app_assoc.
      rewrite tl_error_last.
      rewrite app_comm_cons in Htl2.
      rewrite tl_error_last in Htl2.
      auto. 
Qed.

(* cons构造的epath以分解为一个单步和一个epath *)
Lemma valid_epath_cons_inv:
  forall g u e p w,
  valid_epath g u (e :: p) w ->
  exists v, step_aux g e u v /\ valid_epath g v p w.
Proof. 
  intros.
  destruct H as [p0 [Hp [Hedge [Hhd Htl]]]].
  pose proof (destruct_1n_spec g p0 Hp).
  destruct (destruct_1n_path p0).
  - (* Base Case: P implies empty edges *)
    subst. rewrite (empty_path_edge g) in Hedge. discriminate.
  - (* Step Case *)
    destruct H as [Hp' [Hhd' [Hstep Heq]]].
    subst p0.
    rewrite concat_path_edge in Hedge.
    rewrite single_path_edge in Hedge.
    simpl in Hedge. injection Hedge as He Hp_eq. subst.
    
    rewrite concat_path_vertex in Hhd.
    rewrite single_path_vertex in Hhd.
    simpl in Hhd. injection Hhd as Hu. subst u0.

    exists (head p1). split; auto.
    
    exists p1. split; [|split; [|split]]; auto.
    + erewrite head_valid; eauto.
    + rewrite concat_path_vertex in Htl.
      rewrite single_path_vertex in Htl.
      destruct (vertex_in_path p1) eqn:Hvpath.
      * eapply path_valid_vertex_not_nil in Hp'; congruence.
      * simpl in Htl. 
        destruct (list_snoc_destruct l); [subst; simpl in *|].
        { unfold tl_error in Htl; simpl in Htl.
          unfold tl_error; simpl.
          erewrite head_valid in Htl; eauto. 
          rewrite Hvpath in Htl; simpl in Htl. 
          auto. }
        { destruct H as [? []]; subst. 
          rewrite app_comm_cons.
          rewrite tl_error_last.
          simpl in Htl. 
          rewrite! app_comm_cons in Htl.
          rewrite tl_error_last in Htl.
          auto. }
Qed.

(* ++构成的epath能够被拆散 *)
Lemma valid_epath_app_inv:
  forall g u p1 p2 w,
  valid_epath g u (p1 ++ p2) w ->
  exists v, valid_epath g u p1 v /\ valid_epath g v p2 w.
Proof.
  intros g u p1.
  revert u.
  induction p1; intros u p2 w H.
  - simpl in H.
    exists u; split; auto.
    apply valid_epath_empty.
  - (* p1 = a :: p1 *)
    rewrite <- app_comm_cons in H.
    apply valid_epath_cons_inv in H.
    destruct H as [v' [Hstep Hvalid_rest]].
    apply IHp1 in Hvalid_rest.
    destruct Hvalid_rest as [target [Hsub1 Hsub2]].
    exists target. split; auto.
    apply (valid_epath_app g u (a::nil) v' p1 target); auto.
    apply valid_epath_single; auto.
Qed.

(* epath的单步cons也是epath *)
Lemma valid_epath_cons:  
  forall g u e p v w,
  step_aux g e u v ->
  valid_epath g v p w ->
  valid_epath g u (e :: p) w.
Proof.
  intros.
  replace (e :: p) with ((e :: nil) ++ p) by auto.
  eapply valid_epath_app; [| apply H0].
  apply valid_epath_single; auto.
Qed.

(* epath的尾部接上单步也是epath *)
Lemma valid_epath_snoc:
  forall g u p v w e,
  valid_epath g u p v ->
  step_aux g e v w ->
  valid_epath g u (p ++ e :: nil) w.
Proof.
  intros.
  eapply valid_epath_app.
  - apply H.
  - apply valid_epath_single; auto.
Qed.

(* epath能够从尾部拆分 *)
Lemma valid_epath_snoc_inv:
  forall g u p e w,
  valid_epath g u (p ++ e :: nil) w ->
  exists v, valid_epath g u p v /\ step_aux g e v w.
Proof.
  intros.
  apply valid_epath_app_inv in H.
  destruct H as [v [Hpre Hsuf]].
  apply valid_epath_single_inv in Hsuf.
  exists v. auto.
Qed.

(* epath上对list E的1n归纳法则 *)
Lemma valid_epath_ind_1n:
  forall g (X : V -> list E -> V -> Prop)
  (Hbase: forall v, X v nil v)
  (Hind: forall u v e p w,
    step_aux g e u v -> 
    valid_epath g v p w -> 
    X v p w ->
    X u (e :: p) w),
  forall u p v, valid_epath g u p v -> X u p v.
Proof.
  intros g X Hbase Hind u p v Hvalid.
  revert u v Hvalid.
  induction p as [|e p IH]; intros u v Hvalid.
  - (* Base Case: nil *)
    apply valid_epath_nil_inv in Hvalid. subst.
    apply Hbase.
  - (* Step Case: e :: p *)
    apply valid_epath_cons_inv in Hvalid.
    destruct Hvalid as [v_next [Hstep Hvalid_rest]].
    apply Hind with (v := v_next); auto.
Qed.

(* epath 上对 list E 的 n1 归纳法则 *)
Lemma valid_epath_ind_n1:
  forall g (X : V -> list E -> V -> Prop)
  (Hbase: forall v, X v nil v)
  (Hind: forall u p v w e,
    valid_epath g u p v -> 
    X u p v ->
    step_aux g e v w -> 
    X u (p ++ e :: nil) w),
  forall u p v, valid_epath g u p v -> X u p v.
Proof.
  intros g X Hbase Hind u p v H.
  revert u v H.
  induction p using rev_ind; intros u v H.
  - apply valid_epath_nil_inv in H. subst.
    apply Hbase.
  - apply valid_epath_snoc_inv in H.
    destruct H as [v_mid [H_prefix H_step]].
    apply Hind with (v := v_mid).
    + exact H_prefix.
    + apply IHp with (v := v_mid).
      exact H_prefix.
    + exact H_step.
Qed.

(* epath能够被n1分解，即平凡的单步或epath++单步 *)
Lemma valid_epath_inv_n1:
  forall g u p v,
  valid_epath g u p v ->
  (u = v /\ p = nil) \/
  (exists p' w e, p = p' ++ e :: nil /\ valid_epath g u p' w /\ step_aux g e w v).
Proof.
  intros.
  destruct p as [| x l] using rev_ind.
  - left. split; [eapply valid_epath_nil_inv; eauto | reflexivity].
  - right. apply valid_epath_snoc_inv in H as [w [Hpre Hstep]].
    exists l, w, x. auto.
Qed.

(* epath能够被1n分解，即平凡的单步或单步++epath *)
Lemma valid_epath_inv_1n: 
  forall g u p v,
  valid_epath g u p v ->
  (u = v /\ p = nil) \/
  (exists e w p', p = e :: p' /\ step_aux g e u w /\ valid_epath g w p' v).
Proof.
  intros.
  destruct p as [|e p].
  - apply valid_epath_nil_inv in H; subst; auto.
  - apply valid_epath_cons_inv in H as [w [Hstep Hvalid_rest]]. 
    right; exists e; exists w; exists p; split; [|split]; auto.
Qed.

(* epath能够被转换为reachable *)
Lemma valid_epath_reachable:
  forall g u p v,
  valid_epath g u p v ->
  reachable g u v.
Proof.
  intros.
  revert u p v H.
  apply valid_epath_ind_1n.
  - (* Base: nil *)
    intros. reflexivity.
  - (* Step: e :: p *)
    intros.
    eapply step_reachable_reachable.
    exists e. eauto. auto.
Qed.

(* reachable能够被转换为epath *)
Lemma reachable_valid_epath:
  forall g u v,
  reachable g u v ->
  exists p, valid_epath g u p v.
Proof.
  intros.
  unfold reachable in H.
  induction_1n H.
  - exists nil. apply valid_epath_empty.
  - destruct IHrt as [p Hvalid].
    destruct H0 as [e Hstep].
    exists (e :: p).
    eapply valid_epath_cons; eauto.
Qed.

(* epath上的简单路径：不经过重复边 *)
Definition is_simple_epath (g: G) (u: V) (p: list E) (v: V): Prop :=
  valid_epath g u p v /\ NoDup p.

(* 移除epath中的环 *)
(* 需要边的某种唯一性；有向图的边唯一性强于无向图的边唯一性，所有我们只证明后者 *)
Lemma valid_epath_shorten_cycle
  {step_aux_unique_undirected: forall g e x1 y1 x2 y2, step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1)}: 
  forall g u v l1 e l2 l3,
  valid_epath g u (l1 ++ e :: l2 ++ e :: l3) v ->
  exists q, valid_epath g u q v /\ length q < length (l1 ++ e :: l2 ++ e :: l3).
Proof.
  intros g u v l1 e l2 l3 H.
  apply valid_epath_app_inv in H.
  destruct H as [u_mid [H_path_l1 H_rest1]].
  apply valid_epath_cons_inv in H_rest1.
  destruct H_rest1 as [v_mid [H_step1 H_rest2]].
  apply valid_epath_app_inv in H_rest2.
  destruct H_rest2 as [u_mid2 [H_path_l2 H_tail]].
  apply valid_epath_cons_inv in H_tail.
  destruct H_tail as [v_mid2 [H_step2 H_path_l3]].
  pose proof (step_aux_unique_undirected g e u_mid v_mid u_mid2 v_mid2 H_step1 H_step2) 
  as [[]|[]]; subst.
  - exists (l1 ++ e :: l3).
    split.
    + eapply valid_epath_app; eauto.
      eapply valid_epath_cons; eauto.
    + rewrite !length_app; simpl.
      rewrite !length_app; simpl. lia.
  - exists (l1 ++ l3).
    split.
    + eapply valid_epath_app; eauto.
    + rewrite !length_app; simpl. 
      rewrite !length_app; simpl. lia.
Qed.

(* 任意两点之间的epath能够被转换为简单的epath *)
(* 前提：给出无向图或有向图的step_aux的type class *)
(* 这也提示出step_aux或许处于一个不正确的位置 *)
Theorem valid_epath_simple 
{step_aux_unique_undirected: forall g e x1 y1 x2 y2, step_aux g e x1 y1 -> step_aux g e x2 y2 -> 
  (x1 = x2 /\ y1 = y2) \/ (x1 = y2 /\ x2 = y1)}:
  forall g u p v,
  valid_epath g u p v ->
  exists q, is_simple_epath g u q v.
Proof.
  intros g u p v H_valid.
  remember (length p) as n.
  revert u p v H_valid Heqn.
  induction n using lt_wf_ind; intros u p v H_valid Heqn.
  destruct (classic (NoDup p)).
  - exists p. split; auto.
  - apply Nodup_exists_repetition in H0.
    destruct H0 as [e [l1 [l2 [l3 H_eq]]]].
    subst p.
    pose proof (@valid_epath_shorten_cycle step_aux_unique_undirected g u v l1 e l2 l3 H_valid) as [q [H_valid_q H_len_q]].
    apply (H (length q)) in H_valid_q; auto.
    lia.
Qed.


(* 我们也可以基于epath而不是path进行最短路径的定义和证明。 *)

Context {ew: EdgeWeight G E}.

(* vset就等于path去掉首尾后的所有点的集合 *)
Definition is_epath_through_exactly_vset 
  (g: G) (u: V) (p: list E) (v: V) (vset: V -> Prop): Prop :=
  valid_epath g u p v /\ 
  forall x, x ∈ vset <-> 
  exists p1 p2, 
    p1 <> nil /\ 
    p2 <> nil /\ 
    p1 ++ p2 = p /\ 
    valid_epath g x p1 v /\ 
    valid_epath g v p2 x. 

Local Open Scope Z.
(* vset是path中间节点可以经过的节点集合，但是这个定义相比Path上的定义比较抽象 *)
Definition is_epath_through_vset
  (g: G) (u: V) (p: list E) (v: V) (vset: V -> Prop): Prop :=
  forall S, is_epath_through_exactly_vset g u p v S -> vset ⊆ S. 

Definition epath_weight (g: G) (p: list E): option Z :=
  fold_right Z_op_plus (Some 0) (map (weight g) p). 

Definition min_object_weight_epath (g: G) (u: V) (v: V) (p: list E): Prop :=
  min_object_of_subset Z_op_le (fun p => valid_epath g u p v) (epath_weight g) p. 

Definition min_value_weight_epath (g: G) (u: V) (v: V) (z: option Z): Prop :=
  min_value_of_subset_with_default Z_op_le (fun p => valid_epath g u p v) (epath_weight g) None z. 

Definition min_object_weight_epath_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (p: list E): Prop :=
  min_object_of_subset Z_op_le (fun p => is_epath_through_vset g u p v vset) (epath_weight g) p. 

Definition min_value_weight_epath_in_vset (g: G) (u: V) (v: V) (vset: V -> Prop) (z: option Z): Prop :=
  min_value_of_subset_with_default Z_op_le (fun p => is_epath_through_vset g u p v vset) (epath_weight g) None z. 

End EPATH.