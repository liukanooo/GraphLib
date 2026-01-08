(* Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight.
From MaxMinLib Require Import MaxMin Interface.
From ListLib Require Import Base.Inductive.

Import SetsNotation.

Local Open Scope sets.
Local Open Scope Z.

(** 
  Dijkstra 算法证明所需的辅助引理库
  
  本文件提供 Dijkstra 算法正确性证明所需的所有引理，
  使用抽象的类型类定义，与 eweight.v 保持一致。
*)

Section dijkstra.

Context {G V E: Type}
        {pg: Graph G V E}
        {gv: GValid G}
        (g: G).

Context {P: Type}
        {path: Path G V E P}
        {emptypath: EmptyPath G V E P path}
        {singlepath: SinglePath G V E P path}
        {concatpath: ConcatPath G V E P path}
        {destruct1npath: Destruct1nPath G V E P path emptypath singlepath concatpath}.

Context {ew: EdgeWeight G E}.

Notation step := (step g).
Notation reachable := (reachable g).


(** ===== 初始化相关引理 ===== *)

(** 引理1: 路径权重的非负性 (由边权重非负推出) *)
Lemma path_weight_nonneg: forall p,
  path_valid g p ->
  Z_op_le (Some 0) (path_weight g p).
Proof. 
Admitted.
  
(** 引理2：路径拼接的权重等于两段路径权重之和 *)
Lemma path_concat_weight: 
  forall (p1 p2: P),
    path_valid g p1 ->
    path_valid g p2 ->
    tail p1 = head p2 ->
    path_weight g (concat_path p1 p2) = Z_op_plus (path_weight g p1) (path_weight g p2).
Proof.
  intros.
  unfold path_weight. 
  rewrite concat_path_edge.
  rewrite map_app.
  rewrite Zlist_sum_app.
  reflexivity.
Qed.

(** 引理3: 路径扩展权重单调性 (Dijkstra 核心性质), 即路径的拼接会使路径的权重和增加 *)
Lemma path_weight_monotone_prefix: forall p1 p2,
  path_valid g p1 ->
  path_valid g p2 ->
  tail p1 = head p2 ->
  Z_op_le (path_weight g p1) (path_weight g (concat_path p1 p2)).
Proof.
  intros.
  rewrite path_concat_weight; auto.
  pose proof path_weight_nonneg p1 H.
  pose proof path_weight_nonneg p2 H0.
  destruct (path_weight g p1); destruct (path_weight g p2); simpl in *; auto.
  lia.
Qed.


(** ===== 1. 初始化性质 ===== *)

(** 引理4: (初始状态)
  对于源点 src：
  - dist[src] = g_zero，且这是真正的最短距离（空路径）
  
  对于其他顶点 v ≠ src：
  - dist[v] = W_inf，表示通过空集不可达
*)
Lemma init_dist_from_source: forall (src: V),
  min_weight_distance g src src (Some 0).
Proof.
  intros.
  unfold min_weight_distance.
  left. split; [|simpl; auto]. 
  assert (Hweight: path_weight g (empty_path src) = Some 0).
  { unfold path_weight. 
    erewrite empty_path_edge; eauto. } 
  exists (empty_path src); split; auto. 
  split. 
  * split; [|split]. 
    + apply empty_path_valid. 
    + apply Some_inversion. 
      erewrite (head_valid g); [|apply empty_path_valid]. 
      rewrite empty_path_vertex. 
      reflexivity. 
    + apply Some_inversion. 
      erewrite (tail_valid g); [|apply empty_path_valid]. 
      rewrite empty_path_vertex. 
      reflexivity. 
  * intros. 
    rewrite Hweight. 
    apply path_weight_nonneg. 
    apply H. 
Qed.

(** 引理5: (初始状态)
  对于其他顶点 v ≠ src，初始状态下通过空集不可达
*)
Lemma init_dist_others_unreachable: forall (v: V),
  v <> src ->
  min_weight_distance_in_vset g src v ∅ None.
Proof. 
  intros. 
  unfold min_weight_distance_in_vset. 
  right; split; [intros p Hp; exfalso|reflexivity]. 
  destruct Hp as [Hpath Hbody].
  destruct Hpath as [Hvalid [Hhd Htl]]. 
  unfold interior in Hbody. 
  destruct (vertex_in_path p) eqn:Heq. 
  - eapply path_valid_vertex_not_nil; eauto. 
  - simpl in Hbody. 
    destruct l. 
    * subst. 
      apply H. 
      apply Some_inversion. 
      erewrite head_valid; eauto.
      erewrite tail_valid; eauto. 
      rewrite Heq. 
      reflexivity. 
    * subst. 
      destruct l. 
      + simpl in Hbody. 
      Print removelast.  
      simpl in Hbody. 
Admitted.

(** ===== 2. 路径结构引理 (关键分解) ===== *)

(**
  First-Exit Decomposition (首次离开分解引理)
  
  这是证明 Dijkstra 贪心选择性质最关键的步骤。
  如果一条从 src 到 u 的路径 p (u ∉ visited) 存在，且 src ∈ visited，
  那么 p 可以分解为 p_pre ++ (x, y) ++ p_rem，其中：
  1. p_pre 完全在 visited 内部 (中间节点 ∈ visited，终点 x ∈ visited)
  2. (x, y) 是第一条离开 visited 的边 (x ∈ visited, y ∉ visited)
  3. p_rem 是剩余路径
*)
Lemma path_first_exit_decomposition: 
  forall (u: V) (p: P) (visited: V -> Prop),
    path_valid g p ->
    head p = src ->
    tail p = u ->
    src ∈ visited ->
    ~ u ∈ visited ->
    exists p_pre x y e p_rem,
      (* 结构分解 *)
      p = concat_path (concat_path p_pre (single_path x y e)) p_rem /\
      path_valid g p_pre /\
      path_valid g p_rem /\
      step_aux g e x y /\
      (* 集合性质 *)
      is_path_through_vset g p_pre src x visited /\  (* p_pre 中间点在 visited 中 *)
      x ∈ visited /\
      ~ y ∈ visited. (* y 是第一个未访问点 *)
Admitted.

(** ===== 辅助工具 ===== *)

(** 三角不等式 (用于通用的距离性质推导) *)
Lemma triangle_inequality:
  forall (u v w: V) (d_uw d_uv d_vw: option Z),
    min_weight_distance g u w d_uw ->
    min_weight_distance g u v d_uv ->
    min_weight_distance g v w d_vw ->
    Z_op_le d_uw (Z_op_plus d_uv d_vw).
Admitted.

(** 集合单调性 *)
Lemma min_distance_vset_monotone:
  forall (u v: V) (vset1 vset2: V -> Prop) (d1 d2: option Z),
    min_weight_distance_in_vset g u v vset1 d1 ->
    min_weight_distance_in_vset g u v vset2 d2 ->
    vset1 ⊆ vset2 ->
    Z_op_le d2 d1.
Admitted.


(** ===== 松弛操作相关引理 ===== *)

(**
  Dijkstra 松弛操作的正确性
  
  假设：
  - dist[u] 已经是从 src 到 u 的最短距离
  - dist[v] 是从 src 到 v、仅通过 visited 的最短距离
  - 存在边 e: u -> v，权重为 w_e
  
  则：松弛后 dist[v] = min(dist[v], dist[u] + w_e) 是
      从 src 到 v、仅通过 visited ∪ {u} 的最短距离
  
  证明思路：
  1. 下界：任何通过 visited ∪ {u} 的路径权重 ≥ min(dist[v], dist[u] + w_e)
     - 不经过 u：权重 ≥ dist[v]
     - 经过 u：最短的是 src ~> u -> v，权重 ≥ dist[u] + w_e
  2. 可达：存在路径达到这个下界
*)
Lemma dijkstra_relax_correct:
  forall (src u v: V) (visited: V -> Prop) (e: E) 
         (dist_u dist_v w_e: option Z),
    (* 前提条件 *)
    u ∈ visited ->  (* u 已经被访问 *)
    step_aux g e u v ->  (* 存在边 u -> v *)
    weight g e = w_e ->
    (* dist[u] 是最终的最短距离 *)
    min_weight_distance g src u dist_u ->
    (* dist[v] 是通过 visited 的最短距离 *)
    min_weight_distance_in_vset g src v visited dist_v ->
    (* 结论：松弛后是通过 visited ∪ {u} 的最短距离 *)
    min_weight_distance_in_vset g src v (visited ∪ [u]) 
      (Z_op_min dist_v (Z_op_plus dist_u w_e)).
Admitted.


(** ===== 贪心选择的正确性引理 ===== *)

(**
  贪心选择引理（Dijkstra 算法的核心）
  
  假设：
  - 所有已访问顶点的 dist 值都是最终的最短距离
  - 所有未访问顶点的 dist 值是仅通过已访问顶点的最短距离
  - 选择 dist 值最小的未访问顶点 u
  
  则：dist[u] 已经是从 src 到 u 的真正最短距离
  
  证明（反证法）：
  假设存在更短的路径 P: src ~> u，权重 < dist[u]。
  
  考虑 P 上第一个离开 visited 集合的顶点 v：
  - v 的前驱 w 在 visited 中
  - 根据循环不变量，dist[w] = 真正的最短距离到 w
  - 经过 w 到达 v 的路径权重 ≥ dist[w] + weight(w, v)
  - 根据循环不变量，dist[v] ≤ dist[w] + weight(w, v)
    （因为 dist[v] 是通过 visited 的最短距离，包括经过 w 的路径）
  
  所以：dist[v] ≤ weight(P 的前缀到 v) < weight(P) < dist[u]
  
  但这与"选择了 u"矛盾，因为我们应该选择 dist 值最小的顶点 v。
  
  关键：这个证明依赖于边权重非负！
*)
Lemma greedy_choice_correct:
  forall (src u: V) (visited: V -> Prop) (dist: V -> option Z),
    (* 前提：循环不变量成立 *)
    (forall v, v ∈ visited -> min_weight_distance g src v (dist v)) ->
    (forall v, ~ v ∈ visited -> min_weight_distance_in_vset g src v visited (dist v)) ->
    (* u 是未访问顶点中 dist 值最小的 *)
    ~ u ∈ visited ->
    dist u <> None ->
    (forall v, ~ v ∈ visited -> dist v <> None -> Z_op_le (dist u) (dist v)) ->
    (* 结论：dist[u] 是最终的最短距离 *)
    min_weight_distance g src u (dist u).
Proof.
  intros src u visited dist H_visited_correct H_unvisited_optimal 
         H_u_unvisited H_u_finite H_u_minimal.
  (* 
    证明提示：
    1. 使用反证法：假设存在更短的路径 P
    2. 分析 P 上第一个离开 visited 的顶点
    3. 使用非负权重性质
    4. 推导矛盾
    
    需要的辅助引理：
    - 路径分解：可以在任意顶点分解路径
    - 权重单调性：部分路径权重 ≤ 完整路径权重（非负权重）
    - 最短距离的下界性质
  *)
Admitted.


(** ===== 非负权重的性质引理 ===== *)

(**
  路径延长不会减少权重（非负权重的关键性质）
  
  如果 p1 是 p2 的前缀，则 weight(p1) ≤ weight(p2)
*)
Lemma path_extension_weight_monotone:
  forall (u v w: V) (p_short p_long: P),
    is_path g p_short u v ->
    is_path g p_long u w ->
    In v (vertex_in_path p_long) ->
    (* p_short 相当于 p_long 的前缀 *)
    Z_op_le (path_weight g p_short) (path_weight g p_long).
Admitted.


End dijkstra.
 *)
