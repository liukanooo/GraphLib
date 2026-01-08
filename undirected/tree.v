Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.reachable.path.
Require Import GraphLib.reachable.epath.
Require Import GraphLib.subgraph.subgraph.
Require Import GraphLib.Syntax.
Require Import SetsClass.
Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Lia.
Local Open Scope list.

Import ListNotations.
Import SetsNotation.
Local Open Scope sets.

(** * 树的基本定义 *)

Class Tree 
    (G V E: Type) 
    {pg: Graph G V E} 
    {gv: GValid G} 
    (A: Type) 
    {path: Path G V E A}:=
{
  tree_connected: forall g, gvalid g -> connected g;
  tree_no_curcuit: forall g, gvalid g -> ~ exists u p, is_simple_epath g u p u;
}.


Section TREE.
Context {G V E: Type} 
        {pg: Graph G V E} 
        {gv: GValid G}
        {stepvalid: StepValid G V E}
        {step_aux_unique_undirected: StepUniqueUndirected G V E}
        {undirectedgraph: UndirectedGraph G V E}
        {A: Type}
        {path: Path G V E A}
        {emptypath: EmptyPath G V E A path}
        {singlepath: SinglePath G V E A path}
        {concatpath: ConcatPath G V E A path}
        {tree: @Tree G V E pg gv A path}
        {g: G}
        {gvalid: gvalid g}.

Lemma tree_have_path: 
  forall u v,
  vvalid g u ->
  vvalid g v ->
  exists p, valid_epath g u p v.
Proof.

Admitted.


End TREE.


