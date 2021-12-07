theory Directed_Graph
  imports Main Graph_Theory.Graph_Theory
begin

definition Verts :: "nat set" where
  "Verts = { 0, 1, 2 }"

definition Arcs :: "(nat * nat) set" where
  "Arcs = { (0, 1), (1, 2) }"

definition graph :: "(nat, (nat * nat)) pre_digraph" where
  "graph = \<lparr> verts = Verts, arcs = Arcs, tail = fst, head = snd \<rparr>"

interpretation pre_digraph graph .
interpretation wf_digraph graph
  by unfold_locales (auto simp: graph_def Verts_def Arcs_def)

end