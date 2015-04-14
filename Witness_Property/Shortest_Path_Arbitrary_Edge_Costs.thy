theory Shortest_Path_Arbitrary_Edge_Costs

(*
  This theory uses the graph library and  
  several lemmas that were proven in the 
  shortest path theory
*)
imports 
  "../Graph_Theory/Graph_Theory"
  "Shortest_Path_Theory"
begin
(*
section {*
  Shortest Path (with general edge costs)
*}
*)
(*
text
{*
  In this theory,  we give a formal proof of the correctness of an axiomatic characterization of the 
  single-source shortest path problem for directed graphs with a general cost functions $c:E\to\mathbb{R}$.
  The axioms here are involved because we have to account for negative cycles in the graph. 
  The axioms are summarized in the the isabelle locale  @{term shortest_paths_neg_cyc}. 

  This formalization also serves as a self-contained formal specification for the LEDA shortest path 
  checker. The proof could be viewed as a refinement proof stating that if the checker corresponds 
  to the  the low-level specification described in @{term shortest_paths_neg_cyc} then the checker is correct 
  (implies it's high level specification).
*}

text{* 
  Given a directed graph $G=(V,E)$, the graph $G$ is \emph{wellformed} if each of the endpoints of 
  $E$ are in $V$ and $G$ is \emph{finite} if it has a  finite vertex set $V$ and a finite edge set $E$.
  The @{term shortest_paths_init} locale states the following: Let 
  @{term G} be a finite wellformed directed graph (assumption @{term graphG}),  
  @{term s} be a vertex,  
  @{term c} be a cost function on edges,
  @{term num} be a  function from vertices to natural numbers,
  @{term parent_edge} be a partial function from vertices to edges, and
  @{term dist} be a distance function from vertices to real numbers.
*}
*)
locale shortest_paths_init = 
  fixes G :: "('a, 'b) pre_digraph" (structure)
  fixes s :: "'a"
  fixes c :: "'b \<Rightarrow> real"
  fixes num :: "'a \<Rightarrow> nat"
  fixes parent_edge :: "'a \<Rightarrow> 'b option"
  fixes dist :: "'a  \<Rightarrow> ereal"
  assumes graphG: "fin_digraph G"
(*
text{* 
  Let 
  $V_f$ be the set of vertices in @{term G} with finite distance, 
  $V_p$ be the set of vertices in @{term G} with distance $\infty$, and
  $V_n$ be the set of vertices in @{term G} with distance $-\infty$.
  
*}
*)
abbreviation (in shortest_paths_init) V\<^sub>f :: "'a set" where
  "V\<^sub>f \<equiv> {v. v \<in> verts G \<and> (\<exists>r. dist v = ereal r)}"

abbreviation (in shortest_paths_init) V\<^sub>p :: "'a set" where
  "V\<^sub>p \<equiv> {v. v \<in> verts G \<and> dist v = \<infinity>}"

abbreviation (in shortest_paths_init) V\<^sub>n :: "'a set" where
  "V\<^sub>n \<equiv> {v. v \<in> verts G \<and> dist v = -\<infinity>}"
(*
text{* 
  The @{term shortest_paths_reachable} locale summarizes assumptions that imply that there exists a 
  tree rooted at @{term s} that covers exactly the vertices in @{term G} that are not in $V_p$. 
  The tree is represented using the @{term parent_edge} function, which returns for each vertex other 
  than @{term s} its parent edge in the tree and @{term num} which returns how far a vertex is from the 
  root.
*}
*)
locale shortest_paths_reachable = 
  shortest_paths_init +
  assumes s_assms: 
    "s \<in> verts G" 
   (* "s \<notin> V\<^sub>p" 
    "parent_edge s = None" *)
    "num s = 0"
  assumes  pna: 
    "\<And>v.  \<lbrakk>v \<in> verts G; v \<noteq> s; v \<notin> V\<^sub>p\<rbrakk> \<Longrightarrow>
    (\<exists>e \<in> arcs G. parent_edge v = Some e \<and> 
    head G e = v \<and> tail G e \<notin> V\<^sub>p \<and>
    num v  = num (tail G e) + 1)"
(*  assumes noPedge: "\<And>e. e\<in>arcs G \<Longrightarrow> 
    tail G e \<notin> V\<^sub>p \<Longrightarrow> head G e \<notin> V\<^sub>p"*)

sublocale shortest_paths_reachable \<subseteq> fin_digraph G
  using graphG by auto

definition (in shortest_paths_reachable) enum :: "'a \<Rightarrow> enat" where
  "enum v = (if (dist v = \<infinity> \<or> dist v = - \<infinity>) then \<infinity> else num v)"
(*
text{* 
  The @{term shortest_paths_basic} locale summarizes assumptions that imply that there exists a 
  tree rooted @{term s} that covers exactly the vertices in @{term G} that are not in $V_p$. 
  The tree is represented using the @{term parent_edge} function, which returns for each vertex other 
  than @{term s} its parent edge in the tree and @{term num} which returns how far a vertex is from the 
  root.
*}
*)
locale shortest_paths_basic = 
  shortest_paths_reachable +
  basic_just_sp G dist c s enum +
  assumes source_val: "(\<exists>v \<in> verts G. enum v \<noteq> \<infinity>) \<Longrightarrow> dist s = 0"
(*  assumes no_edge_Vn_Vf: 
    "\<And>e. e \<in> arcs G \<Longrightarrow> (tail G e) \<in> V\<^sub>n \<Longrightarrow>  (head G e) \<notin> V\<^sub>f"*)

function (in shortest_paths_reachable) pwalk :: "'a \<Rightarrow> 'b list" 
where
  "pwalk v = 
    (if (v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G)
      then [] 
      else pwalk (tail G (the (parent_edge v))) @ [the (parent_edge v)]
    )"
by auto 
termination (in shortest_paths_reachable) 
  using pna
  by (relation "measure num", auto, fastforce)


lemma (in shortest_paths_reachable) pwalk_simps:
  "v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G \<Longrightarrow> pwalk v = []"
  "v \<noteq> s \<Longrightarrow> dist v \<noteq> \<infinity> \<Longrightarrow> v \<in> verts G \<Longrightarrow> 
    pwalk v = pwalk (tail G (the (parent_edge v))) @ [the (parent_edge v)]"
by auto

definition (in shortest_paths_reachable) pwalk_verts :: "'a  \<Rightarrow> 'a set" where 
  "pwalk_verts v = {u. u \<in> set (awalk_verts s (pwalk v))}" 

locale shortest_paths_neg_cyc =
  shortest_paths_basic +
  fixes C :: "('a \<times>('b awalk)) set"
  assumes C_se: 
    "C \<subseteq> {(u, p). dist u \<noteq> \<infinity> \<and> awalk u p u \<and> awalk_cost c p < 0}"
  assumes int_neg_cyc: 
    "\<And>v. v \<in> V\<^sub>n \<Longrightarrow> 
      (fst ` C) \<inter> pwalk_verts v  \<noteq> {}"

locale shortest_paths_basic_pred = 
  shortest_paths_reachable +
  fixes pred :: "'a \<Rightarrow> 'b option" 
  assumes bj: "basic_just_sp_pred G dist c s enum pred" 
  assumes source_val: "(\<exists>v \<in> verts G. enum v \<noteq> \<infinity>) \<Longrightarrow> dist s = 0"
(*  assumes no_edge_Vn_Vf: 
    "\<And>e. e \<in> arcs G \<Longrightarrow> dist (tail G e) = - \<infinity> \<Longrightarrow> \<forall> r. dist (head G e) \<noteq> ereal r"*)


sublocale shortest_paths_basic_pred \<subseteq> shortest_paths_basic
  using shortest_paths_basic_pred_axioms 
  unfolding shortest_paths_basic_pred_def shortest_paths_basic_pred_axioms_def 
  shortest_paths_basic_def shortest_paths_basic_axioms_def 
  basic_just_sp_pred_def basic_just_sp_pred_axioms_def 
  basic_just_sp_def basic_just_sp_axioms_def
  by blast

lemma (in shortest_paths_reachable) num_s_is_min:
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "v \<notin> V\<^sub>p"
  shows "num v > 0"
     using pna[OF assms] by fastforce


theorem (in shortest_paths_reachable) path_from_root_Vr_ex:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "v \<notin> V\<^sub>p"
  shows  "\<exists>e. s \<rightarrow>\<^sup>* tail G e \<and>
          e \<in> arcs G \<and> head G e = v \<and> dist (tail G e) \<noteq> \<infinity> \<and>
          parent_edge v = Some e \<and> num v = num (tail G e) + 1"
using assms
proof(induct "num v - 1" arbitrary : v)
case 0
  obtain e where ee:
    "e \<in> arcs G" 
    "head G e = v" 
    "(tail G e) \<notin> V\<^sub>p" 
    "parent_edge v = Some e" 
    "num v = num (tail G e) + 1"
    using pna[OF 0(2-4)]  by fast
  have "tail G e = s" 
    using num_s_is_min[OF tail_in_verts [OF ee(1)] _ ee(3)] 
    ee(5) 0(1) by auto
  then show ?case using ee by auto
next
case (Suc n')
  obtain e where ee:
    "e \<in> arcs G" 
    "head G e = v" 
    "(tail G e) \<notin> V\<^sub>p" 
    "parent_edge v = Some e" 
    "num v = num (tail G e) + 1"
    using pna[OF Suc(3-5)] by fast
  then have ss: "tail G e \<noteq> s"
    using num_s_is_min tail_in_verts ee
    Suc(2) s_assms(2) by force
  have nst: "n' = num (tail G e) - 1"
    using ee(5) Suc(2) by presburger
  obtain e' where 
    reach: "s \<rightarrow>\<^sup>* tail G e'" and 
    e': "e' \<in> arcs G \<and> head G e' = tail G e \<and> (tail G e') \<notin> V\<^sub>p" 
    using Suc(1)[OF nst tail_in_verts[OF ee(1)] ss ee(3)] by blast
  from reach also have "tail G e' \<rightarrow> tail G e" using e'
    by (metis in_arcs_imp_in_arcs_ends)
  finally show ?case using e' ee by auto
qed


corollary (in shortest_paths_reachable) path_from_root_Vr:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<notin> V\<^sub>p"
  shows "s \<rightarrow>\<^sup>* v"
proof(cases "v = s")
case True thus ?thesis using assms by simp
next
case False
  obtain e where "s \<rightarrow>\<^sup>* tail G e" and "e \<in> arcs G" and "head G e = v"
      using path_from_root_Vr_ex[OF assms(1) False assms(2)] by blast
  then have "s \<rightarrow>\<^sup>* tail G e" and "tail G e \<rightarrow> v"
    by (auto intro: in_arcs_imp_in_arcs_ends)
  then show ?thesis by (rule reachable_adj_trans)
qed


corollary (in shortest_paths_reachable) not_Vp_\<mu>_less_inf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<notin> V\<^sub>p"
  shows "\<mu> c s v \<noteq> \<infinity>"
  using assms path_from_root_Vr \<mu>_reach_conv by force

lemma (in shortest_paths_basic) enum_not0:
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  shows "enum v \<noteq> enat 0"
  using pna[OF assms(1,2)] assms unfolding enum_def by auto
(*
text{*
  Assumptions: source_val s_assms 
  Important used lemmas : dist_ge_\<mu> dist_le_\<mu>
*}
*)

lemma (in shortest_paths_basic) dist_Vf_\<mu>:
  fixes v :: 'a
  assumes vG: "v \<in> verts G"
  assumes "\<exists>r. dist v = ereal r"
  shows "dist v = \<mu> c s v"
proof -
  have ds: "dist s =  0" 
    using assms source_val unfolding enum_def by force
  have ews:"awalk s [] s" 
    using s_assms(1) unfolding awalk_def by simp
  have mu: "\<mu> c s s = ereal 0" 
    using min_cost_le_walk_cost[OF ews, where c=c] 
    awalk_cost_Nil ds  dist_le_\<mu>[OF s_assms(1)] zero_ereal_def
    by simp
  thus ?thesis 
    using ds assms dist_le_\<mu>[OF vG] 
    dist_ge_\<mu>[OF vG _ _ mu ds enum_not0]
    unfolding enum_def by fastforce
qed

lemma (in shortest_paths_reachable) pwalk_awalk:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "dist v \<noteq> \<infinity>"
  shows "awalk s (pwalk v) v" 
proof (cases "v=s")
case True
  thus ?thesis 
    using assms pwalk.simps[where v=v] 
    awalk_Nil_iff by presburger 
next
case False
  from assms show ?thesis 
  proof (induct rule: pwalk.induct)
    fix v 
    let ?e = "the (parent_edge v)"
    let ?u = "tail G ?e"
    assume ewu: "\<not> (v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G) \<Longrightarrow> 
                 ?u \<in> verts G \<Longrightarrow> dist ?u \<noteq> \<infinity> \<Longrightarrow> 
                 awalk s (pwalk ?u) ?u"
    assume vG: "v \<in> verts G" 
    assume dv: "dist v \<noteq> \<infinity>"
    thus "awalk s (pwalk v) v "
    proof (cases "v = s \<or> dist v = \<infinity> \<or> v \<notin> verts G")
    case True
      thus ?thesis 
        using pwalk.simps vG dv 
        awalk_Nil_iff by fastforce
    next
    case False
      obtain e  where ee:
        "e \<in>arcs G" 
        "parent_edge v = Some e" 
        "head G e = v" 
        "(tail G e) \<notin> V\<^sub>p" 
        using pna False by blast
      hence "awalk s (pwalk ?u) ?u"
        using ewu[OF False] tail_in_verts by simp
      hence "awalk s (pwalk (tail G e) @ [e]) v"
        using ee(1-3) vG
        by (auto simp: awalk_simps simp del: pwalk.simps)
      thus ?thesis 
        by (simp only: pwalk.simps[where v=v, unfolded ee(2), simplified False if_False option.sel])
    qed
  qed
qed

lemma (in shortest_paths_neg_cyc) Vn_\<mu>_ninf:
  fixes v :: 'a
  assumes "v \<in> V\<^sub>n"
  shows "\<mu> c s v = - \<infinity>"
proof -
  have "awalk s (pwalk v) v"
    using pwalk_awalk assms by force
moreover
  obtain w where ww: "w \<in> fst ` C \<inter> pwalk_verts v"
    using int_neg_cyc[OF assms] by blast
  then obtain q where 
    "awalk w q w" and 
    "awalk_cost c q < 0"
    using C_se by auto
moreover 
  have "w \<in> set (awalk_verts s (pwalk v))"
    using ww unfolding pwalk_verts_def by fast
ultimately
  show ?thesis using neg_cycle_imp_inf_\<mu> by force
qed

theorem (in shortest_paths_neg_cyc) correct_shortest_path:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
proof(cases "dist v")
show " \<And>r. dist v = ereal r \<Longrightarrow> dist v = \<mu> c s v"
  using dist_Vf_\<mu>[OF assms] by simp 
next
show "dist v = \<infinity> \<Longrightarrow> dist v = \<mu> c s v"
  using dist_le_\<mu>[OF assms] by simp
next
show "dist v = -\<infinity> \<Longrightarrow> dist v = \<mu> c s v"
  using Vn_\<mu>_ninf assms by simp
qed

end


