theory Check_Connected_Verification
imports Vcg Check_Connected_Impl
begin

definition no_loops :: "('a, 'b) pre_digraph \<Rightarrow> bool" where
  "no_loops G \<equiv> \<forall>e \<in> arcs G. tail G e \<noteq> head G e"

definition abs_IGraph :: "IGraph \<Rightarrow> (nat, nat) pre_digraph" where
  "abs_IGraph G \<equiv> \<lparr> verts = {0..<ivertex_cnt G}, arcs = {0..<iedge_cnt G},
    tail = fst o iedges G, head = snd o iedges G \<rparr>"

lemma verts_absI[simp]: "verts (abs_IGraph G) = {0..<ivertex_cnt G}"
  and arcs_absI[simp]: "arcs (abs_IGraph G) = {0..<iedge_cnt G}"
  and tail_absI[simp]: "tail (abs_IGraph G) e = fst (iedges G e)"
  and head_absI[simp]: "head (abs_IGraph G) e = snd (iedges G e)"
  by (auto simp: abs_IGraph_def)

lemma is_wellformed_inv_step:
  "is_wellformed_inv G (Suc i) \<longleftrightarrow> is_wellformed_inv G i
      \<and> fst (iedges G i) < ivertex_cnt G \<and> snd (iedges G i) < ivertex_cnt G"
  by (auto simp add: is_wellformed_inv_def less_Suc_eq)

lemma (in is_wellformed_impl) is_wellformed_spec:
  "\<forall>G. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<acute>G = G\<rbrace> \<acute>R :== PROC is_wellformed(\<acute>G) \<lbrace>\<acute>R = is_wellformed_inv G (iedge_cnt G)\<rbrace>"
  apply vcg
  apply (auto simp: is_wellformed_inv_step)
  apply (auto simp: is_wellformed_inv_def)
  done

lemma parent_num_assms_inv_step:
  "parent_num_assms_inv G r p n (Suc i) \<longleftrightarrow> parent_num_assms_inv G r p n i
    \<and> (i \<noteq> r \<longrightarrow> (case p i of
      None \<Rightarrow> False
    | Some x \<Rightarrow> x < iedge_cnt G \<and> snd (iedges G x) = i \<and> n i = n (fst (iedges G x)) + 1))"
  by (auto simp: parent_num_assms_inv_def less_Suc_eq)

lemma (in parent_num_assms_impl) parent_num_assms_spec:
  "\<forall>G r p n. \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>r = r \<and> \<acute>parent_edge = p \<and> \<acute>num = n\<rbrace>
    \<acute>R :== PROC parent_num_assms(\<acute>G, \<acute>r, \<acute>parent_edge, \<acute>num)
    \<lbrace> \<acute>R = parent_num_assms_inv G r p n (ivertex_cnt G)\<rbrace>"
  apply vcg
  apply (simp_all add: parent_num_assms_inv_step)
  apply (auto simp: parent_num_assms_inv_def)
  done

lemma connected_components_locale_eq_invariants:
"\<And>G r p n. 
  connected_components_locale (abs_IGraph G) n p r = 
    (is_wellformed_inv G (iedge_cnt G) \<and> 
    r < ivertex_cnt G \<and> n r = 0 \<and> p r = None \<and> 
    parent_num_assms_inv G r p n (ivertex_cnt G))" 
proof -
  fix G r p n
  let ?aG = "abs_IGraph G"
  have "is_wellformed_inv G (iedge_cnt G) = fin_digraph ?aG"
    unfolding is_wellformed_inv_def fin_digraph_def fin_digraph_axioms_def
      wf_digraph_def 
      by auto
moreover
  have "(\<forall>v \<in> verts ?aG. v \<noteq> r \<longrightarrow>
    (\<exists>e \<in> arcs ?aG. p v = Some e \<and> 
    head ?aG e = v \<and> 
    n v =  n (tail ?aG e) + 1)) 
    = parent_num_assms_inv G r p n (ivertex_cnt G)"
  proof -
    { fix i assume "(case p i of None \<Rightarrow> False
        | Some x \<Rightarrow> x < iedge_cnt G \<and> snd (iedges G x) = i \<and> n i = n (fst (iedges G x)) + 1)"
      then have "\<exists>x\<in>{0..<iedge_cnt G}. p i = Some x \<and> snd (iedges G x) = i \<and> n i = n (fst (iedges G x)) + 1"
      by (case_tac "p i") auto }
    then show ?thesis
      by (auto simp: parent_num_assms_inv_def)
  qed
ultimately
show  "?thesis G r p n"
  unfolding connected_components_locale_def 
  connected_components_locale_axioms_def by auto
qed

theorem (in check_connected_impl) check_connected_eq_locale:
  "\<forall>G r p n. \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>r = r \<and> \<acute>parent_edge = p \<and> \<acute>num = n \<rbrace>
    \<acute>R :== PROC check_connected (\<acute>G, \<acute>r, \<acute>parent_edge, \<acute>num)
    \<lbrace> \<acute>R = connected_components_locale (abs_IGraph G) n p r\<rbrace>"
by vcg (auto simp: connected_components_locale_eq_invariants)

lemma connected_components_locale_imp_correct:
  assumes "connected_components_locale (abs_IGraph G)n p r"
  assumes "u \<in> pverts (mk_symmetric (abs_IGraph G))"
  assumes "v \<in> pverts (mk_symmetric (abs_IGraph G))"
  shows "\<exists>p. pre_digraph.apath (mk_symmetric (abs_IGraph G)) u p v"
proof -
  interpret S: pair_wf_digraph "mk_symmetric (abs_IGraph G)"
    by (intro wf_digraph.wellformed_mk_symmetric
        connected_components_locale.ccl_wellformed[OF assms(1)])
  show ?thesis
    using connected_components_locale.connected_by_path[OF assms]
    by (simp only: S.reachable_apath)
qed

theorem (in check_connected_impl) check_connected_spec:
  "\<And>G r p n. \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>r = r \<and> \<acute>parent_edge = p \<and> \<acute>num = n \<rbrace>
    \<acute>R :== PROC check_connected(\<acute>G, \<acute>r, \<acute>parent_edge, \<acute>num)
    \<lbrace> \<acute>R \<longrightarrow>
        (\<forall>u \<in> pverts (mk_symmetric (abs_IGraph G)).
          \<forall>v \<in> pverts (mk_symmetric (abs_IGraph G)). 
          \<exists>p. pre_digraph.apath (mk_symmetric (abs_IGraph G)) u p v)\<rbrace>"
using connected_components_locale_eq_invariants
      connected_components_locale_imp_correct 
by vcg metis

end
