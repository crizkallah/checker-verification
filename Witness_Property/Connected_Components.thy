theory Connected_Components
imports "../Graph_Theory/Graph_Theory"
begin

locale connected_components_locale =
  fin_digraph +
  fixes num :: "'a \<Rightarrow> nat"
  fixes parent_edge :: "'a \<Rightarrow> 'b option"
  fixes r :: 'a
  assumes r_assms: "r \<in> verts G \<and> parent_edge r = None \<and> num r = 0"
  assumes parent_num_assms: 
    "\<And>v. v \<in> verts G \<and> v \<noteq> r \<Longrightarrow>
       \<exists>e \<in> arcs G.
         parent_edge v = Some e \<and>
         head G e = v \<and>
         num v =  num (tail G e) + 1"

sublocale connected_components_locale \<subseteq> fin_digraph G
  by auto

context connected_components_locale
begin

lemma ccl_wellformed: "wf_digraph G"
  by unfold_locales

lemma num_r_is_min:
  assumes "v \<in> verts G" 
  assumes "v \<noteq> r"
  shows "num v > 0"
  using parent_num_assms assms
  by fastforce

lemma path_from_root:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "r \<rightarrow>\<^sup>* v"
  using assms
proof (induct "num v" arbitrary: v)
  case 0
  hence "v = r" using num_r_is_min by fastforce
  with `v \<in> verts G` show ?case by auto
next
  case (Suc n')
  hence "v \<noteq> r" using r_assms by auto
  then obtain e where ee:
    "e \<in> arcs G"
    "head G e = v \<and> num v = num (tail G e) + 1"  
    using Suc parent_num_assms by blast
  with `v \<in> verts G` Suc(1,2) tail_in_verts
  have "r \<rightarrow>\<^sup>* (tail G e)" "tail G e \<rightarrow> v"
    by (auto intro: in_arcs_imp_in_arcs_ends)
  then show ?case by (rule reachable_adj_trans)
qed

text {* The underlying undirected, simple graph is connected *}
lemma connectedG: "connected G"
proof (unfold connected_def, intro strongly_connectedI)
    show "verts (with_proj (mk_symmetric G)) \<noteq> {}" 
      by (metis equals0D r_assms reachable_in_vertsE reachable_mk_symmetricI reachable_refl)
  next
  let ?SG = "mk_symmetric G"
  interpret S: pair_fin_digraph "?SG" ..
  fix u v assume uv_sG: "u \<in> verts ?SG" "v \<in> verts ?SG"
  from uv_sG have "u \<in> verts G" "v \<in> verts G" by auto
  then have "u \<rightarrow>\<^sup>*\<^bsub>?SG\<^esub> r" "r \<rightarrow>\<^sup>*\<^bsub>?SG\<^esub> v" 
    by (auto intro: reachable_mk_symmetricI path_from_root  symmetric_reachable
      symmetric_mk_symmetric simp del: pverts_mk_symmetric)
  then show "u \<rightarrow>\<^sup>*\<^bsub>?SG\<^esub> v"
    by (rule S.reachable_trans)
qed

theorem connected_by_path:
  fixes u v :: 'a
  assumes "u \<in> pverts (mk_symmetric G)"
  assumes "v \<in> pverts (mk_symmetric G)"
  shows "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric G\<^esub> v"
using connectedG  wellformed_mk_symmetric assms
unfolding connected_def strongly_connected_def by fastforce
end

corollary (in connected_components_locale) connected_graph:
  assumes "u \<in> verts G" and "v \<in> verts G"
  shows "\<exists>p. vpath p (mk_symmetric G) \<and> hd p = u \<and> last p = v"
proof -
  interpret S: pair_fin_digraph "mk_symmetric G" ..
  show "?thesis" unfolding S.reachable_vpath_conv[symmetric]
    using assms by (auto intro: connected_by_path)
qed

end
