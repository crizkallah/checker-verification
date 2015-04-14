theory Check_Shortest_Path_Verification
imports
  "Vcg"
  "../Simpl_Verification/Check_Shortest_Path_Impl"

begin

definition no_loops :: "('a, 'b) pre_digraph \<Rightarrow> bool" where
  "no_loops G \<equiv> \<forall>e \<in> arcs G. tail G e \<noteq> head G e"

definition abs_IGraph :: "IGraph \<Rightarrow> (nat, nat) pre_digraph" where
  "abs_IGraph G \<equiv> \<lparr> verts = {0..<ivertex_cnt G}, arcs = {0..<iedge_cnt G},
    tail = fst o iarcs G, head = snd o iarcs G \<rparr>"

lemma verts_absI[simp]: "verts (abs_IGraph G) = {0..<ivertex_cnt G}"
  and arcs_absI[simp]: "arcs (abs_IGraph G) = {0..<iedge_cnt G}"
  and tail_absI[simp]: "tail (abs_IGraph G) e = fst (iarcs G e)"
  and head_absI[simp]: "head (abs_IGraph G) e = snd (iarcs G e)"
  by (auto simp: abs_IGraph_def)

lemma is_wellformed_inv_step:
  "is_wellformed_inv G (Suc i) \<longleftrightarrow> is_wellformed_inv G i
      \<and> fst (iarcs G i) < ivertex_cnt G \<and> snd (iarcs G i) < ivertex_cnt G"
  by (auto simp add: is_wellformed_inv_def less_Suc_eq)

lemma (in is_wellformed_impl) is_wellformed_spec:
  "\<forall>G. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<acute>G = G\<rbrace> \<acute>R :== PROC is_wellformed(\<acute>G) \<lbrace>\<acute>R = is_wellformed_inv G (iedge_cnt G)\<rbrace>"
  apply vcg
  apply (auto simp: is_wellformed_inv_step)
  apply (auto simp: is_wellformed_inv_def) 
done

lemma trian_inv_step:
  "trian_inv G d c (Suc i) \<longleftrightarrow> trian_inv G d c i
    \<and> d (snd (iarcs G i)) \<le> d (fst (iarcs G i)) + c i"
  by (auto simp: trian_inv_def less_Suc_eq)

lemma (in trian_impl) trian_spec:
  "\<forall>G d c. \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>dist = d \<and> \<acute>c = c\<rbrace>
    \<acute>R :== PROC trian(\<acute>G, \<acute>dist, \<acute>c)
    \<lbrace> \<acute>R = trian_inv G d c (iedge_cnt G)\<rbrace>"
  apply vcg   
  apply (auto simp add: trian_inv_step)
  apply (auto simp: trian_inv_def) 
done

lemma just_inv_step:
  "just_inv G d c s n p (Suc v) \<longleftrightarrow> just_inv G d c s n p v
    \<and> (v \<noteq> s \<and> n v \<noteq> \<infinity> \<longrightarrow> 
      (\<exists> e. e = the (p v) \<and> e < iedge_cnt G \<and> 
        v = snd (iarcs G e) \<and>
        d v = d (fst (iarcs G e)) + ereal (c e) \<and>
        n v = n (fst (iarcs G e)) + (enat 1)))"
  by (auto simp: just_inv_def less_Suc_eq)

lemma just_inv_le:
  assumes "j \<le> i" "just_inv G d c s n p i"
  shows "just_inv G d c s n p j"
  using assms by (induct rule: dec_induct) (auto simp: just_inv_step)

lemma not_just_verts:
  fixes G R c d n p s v
  assumes "v < ivertex_cnt G"
  assumes "v \<noteq> s \<and> n v \<noteq> \<infinity> \<and>
        (iedge_cnt G \<le> the (p v) \<or>
        snd (iarcs G (the (p v))) \<noteq> v \<or> 
        d v \<noteq> 
          d (fst (iarcs G (the (p v)))) + ereal (c (the (p v))) \<or> 
        n v \<noteq> n (fst (iarcs G (the (p v)))) + enat 1)"
  shows "\<not> just_inv G d c s n p (ivertex_cnt G)"
proof (rule notI)
  assume jv: "just_inv G d c s n p (ivertex_cnt G)"
  have "just_inv G d c s n p (Suc v)"
    using just_inv_le[OF _ jv] assms(1) by simp
  then have "(v \<noteq> s \<and> n v \<noteq> \<infinity> \<longrightarrow> 
      (\<exists> e. e = the (p v) \<and> e < iedge_cnt G \<and> 
        v = snd (iarcs G e) \<and>
        d v = d (fst (iarcs G e)) + ereal (c e) \<and>
        n v = n (fst (iarcs G e)) + (enat 1)))"
        by (auto simp: just_inv_step)
  with assms show False  by force
qed

lemma (in just_impl) just_spec:
  "\<forall>G d c s n p. 
    \<Gamma>  \<turnstile>\<^sub>t \<lbrace>\<acute>G = G \<and> \<acute>dist = d \<and> 
    \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = n \<and> \<acute>pred = p\<rbrace>
    \<acute>R :== PROC just(\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred)
    \<lbrace> \<acute>R = just_inv  G d c s n p (ivertex_cnt G)\<rbrace>"
  apply vcg 
  apply (auto simp: not_just_verts just_inv_step)
  apply (simp add: just_inv_def) 
done

lemma no_path_inv_step:
  "no_path_inv G d n (Suc v) \<longleftrightarrow> no_path_inv G d n v
    \<and> (d v = \<infinity> \<longleftrightarrow> n v = \<infinity>)"
  by (auto simp add: no_path_inv_def less_Suc_eq)

lemma (in no_path_impl) no_path_spec:
  "\<forall>G d n. \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>dist = d \<and> \<acute>enum = n\<rbrace>
    \<acute>R :== PROC no_path(\<acute>G, \<acute>dist, \<acute>enum)
    \<lbrace> \<acute>R = no_path_inv G d n (ivertex_cnt G)\<rbrace>"
  apply vcg
  apply (simp_all add: no_path_inv_step)
  apply (auto simp: no_path_inv_def)
done

lemma non_neg_cost_inv_step:
  "non_neg_cost_inv G c (Suc i) \<longleftrightarrow> non_neg_cost_inv G c i
    \<and> c i \<ge> 0"
  by (auto simp add: non_neg_cost_inv_def less_Suc_eq)

lemma (in non_neg_cost_impl) non_neg_cost_spec:
  "\<forall>G c. \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>c = c\<rbrace>
    \<acute>R :== PROC non_neg_cost(\<acute>G, \<acute>c)
    \<lbrace> \<acute>R = non_neg_cost_inv G c (iedge_cnt G)\<rbrace>"
  apply vcg
  apply (simp_all add: non_neg_cost_inv_step)
  apply (auto simp: non_neg_cost_inv_def)
done

lemma basic_just_sp_eq_invariants:
"\<And>G dist c s enum pred. 
  basic_just_sp_pred (abs_IGraph G) dist c s enum pred \<longleftrightarrow> 
    (is_wellformed_inv G (iedge_cnt G) \<and> 
    dist s \<le> 0 \<and> 
    trian_inv G dist c (iedge_cnt G) \<and> 
    just_inv G dist c s enum pred (ivertex_cnt G))"
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  have "fin_digraph (abs_IGraph G) \<longleftrightarrow> is_wellformed_inv G (iedge_cnt G)"
    unfolding is_wellformed_inv_def fin_digraph_def fin_digraph_axioms_def
      wf_digraph_def no_loops_def 
      by auto
moreover
  have "trian_inv G d c (iedge_cnt G) = 
    (\<forall>e. e \<in> arcs (abs_IGraph G) \<longrightarrow> 
   (d (head ?aG e) \<le> d (tail ?aG e) + ereal (c e)))"
    by (simp add: trian_inv_def)
moreover
  have "just_inv  G d c s n p (ivertex_cnt G) =
    (\<forall>v. v \<in> verts ?aG \<longrightarrow>
      v \<noteq> s \<longrightarrow> n v \<noteq> \<infinity> \<longrightarrow> 
      (\<exists>e\<in>arcs ?aG. e = the (p v) \<and>
      v = head ?aG e \<and> 
      d v = d (tail ?aG e) + ereal (c e) \<and> 
     n v = n (tail ?aG e) + enat 1))"
      unfolding just_inv_def by fastforce
ultimately
   show "?thesis G d c s n p"
   unfolding 
    basic_just_sp_pred_def 
    basic_just_sp_pred_axioms_def 
    basic_sp_def basic_sp_axioms_def
   by presburger
qed

lemma (in check_basic_just_sp_impl) check_basic_just_sp_imp_locale:
  "\<forall> G d c s n p . \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>dist = d \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = n \<and> \<acute>pred = p \<rbrace>
    \<acute>R :== PROC check_basic_just_sp (\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred)
    \<lbrace> \<acute>R =  basic_just_sp_pred (abs_IGraph G) d c s n p\<rbrace>"
    by vcg (simp add: basic_just_sp_eq_invariants)

(*
lemma (in check_basic_just_sp_impl) check_basic_just_sp_imp_locale:
  "\<And>G d c s n p . \<Gamma> \<turnstile> \<lbrace> \<acute>G = G \<and> \<acute>dist = d \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = n \<and> \<acute>pred = p \<rbrace>
    \<acute>R :== PROC check_basic_just_sp (\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred)
    \<lbrace> \<acute>R =  basic_just_sp_pred (abs_IGraph G) d c s n p\<rbrace>"
    by vcg (simp add: basic_just_sp_eq_invariants)
*)
lemma shortest_path_non_neg_cost_eq_invariants:
"\<And>G d c s n p . 
  shortest_path_non_neg_cost_pred (abs_IGraph G) d c s n p \<longleftrightarrow> 
    (is_wellformed_inv G (iedge_cnt G) \<and> 
    d s \<le> 0 \<and> 
    trian_inv G d c (iedge_cnt G) \<and> 
    just_inv G d c s n p (ivertex_cnt G) \<and>
    s < ivertex_cnt G \<and> d s = 0 \<and> 
    no_path_inv G d n (ivertex_cnt G) \<and>
    non_neg_cost_inv G c (iedge_cnt G))"
proof -
  fix G d c s n p 
  let ?aG = "abs_IGraph G"
  have "no_path_inv G d n (ivertex_cnt G) \<longleftrightarrow> 
    (\<forall>v. v \<in> verts ?aG \<longrightarrow> (d v = \<infinity>) = (n v = \<infinity>))"
    by (simp add: no_path_inv_def)
moreover
  have "non_neg_cost_inv G c (iedge_cnt G) \<longleftrightarrow> 
    (\<forall>e. e \<in> arcs ?aG \<longrightarrow> 0 \<le> c e)"
    by (simp add: non_neg_cost_inv_def)
ultimately
   show "?thesis G d c s n p"
   unfolding shortest_path_non_neg_cost_pred_def 
    shortest_path_non_neg_cost_pred_axioms_def
   using basic_just_sp_eq_invariants by simp
qed

theorem (in check_sp_impl) check_sp_eq_locale:
  "\<forall> G d c s n p . \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>dist = d \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = n \<and> \<acute>pred = p \<rbrace>
    \<acute>R :== PROC check_sp(\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred)
    \<lbrace> \<acute>R = shortest_path_non_neg_cost_pred (abs_IGraph G) d c s n p\<rbrace>"
    by vcg (auto simp add: shortest_path_non_neg_cost_eq_invariants)

lemma shortest_path_non_neg_cost_imp_correct:
"\<And>G d c s n p . 
  shortest_path_non_neg_cost_pred (abs_IGraph G) d c s n p \<longrightarrow>
   (\<forall>v \<in> verts (abs_IGraph G). 
   d v = wf_digraph.\<mu> (abs_IGraph G) c s v)"
using shortest_path_non_neg_cost_pred.correct_shortest_path_pred by fast

theorem (in check_sp_impl) check_sp_spec:
  "\<forall> G d c s n p . \<Gamma> \<turnstile>\<^sub>t \<lbrace> \<acute>G = G \<and> \<acute>dist = d \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = n \<and> \<acute>pred = p \<rbrace>
    \<acute>R :== PROC check_sp(\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred)
    \<lbrace> \<acute>R \<longrightarrow>  (\<forall>v \<in> verts (abs_IGraph G). d v = wf_digraph.\<mu> (abs_IGraph G) c s v)\<rbrace>"
using shortest_path_non_neg_cost_eq_invariants
      shortest_path_non_neg_cost_imp_correct 
by vcg blast

end
