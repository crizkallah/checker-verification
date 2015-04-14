(* uses Isabelle2014 and autocorres version 1.0 *)
theory Check_Connected
imports 
  "../Library/Autocorres_Misc"
  "../Witness_Property/Connected_Components"
begin
(* Parse the input file. *)
install_C_file "check_connected.c"

autocorres "check_connected.c"

context check_connected begin

(* Autocorres wp lemmas *)

lemma validNFE_getsE[wp]: 
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> getsE f \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  by (auto simp: getsE_def) wp

lemma validNFE_guardE[wp]: 
  "\<lbrace>\<lambda>s. f s \<and> P () s\<rbrace> guardE f \<lbrace>P\<rbrace>, \<lbrace>Q\<rbrace>!" 
  by (auto simp: guardE_def, wp, linarith)  

(* Lemmas for unat and of_nat *)
lemma eq_of_nat_conv:
  assumes "unat w1 = n"
  shows "w2 = of_nat n \<longleftrightarrow> w2 = w1"
  using assms by auto

(* More Lemmas for unat and of_nat *)
lemma less_unat_plus1: 
  assumes "a < unat (b + 1)"
  shows "a < unat b \<or> a = unat b"
  apply (subgoal_tac  "b + 1 \<noteq> 0 ")
  using assms unat_minus_one add_diff_cancel 
  by fastforce+

lemma unat_minus_plus1_less:
  fixes a b
  assumes "a < b"
  shows "unat (b - (a + 1)) < unat (b - a)"
  by (metis (no_types) ab_semigroup_add_class.add_ac(1) right_minus_eq measure_unat
      add_diff_cancel2 assms is_num_normalize(1) zadd_diff_inverse linorder_neq_iff)

lemma unat_image_upto:
  fixes n :: "32 word"
  shows "unat ` {0..<n} = {unat 0..<unat n}" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"  
  proof 
    fix i assume a: "i \<in> ?B"
    then obtain i':: "32 word" where ii: "i=  unat i'"
      by (metis ex_nat_less_eq le_unat_uoi not_leE order_less_asym unat_0)
    then have "i' \<in> {0..<n}" 
      by (metis (hide_lams, mono_tags) atLeast0LessThan a unat_0
          word_zero_le lessThan_iff not_leE not_less_iff_gr_or_eq 
          order_antisym  word_le_nat_alt Un_iff ivl_disj_un(8)) 
    thus  "i \<in> ?A" using ii by fast
  qed
next
  show "?A \<subseteq> ?B"
  proof
     fix i assume a: "i \<in> ?A"
    then obtain i':: "32 word" where ii: "i=  unat i'" by blast
    then have "i' \<in> {0..<n}" using a by force
    thus  "i \<in> ?B"   
      by (metis Un_iff atLeast0LessThan ii ivl_disj_un(8) 
          lessThan_iff unat_0 unat_mono word_zero_le)
  qed
qed
(*Implementation Graph Types*)

type_synonym IVertex = "32 word"
type_synonym IEdge_Id = "32 word"
type_synonym IEdge = "IVertex \<times> IVertex"             
type_synonym IPEdge = "IVertex \<Rightarrow> 32 word"
type_synonym INum = "IVertex \<Rightarrow> 32 word"
type_synonym IGraph = "32 word \<times> 32 word \<times> (IEdge_Id \<Rightarrow> IEdge)"

abbreviation 
  ivertex_cnt :: "IGraph \<Rightarrow> 32 word"
where 
  "ivertex_cnt G \<equiv> fst G"

abbreviation 
  iedge_cnt :: "IGraph \<Rightarrow> 32 word"
where 
  "iedge_cnt G \<equiv> fst (snd G)"

abbreviation 
  iedges :: "IGraph \<Rightarrow> IEdge_Id \<Rightarrow> IEdge"
where 
  "iedges G \<equiv> snd (snd G)"

(* Make List - makes a list containing the result of a function *)
fun 
  bool::"32 word \<Rightarrow> bool" 
where 
  "bool b = (if b=0 then False else True)"

fun 
  mk_list' :: "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> 'b list" 
where 
  "mk_list' n f = map f  (map of_nat [0..<n])"

fun 
  mk_list'_temp :: "nat \<Rightarrow> (32 word \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b list" 
where 
  "mk_list'_temp 0 _ _ = []" |
  "mk_list'_temp (Suc x) f i = (f (of_nat i)) # mk_list'_temp x f (Suc i)"

(* Make graph lists *)
fun
  mk_iedge_list :: "IGraph \<Rightarrow> IEdge list" 
where 
  "mk_iedge_list G = mk_list' (unat (iedge_cnt G)) (iedges G)"

fun 
  mk_inum_list :: "IGraph \<Rightarrow> INum \<Rightarrow> 32 word list" 
where 
  "mk_inum_list G num = mk_list' (unat (ivertex_cnt G)) num"
  
fun 
  mk_ipedge_list :: "IGraph \<Rightarrow> IPEdge \<Rightarrow> 32 word list" 
where 
  "mk_ipedge_list G pedge = mk_list' (unat (ivertex_cnt G)) pedge"

(* Equate to Implementation *)
fun 
  to_edge :: "IEdge \<Rightarrow> Edge_C" 
where
  "to_edge (u,v) = Edge_C u v"

lemma s_C_pte[simp]:
  "s_C (to_edge e) = fst e"
  by (cases e) auto

lemma t_C_pte[simp]:
  "t_C (to_edge e) = snd e"
  by (cases e) auto

definition is_graph where
  "is_graph h iG p \<equiv>
    is_valid_Graph_C h p \<and> 
    ivertex_cnt iG = n_C (heap_Graph_C h p) \<and> 
    iedge_cnt iG = m_C (heap_Graph_C h p) \<and>
    arrlist (heap_Edge_C h) (is_valid_Edge_C h)
      (map to_edge (mk_iedge_list iG)) (es_C (heap_Graph_C h p))"

definition 
  "is_numm h iG iN p \<equiv> arrlist (heap_w32 h) (is_valid_w32 h) (mk_inum_list iG iN) p"

definition
  "is_pedge h iG iP (p:: 32 signed word ptr) \<equiv> arrlist (\<lambda>p. heap_w32 h (ptr_coerce p))
        (\<lambda>p. is_valid_w32 h (ptr_coerce p)) (mk_ipedge_list iG iP) p"

lemma sint_ucast: 
  "sint (ucast (x ::word32) :: sword32) = sint x"
  by (clarsimp simp: sint_uint uint_up_ucast is_up)

definition 
  is_root :: "IGraph \<Rightarrow> IVertex \<Rightarrow> IPEdge \<Rightarrow> INum \<Rightarrow> bool" 
where 
  "is_root iG r iP iN \<equiv> r < (ivertex_cnt iG) \<and> (iN r = 0) \<and> (sint (iP r) < 0)"

definition 
  parent_num_assms_inv :: "IGraph \<Rightarrow> IVertex \<Rightarrow> IPEdge \<Rightarrow> INum \<Rightarrow> nat \<Rightarrow> bool" 
where
  "parent_num_assms_inv G r p n k \<equiv> 
    \<forall>i < k. (of_nat i) \<noteq> r \<longrightarrow> 
            0 \<le> sint (p (of_nat i)) \<and>
            ((p (of_nat i)) < iedge_cnt G \<and>
            snd (iedges G (p (of_nat i))) = (of_nat i) \<and> 
            n (of_nat i) = n (fst (iedges G (p (of_nat i)))) + 1) \<and>
            n (of_nat i) < ivertex_cnt G"

function (in connected_components_locale) 
  pwalk :: "'a \<Rightarrow> 'a list" 
where
  "pwalk v = 
    (if (v = r  \<or> v \<notin> verts G)
      then [v] 
      else 
       pwalk (tail G (the (parent_edge v))) \<oplus> [tail G (the (parent_edge v)), v])"
  by simp+
termination (in connected_components_locale) 
  using parent_num_assms
  by (relation "measure num", auto, fastforce)

lemma (in connected_components_locale) pwalk_simps:
  "v = r \<or> v \<notin> verts G \<Longrightarrow> pwalk v = [v]"
  "v \<noteq> r \<Longrightarrow> v \<in> verts G \<Longrightarrow> pwalk v =
    pwalk (tail G (the (parent_edge v))) @ [v]"
  by (simp, metis drop_0 pwalk.simps
    drop_Suc_Cons vwalk_join_def drop_Suc)

lemma (in connected_components_locale) pwalk_ne: "pwalk v \<noteq> []" 
  by (metis drop_0 drop_Suc drop_Suc_Cons not_Cons_self
      pwalk.simps snoc_eq_iff_butlast vwalk_join_def)

lemma (in connected_components_locale) vwalk_length_pwalk:
  assumes "v \<in> verts G"
  assumes "v \<noteq> r"
  shows "vwalk_length (pwalk v) = 
         vwalk_length (pwalk (tail G (the (parent_edge v)))) + 1"
  by (smt append_Cons assms length_append length_tl list.size(3,4) pwalk_ne
     pwalk.simps tl_append2 vwalk_join_Cons vwalk_join_def vwalk_length_simp)

lemma (in connected_components_locale) pwalk_split:
  assumes "x \<in> set (pwalk v)"
  shows "\<exists>p. pwalk v = pwalk x @ p"
using assms
proof (induct "vwalk_length (pwalk v)" arbitrary: v)
case (Suc n)
have vnr: "v \<noteq> r" 
  using Suc(2) by fastforce
show ?case 
  proof (cases "v \<in> verts G")
  case True
    thus ?thesis
    proof (cases "x = v") 
    case False 
      let ?u = "tail G (the (parent_edge v))"
      have xpu: "x \<in> set (pwalk ?u)"
        using Suc(3) pwalk_simps(2)[OF vnr True] False by fastforce
      hence "\<exists>p. pwalk (tail G (the (parent_edge v))) = pwalk x @ p"
        using vwalk_length_pwalk[OF True vnr] Suc(2)
        by (metis Suc(1)[OF _ xpu] Suc_eq_plus1 
            Suc_eq_plus1_left diff_add_inverse)
      thus ?thesis using pwalk_simps(2)[OF vnr True] by fastforce
    qed fast
  qed (metis Suc.prems append_Nil2 empty_iff empty_set pwalk_simps(1) set_ConsD)
qed (metis pwalk_simps(1) add_is_0 vwalk_length_pwalk
     append_Nil2 empty_iff empty_set one_neq_zero set_ConsD)

lemma (in connected_components_locale) path_from_root_num:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "vpath (pwalk v) G \<and> 
         hd (pwalk v) = r \<and> 
         last (pwalk v) = v \<and> 
         num v = vwalk_length (pwalk v)"
using assms
proof (induct "vwalk_length (pwalk v)" arbitrary: v rule: less_induct)
case less
  thus ?case
  proof (cases "v=r")
    case True
      thus ?thesis using r_assms unfolding vpath_def by force 
  next
    case False
      then obtain e where ee:
        "e \<in> arcs G"
        "e = the (parent_edge v)"
        "head G e = v \<and> num v = num (tail G e) + 1"  
        using less.prems parent_num_assms by force 
      let ?te = "tail G e"
      let ?p' = "pwalk ?te"
      let ?q = "[?te, v]"
      obtain p where 
        pp: "p = ?p' \<oplus> ?q" 
        by presburger 
      hence pv: "p = pwalk v" 
        using less.prems False ee(2) by force
      have ew: "vwalk ?q G" unfolding vwalk_def
        using ee(3) in_arcs_imp_in_arcs_ends[OF ee(1)] 
              less.prems  tail_in_verts[OF ee(1)] 
        by auto
      have wlp: "vwalk_length ?p' < vwalk_length (pwalk v)"
        using vwalk_length_pwalk[OF less.prems False] ee(2) 
        by presburger
      hence pp': 
        "vwalk ?p' G"
        "distinct ?p'" 
        "hd ?p' = r" 
        "last ?p' = ?te" 
        "num ?te = vwalk_length ?p'" 
        using less.hyps[where v="?te", 
              OF _ tail_in_verts[OF ee(1)]] 
        unfolding vpath_def by linarith+
      have jp: "joinable ?p' ?q" 
         unfolding  joinable_def 
         by (simp only: pp'(4) pp'(1)[unfolded vwalk_def], simp)
      have "vwalk_length [tail G e, v] = 1" by force
      hence np: "num v = vwalk_length p" 
        using pp vwalk_join_vwalk_length[OF jp] ee pp'(5)
        by (simp only: pp vwalk_join_vwalk_length[OF jp] ee pp'(5))
      have wp: "vwalk p G"
        by (metis pp ew pp'(1) jp vwalk_joinI_vwalk)
      {
        fix x assume xp: "x \<in> set ?p'"
        have "vwalk_length (pwalk x) \<le> vwalk_length ?p'"
        using pwalk_split[OF xp] by (smt length_append vwalk_length_simp)
        then have wlx: "vwalk_length (pwalk x) < vwalk_length (pwalk v)"
          using wlp by linarith
        hence "num x = vwalk_length (pwalk x)"
          using pp'(1) less.hyps[OF wlx] xp vwalk_verts_in_verts by blast
        with wlx have "num x < vwalk_length (pwalk v)" by presburger
      }
    then have "v \<notin> set ?p'" using wlp np pv  by (metis less_not_refl)
    hence dp: "distinct p" 
      by (metis butlast_snoc distinct.simps(2) distinct1_rotate pp pp'(2)
        list.simps(2) rotate1.simps(2) rotate1_hd_tl vwalk_join_def)
    hence "vpath p G \<and> hd p = r \<and> last p = v \<and> 
           num v = vwalk_length p"
      using dp wp np pp' pp 
      by (metis hd_append2 last_snoc list.sel(3) pwalk_ne vpathI vwalk_join_def)
    thus ?thesis using pv by fast
  qed
qed

(* Abstract Graph *)

definition 
  no_loops :: "('a, 'b) pre_digraph \<Rightarrow> bool" 
where
  "no_loops G \<equiv> \<forall>e \<in> arcs G. tail G e \<noteq> head G e"

definition 
  abs_IGraph :: "IGraph \<Rightarrow> (32 word, 32 word) pre_digraph" 
where
  "abs_IGraph G \<equiv> \<lparr> verts = {0..<ivertex_cnt G}, arcs = {0..<iedge_cnt G},
    tail = fst o iedges G, head = snd o iedges G \<rparr>"

lemma verts_absI[simp]: "verts (abs_IGraph G) = {0..<ivertex_cnt G}"
  and edges_absI[simp]: "arcs (abs_IGraph G) = {0..<iedge_cnt G}"
  and start_absI[simp]: "tail (abs_IGraph G) e = fst (iedges G e)"
  and target_absI[simp]: "head (abs_IGraph G) e = snd (iedges G e)"
  by (auto simp: abs_IGraph_def)

definition 
  abs_pedge :: "(32 word \<Rightarrow> 32 word) \<Rightarrow> 32 word \<Rightarrow> 32 word option" 
where
  "abs_pedge p \<equiv> (\<lambda>v. if sint (p v) < 0 then None else Some (p v))"

lemma None_abs_pedgeI[simp]: 
  "((abs_pedge p) v = None) = (sint (p v) < 0)"
  using abs_pedge_def by auto

lemma Some_abs_pedgeI[simp]: 
  "(\<exists>e. (abs_pedge p) v = Some e) = (sint (p v) \<ge> 0)"
  using None_not_eq None_abs_pedgeI 
  by (metis abs_pedge_def linorder_not_le option.simps(3))
    
(*Helper Lemmas*)

lemma wellformed_iGraph:
  assumes "wf_digraph (abs_IGraph G)"
  shows "\<And>e. e < iedge_cnt G \<Longrightarrow> 
        fst (iedges G e) < ivertex_cnt G \<and> 
        snd (iedges G e) < ivertex_cnt G" 
using assms unfolding wf_digraph_def by simp

lemma path_length:
  assumes "vpath p (abs_IGraph iG)"
  shows "vwalk_length p < unat (ivertex_cnt iG)" 
proof -
  have pne: "p \<noteq> []" and dp: "distinct p" using assms by fast+
  have "unat (ivertex_cnt iG) = card (unat ` {0..<(fst iG)})"  
    using unat_image_upto by simp
  then have "unat (ivertex_cnt iG) = card ((verts (abs_IGraph iG)))"  
     by (simp add: inj_on_def card_image)
  hence "length p  \<le> unat (ivertex_cnt iG)" 
      by (metis finite_code card_mono vwalk_def
          distinct_card[OF dp] vpath_def assms)
  hence "length p - 1 < unat (ivertex_cnt iG)" 
    by (metis pne Nat.diff_le_self le_neq_implies_less 
        less_imp_diff_less minus_eq one_neq_zero length_0_conv)
  thus "vwalk_length p < unat (fst iG)"
    using  assms 
    unfolding vpath_def vwalk_def by simp
qed

lemma ptr_coerce_ptr_add_uint[simp]:
  "ptr_coerce (p +\<^sub>p uint x) =  p +\<^sub>p  (uint x)"
  by auto

lemma check_r'_spc:
  "is_graph s iG p \<Longrightarrow>
   is_numm s iG iN p' \<Longrightarrow>
   is_pedge s iG iP p'' \<Longrightarrow>
   check_r' p r p'' p' s = 
   Some (if is_root iG r iP iN then 1 else 0)"
  unfolding check_r'_def unfolding is_graph_def is_numm_def is_pedge_def
  apply (simp add: ocondition_def oguard_def ogets_def oreturn_def obind_def)
  apply (simp add: is_root_def uint_nat word_less_def sint_ucast)
  apply (safe, simp_all add: arrlist_nth)  
     apply (fastforce simp: dest:arrlist_nth_value[where i="int (unat r)"])
    apply (fastforce dest:arrlist_nth_valid[where i="int (unat r)"])
   apply (fastforce dest:arrlist_nth_value[where i="int (unat r)"])
  apply (fastforce dest:arrlist_nth_valid[where i="int (unat r)"])
  done

(*state monad without exception*)
lemma pedge_num_heap:
  "\<lbrakk>arrlist (\<lambda>p. heap_w32 h (ptr_coerce p)) (\<lambda>p. is_valid_w32 h (ptr_coerce p)) 
  (map (iL \<circ> of_nat) [0..<unat n]) l; i < n\<rbrakk> \<Longrightarrow>
    iL i = heap_w32 h (l +\<^sub>p int (unat i))" 
  apply (subgoal_tac 
  "heap_w32 h (l +\<^sub>p int (unat i)) = map (iL \<circ> of_nat) [0..<unat n] ! unat i") 
   apply (subgoal_tac "map (iL \<circ> of_nat) [0..<unat n] ! unat i = iL i") 
    apply fastforce
   apply (metis (hide_lams, mono_tags) unat_mono word_unat.Rep_inverse 
    minus_nat.diff_0 nth_map_upt o_apply plus_nat.add_0)
  apply (simp add: arrlist_nth_value unat_mono)
  done

lemma pedge_num_heap_ptr_coerce:
  "\<lbrakk>arrlist (\<lambda>p. heap_w32 h (ptr_coerce p)) (\<lambda>p. is_valid_w32 h (ptr_coerce p)) 
  (map (iL \<circ> of_nat) [0..<unat n]) l; i < n; 0 \<le> i\<rbrakk> \<Longrightarrow>
    iL i = heap_w32 h (ptr_coerce (l +\<^sub>p int (unat i)))" 
  apply (subgoal_tac 
  "heap_w32 h (ptr_coerce (l +\<^sub>p int (unat i))) = map (iL \<circ> of_nat) [0..<unat n] ! unat i") 
   apply (subgoal_tac "map (iL \<circ> of_nat) [0..<unat n] ! unat i = iL i") 
    apply fastforce
   apply (metis (hide_lams, mono_tags) unat_mono word_unat.Rep_inverse 
    minus_nat.diff_0 nth_map_upt o_apply plus_nat.add_0)
  apply (drule arrlist_nth_value[where i="int (unat i)"], (simp add:unat_mono)+)
  done


lemma edge_heap:
  "\<lbrakk> arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep;
  e < m\<rbrakk> \<Longrightarrow> to_edge ((iedges iG) e) = h (ep +\<^sub>p (int (unat e)))" 
  apply (subgoal_tac "h (ep +\<^sub>p (int (unat e))) = 
  (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ! unat e")
   apply (subgoal_tac "to_edge ((iedges iG) e) = 
   (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ! unat e")
    apply presburger 
   apply (metis (hide_lams, mono_tags) length_map length_upt o_apply
      map_upt_eq_vals_D minus_nat.diff_0 unat_mono word_unat.Rep_inverse)
  apply (fastforce simp: unat_mono arrlist_nth_value)
  done

lemma head_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  snd ((iedges iG) e) = t_C (h (ep +\<^sub>p (uint e)))" 
  using edge_heap to_edge.simps t_C_pte by (metis uint_nat)            

lemma tail_heap:
  "\<lbrakk>arrlist h v (map (to_edge \<circ> (iedges iG \<circ> of_nat)) [0..<unat m]) ep; e < m\<rbrakk> \<Longrightarrow>
  fst ((iedges iG) e) =  s_C (h (ep +\<^sub>p  (uint e)))" 
  using edge_heap to_edge.simps s_C_pte uint_nat by metis


lemma check_parent_num_spc':
  "\<lbrace> P and 
    (\<lambda>s. wf_digraph (abs_IGraph iG) \<and> 
         is_graph s iG g \<and> 
         is_numm s iG iN n \<and> 
         is_pedge s iG iP p \<and> 
         r < ivertex_cnt iG)\<rbrace>
  check_parent_num' g r p n 
  \<lbrace> (\<lambda>_ s. P s) And 
    (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> parent_num_assms_inv iG r iP iN (unat (ivertex_cnt iG))) \<rbrace>!"
  apply (clarsimp simp: check_parent_num'_def)
  apply (subst whileLoopE_add_inv[where
        M="\<lambda>(vv, s). unat (ivertex_cnt iG - vv)" and
        I="\<lambda>vv s. P s \<and> parent_num_assms_inv iG r iP iN (unat vv) \<and> 
          vv \<le> ivertex_cnt iG \<and> 
          wf_digraph (abs_IGraph iG) \<and> 
          is_graph s iG g \<and> is_numm s iG iN n \<and> 
          is_pedge s iG iP p \<and> 
          r < ivertex_cnt iG"])
  apply (simp add: skipE_def)
  apply wp
    unfolding is_graph_def is_numm_def is_pedge_def parent_num_assms_inv_def
    apply (subst if_bool_eq_conj)+
    apply (simp split: split_if_asm, safe, simp_all add: arrlist_nth)  
                              apply (rule_tac i=" (uint vv)" in arrlist_nth_valid, simp+)
                              apply (metis uint_nat word_less_def)
                             apply (rule_tac x="unat vv" in exI) 
                             apply (subgoal_tac "n_C (heap_Graph_C s g) \<le> iN vv") 
                              apply (metis (hide_lams) word_less_nat_alt 
                              word_not_le word_unat.Rep_inverse)
                             apply (subst pedge_num_heap[where l=n and iL=iN])
                               apply simp 
                              apply simp
                             apply (metis uint_nat)
                            apply (rule_tac i=" (uint vv)" in arrlist_nth_valid)
                              apply simp+
                            apply (metis uint_nat word_less_def)
                           apply (rule_tac x="unat vv" in exI) 
                           apply (rule conjI, metis unat_mono, simp)
                           apply (metis sint_ucast not_le uint_nat 
                           pedge_num_heap_ptr_coerce word_zero_le)
                          apply (rule_tac x="unat vv" in exI) 
                          apply (rule conjI, metis unat_mono, simp)
                          apply (metis not_le uint_nat pedge_num_heap_ptr_coerce word_zero_le)
                         apply (rule_tac x="unat vv" in exI) 
                         apply (rule conjI, metis unat_mono, simp)
                         apply (subgoal_tac "snd (snd (snd iG) (iP vv)) = 
                           t_C (heap_Edge_C s (es_C (heap_Graph_C s g) +\<^sub>p uint (iP vv)))")
                          apply (metis uint_nat pedge_num_heap_ptr_coerce word_zero_le)
                         apply (subst head_heap[where iG=iG], simp)
                          apply (metis not_le uint_nat pedge_num_heap_ptr_coerce word_zero_le)
                         apply simp
                        apply (rule_tac x="unat vv" in exI) 
                        apply (rule conjI, metis unat_mono, simp,clarsimp)
                        apply (subgoal_tac "iN vv \<noteq> iN (fst (snd (snd iG) (iP vv))) + 1")
                         apply fast
                        apply (subst pedge_num_heap[where l=n and iL=iN])
                          apply simp+
                        apply (subst pedge_num_heap[where l=n and iL=iN])
                          apply simp
                         apply (drule wellformed_iGraph[where G=iG])
                          apply simp+
                        apply (subst tail_heap[where iG=iG], simp+) 
                        apply (subst pedge_num_heap_ptr_coerce[where l=p and iL=iP])
                           apply simp+
                        apply (metis uint_nat)
                       apply (drule less_unat_plus1, safe, blast)
                       apply (subst pedge_num_heap_ptr_coerce[where l=p and iL=iP])
                          apply simp+
                       apply (metis sint_ucast not_less uint_nat)
                      apply (drule less_unat_plus1, safe, blast)
                      apply (subst pedge_num_heap_ptr_coerce[where l=p and iL=iP])
                         apply simp+
                      apply (metis not_less uint_nat)
                     apply (drule less_unat_plus1, safe, blast)
                     apply (subst pedge_num_heap_ptr_coerce[where l=p and iL=iP])
                        apply simp+
                     apply (subst head_heap[where iG=iG], (simp add: uint_nat)+)
                    apply (drule less_unat_plus1, safe, blast)
                    apply (subst pedge_num_heap[where l=n and iL=iN], simp+) 
                    apply (subst pedge_num_heap[where l=n and iL=iN], simp)
                     apply (drule_tac e="iP vv" in  wellformed_iGraph[where G=iG])
                      apply (metis not_le pedge_num_heap_ptr_coerce word_zero_le)
                     apply simp
                    apply (subst tail_heap[where iG=iG], simp+) 
                     apply (metis not_le pedge_num_heap_ptr_coerce word_zero_le)
                    apply (subst pedge_num_heap_ptr_coerce[where l=p and iL=iP])
                       apply simp+
                    apply (metis uint_nat)
                   apply (drule less_unat_plus1, safe, blast)
                   apply (subst pedge_num_heap[where l=n and iL=iN])
                     apply (simp add: uint_nat)+
                  apply (metis le_def word_le_nat_alt word_not_le 
                  less_unat_plus1 eq_of_nat_conv) 
                 apply (metis unat_minus_plus1_less)
                apply (rule arrlist_nth, blast, blast) 
                apply (simp add: uint_nat unat_mono) 
               apply (rule arrlist_nth, blast, blast)
               apply (simp add: uint_nat)
               apply (drule_tac i=vv in pedge_num_heap_ptr_coerce[where l=p and iL=iP])
                 apply simp+
               apply (drule_tac e="iP vv" in wellformed_iGraph[where G=iG])
                apply simp+
               apply (drule_tac e="iP vv" in tail_heap[where iG=iG])
                apply (simp add: uint_nat unat_mono)+
              apply (rule arrlist_nth, (simp add: uint_nat unat_mono)+)+
          apply (metis less_unat_plus1 word_unat.Rep_inverse)
         apply (metis eq_of_nat_conv less_unat_plus1)
        apply (metis (hide_lams, no_types) eq_of_nat_conv less_unat_plus1)
       apply (metis (no_types) less_unat_plus1 word_unat.Rep_inverse)
      apply (metis (no_types) less_unat_plus1 word_unat.Rep_inverse)
     apply (metis inc_le)
    apply (metis unat_minus_plus1_less)
   apply metis 
  apply wp 
  apply fast
  done
lemma num_less_n:
  fixes v
  assumes "is_root G r p n"
  assumes "parent_num_assms_inv G r p n (unat (ivertex_cnt G))"
  assumes "v < ivertex_cnt G"
  shows "n v < ivertex_cnt G"
proof -
  have "ivertex_cnt G > 0"
    using assms by (metis word_neq_0_conv word_not_simps(1))
  thus ?thesis
    using assms unfolding parent_num_assms_inv_def is_root_def 
    by (cases "v=r", presburger , metis unat_mono word_unat.Rep_inverse)
qed

lemma parent_num_assms_inv_num_ne_0:
  fixes v
  assumes "wf_digraph (abs_IGraph G)"
  assumes "is_root G r p n"
  assumes "parent_num_assms_inv G r p n (unat (ivertex_cnt G))"
  assumes "v \<noteq> r"
  assumes "v < (ivertex_cnt G)"
  shows "n v \<noteq> 0"
proof-
  have "p v \<in> arcs (abs_IGraph G)"
    using assms(3-5) unat_mono 
    unfolding parent_num_assms_inv_def  
    by fastforce
  hence "fst (iedges G (p v)) \<in> verts (abs_IGraph G)"
     using assms(1) wf_digraph_def  by fastforce
  hence "n (fst (snd (snd G) (p v))) < ivertex_cnt G"
    using num_less_n[OF assms(2,3)] by fastforce
  moreover
  have "n v = n (fst (snd (snd G) (p v))) + 1"
    using assms unat_mono
    unfolding parent_num_assms_inv_def
    by force 
  ultimately
  show ?thesis using assms  
  by (metis less_is_non_zero_p1)
qed

lemma connected_components_locale_num_eq_invariants':
"\<And>G r p n. 
  (connected_components_locale (abs_IGraph G) (unat \<circ>  n) (abs_pedge p) r 
  \<and> (\<forall>v \<in> verts (abs_IGraph G). v\<noteq> r \<longrightarrow> (unat \<circ> n) v < unat (ivertex_cnt G))) = 
    (wf_digraph (abs_IGraph G) \<and> 
    is_root G r p n \<and> 
    parent_num_assms_inv G r p n (unat (ivertex_cnt G)))" 
proof -
  fix G fix r::"32 word" fix p n::"32 word \<Rightarrow> 32 word"
  let ?aG = "abs_IGraph G"
  let ?ap = "abs_pedge p"
  let ?an = "unat \<circ>  n"
  let ?wf = "wf_digraph ?aG"
  let ?is_root = "r \<in> verts ?aG \<and> ?ap r = None \<and> ?an r = 0"
  let ?pnai = "(\<forall>v. v \<in> verts ?aG \<and> v \<noteq> r \<longrightarrow>
                  (\<exists>e\<in>arcs ?aG. ?ap v = Some e \<and> 
                  head ?aG e = v \<and> 
                  ?an v = ?an (tail ?aG e) + 1)) \<and>
               (\<forall>v. v \<in>verts ?aG \<and>  v \<noteq> r \<longrightarrow> 
                  ?an v < unat (ivertex_cnt G))"
  have isr_eq: "?is_root = is_root G r p n" 
    unfolding is_root_def 
    using None_abs_pedgeI unat_eq_0 by auto 
moreover
  have "(?wf \<and> ?is_root \<and> ?pnai)
      = (?wf \<and> is_root G r p n \<and> 
        parent_num_assms_inv G r p n (unat (ivertex_cnt G)))"
  proof -
  {
    assume wf: "?wf"
    assume isr: "?is_root"    
    assume *: "\<And> v. v \<in> verts ?aG \<and> v \<noteq> r \<Longrightarrow>
    (\<exists>e \<in> arcs ?aG. ?ap v = Some e \<and> 
    head ?aG e = v \<and> 
    ?an v =  ?an (tail ?aG e) + 1) \<and> (?an v < unat (ivertex_cnt G))"
    {
      fix i 
      let ?i = "of_nat i"
      assume "i < unat (ivertex_cnt G) \<and> ?i \<noteq> r"
      then have ii: "?i \<in> verts (abs_IGraph G) \<and> ?i \<noteq> r" 
        by (simp add: word_of_nat_less)
      then obtain e where e_assms:
        "e \<in> arcs ?aG" 
        "?ap ?i = Some e"
        "head ?aG e = ?i"
        "?an ?i =  ?an (tail ?aG e) + 1"
        "?an ?i < unat (ivertex_cnt G)" using *[OF ii] by auto 
      have pi_e: "p ?i = e" 
        using e_assms(2) abs_pedge_def Some_abs_pedgeI 
        by (cases "?ap ?i") force+
      with e_assms pi_e  Some_abs_pedgeI have 
        "p ?i < iedge_cnt G \<and> 
         0 \<le> sint (p ?i) \<and>
         snd (iedges G (p ?i)) = ?i \<and> 
         n ?i = n (fst (iedges G (p ?i))) + 1 \<and>
         n ?i < ivertex_cnt G \<and>
         n ?i \<noteq> 0" 
         by (auto, 
             metis Some_abs_pedgeI, 
             metis (hide_lams, mono_tags) Suc_eq_plus1 unat_1 
                    word_arith_nat_add word_unat.Rep_inverse,
             metis word_less_nat_alt)
    } then have "is_root G r p n \<and>
                parent_num_assms_inv G r p n (unat (ivertex_cnt G))"
    unfolding parent_num_assms_inv_def using isr isr_eq by blast
  }
  hence "?wf \<and> ?is_root \<and> ?pnai
      \<Longrightarrow> is_root G r p n \<and> 
        parent_num_assms_inv G r p n (unat (ivertex_cnt G))" by presburger
  moreover
  {
    assume wf: "?wf"
    assume isr: "is_root G r p n"
    assume pna: "parent_num_assms_inv G r p n (unat (ivertex_cnt G))"
    {
      fix v 
      assume vG: "v \<in> verts ?aG"
      assume vnr: "v \<noteq> r"
      have uvG: "unat v < unat (ivertex_cnt G)" 
        using vG by (simp add: word_less_nat_alt)
      have nv_ne0: "n v \<noteq> 0" using pna isr wf unfolding parent_num_assms_inv_def  
        by (metis parent_num_assms_inv_num_ne_0 pna uvG vnr word_less_nat_alt)
      then have *: "
        p v < iedge_cnt G \<and> 
        0 \<le> sint (p v) \<and>
        snd (iedges G (p v)) =  v \<and> 
        n v = n (fst (iedges G (p v))) + 1 \<and>
        n v < ivertex_cnt G"
        using vnr pna
        unfolding parent_num_assms_inv_def
        by (metis uvG word_unat.Rep_inverse)
      then have 1:
      "\<exists>e. e \<in> arcs ?aG \<and> ?ap v = Some e \<and>
           head ?aG e = v \<and>
           ?an v = ?an (tail ?aG e) + 1"
        using abs_pedge_def linorder_not_less unatSuc2 nv_ne0 by auto 
     have 2: "?an v < unat (ivertex_cnt G)"
     using * by (metis o_apply word_less_nat_alt)
     from 1 2 have 
     "(\<exists>e. e \<in> arcs ?aG \<and> ?ap v = Some e \<and>
           head ?aG e = v \<and>
           ?an v = ?an (tail ?aG e) + 1) \<and> 
      ?an v < unat (ivertex_cnt G)" by blast
   } then have "?is_root \<and> ?pnai" using  isr isr_eq by fast
  } 
  hence "?wf \<and> is_root G r p n \<and> 
        parent_num_assms_inv G r p n (unat (ivertex_cnt G)) \<Longrightarrow>
        ?is_root \<and> ?pnai" by presburger
  ultimately 
    show ?thesis by blast 
  qed
ultimately
show  "?thesis G r p n"
  unfolding connected_components_locale_def 
  connected_components_locale_axioms_def 
  fin_digraph_def fin_digraph_axioms_def 
  by auto
qed

lemma cc_num_less_n:
  assumes "connected_components_locale (abs_IGraph G) (unat \<circ>  n) (abs_pedge p) r"
  assumes "v \<in> verts (abs_IGraph G)"
  shows "(unat \<circ> n) v < unat (ivertex_cnt G)"
using connected_components_locale.path_from_root_num[OF assms] path_length
by presburger 

lemma connected_components_locale_eq_invariants':
"\<And>G r p n. 
  (connected_components_locale (abs_IGraph G) (unat \<circ>  n) (abs_pedge p) r) = 
    (wf_digraph (abs_IGraph G) \<and> 
    is_root G r p n \<and> 
    parent_num_assms_inv G r p n (unat (ivertex_cnt G)))" 
    using connected_components_locale_num_eq_invariants' cc_num_less_n by blast

lemma check_connected_spc:
  "\<lbrace> P and 
    (\<lambda>s. wf_digraph (abs_IGraph iG) \<and> 
         is_graph s iG g \<and> 
         is_numm s iG iN n \<and> 
         is_pedge s iG iP p)\<rbrace>
  check_connected' g r p n 
  \<lbrace> (\<lambda>_ s. P s) And 
    (\<lambda>rr s. rr \<noteq> 0 \<longleftrightarrow> 
      connected_components_locale (abs_IGraph iG) (unat \<circ>  iN) (abs_pedge iP) r) \<rbrace>!"
  apply (clarsimp simp: check_connected'_def 
  connected_components_locale_eq_invariants')
  apply wp
  apply (rule_tac P1=" P and 
    (\<lambda>s. wf_digraph (abs_IGraph iG) \<and> 
         is_graph s iG g \<and> 
         is_numm s iG iN n \<and> 
         is_pedge s iG iP p \<and> 
         r < ivertex_cnt iG \<and> 
         is_root iG r iP iN)" 
     in validNF_post_imp[OF _ check_parent_num_spc'])
  unfolding fin_digraph_def fin_digraph_axioms_def
  apply force
  apply wp 
  apply (auto simp: check_r'_spc is_root_def)[]
done

end
end
