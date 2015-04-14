theory Matching
imports
  Main
  Parity
  "../Graph_Theory/Graph_Theory"
begin


type_synonym label = nat
(*
section {* Definitions *}
*)
definition disjoint_arcs :: "('a, 'b) pre_digraph => 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "disjoint_arcs G e1 e2 = (
     tail G e1 \<noteq> tail G e2 \<and> tail G e1 \<noteq> head G e2 \<and> 
     head G e1 \<noteq> tail G e2 \<and> head G e1 \<noteq> head G e2)"

definition matching :: "('a, 'b) pre_digraph \<Rightarrow> 'b set \<Rightarrow> bool" where
  "matching G M = (M \<subseteq> arcs G \<and> (\<forall>e1 \<in> M. \<forall>e2 \<in> M. e1 \<noteq> e2 \<longrightarrow> disjoint_arcs G e1 e2))"

definition OSC :: "('a, 'b) pre_digraph \<Rightarrow> ('a \<Rightarrow> label) \<Rightarrow> bool" where
  "OSC G L = (
     \<forall>e \<in> arcs G.
       L (tail G e) = 1 \<or> L (head G e) = 1 \<or> 
       L (tail G e) = L (head G e) \<and> L (tail G e) \<ge> 2)"

definition weight:: "label set \<Rightarrow> (label \<Rightarrow> nat) \<Rightarrow> nat" where
  "weight LV f \<equiv> f 1 + (\<Sum>i\<in>LV. (f i) div 2)"

definition N :: "'a set \<Rightarrow> ('a \<Rightarrow> label) \<Rightarrow> label \<Rightarrow> nat" where
  "N V L i \<equiv> card {v \<in> V. L v = i}"

locale matching_locale = digraph +
  fixes maxM :: "'b set"
  fixes L :: "'a \<Rightarrow> label"
  assumes matching: "matching G maxM" 
  assumes OSC: "OSC G L"
  assumes weight: "card maxM = weight {i \<in> L ` verts G. i > 1} (N (verts G) L)"

sublocale matching_locale \<subseteq> digraph ..

context matching_locale begin

definition degree :: "'a \<Rightarrow> nat" where
  "degree v \<equiv> card {e \<in> arcs G. tail G e = v \<or> head G e = v}"

definition edge_as_set :: "'b \<Rightarrow> 'a set" where
  "edge_as_set e \<equiv> {tail G e, head G e}"

definition matched :: "'b set \<Rightarrow> 'a \<Rightarrow> bool" where
  "matched M v \<equiv> v \<in> \<Union> (edge_as_set ` M)"

definition free :: "'b set \<Rightarrow> 'a \<Rightarrow> bool" where
  "free M v \<equiv> \<not> matched M v"


definition matching_i :: "nat \<Rightarrow> 'b set \<Rightarrow> 'b set" where
  "matching_i i M \<equiv> {e \<in> M. i=1 \<and> (L (tail G e) = i \<or> L (head G e) = i) 
  \<or> i>1 \<and> L (tail G e) = i \<and> L (head G e) = i}"

definition V_i:: "nat \<Rightarrow> 'b set \<Rightarrow> 'a set" where
  "V_i i M \<equiv> \<Union> (edge_as_set ` matching_i i M)"

definition endpoint_inV :: "'a set \<Rightarrow> 'b \<Rightarrow> 'a" where 
  "endpoint_inV V e \<equiv>  if tail G e \<in> V then tail G e else head G e" 

definition relevant_endpoint :: "'b \<Rightarrow> 'a" where 
  "relevant_endpoint e \<equiv> if L (tail G e) = 1 then tail G e else head G e"
(*
section {* Lemmas *}
*)

lemma definition_of_range:
  "endpoint_inV V1 ` matching_i 1 M = 
  { v. \<exists> e \<in> matching_i 1 M. endpoint_inV V1 e = v }" by auto

lemma matching_i_arcs_as_sets:
  "edge_as_set ` matching_i i M = 
  { e1. \<exists> e \<in> matching_i i M. edge_as_set e = e1}" by auto

lemma matching_disjointness:
  assumes "matching G M"
  assumes "e1 \<in> M"
  assumes "e2 \<in> M"
  assumes "e1 \<noteq> e2"
  shows  "edge_as_set e1 \<inter> edge_as_set e2 = {}"
  using assms 
  by (auto simp add: edge_as_set_def disjoint_arcs_def matching_def)

lemma expand_set_containment:
  assumes "matching G M"
  assumes "e \<in> M"
  shows "e \<in> arcs G"
  using assms
  by (auto simp add:matching_def)

theorem injectivity:
  assumes is_m: "matching G M"
  assumes e1_in_M1: "e1 \<in> matching_i 1 M"
      and e2_in_M1: "e2 \<in> matching_i 1 M"
  assumes diff: "(e1 \<noteq> e2)"
  shows "endpoint_inV {v \<in> V. L v = 1} e1 \<noteq> endpoint_inV {v \<in> V. L v = 1} e2"
proof -
  from e1_in_M1 have "e1 \<in> M" by (auto simp add: matching_i_def)
  moreover
  from e2_in_M1 have "e2 \<in> M" by (auto simp add: matching_i_def)
  ultimately
  have disjoint_edge_sets: "edge_as_set e1 \<inter> edge_as_set e2 = {}" 
    using diff is_m matching_disjointness by fast
  then show ?thesis by (auto simp add: edge_as_set_def endpoint_inV_def)
qed
(*
subsection {* @text{"|M1| \<le> n1"} *}
*)
lemma card_M1_le_NVL1: 
  assumes "matching G M"
  shows "card (matching_i 1 M) \<le> N (verts G) L 1"
proof -
  let ?f = "endpoint_inV {v \<in> verts G. L v = 1}"
  let ?A = "matching_i 1 M"
  let ?B = "{v \<in> verts G. L v = 1}"
  have "inj_on ?f ?A" using assms injectivity
    unfolding inj_on_def by blast
  moreover have "?f ` ?A \<subseteq> ?B"
  proof -
    {
      fix e assume "e \<in> matching_i 1 M"
      hence "e \<in> arcs G"
        using assms by (auto simp add: matching_def matching_i_def)
      with `e \<in> matching_i 1 M`
      have "endpoint_inV {v \<in> verts G. L v = 1} e \<in> {v \<in> verts G. L v = 1}"
        using assms
        by (auto simp add: endpoint_inV_def matching_i_def intro: tail_in_verts head_in_verts)
    }
    then show ?thesis using assms definition_of_range by blast
  qed
  moreover have "finite ?B" by simp
  ultimately show ?thesis unfolding N_def by (rule card_inj_on_le)
qed

lemma edge_as_set_inj_on_Mi: 
  assumes "matching G M"
  shows "inj_on edge_as_set (matching_i i M)"
  using assms
  unfolding inj_on_def edge_as_set_def matching_def
    disjoint_arcs_def matching_i_def 
  by blast

lemma card_edge_as_set_Mi_twice_card_partitions:
  assumes "matching G M \<and> i > 1"
  shows "2 * card (edge_as_set`matching_i i M) 
  = card (V_i i M)" (is "2 * card ?C = card ?Vi")
proof -
  from assms have 1: "finite (\<Union> ?C)" 
    by (auto simp add: matching_def
      matching_i_def edge_as_set_def finite_subset)
  show ?thesis unfolding V_i_def
  proof (rule card_partition)
    show "finite ?C" using 1 by (rule finite_UnionD)
  next
    show "finite (\<Union> ?C)" using 1 .
  next
    fix c assume "c \<in> ?C" then show "card c = 2"
    proof (rule imageE)
      fix x 
      assume 2: "c = edge_as_set x" and 3: "x \<in> matching_i i M"
      with assms have "x \<in> arcs G" 
        unfolding matching_i_def matching_def by blast
      then have "tail G x \<noteq> head G x" using assms 3 by (metis no_loops)
      with 2 show ?thesis by (auto simp add: edge_as_set_def)
    qed
  next
    fix x1 x2
    assume 4: "x1 \<in> ?C" and 5: "x2 \<in> ?C" and 6: "x1 \<noteq> x2"
    {
      fix e1 e2
      assume 7: "x1 = edge_as_set e1" "e1 \<in> matching_i i M"
        "x2 = edge_as_set e2" "e2 \<in> matching_i i M"
      from assms have "matching G M" by simp
      moreover
      from 7 assms have "e1 \<in> M" and "e2 \<in> M"
        by (simp_all add: matching_i_def)
      moreover from 6 7 have "e1 \<noteq> e2" by blast
      ultimately have "x1 \<inter> x2 = {}" unfolding 7 
        by (rule matching_disjointness)
    }
    with 4 5 show "x1 \<inter> x2 = {}" by clarsimp
  qed
qed

lemma card_Mi_twice_card_Vi:
  assumes "matching G M \<and> i > 1"
  shows "2 * card (matching_i i M) = card (V_i i M)"
proof -
  show ?thesis  
    by (metis assms card_edge_as_set_Mi_twice_card_partitions
      edge_as_set_inj_on_Mi card_image)
qed

lemma card_Mi_le_floor_div_2_Vi:
  assumes "matching G M \<and> i > 1"
  shows "card (matching_i i M) \<le> (card (V_i i M)) div 2"
  using card_Mi_twice_card_Vi[OF assms]
  by arith

lemma card_Vi_le_NVLi:
  assumes "i>1 \<and> matching G M"
  shows "card (V_i i M) \<le> N (verts G) L i"
  unfolding N_def
proof (rule card_mono)
  show "finite {v \<in> verts G. L v = i}" using assms 
    by (simp add: matching_def)
next
  let ?A = "edge_as_set ` matching_i i M"
  let ?C = "{v \<in> verts G. L v = i}" 
  show "V_i i M \<subseteq> ?C" using assms unfolding V_i_def
  proof (intro Union_least)
    fix X assume "X \<in> ?A"
    with assms have "\<exists>x \<in> matching_i i M. edge_as_set x = X"
      by (simp add: matching_i_arcs_as_sets)
    with assms show "X \<subseteq> ?C" 
      unfolding matching_def
        matching_i_def edge_as_set_def by (blast intro: tail_in_verts head_in_verts)
  qed
qed

lemma card_Mi_le_floor_div_2_NVLi:
  assumes "matching G M \<and> i > 1"
  shows "card (matching_i i M) \<le> (N (verts G) L i) div 2"
proof -  
  from assms have "card (V_i i M) \<le> (N (verts G) L i)"
    by (simp add: card_Vi_le_NVLi) 
  then have "card (V_i i M) div 2 \<le> (N (verts G) L i) div 2"
    by simp
  moreover from assms have 
    "card (matching_i i M) \<le> card (V_i i M) div 2"
    by (intro card_Mi_le_floor_div_2_Vi)
  ultimately show ?thesis by auto
qed

lemma card_M_le_sum_card_Mi: 
assumes "matching G M" and "OSC G L"
shows "card M \<le> (\<Sum> i \<in> L`verts G. card (matching_i i M))"
  (is "card _ \<le> ?CardMi")
proof -
  let ?UnMi = "\<Union>x \<in> L`verts G. matching_i x M"
  from assms have 1: "finite ?UnMi"
    by (auto simp add: matching_def matching_i_def finite_subset)
  {
    fix e assume e_inM: "e \<in> M"
    let ?v = "relevant_endpoint e"
    have 1: "e \<in> matching_i (L ?v) M" using assms e_inM
      proof cases
        assume "L (tail G e) = 1"
        thus ?thesis using assms e_inM 
          by (simp add: relevant_endpoint_def matching_i_def)
      next
        assume a: "L (tail G e) \<noteq> 1" 
        have "L (tail G e) = 1 \<or> L (head G e) = 1 
          \<or>  (L (tail G e) = L (head G e) \<and> L (tail G e) >1)"
          using assms e_inM unfolding OSC_def 
          by (auto intro: expand_set_containment)
        thus ?thesis using assms e_inM a 
          by (auto simp add: relevant_endpoint_def matching_i_def)
      qed
      have 2: "?v \<in> verts G" using assms e_inM 
        by (auto simp add: matching_def relevant_endpoint_def intro: tail_in_verts head_in_verts)
      then have "\<exists> v \<in> verts G. e \<in> matching_i (L v) M" using assms 1 2
        by (intro bexI) 
    }
    with assms have "M \<subseteq> ?UnMi" by (auto)
    with assms and 1 have "card M \<le> card ?UnMi" by (intro card_mono)
    moreover from assms have "card ?UnMi = ?CardMi"
    proof (intro card_UN_disjoint) 
      show "finite (L`verts G)" by simp
    next 
      show "\<forall>i\<in>L`verts G. finite (matching_i i M)" using assms
        using finite_arcs
        unfolding matching_def matching_i_def
        by (blast intro: finite_subset finite_arcs)
    next 
      show "\<forall>i \<in> L`verts G. \<forall>j \<in> L`verts G. i \<noteq> j \<longrightarrow> 
        matching_i i M \<inter> matching_i j M = {}" using assms
        by (auto simp add: matching_i_def)
    qed
  ultimately show ?thesis by simp
qed

theorem card_M_le_weight_NVLi:
  assumes "matching G M" and "OSC G L"
  shows "card M \<le> weight {i \<in> L ` verts G. i > 1} (N (verts G) L)" (is "_ \<le> ?W")
proof -
  let ?M01 = "\<Sum>i| i \<in> L ` verts G \<and> (i=1 \<or> i=0). card (matching_i i M)"
  let ?Mgr1 = "\<Sum>i| i \<in> L ` verts G \<and> 1 < i. card (matching_i i M)"
  let ?Mi = "\<Sum> i\<in>L ` verts G. card (matching_i i M)"
  have "card M \<le> ?Mi" using assms by (rule card_M_le_sum_card_Mi) 
  moreover
  have "?Mi \<le> ?W"
  proof -
    let ?A = "{i \<in> L ` verts G. i = 1 \<or> i = 0}"
    let ?B = "{i \<in> L ` verts G. 1 < i}"
    let ?g = "\<lambda> i. card (matching_i i M)"
    let ?set01 = "{ i. i : L ` verts G & (i = 1 | i = 0)}"
    have a: "L ` verts G = ?A \<union> ?B" using assms by auto
    have b: "setsum ?g (?A \<union> ?B) = setsum ?g ?A + setsum ?g ?B"
      by (auto intro: setsum.union_disjoint)
    have 1: "?Mi = ?M01+ ?Mgr1" using assms a b by simp
    moreover
    have 0: "card (matching_i 0 M) = 0" using assms
      by (simp add: matching_i_def)
      have 2: "?M01 \<le> N (verts G) L 1"
      proof cases
        assume a: "1 \<in> L ` verts G"
        have "?M01 = card (matching_i 1 M)" 
        proof cases
          assume b: "0 \<in> L ` verts G"
          with a assms have  "?set01 = {0, 1}" by blast
          thus ?thesis using assms 0 by simp
        next
          assume b: "0 \<notin> L ` verts G"
          with a have "?set01 = {1}" by (auto simp del:One_nat_def)
          thus ?thesis by simp
        qed
        thus ?thesis using assms a 
          by (simp del: One_nat_def, intro card_M1_le_NVL1)
      next
        assume a: "1 \<notin> L ` verts G"
        show ?thesis
        proof cases
          assume b: "0 \<in> L ` verts G"
          with a assms have  "?set01 = {0}" by (auto simp del:One_nat_def)
          thus ?thesis using assms 0 by auto
        next
          assume b: "0 \<notin> L ` verts G"
          with a have "?set01 = {}" by (auto simp del:One_nat_def)
            then have "?M01 = (\<Sum>i\<in>{}. card (matching_i i M))" by auto
            thus ?thesis by simp
          qed
        qed
      moreover
      have 3: "?Mgr1 \<le> (\<Sum>i|i\<in>L ` verts G \<and> 1 < i. N (verts G) L i div 2)" 
        using assms
        by (intro setsum_mono card_Mi_le_floor_div_2_NVLi, simp)
    ultimately
    show ?thesis using 1 2 3 assms by (simp add: weight_def)
  qed
  ultimately show ?thesis by simp
qed                                 
(*
section {* Final Theorem *}
*)
theorem maximum_cardinality_matching:
  "matching G M' \<longrightarrow> card M' \<le> card maxM"
  using card_M_le_weight_NVLi OSC matching weight
  by simp

end

end
