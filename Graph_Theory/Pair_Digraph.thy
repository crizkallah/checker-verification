(* Title:  Pair_Digraph.thy
   Author: Lars Noschinski, TU München
*)

theory Pair_Digraph
imports
  Digraph
  Arc_Walk
begin

section {* Digraphs without Parallel Arcs *}

text {*
  If no parallel arcs are desired, arcs can be accurately described as pairs of
  This is the natural representation for Digraphs without multi-arcs.
  and @{term "head G"}, making it easier to deal with multiple related graphs
  and to modify a graph by adding edges.

  This theory introduces such a specialisation of digraphs.
*}

record 'a pair_pre_digraph = pverts :: "'a set" parcs :: "'a rel"

definition with_proj :: "'a pair_pre_digraph \<Rightarrow> ('a, 'a \<times> 'a) pre_digraph" where
  "with_proj G = \<lparr> verts = pverts G, arcs = parcs G, tail = fst, head = snd \<rparr>"

declare [[coercion with_proj]]

primrec pawalk_verts :: "'a \<Rightarrow> ('a \<times> 'a) awalk \<Rightarrow> 'a list" where
  "pawalk_verts u [] = [u]" |
  "pawalk_verts u (e # es) = fst e # pawalk_verts (snd e) es"

fun pcas :: "'a \<Rightarrow> ('a \<times> 'a) awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "pcas u [] v = (u = v)" |
  "pcas u (e # es) v = (fst e = u \<and> pcas (snd e) es v)"

lemma with_proj_simps[simp]:
  "verts (with_proj G) = pverts G"
  "arcs (with_proj G) = parcs G"
  "arcs_ends (with_proj G) = parcs G"
  "tail (with_proj G) = fst"
  "head (with_proj G) = snd"
  by (auto simp: with_proj_def arcs_ends_conv)

lemma cas_with_proj_eq: "pre_digraph.cas (with_proj G) = pcas"
proof (unfold fun_eq_iff, intro allI)
  fix u es v show "pre_digraph.cas (with_proj G) u es v = pcas u es v"
    by (induct es arbitrary: u) (auto simp:  pre_digraph.cas.simps)
qed

lemma awalk_verts_with_proj_eq: "pre_digraph.awalk_verts (with_proj G) = pawalk_verts"
proof (unfold fun_eq_iff, intro allI)
  fix u es show "pre_digraph.awalk_verts (with_proj G) u es = pawalk_verts u es"
    by (induct es arbitrary: u) (auto simp: pre_digraph.awalk_verts.simps)
qed



locale pair_pre_digraph = fixes G :: "'a pair_pre_digraph"
begin

lemmas [simp] = cas_with_proj_eq awalk_verts_with_proj_eq

end



locale pair_wf_digraph = pair_pre_digraph +
  assumes arc_fst_in_verts: "\<And>e. e \<in> parcs G \<Longrightarrow> fst e \<in> pverts G"
  assumes arc_snd_in_verts: "\<And>e. e \<in> parcs G \<Longrightarrow> snd e \<in> pverts G"
begin

lemma in_arcsD1: "(u,v) \<in> parcs G \<Longrightarrow> u \<in> pverts G"
  and in_arcsD2: "(u,v) \<in> parcs G \<Longrightarrow> v \<in> pverts G"
  by (auto dest: arc_fst_in_verts arc_snd_in_verts)

lemmas wellformed' = in_arcsD1 in_arcsD2

end

locale pair_fin_digraph = pair_wf_digraph +
  assumes pair_finite_verts: "finite (pverts G)"
    and pair_finite_arcs: "finite (parcs G)"

locale pair_pseudo_graph = pair_fin_digraph  +
  assumes pair_sym_arcs: "symmetric G"

locale pair_digraph = pair_fin_digraph  +
  assumes pair_no_loops: "e \<in> parcs G \<Longrightarrow> fst e \<noteq> snd e"

locale pair_graph = pair_digraph + pair_pseudo_graph

sublocale pair_pre_digraph \<subseteq> pre_digraph "with_proj G"
  where "verts G = pverts G" and "arcs G = parcs G" and "tail G = fst" and "head G = snd"
    and "arcs_ends G = parcs G"
    and "pre_digraph.awalk_verts G = pawalk_verts"
    and "pre_digraph.cas G = pcas"
  by unfold_locales auto

sublocale pair_wf_digraph \<subseteq> wf_digraph "with_proj G"
  where "verts G = pverts G" and "arcs G = parcs G" and "tail G = fst" and "head G = snd"
    and "arcs_ends G = parcs G"
    and "pre_digraph.awalk_verts G = pawalk_verts"
    and "pre_digraph.cas G = pcas"
  by unfold_locales (auto simp: arc_fst_in_verts arc_snd_in_verts)

sublocale pair_fin_digraph \<subseteq> fin_digraph "with_proj G"
  where "verts G = pverts G" and "arcs G = parcs G" and "tail G = fst" and "head G = snd"
    and "arcs_ends G = parcs G"
    and "pre_digraph.awalk_verts G = pawalk_verts"
    and "pre_digraph.cas G = pcas"
  using pair_finite_verts pair_finite_arcs by unfold_locales auto

sublocale pair_pseudo_graph \<subseteq> pseudo_graph "with_proj G"
  where "verts G = pverts G" and "arcs G = parcs G" and "tail G = fst" and "head G = snd"
    and "arcs_ends G = parcs G"
    and "pre_digraph.awalk_verts G = pawalk_verts"
    and "pre_digraph.cas G = pcas"
  using pair_sym_arcs by unfold_locales auto

sublocale pair_digraph \<subseteq> digraph "with_proj G"
  where "verts G = pverts G" and "arcs G = parcs G" and "tail G = fst" and "head G = snd"
    and "arcs_ends G = parcs G"
    and "pre_digraph.awalk_verts G = pawalk_verts"
    and "pre_digraph.cas G = pcas"
  using pair_no_loops by unfold_locales (auto simp: arc_to_ends_def)

sublocale pair_graph \<subseteq> graph "with_proj G"
  where "verts G = pverts G" and "arcs G = parcs G" and "tail G = fst" and "head G = snd"
    and "arcs_ends G = parcs G"
    and "pre_digraph.awalk_verts G = pawalk_verts"
    and "pre_digraph.cas G = pcas"
  by unfold_locales auto

lemma wf_digraph_wp_iff: "wf_digraph (with_proj G) = pair_wf_digraph G" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then interpret wf_digraph "with_proj G" .
  show ?R using wellformed by unfold_locales auto
next
  assume ?R then interpret pair_wf_digraph G .
  show ?L by unfold_locales
qed

lemma (in pair_fin_digraph) pair_fin_digraph[intro!]: "pair_fin_digraph G" by default

context pair_digraph begin

lemma pair_digraph[intro!]: "pair_digraph G" by default

lemma no_loops':
  "(u,v) \<in> parcs G \<Longrightarrow> u \<noteq> v"
  by (auto dest: no_loops)

end

lemma (in pair_fin_digraph) apath_succ_decomp:
  assumes "apath u p v"
  assumes "(x,y) \<in> set p"
  assumes "y \<noteq> v"
  shows "\<exists>p1 z p2. p = p1 @ (x,y) # (y,z) # p2 \<and> x \<noteq> z \<and> y \<noteq> z"
proof -
  from `(x,y) \<in> set p` obtain p1 p2 where p_decomp: "p = p1 @ (x,y) # p2"
    by (metis (no_types) in_set_conv_decomp_first)
  from p_decomp `apath u p v` `y \<noteq> v` have "p2 \<noteq> []" "awalk y p2 v"
    by (auto simp: apath_def awalk_Cons_iff)
  then obtain z p2' where p2_decomp: "p2 = (y,z) # p2'"
    by atomize_elim (cases p2, auto simp: awalk_Cons_iff)
  then have "x \<noteq> z \<and> y \<noteq> z" using p_decomp p2_decomp `apath u p v`
    by (auto simp: apath_append_iff apath_simps hd_in_awalk_verts)
  with p_decomp p2_decomp have "p = p1 @ (x,y) # (y,z) # p2' \<and> x \<noteq> z \<and> y \<noteq> z"
    by auto
  then show ?thesis by blast
qed


context pair_pseudo_graph begin

lemma pair_pseudo_graph[intro]: "pair_pseudo_graph G" by default

lemma arcs_symmetric:
  "(a,b) \<in> parcs G \<Longrightarrow> (b,a) \<in> parcs G"
  using sym_arcs by (auto simp: symmetric_def elim: symE)

end

lemma (in pair_graph) pair_graph[intro]: "pair_graph G" by default



subsection {* Path reversal for Pair Digraphs *}

text {* This definition is only meaningful in @{term Pair_Digraph} *}

primrec rev_path :: "('a \<times> 'a) awalk \<Rightarrow> ('a \<times> 'a) awalk" where
  "rev_path [] = []" |
  "rev_path (e # es) = rev_path es @ [(snd e, fst e)]"

lemma rev_path_append[simp]: "rev_path (p @ q) = rev_path q @ rev_path p"
  by (induct p) auto

lemma rev_path_rev_path[simp]:
  "rev_path (rev_path p) = p"
  by (induct p) auto

lemma rev_path_empty[simp]:
  "rev_path p = [] \<longleftrightarrow> p = []"
  by (induct p) auto 

lemma rev_path_eq: "rev_path p = rev_path q \<longleftrightarrow> p = q"
  by (metis rev_path_rev_path)

lemma (in pair_pseudo_graph)
  assumes "awalk u p v"
  shows awalk_verts_rev_path: "awalk_verts v (rev_path p) = rev (awalk_verts u p)"
    and awalk_rev_path': "awalk v (rev_path p) u"
using assms
proof (induct p arbitrary: u)
  case Nil case 1 then show ?case by auto
next
  case Nil case 2 then show ?case by (auto simp: awalk_Nil_iff)
next
  case (Cons e es) case 1
  with Cons have walks: "awalk v (rev_path es) (snd e)"
        "awalk (snd e) [(snd e, fst e)] u"
      and verts: "awalk_verts v (rev_path es) = rev (awalk_verts (snd e) es)"
    by (auto simp: awalk_simps intro: arcs_symmetric)

  from walks have "awalk v (rev_path es @ [(snd e, fst e)]) u"
    by simp
  moreover
  have "tl (awalk_verts (awlast v (rev_path es)) [(snd e, fst e)]) = [fst e]"
    by auto
  ultimately
  show ?case using 1 verts by (auto simp: awalk_verts_append)
next
  case (Cons e es) case 2
  with Cons have "awalk v (rev_path es) (snd e)"
    by (auto simp: awalk_Cons_iff)
  moreover
  have "rev_path (e # es) = rev_path es @ [(snd e, fst e)]"
    by auto
  moreover
  from Cons 2 have "awalk (snd e) [(snd e, fst e)] u"
    by (auto simp: awalk_simps intro: arcs_symmetric)
  ultimately show "awalk v (rev_path (e # es)) u"
    by simp
qed

lemma (in pair_pseudo_graph) awalk_rev_path[simp]:
  "awalk v (rev_path p) u = awalk u p v" (is "?L = ?R")
by (metis awalk_rev_path' rev_path_rev_path)

lemma (in pair_pseudo_graph) apath_rev_path[simp]:
  "apath v (rev_path p) u = apath u p v"
by (auto simp: awalk_verts_rev_path apath_def)


subsection {* Subdivisions *}

text {* subdivide an arc in araph *}
fun subdivide :: "'a pair_pre_digraph \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> 'a pair_pre_digraph" where
  "subdivide G (u,v) w = \<lparr>
    pverts = pverts G \<union> {w},
    parcs = (parcs G - {(u,v),(v,u)}) \<union> {(u,w), (w,u), (w, v), (v, w)}\<rparr>"

declare subdivide.simps[simp del]

inductive subdivision :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> bool"
  for G where
    base: "subdivision G G"
  | divide: "\<And>e w H. \<lbrakk>e \<in> parcs H; w \<notin> pverts H; subdivision G H\<rbrakk>
      \<Longrightarrow> subdivision G (subdivide H e w)"

text {* subdivide an arc in a path *}
fun sd_path :: "'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) awalk \<Rightarrow> ('a \<times> 'a) awalk" where
    "sd_path _ _ [] = []"
  | "sd_path (u,v) w (e # es) = (if e = (u,v)
                                 then [(u,w),(w,v)]
                                 else if e = (v,u)
                                 then [(v,w),(w,u)]
                                 else [e]) @ sd_path (u,v) w es"

text {* contract an arc in a path  *}
fun co_path :: "'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) awalk \<Rightarrow> ('a \<times> 'a) awalk" where
    "co_path _ _ [] = []"
  | "co_path _ _ [e] = [e]"
  | "co_path (u,v) w (e1 # e2 # es) = (if e1 = (u,w) \<and> e2 = (w,v)
      then (u,v) # co_path (u,v) w es
      else if e1 = (v,w) \<and> e2 = (w,u)
      then (v,u) # co_path (u,v) w es
      else e1 # co_path (u,v) w (e2 # es))"

lemma co_path_simps[simp]:
  "\<lbrakk>e1 \<noteq> (fst e, w); e1 \<noteq> (snd e,w)\<rbrakk> \<Longrightarrow> co_path e w (e1 # es) = e1 # co_path e w es" 
  "\<lbrakk>e1 = (fst e, w); e2 = (w, snd e)\<rbrakk> \<Longrightarrow> co_path e w (e1 # e2 # es) = e # co_path e w es"
  "\<lbrakk>e1 = (snd e, w); e2 = (w, fst e)\<rbrakk>
    \<Longrightarrow> co_path e w (e1 # e2 # es) = (snd e, fst e) # co_path e w es"
  "\<lbrakk>e1 \<noteq> (fst e, w) \<or> e2 \<noteq> (w, snd e); e1 \<noteq> (snd e, w) \<or> e2 \<noteq> (w, fst e)\<rbrakk>
    \<Longrightarrow> co_path e w (e1 # e2 # es) = e1 # co_path e w (e2 # es)"
  apply (cases es)
  apply (case_tac [!] e)
  apply (case_tac [!] "fst e = snd e")
  apply auto
  done

lemma co_path_nonempty[simp]: "co_path e w p = [] \<longleftrightarrow> p = []"
  by (cases e) (cases p rule: list_exhaust_NSC, auto)

declare co_path.simps(3)[simp del]

lemma verts_subdivide[simp]: "pverts (subdivide G e w) = pverts G \<union> {w}"
  by (cases e) (auto simp: subdivide.simps)

lemma arcs_subdivide[simp]:
  shows "parcs (subdivide G (u,v) w) = (parcs G - {(u,v),(v,u)}) \<union> {(u,w), (w,u), (w, v), (v, w)}"
  by (auto simp: subdivide.simps)

lemmas subdivide_simps = verts_subdivide arcs_subdivide

lemma sd_path_induct[case_names empty pass sd sdrev]:
  assumes A: "P e []"
    and B: "\<And>e' es. e' \<noteq> e \<Longrightarrow> e' \<noteq> (snd e , fst e) \<Longrightarrow> P e es \<Longrightarrow> P e (e' # es)"
      "\<And>es. P e es \<Longrightarrow> P e (e # es)"
      "\<And>es. fst e \<noteq> snd e \<Longrightarrow> P e es \<Longrightarrow> P e ((snd e, fst e) # es)"
  shows "P e es"
  by (induct es) (rule A, metis B pair_collapse)

lemma co_path_induct[case_names empty single co corev pass]:
  fixes e :: "'a \<times> 'a"
    and w :: "'a"
    and p :: "('a \<times> 'a) awalk"
  assumes Nil: "P e w []"
    and ConsNil:"\<And>e'. P e w [e']"
    and ConsCons1: "\<And>e1 e2 es. e1 = (fst e, w) \<and> e2 = (w, snd e) \<Longrightarrow> P e w es \<Longrightarrow>
            P e w (e1 # e2 # es)"
    and ConsCons2: "\<And>e1 e2 es. \<not>(e1 = (fst e, w) \<and> e2 = (w, snd e)) \<and>
            e1 = (snd e, w) \<and> e2 = (w, fst e) \<Longrightarrow> P e w es \<Longrightarrow>
            P e w (e1 # e2 # es)"
    and ConsCons3: "\<And>e1 e2 es.
            \<not> (e1 = (fst e, w) \<and> e2 = (w, snd e)) \<Longrightarrow>
             \<not> (e1 = (snd e, w) \<and> e2 = (w, fst e)) \<Longrightarrow> P e w (e2 # es) \<Longrightarrow>
            P e w (e1 # e2 # es)"
  shows "P e w p"
proof (induct p rule: length_induct)
  case (1 p) then show ?case
  proof (cases p rule: list_exhaust_NSC)
    case (Cons_Cons e1 e2 es)
    then have "P e w es" "P e w (e2 # es)"using 1 by auto
    then show ?thesis unfolding Cons_Cons by (blast intro: ConsCons1 ConsCons2 ConsCons3)
  qed (auto intro: Nil ConsNil)
qed

lemma co_sd_id:
  assumes "(u,w) \<notin> set p" "(v,w) \<notin> set p"
  shows "co_path (u,v) w (sd_path (u,v) w p) = p"
using assms by (induct p) auto

lemma sd_path_id:
  assumes "(x,y) \<notin> set p" "(y,x) \<notin> set p"
  shows "sd_path (x,y) w p = p"
using assms by (induct p) auto

lemma (in pair_pseudo_graph) pair_pseudo_graph_subdivide:
  assumes props: "e \<in> parcs G" "w \<notin> pverts G"
  shows "pair_pseudo_graph (subdivide G e w)" (is "pair_pseudo_graph ?sG")
proof
  obtain u v where [simp]: "e = (u,v)" by (cases e) auto
  {
    show "finite (pverts ?sG)" "finite (parcs ?sG)" by auto
    have "\<And>a b. (a, b) \<in> parcs (subdivide G e w) \<Longrightarrow> (b, a) \<in> parcs (subdivide G e w)"
      unfolding `e = _` arcs_subdivide
      by (elim UnE, rule UnI1, rule_tac [2] UnI2) (blast intro: arcs_symmetric)+
    then show "symmetric ?sG"
      unfolding symmetric_def with_proj_simps by (rule symI)
  next
    fix e' assume "e' \<in> parcs ?sG"
    then show "fst e' \<in> pverts ?sG" "snd e' \<in> pverts ?sG"
      using props by (auto dest: wellformed)
  }
qed

lemma (in pair_graph) pair_graph_subdivide:
  assumes "e \<in> parcs G" "w \<notin> pverts G"
  shows "pair_graph (subdivide G e w)" (is "pair_graph ?sG")
proof -
  interpret PPG: pair_pseudo_graph "subdivide G e w"
    using assms by (rule pair_pseudo_graph_subdivide)
  from assms show ?thesis
    by unfold_locales (cases e, auto dest: wellformed no_loops)
qed

lemma (in pair_graph) pair_graph_subdivision:
  assumes "subdivision G H"
  shows "pair_graph H"
using assms
by (induct rule: subdivision.induct) (blast intro: pair_graph.pair_graph_subdivide divide)+

lemma arcs_subdivideD:
  assumes "x \<in> parcs (subdivide G e w)" "fst x \<noteq> w" "snd x \<noteq> w"
  shows "x \<in> parcs G"
using assms by (cases e) auto

context pair_pseudo_graph begin

lemma
  assumes path: "apath u p v"
  assumes elems: "e \<in> parcs G" "w \<notin> pverts G"
  shows apath_sd_path: "pre_digraph.apath (subdivide G e w) u (sd_path e w p) v" (is ?A)
    and set_awalk_verts_sd_path: "set (awalk_verts u (sd_path e w p))
      \<subseteq> set (awalk_verts u p) \<union> {w}" (is ?B)
proof -
  obtain x y where e_conv: "e = (x,y)" by (cases e) auto
  def sG \<equiv> "subdivide G e w"
  interpret S: pair_pseudo_graph sG
    unfolding sG_def using elems by (rule pair_pseudo_graph_subdivide)

  have ev_sG: "S.awalk_verts = awalk_verts"
    by (auto simp: fun_eq_iff pre_digraph.awalk_verts_conv)
  have w_sG: "{(x,w), (y,w), (w,x), (w,y)} \<subseteq> parcs sG"
    by (auto simp: sG_def e_conv)

  from path have "S.apath u (sd_path (x,y) w p) v"
    and "set (S.awalk_verts u (sd_path (x,y) w p)) \<subseteq> set (awalk_verts u p) \<union> {w}"
  proof (induct p arbitrary: u rule: sd_path_induct)
    case empty case 1
    moreover have "pverts sG = pverts G \<union> {w}" by (simp add: sG_def)
    ultimately show ?case by (auto simp: apath_Nil_iff S.apath_Nil_iff)
  next
    case empty case 2 then show ?case by simp
  next
    case (pass e' es)
    { case 1
      then have "S.apath (snd e') (sd_path (x,y) w es) v" "u \<noteq> w" "fst e' = u"
          "u \<notin> set (S.awalk_verts (snd e') (sd_path (x,y) w es))"
        using pass elems by (fastforce simp: apath_Cons_iff)+
      moreover then have "e' \<in> parcs sG"
        using 1 pass by (auto simp: e_conv sG_def S.apath_Cons_iff apath_Cons_iff)
      ultimately show ?case using pass by (auto simp: S.apath_Cons_iff) }
    note case1 = this
    { case 2 with pass 2 show ?case by (simp add: apath_Cons_iff) blast }
  next
    { fix u es a b
      assume A: "apath u ((a,b) # es) v"
        and ab: "(a,b) = (x,y) \<or> (a,b) = (y,x)"
        and hyps: "\<And>u. apath u es v \<Longrightarrow> S.apath u (sd_path (x, y) w es) v"
          "\<And>u. apath u es v \<Longrightarrow> set (awalk_verts u (sd_path (x, y) w es)) \<subseteq> set (awalk_verts u es) \<union> {w}"

      from ab A have "(x,y) \<notin> set es" "(y,x) \<notin> set es"
        by (auto simp: apath_Cons_iff dest!: awalkI_apath dest: awalk_verts_arc1 awalk_verts_arc2)
      then have ev_sd: "set (S.awalk_verts b (sd_path (x,y) w es)) = set (awalk_verts b es)"
        by (simp add: sd_path_id)

      from A ab have [simp]: "x \<noteq> y"
        by (simp add: apath_Cons_iff) (metis awalkI_apath awalk_verts_non_Nil awhd_of_awalk hd_in_set NOMATCH_def)
 
      from A have "S.apath b (sd_path (x,y) w es) v" "u = a" "u \<noteq> w"
        using ab hyps elems by (auto simp: apath_Cons_iff wellformed')
      moreover
      then have "S.awalk u (sd_path (x, y) w ((a, b) # es)) v "
        using ab w_sG by (auto simp: S.apath_def S.awalk_simps S.wellformed')
      then have "u \<notin> set (S.awalk_verts w ((w,b) # sd_path (x,y) w es))"
        using ab `u \<noteq> w` ev_sd A by (auto simp: apath_Cons_iff S.awalk_def)
      moreover
      have "w \<notin> set (awalk_verts b (sd_path (x, y) w es))"
        using ab ev_sd A elems by (auto simp: awalk_Cons_iff apath_def)
      ultimately
      have path: "S.apath u (sd_path (x, y) w ((a, b) # es)) v "
        using ab hyps w_sG `u = a` by (auto simp: S.apath_Cons_iff ) }
    note path = this
    { case (sd es)
      { case 1 with sd show ?case by (intro path) auto }
      { case 2 show ?case using 2 sd
          by (auto simp: apath_Cons_iff) } }
    { case (sdrev es)
      { case 1 with sdrev show ?case by (intro path) auto }
      { case 2 show ?case using 2 sdrev
          by (auto simp: apath_Cons_iff) } }
  qed
  then show ?A ?B unfolding sG_def e_conv .
qed

lemma
  assumes elems: "e \<in> parcs G" "w \<notin> pverts G" "u \<in> pverts G" "v \<in> pverts G"
  assumes path: "pre_digraph.apath (subdivide G e w) u p v"
  shows apath_co_path: "apath u (co_path e w p) v" (is ?thesis_path)
    and set_awalk_verts_co_path: "set (awalk_verts u (co_path e w p)) = set (awalk_verts u p) - {w}" (is ?thesis_set)
proof -
  obtain x y where e_conv: "e = (x,y)" by (cases e) auto
  interpret S: pair_pseudo_graph "subdivide G e w"
    using elems(1,2) by (rule pair_pseudo_graph_subdivide)

  have e_w: "fst e \<noteq> w" "snd e \<noteq> w" using elems by auto

  have "S.apath u p v" "u \<noteq> w" using elems path by auto
  then have co_path: "apath u (co_path e w p) v
    \<and> set (awalk_verts u (co_path e w p)) = set (awalk_verts u p) - {w}"
  proof (induction p arbitrary: u rule: co_path_induct)
    case empty with elems show ?case
      by (simp add: apath_Nil_iff S.apath_Nil_iff)
  next
    case (single e') with elems show ?case
     by (auto simp: apath_Cons_iff S.apath_Cons_iff apath_Nil_iff S.apath_Nil_iff
        dest: arcs_subdivideD)
  next
    case (co e1 e2 es)
    then have "apath u (co_path e w (e1 # e2 # es)) v" using co e_w elems
      by (auto simp: apath_Cons_iff S.apath_Cons_iff)
    moreover
    have "set (awalk_verts u (co_path e w (e1 # e2 # es))) = set (awalk_verts u (e1 # e2 # es)) - {w}"
      using co e_w by (auto simp: apath_Cons_iff S.apath_Cons_iff)
    ultimately
    show ?case by fast
  next
    case (corev e1 e2 es)
    have "apath u (co_path e w (e1 # e2 # es)) v" using corev(1-3) e_w(1) elems(1)
      by (auto simp: apath_Cons_iff S.apath_Cons_iff  intro: arcs_symmetric)
    moreover
    have "set (awalk_verts u (co_path e w (e1 # e2 # es))) = set (awalk_verts u (e1 # e2 # es)) - {w}"
      using corev e_w by (auto simp: apath_Cons_iff S.apath_Cons_iff)
    ultimately
    show ?case by fast
  next
    case (pass e1 e2 es)
    have "fst e1 \<noteq> w" using elems pass.prems by (auto simp: S.apath_Cons_iff)
    have "snd e1 \<noteq> w"
    proof
      assume "snd e1 = w"
      then have "e1 \<notin> parcs G" using elems by auto
      then have "e1 \<in> parcs (subdivide G e w) - parcs G"
        using pass by (auto simp: S.apath_Cons_iff)
      then have "e1 = (x,w) \<or> e1 = (y,w)"
        using `fst e1 \<noteq> w` e_w by (auto simp add: e_conv)
      moreover
      have "fst e2 = w" using `snd e1 = w` pass.prems by (auto simp: S.apath_Cons_iff)
      then have "e2 \<notin> parcs G" using elems by auto
      then have "e2 \<in> parcs (subdivide G e w) - parcs G"
        using pass by (auto simp: S.apath_Cons_iff)
      then have "e2 = (w,x) \<or> e2 = (w,y)"
        using `fst e2 = w` e_w by (cases e2) (auto simp add: e_conv)
      ultimately
      have "e1 = (x,w) \<and> e2 = (w,x) \<or> e1 = (y,w) \<and> e2 = (w,y)"
        using pass.hyps[simplified e_conv] by auto
      then show False
        using pass.prems by (cases es) (auto simp: S.apath_Cons_iff)
    qed
    then have "e1 \<in> parcs G"
      using `fst e1 \<noteq> w` pass.prems by (auto simp: S.apath_Cons_iff dest: arcs_subdivideD)

    have ih: "apath (snd e1) (co_path e w (e2 # es)) v \<and> set (awalk_verts (snd e1) (co_path e w (e2 # es))) = set (awalk_verts (snd e1) (e2 # es)) - {w}"
      using pass.prems `snd e1 \<noteq> w` by (intro pass.IH) (auto simp: apath_Cons_iff S.apath_Cons_iff)
    then have "fst e1 \<notin> set (awalk_verts (snd e1) (co_path e w (e2 # es)))" "fst e1 = u"
      using pass.prems by (clarsimp simp: S.apath_Cons_iff)+
    then have "apath u (co_path e w (e1 # e2 # es)) v"
      using ih pass `e1 \<in> parcs G` by (auto simp: apath_Cons_iff S.apath_Cons_iff)[]
    moreover
    have "set (awalk_verts u (co_path e w (e1 # e2 # es))) = set (awalk_verts u (e1 # e2 # es)) - {w}"
      using pass.hyps ih `fst e1 \<noteq> w` by auto
    ultimately show ?case by fast
  qed
  then show ?thesis_set ?thesis_path by blast+
qed

end


end
