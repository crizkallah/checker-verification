theory Autocorres_Misc imports
  AutoCorres
begin

section {* Auxilliary Lemmas for Autocorres *}

subsection {* Memory Model *}

abbreviation "c_lift s \<equiv> clift (hst_mem s, hst_htd s)"

lemma cptr_add_0[simp]:
  "p +\<^sub>p 0 = p"
  by (cases p) simp

lemma cptr_add_add[simp]:
  "p +\<^sub>p m +\<^sub>p n = p +\<^sub>p (m + n)"
  by (cases p) (simp add: algebra_simps CTypesDefs.ptr_add_def)

fun arrlist :: "('a :: c_type ptr \<Rightarrow> 'b) \<Rightarrow> ('a :: c_type ptr \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'a ptr \<Rightarrow> bool" where
  "arrlist h v [] p = True" |
  "arrlist h v (x # xs) p = (v p \<and> h p = x \<and> arrlist h v xs (p +\<^sub>p 1))"

lemma arrlist_nth_value:
  fixes i :: int
  assumes "arrlist h v xs p" "0 \<le> i" "i < int (length xs)"
  shows "h (p +\<^sub>p i) = xs ! nat i"
proof -
  { fix n assume "arrlist h v xs p" "n < length xs"
    then have "h (p +\<^sub>p int n) = xs ! n"
    proof (induct n arbitrary: p xs)
      case 0 then show ?case by (cases xs) auto
    next
      case (Suc n)
      then have "n < length (tl xs)" by (cases xs) auto
      have "h (p +\<^sub>p 1 +\<^sub>p int n) = tl xs ! n"
        apply (rule Suc)
        apply (case_tac [!] xs)
        using Suc by auto
      then show ?case using Suc by (auto simp: nth_tl)
    qed }
  with assms show ?thesis by (cases i) auto
qed

lemma arrlist_nth_valid:
  fixes i :: int
  assumes "arrlist h v xs p" "0 \<le> i" "i < int (length xs)"
  shows "v (p +\<^sub>p i)"
  using assms
proof -
  { fix n assume "arrlist h v xs p" "n < length xs"
    then have "v (p +\<^sub>p int n)"
    proof (induct n arbitrary: p xs)
      case 0 then show ?case by (cases xs) auto
    next
      case (Suc n)
      then have "n < length (tl xs)" by (cases xs) auto
      have "v ((p +\<^sub>p 1) +\<^sub>p int n)"
        apply (rule Suc.hyps[where xs="tl xs"])
        apply (case_tac [!] xs)
        using Suc by auto
      then show ?case by simp
    qed }
  with assms show ?thesis by (cases i) auto
qed

lemmas arrlist_nth = arrlist_nth_value arrlist_nth_valid


subsection {* Total validity for the state monad *}

lemma validNF_conj_prop:
  assumes "Q \<Longrightarrow> \<lbrace>\<lambda>s. P s\<rbrace> f \<lbrace>R\<rbrace>!"
  shows "\<lbrace>\<lambda>s. P s \<and> Q\<rbrace> f \<lbrace>R\<rbrace>!"
  using assms unfolding validNF_def valid_def no_fail_def by blast

lemma validNF_post_imp:
  assumes "\<And>r s. Q r s \<Longrightarrow> R r s" "\<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>!" shows "\<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>!" 
  apply rule
  using assms(1) apply (rule hoare_post_imp) apply assumption
  using assms(2) apply (rule validNF_valid)
  using assms(2) apply (rule validNF_no_fail)
  done

lemma validNF_pre_post_imp:
  assumes "\<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>!" "\<And>s. P' s \<Longrightarrow> P s" "\<And>r s. Q r s \<Longrightarrow> Q' r s" shows "\<lbrace>P'\<rbrace> a \<lbrace>Q'\<rbrace>!" 
  using assms unfolding validNF_def valid_def no_fail_def by blast



subsection {* State monad without exceptions *}

lemma no_fail_select': "no_fail x (select S)"
  by (metis no_fail_pre_and non_fail_select pred_and_true_var)

lemma validNF_assert_opt:
  shows "\<lbrace>\<lambda>s. x \<noteq> None \<and> Q (the x) s\<rbrace> assert_opt x \<lbrace>Q\<rbrace>!" 
  by (case_tac x) (simp add: assert_opt_def | wp)+

lemma validNF_gets_the[wp]: "\<lbrace>\<lambda>s. f s \<noteq> None \<and> Q (the (f s)) s\<rbrace> gets_the f \<lbrace>Q\<rbrace>!"
  by (unfold gets_the_def) (wp validNF_assert_opt)

lemma validNF_unknown[wp]: "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> unknown \<lbrace>P\<rbrace>!"
  using select_wp[where S=UNIV] unfolding unknown_def validNF_def by (auto simp: no_fail_select')

subsection {* State monad with exceptions *}

lemma validE_skipE[wp]:
  "\<lbrace>P ()\<rbrace> skipE \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding returnOk_skip[symmetric] by wp

lemma validE_NF_skipE[wp]:
  "\<lbrace>P ()\<rbrace> skipE \<lbrace>P\<rbrace>, \<lbrace>E\<rbrace>!"
  unfolding returnOk_skip[symmetric] by wp

lemma validE_NF_unlessE[wp]:
  assumes "\<not> P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!"
  shows "\<lbrace>if P then R () else Q\<rbrace> unlessE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>!"
  using assms by (auto simp: unlessE_def) wp

subsection {* Option monad *}

definition owhile_inv :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s,'a) lookup) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> nat) \<Rightarrow> ('s,'a) lookup"   where
 "owhile_inv c b a I M \<equiv> owhile c b a"

lemma owhile_unfold: "owhile C B r s = ocondition (C r) (B r |>> owhile C B) (oreturn r) s"
  by (auto simp: ocondition_def obind_def oreturn_def owhile_def option_while_simps split: option.split)

lemma ovalidNF_owhile:
  assumes "\<And>a m. ovalidNF (\<lambda>s. I a s \<and> C a s \<and> M a s = (m :: nat)) (B a) (\<lambda>r s. I r s \<and> M r s < m)"
    and "\<And>a s. I a s \<Longrightarrow> \<not>C a s \<Longrightarrow> Q a s"
  shows "ovalidNF (I a) (OptionMonad.owhile C B a) Q"
  unfolding ovalidNF_def
proof (intro allI impI)
  fix s assume "I a s"
  moreover have "wf (measure (\<lambda>r. M r s))" by simp
  moreover have "\<And>r r'. I r s \<Longrightarrow> C r s \<Longrightarrow> B r s = Some r' \<Longrightarrow> (r', r) \<in> measure (\<lambda>r. M r s)"
    using assms(1) unfolding ovalidNF_def by fastforce
  moreover have "\<And>r r'. I r s \<Longrightarrow> C r s \<Longrightarrow> B r s = Some r' \<Longrightarrow> I r' s"
    using assms(1) unfolding ovalidNF_def by blast
  moreover have "\<And>r. I r s \<Longrightarrow> C r s \<Longrightarrow> B r s = None \<Longrightarrow> None \<noteq> None \<and> (\<forall>r. None = Some r \<longrightarrow> Q r s)"
    using assms(1) unfolding ovalidNF_def by blast
  ultimately show "owhile C B a s \<noteq> None \<and> (\<forall>r. owhile C B a s = Some r \<longrightarrow> Q r s)"
    by (rule owhile_rule[where I=I]) (auto intro: assms(2))
qed

lemma ovalidNF_owhile_inv[wp]:
  assumes "\<And>a m. ovalidNF (\<lambda>s. I a s \<and> C a s \<and> M a s = (m :: nat)) (B a) (\<lambda>r s. I r s \<and> M r s < m)"
    and "\<And>a s. I a s \<Longrightarrow> \<not>C a s \<Longrightarrow> Q a s"
  shows "ovalidNF (I a) (owhile_inv C B a I M) Q"
  unfolding owhile_inv_def using assms by (rule ovalidNF_owhile)



subsection {* Misc *}

lemma guard_True: "guard (\<lambda>_ . True) = skip"
  by (simp add: guard_def skip_def return_def)

lemma bind_guard_True: "f s \<Longrightarrow> (guard f >>= b) s = b () s"
  and bind_guard_False: "\<not> f s \<Longrightarrow> (guard f >>= b) s = fail s"
  by (auto simp: guard_def bind_def fail_def)


section {* A While Loop with Assertions *}



text {* A while loop asserting its invariant *}

definition owhileA :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s,'a) lookup) \<Rightarrow> 'a \<Rightarrow> ('s,'a) lookup" where
  "owhileA invar c b \<equiv> \<lambda>r. DO
    oguard (\<lambda>s. invar r s);
    owhile c (\<lambda>r. DO
        r2 \<leftarrow> b r;
        oguard (\<lambda>s. invar r2 s);
        oreturn r2
      OD) r
    OD
"

definition whileLoopA :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s,'r) nondet_monad) \<Rightarrow> 'r \<Rightarrow> ('s,'r) nondet_monad" where
  "whileLoopA invar c b \<equiv> \<lambda>r. do
      guard (\<lambda>s. invar r s);
      whileLoop c (\<lambda>r. do
          r2 \<leftarrow> b r;
          guard (\<lambda>s. invar r2 s);
          return r2
        od) r
    od"

(* XXX: Should we lift "invar" here? *)
definition whileLoopEA where
  "whileLoopEA invar c b \<equiv> \<lambda>r. whileLoopA (\<lambda>r s. case r of Inl e \<Rightarrow> True | Inr v \<Rightarrow> invar v s)
    (\<lambda>r s. case r of Inl a \<Rightarrow> False | Inr v \<Rightarrow> c v s)
    (NonDetMonad.lift b)
    (Inr r)"

(* XXX rename*)
definition "owhileAM (a :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (M :: 'a \<Rightarrow> 'b \<Rightarrow> nat) c b \<equiv> owhileA a c b"

definition "whileLoopA_inv (a :: 'r \<Rightarrow> 's \<Rightarrow> bool) c (M :: 'r \<Rightarrow> 's \<Rightarrow> nat) b \<equiv> whileLoopA a c b "

definition "whileLoopEA_inv (a :: 'r \<Rightarrow> 's \<Rightarrow> bool) c (M :: 'r \<Rightarrow> 's \<Rightarrow> nat) b \<equiv> whileLoopEA a c b "


lemma owhileA_triv: "owhileA (\<lambda>_ _. True) c b = owhile c b"
  unfolding owhileA_def by (auto simp: guard_True obind_def)

lemma whileLoopA_triv: "whileLoopA (\<lambda>_ _. True) c b = whileLoop c b"
  unfolding whileLoopA_def by (auto simp: guard_True skip_bind)

lemma whileLoopEA_triv: "whileLoopEA (\<lambda>_ _. True) c b = whileLoopE c b"
  unfolding whileLoopEA_def whileLoopE_def whileLoopA_def by (auto simp: guard_True skip_bind)
(*
lemma whileLoopA_inv_conv: "whileLoopA_inv a c M b \<equiv>
  \<lambda>r. do guard (a r);
         whileLoop_inv c (\<lambda>r. do r2 \<leftarrow> b r; guard (a r2); return r2 od) r I M
      od"
  unfolding whileLoopA_inv_def whileLoopA_def whileLoop_inv_def by simp
*)
lemma valid_whileLoopA[wp]:
  fixes I :: "'r \<Rightarrow> 's \<Rightarrow> bool" 
  assumes loop_end: "\<And>r s. A r s \<Longrightarrow> \<not> c r s \<Longrightarrow> Q r s"
  shows "\<lbrace>\<lambda>s. A r s\<rbrace> whileLoopA_inv A c M b r \<lbrace>Q\<rbrace>" 
proof -
  let ?gb = "(\<lambda>r. do r2 \<leftarrow> b r; guard (A r2); return r2 od)"
  have "\<lbrace>\<lambda>s. A r s\<rbrace> whileLoop c ?gb r \<lbrace>Q\<rbrace>"
    apply (wp whileLoop_wp) by (auto simp: loop_end) wp
  then show ?thesis
    unfolding validNF_def valid_def no_fail_def whileLoopA_inv_def whileLoopA_def
    by (auto simp: bind_guard_True)
qed

definition "whileLoopAm_inv (a :: 'r \<Rightarrow> 's \<Rightarrow> bool) c (M :: 'r \<Rightarrow> 's \<Rightarrow> nat) b \<equiv>
  whileLoopA_inv a c M (\<lambda>r. do m \<leftarrow> gets (M r); b m r od)"

definition "whileLoopEAm_inv (a :: 'r \<Rightarrow> 's \<Rightarrow> bool) c (M :: 'r \<Rightarrow> 's \<Rightarrow> nat) b \<equiv>
  whileLoopEA_inv a c M (\<lambda>r. do m \<leftarrow> gets (M r); b m r od)"

section {* While Loop with assertions *}
 
lemma valid_whileLoopEA[wp]:
  assumes inv: "\<And>r. \<lbrace>\<lambda>s. A r s \<and> c r s\<rbrace> b r \<lbrace>\<lambda>r s. True\<rbrace>, \<lbrace>E\<rbrace>"
    and loop_end: "\<And>r s. A r s \<Longrightarrow> \<not> c r s \<Longrightarrow> Q r s"
  shows "\<lbrace>\<lambda>s. A r s\<rbrace> whileLoopEA_inv A c M b r \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>" 
proof -
  let ?A = "(\<lambda>r s. case r of Inl (e :: 'e) \<Rightarrow> True | Inr v \<Rightarrow> A v s)"
  let ?gb = "(\<lambda>r. do r2 \<leftarrow> b r; guard (?A r2); return r2 od)"
  have lift: "lift ?gb = (\<lambda>r. do r2 \<leftarrow> lift b r; guard (?A r2); return r2 od)"
    by (auto simp add: fun_eq_iff lift_def throwError_def bind_guard_True split: sum.splits)
  have "\<lbrace>\<lambda>s. A r s\<rbrace> whileLoopE c ?gb r \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
    apply (wp whileLoopE_wp)
    unfolding validE_def
    apply wp
    apply (rule hoare_post_imp[rotated])
    apply (rule inv[unfolded validE_def])
    apply (auto simp: loop_end split: sum.splits)
    done
  then show ?thesis
    unfolding whileLoopEA_inv_def whileLoopEA_def whileLoopA_def whileLoopE_def validE_def lift
    apply wp
    apply assumption
    apply wp
    apply simp
    done
qed

lemma ovalidNF_owhileA:
  assumes "\<And>a m. ovalidNF (\<lambda>s. I a s \<and> C a s \<and> M a s = (m :: nat)) (B a) (\<lambda>r s. I r s \<and> M r s < m)"
    and "\<And>a s. I a s \<Longrightarrow> \<not>C a s \<Longrightarrow> Q a s"
  shows "ovalidNF (I a) (owhileA I C B a) Q"
proof -
  let ?gb = "\<lambda>r s. (\<lambda>r. DO r2 \<leftarrow> B r; oguard (I r2); oreturn r2 OD) r s"

  have "ovalidNF (I a) (owhile C B a) Q"
    using assms by (rule ovalidNF_owhile)
  have "ovalidNF (I a) (oguard (I a)) (\<lambda>_. I a)"
    by wp simp
  have "ovalidNF (I a) (owhile C ?gb a) Q"
    by (rule ovalidNF_owhile[where M=M]) (wp, simp_all add: assms)
  show ?thesis
    unfolding owhileA_def
    by wp fact+
qed

lemma ovalidNF_owhileAM[wp]:
  assumes "\<And>a m. ovalidNF (\<lambda>s. I a s \<and> C a s \<and> M a s = (m :: nat)) (B a) (\<lambda>r s. I r s \<and> M r s < m)"
    and "\<And>a s. I a s \<Longrightarrow> \<not>C a s \<Longrightarrow> Q a s"
  shows "ovalidNF (I a) (owhileAM I M C B a) Q"
  unfolding owhileAM_def
  using assms by (rule ovalidNF_owhileA)

end

