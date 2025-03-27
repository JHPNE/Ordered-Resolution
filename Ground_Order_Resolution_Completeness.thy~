theory Ground_Order_Resolution_Completeness
  imports Ground_Order_Resolution
begin

subsection \<open>Mode Construction\<close>

context ground_order_resolution_calculus
begin

context 
  fixes N :: "'f gterm clause set"
begin

function epsilon :: "'f gterm clause \<Rightarrow> 'f gterm set" where
  "epsilon C = {A | A C'. 
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon D) \<TTurnstile> C}"
  by auto

termination epsilon
proof (relation "{(x, y). x \<prec>\<^sub>c y}")
  show "wf {(x, y). x \<prec>\<^sub>c y}"
    using wfp_def by blast
next
  show "\<And>C D. D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (D, C) \<in> {(x, y). x \<prec>\<^sub>c y}"
    by simp
qed
                             
declare epsilon.simps[simp del]

end

lemma (in ground_order_resolution_calculus) epsilon_eq_empty_or_singleton:
  "epsilon N C = {} \<or> (\<exists>A. epsilon N C = {A})"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1A. is_strictly_maximal (Pos A) C"
    by (metis (mono_tags, lifting) Uniq_def literal.inject(1)
        literal.order.Uniq_is_strictly_maximal_in_mset)
  hence "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'. 
    C = add_mset (Pos A) C' \<and> is_strictly_maximal (Pos A) C"
    by (simp add: Uniq_def)
  hence Uniq_epsilon: "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon N D) \<TTurnstile> C"
    using Uniq_antimono'
    by (smt (verit) Uniq_def Uniq_prodI case_prod_conv)

  show ?thesis
    unfolding epsilon.simps[of N C]
    using Collect_eq_if_Uniq[OF Uniq_epsilon]
    by (smt (verit, best) Collect_cong Collect_empty_eq Uniq_def Uniq_epsilon case_prod_conv
        insertCI mem_Collect_eq)
qed

definition (in ground_order_resolution_calculus) rewrite_sys where
  "rewrite_sys N C \<equiv> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon N D)"

lemma (in ground_order_resolution_calculus) mem_epsilonE:
  assumes rule_in: "A \<in> epsilon N C"
  obtains C' where
    "C \<in> N" and
    "C = add_mset (Pos A) C'" and
    "select C = {#}" and
    "is_strictly_maximal (Pos A) C" and
    "\<not> rewrite_sys N C \<TTurnstile> C"
  using rule_in
  unfolding epsilon.simps[of N C] mem_Collect_eq Let_def rewrite_sys_def
  by (metis (no_types, lifting))

lemma (in ground_order_resolution_calculus) epsilon_unfold: "epsilon N C = {A | A C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> rewrite_sys N C \<TTurnstile> C}"
  by (simp add: epsilon.simps[of N C] rewrite_sys_def)

lemma (in ground_order_resolution_calculus) production_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> epsilon N C \<subseteq> rewrite_sys N D"
  unfolding rewrite_sys_def
  using epsilon_unfold by blast

lemma (in ground_order_resolution_calculus)
  assumes
    "D \<preceq>\<^sub>c C" and
    C_prod: "A \<in> epsilon N C" and
    L_in: "L \<in># D"
  shows
    lesseq_trm_if_pos: "is_pos L \<Longrightarrow> atm_of L \<preceq>\<^sub>t A" and
    less_trm_if_neg: "is_neg L \<Longrightarrow> atm_of L \<prec>\<^sub>t A"
proof -
  from C_prod obtain C' where
    C_def: "C = add_mset (Pos A) C'" and
    C_max_lit: "is_strictly_maximal (Pos A) C"
    by (auto elim: mem_epsilonE)

  have "Pos A \<prec>\<^sub>l L" if "is_pos L" and "\<not> atm_of L \<preceq>\<^sub>t A"
  proof -
    from that(2) have "A \<prec>\<^sub>t atm_of L"
      by order
    hence "multp (\<prec>\<^sub>t) {#A#} {#atm_of L#}"
      by auto
    with that(1) show "Pos A \<prec>\<^sub>l L"
      by (metis Ground_Order_Base.mset_lit.simps(1) less\<^sub>l_def literal.collapse(1))
  qed

  moreover have "Pos A \<prec>\<^sub>l L" if "is_neg L" and "\<not> atm_of L \<prec>\<^sub>t A"
  proof -
    from that(2) have "A \<preceq>\<^sub>t atm_of L"
      by order
    hence "multp (\<prec>\<^sub>t) {#A#} {#atm_of L, atm_of L#}"
      by auto
    with that(1) show "Pos A \<prec>\<^sub>l L"
      by (cases L) (simp_all add: less\<^sub>l_def)
  qed

  moreover have False if "Pos A \<prec>\<^sub>l L"
  proof -
    have "C \<prec>\<^sub>c D"
      unfolding less\<^sub>c_def
    proof (rule multp_if_maximal_of_lhs_is_less)
      show "Pos A \<in># C"
        by (simp add: C_def)
    next
      show "L \<in># D"
        using L_in by simp
    next
      show "is_maximal (Pos A) C"
        using C_max_lit
        by auto
    next
      show "Pos A \<prec>\<^sub>l L"
        using that 
        by simp
    qed simp_all

    with \<open>D \<preceq>\<^sub>c C\<close> show False
      by order
  qed

  ultimately show "is_pos L \<Longrightarrow> atm_of L \<preceq>\<^sub>t A" and "is_neg L \<Longrightarrow> atm_of L \<prec>\<^sub>t A"
    by metis+
qed

lemma (in ground_order_resolution_calculus) false_cls_if_productive_production:
  assumes C_prod: "A \<in> epsilon N C" and "D \<in> N" and "C \<prec>\<^sub>c D"
  shows "\<not> rewrite_sys N D \<TTurnstile> C - {#Pos A#}"
proof -
  from C_prod obtain C' where
    C_in: "C \<in> N" and
    C_def: "C = add_mset (Pos A) C'" and
    "select C = {#}" and
    Pox_A_max: "is_strictly_maximal (Pos A) C" and
    "\<not> rewrite_sys N C \<TTurnstile> C"
    by (rule mem_epsilonE) blast

  from \<open>D \<in> N\<close> \<open>C \<prec>\<^sub>c D\<close> have "A \<in> rewrite_sys N D"
    using C_prod production_subset_if_less_cls by auto

  from \<open>D \<in> N\<close> have "rewrite_sys N D \<subseteq> (\<Union>D \<in> N. epsilon N D)"
    by (auto simp: rewrite_sys_def)

  have "\<not> rewrite_sys N D \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L assume L_in: "L \<in># C'"
    hence "L \<in># C"
      by (simp add: C_def)

    have "C' \<prec>\<^sub>c C"
      by (metis C_def add.comm_neutral add_mset_add_single add_mset_not_empty empty_iff less\<^sub>c_def
          one_step_implies_multp set_mset_empty)
    hence "C' \<preceq>\<^sub>c C"
      by order

    show "\<not> rewrite_sys N D \<TTurnstile>l L"
    proof (cases L)
      case (Pos A\<^sub>L)
      moreover have "A\<^sub>L \<notin> rewrite_sys N D"
      proof -
        have "\<forall>y\<in>#C'. y \<prec>\<^sub>l Pos A"
          using Pox_A_max
          by (metis C_def add_mset_remove_trivial is_strictly_maximal_def
              literal.order.not_le_imp_less)
        with Pos have "A\<^sub>L \<notin> insert A (rewrite_sys N C)"
          using L_in \<open>\<not> rewrite_sys N C \<TTurnstile> C\<close> C_def
          by blast

        moreover have "A\<^sub>L \<notin> (\<Union>D' \<in> {D' \<in> N. C \<prec>\<^sub>c D' \<and> D' \<prec>\<^sub>c D}. epsilon N D')"
        proof -
          have "A\<^sub>L \<preceq>\<^sub>t A"
            using Pos lesseq_trm_if_pos[OF \<open>C' \<preceq>\<^sub>c C\<close> C_prod \<open>L \<in># C'\<close>]
            by simp
          thus ?thesis
            using less_trm_iff_less_cls_if_mem_production
            using C_prod calculation rewrite_sys_def by fastforce
        qed

        moreover have "interp N D =
          insert A (interp N C) \<union> (\<Union>D' \<in> {D' \<in> N. C \<prec>\<^sub>c D' \<and> D' \<prec>\<^sub>c D}. production N D')"
        proof -
          have "interp N D = (\<Union>D' \<in> {D' \<in> N. D' \<prec>\<^sub>c D}. production N D')"
            by (simp only: interp_def)
          also have "\<dots> = (\<Union>D' \<in> {D' \<in> {y \<in> N. y \<prec>\<^sub>c C} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y}. D' \<prec>\<^sub>c D}. production N D')"
            using partition_set_around_element[of N "(\<prec>\<^sub>c)", OF _ \<open>C \<in> N\<close>]
              totalp_on_subset[OF totalp_less_cls, simplified]
            by simp
          also have "\<dots> = (\<Union>D' \<in> {y \<in> N. y \<prec>\<^sub>c C \<and> y \<prec>\<^sub>c D} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. production N D')"
            using \<open>C \<prec>\<^sub>c D\<close> by auto
          also have "\<dots> = (\<Union>D' \<in> {y \<in> N. y \<prec>\<^sub>c C} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. production N D')"
            by (metis (no_types, opaque_lifting) assms(3) transpD transp_less_cls)
          also have "\<dots> = interp N C \<union> production N C \<union> (\<Union>D' \<in> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. production N D')"
            by (auto simp: interp_def)
          finally show ?thesis
            using C_prod
            by (metis (no_types, lifting) empty_iff insertE insert_is_Un
                production_eq_empty_or_singleton sup_commute)
        qed

        ultimately show ?thesis
          by simp
      qed
      ultimately show ?thesis
        by simp
    next
      case (Neg A\<^sub>L)
      moreover have "A\<^sub>L \<in> interp N D"
        using Neg \<open>L \<in># C\<close> \<open>C \<prec>\<^sub>c D\<close> \<open>\<not> interp N C \<TTurnstile> C\<close> interp_subset_if_less_cls
        by blast
      ultimately show ?thesis
        by simp
    qed
  qed
  thus "\<not> interp N D \<TTurnstile> C - {#Pos A#}"
    by (simp add: C_def)
qed


lemma (in ground_order_resolution_calculus) pre_model_construction:
  fixes
    N :: "'f gterm clause set" and
    C :: "'f gterm clause"
  defines
    "entails \<equiv> \<lambda>E C. E \<TTurnstile> C"
  assumes "saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows
    "epsilon N C = {} \<longleftrightarrow> entails (rewrite_sys N C) C"
    "(\<Union>D \<in> N. epsilon N D) \<TTurnstile> C"
    "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> entails (rewrite_sys N D) C"
    unfolding atomize_all atomize_conj atomize_imp
    using clause.order.wfp C_in

proof (induction C arbitrary: D rule: wfp_induct_rule)
  case (less C)
  note IH = less.IH

  from \<open>{#} \<notin> N\<close> \<open>C \<in> N\<close> have "C \<noteq> {#}"
    by metis

  define I :: "'f gterm set" where
    "I = rewrite_sys N C"

  have i: "(epsilon N C = {}) \<longleftrightarrow> entails (rewrite_sys N C) C"
  proof (rule iffI)
    show "entails (rewrite_sys N C) C \<Longrightarrow> epsilon N C = {}"
      unfolding entails_def rewrite_sys_def
      by (metis (no_types) empty_iff equalityI mem_epsilonE rewrite_sys_def subsetI)
  next
    assume "epsilon N C = {}"

    show "entails (rewrite_sys N C) C"
    proof (cases "\<exists>A. Neg A \<in># C \<and> (Neg A \<in># select C \<or> select C = {#} \<and> is_maximal (Neg A) C)")
      case ex_neg_lit_sel_or_max: True
      then obtain A where
        "Neg A \<in># C" and
        sel_or_max: "Neg A \<in># select C \<or> select C = {#} \<and> is_maximal (Neg A) C"
        by metis
      then obtain C' where
        C_def: "C = add_mset (Neg A) C'"
        by (metis mset_add)

      show ?thesis
      proof (cases "A \<in> rewrite_sys N C")
        case True
        then obtain D where
          "A \<in> epsilon N D" and "D \<in> N" and "D \<prec>\<^sub>c C"
          unfolding rewrite_sys_def by auto

        then obtain D' where
          D_def: "D = add_mset (Pos A) D'" and
          sel_D: "select D = {#}" and
          max_t_t': "is_strictly_maximal (Pos A) D" and
          "\<not> entails (rewrite_sys N D) D"
          by (metis entails_def mem_epsilonE)

        define \<iota> :: "'f gterm clause inference" where
            "\<iota> = Infer [D, C] (C' + D')"

        have reso: "resolution C D (C' + D')"
        proof (rule resolutionI)
          show "C = add_mset (Neg A) C'"
            by (simp add: C_def)
        next
          show "D = add_mset (Pos A) D'"
            by (simp add: D_def)
        next
          show "D \<prec>\<^sub>c C"
            using \<open>D \<prec>\<^sub>c C\<close> .
        next
          show "select C = {#} \<and> is_maximal (Neg A) C \<or> Neg A \<in># select C"
            using sel_or_max 
            by auto
        next
          show "select D = {#}"
            using sel_D by blast
        next
          show "is_strictly_maximal (Pos A) D"
            using max_t_t' .
        qed simp_all

        hence "\<iota> \<in> G_Inf"
          by (auto simp only: \<iota>_def G_Inf_def)

        moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<longrightarrow> t \<in> N"
          using \<open>C \<in> N\<close> \<open>D \<in> N\<close>
          by (auto simp: \<iota>_def)

        ultimately have "\<iota> \<in> Inf_from N"
          by (auto simp: Inf_from_def)

        hence "\<iota> \<in> Red_I N"
          using \<open>saturated N\<close>
          by (auto simp: saturated_def)

        then obtain DD where
          DD_subset: "DD \<subseteq> N" and
          "finite DD" and
          DD_entails_CD: "G_entails (insert D DD) {C' + D'}" and
          ball_DD_lt_C: "\<forall>D \<in> DD. D \<prec>\<^sub>c C"
          unfolding Red_I_def redundant_infer_def mem_Collect_eq
          by (auto simp: \<iota>_def)

        moreover have "\<forall>D \<in> insert D DD. entails (rewrite_sys N C) D"
          using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
          using \<open>C \<in> N\<close> \<open>D \<in> N\<close> \<open>D \<prec>\<^sub>c C \<close> DD_subset ball_DD_lt_C
          by (metis in_mono insert_iff)

        ultimately have "entails (rewrite_sys N C) (C' + D')"
          using DD_entails_CD
          unfolding entails_def G_entails_def
          by (simp add: I_def true_clss_def)

        moreover have "\<not> entails (rewrite_sys N D) D'"
          using \<open>\<not> entails (rewrite_sys N D) D\<close>
          using D_def entails_def
          by fastforce

        moreover have "D' \<prec>\<^sub>c D"
          by (metis D_def add.comm_neutral add_mset_add_single add_mset_not_empty empty_iff less\<^sub>c_def
              one_step_implies_multp set_mset_empty)

        moreover have "\<not> entails (rewrite_sys N C) D'"
          by (metis D_def \<open>A \<in> epsilon N D\<close> \<open>D \<prec>\<^sub>c C\<close> add_mset_remove_trivial entails_def
              false_cls_if_productive_production less.prems)

        then show "entails (rewrite_sys N C) C"
          using C_def entails_def
          using calculation(1) by fastforce


lemma (in ground_order_resolution_calculus) model_construction:
  fixes
    N :: "'f gterm clause set" and
    C :: "'f gterm clause"
  assumes "saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows
    "epsilon N C = {} \<longleftrightarrow> interp N C \<TTurnstile> C"
    "(\<Union>D \<in> N. epsilon N D) \<TTurnstile> C"
    "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> interp N D \<TTurnstile> C"
  unfolding atomize_conj atomize_imp
  using epsilon_eq_empty_or_singleton[of N C]
proof (elim disjE exE)
  


end
end