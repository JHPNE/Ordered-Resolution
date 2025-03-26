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