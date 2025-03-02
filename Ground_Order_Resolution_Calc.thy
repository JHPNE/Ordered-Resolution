theory Ground_Order_Resolution_Calc
  imports
    Main

    (* Theories from the AFP *)
    "Saturation_Framework.Calculus"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "Abstract-Rewriting.Abstract_Rewriting"

    First_Order_Clause.Multiset_Extra
    First_Order_Clause.Clausal_Calculus_Extra
    First_Order_Clause.Selection_Function
    Ground_Order_Base
begin

section \<open>Resolution Calculus\<close>

locale ground_order_resolution_calculus =
  ground_order_base where less\<^sub>t = less\<^sub>t +
  selection_function select 
for
  less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" and
  select :: "'f gterm clause \<Rightarrow> 'f gterm clause"
begin

subsection \<open>Resolution Calculus\<close>

inductive resolution ::
  "'f gterm clause \<Rightarrow> 'f gterm clause \<Rightarrow> 'f gterm clause \<Rightarrow> bool"
where
  resolutionI: "
    C = add_mset L\<^sub>C C' \<Longrightarrow>
    D = add_mset L\<^sub>D D' \<Longrightarrow>
    L\<^sub>C = (Neg t) \<Longrightarrow>
    L\<^sub>D = (Pos t) \<Longrightarrow>
    D \<prec>\<^sub>c C \<Longrightarrow>
    select C = {#} \<and> is_maximal L\<^sub>C C \<or> ( L\<^sub>C \<in># (select C)) \<Longrightarrow>
    select D = {#} \<Longrightarrow>    
    is_strictly_maximal L\<^sub>D D \<Longrightarrow>
    R = (C' + D') \<Longrightarrow>
    resolution C D R"

inductive factoring ::
  "'f gterm clause \<Rightarrow> 'f gterm clause \<Rightarrow> bool"
where
  factoringI: "
  C = add_mset L\<^sub>1 (add_mset L\<^sub>1 C') \<Longrightarrow>
  L\<^sub>1 = (Pos t) \<Longrightarrow>
  select C = {#} \<Longrightarrow>
  is_maximal L\<^sub>1 C \<Longrightarrow>
  D = add_mset L\<^sub>1 C' \<Longrightarrow>
  factoring C D"

subsection \<open>Ground Layer\<close>

definition G_Inf :: "'f gterm clause inference set" where
  "G_Inf =
    {Infer [D, C] R | D C R. resolution C D R} \<union>
    {Infer [P] C | P C. factoring P C}"

abbreviation G_Bot :: "'f gterm clause set" where
  "G_Bot \<equiv> {{#}}"


definition G_entails :: "'f gterm clause set \<Rightarrow> 'f gterm clause set \<Rightarrow> bool" where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall> I. I \<TTurnstile>s N\<^sub>1 \<longrightarrow> I \<TTurnstile>s N\<^sub>2)"

subsection \<open>Smaller Conclussions\<close>

lemma ground_resolution_smaller_conclusion:
  assumes
    step: "resolution C D R"
  shows "R \<prec>\<^sub>c C"
  using step
proof (cases C D R rule: resolution.cases)
  case (resolutionI L\<^sub>C C' L\<^sub>D D' t)
  have "\<forall>k\<in>#D'. k \<prec>\<^sub>l Pos t"
    using \<open>is_strictly_maximal L\<^sub>D D\<close> \<open>D = add_mset L\<^sub>D D'\<close>
    using is_strictly_maximal_def local.resolutionI(4) by fastforce
  moreover have "\<And>A. Pos A \<prec>\<^sub>l Neg A"
    unfolding literal.order.multiset_extension_def
    by auto
  ultimately have "\<forall>k\<in>#D'. k \<prec>\<^sub>l Neg t"
    using literal.order.dual_order.strict_trans by blast
  hence "D' \<prec>\<^sub>c {#Neg t#}"
    using one_step_implies_multp[of "{#Neg t#}" D' "(\<prec>\<^sub>l)" "{#}"]
    by (simp add: less\<^sub>c_def)
  hence "D' + C' \<prec>\<^sub>c add_mset (Neg t) C'"
    using multp_cancel[of "(\<prec>\<^sub>l)" C' D' "{#Neg t#}"]
    using less\<^sub>c_def by force
  thus ?thesis
    unfolding resolutionI
    by (simp only: add.commute)
qed

lemma ground_factoring_smaller_conclusion:
  assumes step: "factoring C D"
  shows "D \<prec>\<^sub>c C"
  using step
proof (cases C D rule: factoring.cases)
  case (factoringI L\<^sub>1 C')
  then show ?thesis
    by (metis add.right_neutral add_mset_add_single add_mset_not_empty empty_iff
        less\<^sub>c_def one_step_implies_multp set_mset_empty)  
qed

subsection \<open>Redundancy Criterion\<close>
end

sublocale ground_order_resolution_calculus \<subseteq> consequence_relation where
  Bot = G_Bot and
  entails = G_entails
proof unfold_locales
  show "G_Bot \<noteq> {}"
    by simp
next
  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G_entails {B} N"
    by (simp add: G_entails_def)

next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> G_entails N1 N2"
    by (auto simp: G_entails_def elim!: true_clss_mono[rotated])
next
  fix N1 N2 assume ball_G_entails: "\<forall>C \<in> N2. G_entails N1 {C}"
  show "G_entails N1 N2"
    unfolding G_entails_def
  proof (intro allI impI)
    fix I :: "'f gterm set"
    assume "I \<TTurnstile>s N1"
    hence "\<forall>C \<in> N2. I \<TTurnstile>s {C}"
      using ball_G_entails 
      by (simp add: G_entails_def)

    then show "I \<TTurnstile>s N2"
      by (simp add: true_clss_def)
  qed
next
  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def 
    by simp
qed

sublocale ground_order_resolution_calculus \<subseteq> calculus_with_finitary_standard_redundancy where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails and
  less = "(\<prec>\<^sub>c)"
  defines GRed_I = Red_I and GRed_F = Red_F
proof unfold_locales
  show "transp (\<prec>\<^sub>c)"
    by simp
next
  show "wfP (\<prec>\<^sub>c)"
    by auto
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    by (auto simp: G_Inf_def)
next
  fix \<iota>
  have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [D, C] R" and
      infer: "resolution C D R"
    for D C R
    unfolding \<iota>_def
    using infer
    using ground_resolution_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P] C" and
      infer: "factoring P C"
    for P C
    unfolding \<iota>_def
    using infer
    using ground_factoring_smaller_conclusion
    by simp

  ultimately show "\<iota> \<in> G_Inf \<Longrightarrow> concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    unfolding G_Inf_def
    by fast
qed
