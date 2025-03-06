theory Ground_Order_Resolution_Completeness
  imports Ground_Order_resolution
begin

subsection \<open>Mode Construction\<close>

locale ground_order_resolution_calculus_completeness =
  ground_order_resolution_calculus +
 fixes N :: "'f gterm clause set"
begin
end

context ground_order_resolution_calculus
begin
lemma wfP_less_lit[simp]: "wfP (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfp_multp wfp_if_convertible_to_wfp by meson

lemma wfP_less_cls[simp]: "wfP (\<prec>\<^sub>c)"
  using wfP_less_lit wfp_multp by blast

function epsilon :: "_ \<Rightarrow> 'f gterm clause \<Rightarrow> 'f gterm set" where
  "epsilon N C = {A | A C'. 
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. epsilon {E \<in> N. E \<preceq>\<^sub>c D} D) \<TTurnstile> C}"
  by auto

termination epsilon
proof (relation "{((x1, x2), (y1, y2)). x2 \<prec>\<^sub>c y2}")
  have "wfp (\<lambda>(x1, x2) (y1, y2). x2 \<prec>\<^sub>c y2)"
  proof (rule wfp_if_convertible_to_wfp)
    show "\<And>x y. (case x of (x1, x2) \<Rightarrow> \<lambda>(y1, y2). x2 \<prec>\<^sub>c y2) y \<Longrightarrow> (snd x) \<prec>\<^sub>c (snd y)"
      by auto
  next
    show "wfp (\<prec>\<^sub>c)"
      by auto
  qed
  thus "wf {((x1, x2), (y1, y2)). x2 \<prec>\<^sub>c y2}"
    by (simp add: wfp_def)
next
  show "\<And>N C x xa xb xc xd. xd \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (({E \<in> N. E \<preceq>\<^sub>c xd}, xd), N, C) \<in> {((x1, x2), y1, y2). x2 \<prec>\<^sub>c y2}"
    by simp
qed
                             
declare epsilon.simps[simp del]

lemma (in ground_order_resolution_calculus) epsilon_eq_empty_or_singleton:
  "epsilon N C = {} \<or> (\<exists>A. epsilon N C = {A})"
proof -
  have
  
end
end