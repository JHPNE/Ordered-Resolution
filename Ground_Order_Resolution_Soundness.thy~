theory Ground_Order_Resolution_Soundness
  imports Ground_Order_Resolution
begin

lemma (in ground_order_resolution_calculus) soundness_ground_resolution:
  assumes
    step: "resolution C D R"
  shows "G_entails {C, D} {R}"
  using step
proof (cases C D R rule: resolution.cases)
  case (resolutionI L\<^sub>C C' L\<^sub>D D')

  show ?thesis
    unfolding G_entails_def true_clss_singleton
    unfolding true_clss_insert
  proof (intro allI impI, elim conjE)
    fix I :: "'f gterm set"
    assume "I \<TTurnstile> C" and "I \<TTurnstile> D"
    then obtain K1 K2 :: "'f gterm literal" where
      "K1 \<in># C" and "I \<TTurnstile>l K1" and "K2 \<in># D" and "I \<TTurnstile>l K2"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> R"
    proof (cases "K1 = L\<^sub>C")
      case K1_def: True
      hence "I \<TTurnstile>l L\<^sub>C"
        using \<open>I \<TTurnstile>l K1\<close> by simp

      show ?thesis
      proof (cases "K2 = L\<^sub>D")
        case K2_def: True
        hence "I \<TTurnstile>l L\<^sub>D"
          using \<open>I \<TTurnstile>l K2\<close> by simp
        hence False
          using \<open>I \<TTurnstile>l L\<^sub>C\<close> 
          by (simp add: local.resolutionI(3,4))
        thus ?thesis ..
      next
        case False
        hence "K2 \<in># D'"
          using \<open>K2 \<in># D\<close>
          unfolding resolutionI by simp
        hence "I \<TTurnstile> D'"
          using \<open>I \<TTurnstile>l K2\<close> by blast
        thus ?thesis
          unfolding resolutionI by simp
      qed
    next
      case False
      hence "K1 \<in># C'"
        using \<open>K1 \<in># C\<close>
        unfolding resolutionI by simp
      hence "I \<TTurnstile> C'"
        using \<open>I \<TTurnstile>l K1\<close> by blast
      thus ?thesis
        unfolding resolutionI by simp
    qed
  qed
qed

lemma (in ground_order_resolution_calculus) soundness_ground_factoring:
  assumes step: "factoring C D"
  shows "G_entails {C} {D}"
  using step
proof (cases C D rule: factoring.cases)
  case (factoringI L\<^sub>1 C')
  show ?thesis
    unfolding G_entails_def true_clss_singleton
  proof (intro allI impI)
    fix I :: "'f gterm set"
    assume "I \<TTurnstile> C"
    then obtain K :: "'f gterm literal" where
      "K \<in># C" and "I \<TTurnstile>l K"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> D"
    proof (cases "K = L\<^sub>1")
      case True
      hence "I \<TTurnstile>l L\<^sub>1"
        using \<open>I \<TTurnstile>l K\<close> by metis
      thus ?thesis
        unfolding factoringI
        by (metis true_cls_add_mset)
    next
      case False
      hence "K \<in># C'"
       using \<open>K \<in># C\<close>
        unfolding factoringI
        by auto
      hence "K \<in># D"
        unfolding factoringI
        by simp
      thus ?thesis
        using \<open>I \<TTurnstile>l K\<close> by blast
    qed
  qed
qed

end