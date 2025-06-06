theory Resolution_Soundness
  imports
    First_Order_Clause.Nonground_Entailment
    Grounded_Resolution
    Resolution_Welltypedness_Preservation
begin

subsection \<open>Soundness\<close>

context grounded_resolution_calculus
begin

notation lifting.entails_\<G> (infix "\<TTurnstile>\<^sub>F" 50)

lemma factoring_sound:
  assumes factoring: "factoring C D"
  shows "{C} \<TTurnstile>\<^sub>F {D}"
  using factoring
proof (cases C D rule: factoring.cases)
  case (factoringI C L\<^sub>1 \<mu> \<V> t\<^sub>1 t\<^sub>2 L\<^sub>2 C' D)
  {
    fix I :: "'f gterm set" and \<gamma> :: "('f, 'v) subst"

    let ?I = "I"

    assume
      entails_ground_instances: "\<forall>C\<^sub>G \<in> clause.welltyped_ground_instances (C, \<V>). ?I \<TTurnstile> C\<^sub>G" and
      D_is_ground: "clause.is_ground (D \<cdot> \<gamma>)" and
      D_is_welltyped: "clause.is_welltyped \<V> D" and
      \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
      \<V>: "infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term_subst.is_ground_subst \<gamma>'" and
      \<gamma>'_is_welltyped: "is_welltyped \<V> \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars D. \<gamma> x = \<gamma>' x"
      using clause.welltyped_ground_subst_extension[OF D_is_ground \<gamma>_is_welltyped].

    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?C\<^sub>G' = "clause.to_ground (C' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<gamma>')"

    have \<mu>_is_welltyped: "is_welltyped_on (clause.vars C) \<V> \<mu>"
      using factoringI(5)
      by blast

    have "?C\<^sub>G \<in> clause.welltyped_ground_instances (C, \<V>)"
    proof(unfold clause.welltyped_ground_instances_def mem_Collect_eq fst_conv snd_conv,
          intro exI, intro conjI \<V>)
      show "clause.to_ground (C \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (C \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next
      show "clause.is_ground (C \<cdot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next
      show "\<exists>\<tau>. clause.welltyped \<V> C \<tau>"
         using D_is_welltyped
         unfolding factoring_preserves_typing[OF factoring[unfolded factoringI(1, 2)]]
         by auto
    next
      show "is_welltyped_on (clause.vars C) \<V> (\<mu> \<odot> \<gamma>')"
        using \<mu>_is_welltyped \<gamma>'_is_welltyped
        by (simp add: subst_compose_def)
    qed

    then have "?I \<TTurnstile> ?C\<^sub>G"
      using entails_ground_instances
      by blast

    then obtain l\<^sub>G where l\<^sub>G_in_C\<^sub>G: "l\<^sub>G \<in># ?C\<^sub>G" and I_models_l\<^sub>G: "?I \<TTurnstile>l l\<^sub>G"
      by (auto simp: true_cls_def)

    have [simp]: "?t\<^sub>G\<^sub>2 = ?t\<^sub>G\<^sub>1"
      using factoringI(5) term_subst.is_imgu_unifies_pair
      by metis

    have [simp]: "?l\<^sub>G\<^sub>1 = Pos ?t\<^sub>G\<^sub>1"
      unfolding factoringI
      by simp

    have [simp]: "?l\<^sub>G\<^sub>2 = Pos ?t\<^sub>G\<^sub>2"
      unfolding factoringI
      by simp

    have [simp]: "?C\<^sub>G = add_mset (Pos ?t\<^sub>G\<^sub>1) (add_mset (Pos ?t\<^sub>G\<^sub>2) ?C\<^sub>G')"
      unfolding factoringI
      by simp

    have "?I \<TTurnstile> clause.to_ground (D \<cdot> \<gamma>)"
      by (smt (verit) \<gamma>'_\<gamma> \<open>I \<TTurnstile> clause.to_ground (C \<cdot> \<mu> \<cdot> \<gamma>')\<close>
          \<open>clause.to_ground (C \<cdot> \<mu> \<cdot> \<gamma>') = add_mset (Pos (term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>'))) (add_mset (Pos (term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'))) (clause.to_ground (C' \<cdot> \<mu> \<cdot> \<gamma>')))\<close>
          \<open>literal.to_ground (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>') = Pos (term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>'))\<close> \<open>term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>') = term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')\<close> clause.map_add clause.subst_def clause.subst_eq
          clause.to_ground_add local.factoringI(9) true_cls_add_mset)
  }

  then show ?thesis
    unfolding
      factoringI(1, 2)
      ground.G_entails_def
      true_clss_def
      clause.welltyped_ground_instances_def
    by auto
qed

lemma resolution_sound:
  assumes resolution: "resolution D C R"
  shows "{C, D} \<TTurnstile>\<^sub>F {R}"
  using resolution
proof (cases D C R rule: resolution.cases)
  case (resolutionI \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 C D \<V>\<^sub>3 t\<^sub>1 t\<^sub>2 \<mu> L\<^sub>1 L\<^sub>2 C' D' R)
  {
    fix I :: "'f gterm set" and \<gamma> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "I"

    assume
      C_entails_ground_instances: "\<forall>C\<^sub>G \<in> clause.welltyped_ground_instances (C, \<V>\<^sub>1). ?I \<TTurnstile> C\<^sub>G" and
      D_entails_ground_instances: "\<forall>D\<^sub>G \<in> clause.welltyped_ground_instances (D, \<V>\<^sub>2). ?I \<TTurnstile> D\<^sub>G" and
      R_is_ground: "clause.is_ground (R \<cdot> \<gamma>)" and
      R_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 R" and
      \<gamma>_is_welltyped: "is_welltyped_on (clause.vars R) \<V>\<^sub>3 \<gamma>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term_subst.is_ground_subst \<gamma>'" and
      \<gamma>'_is_welltyped: "is_welltyped \<V>\<^sub>3 \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars R. \<gamma> x = \<gamma>' x"
      using clause.welltyped_ground_subst_extension[OF R_is_ground \<gamma>_is_welltyped].

    let ?C\<^sub>G = "clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G = "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?l\<^sub>G\<^sub>1 = "literal.to_ground (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>G\<^sub>2 = "literal.to_ground (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"

    let ?C\<^sub>G' = "clause.to_ground (C' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D\<^sub>G' = "clause.to_ground (D' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?t\<^sub>G\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>G\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"

    let ?R\<^sub>G = "clause.to_ground (R \<cdot> \<gamma>')"


    have \<mu>_\<gamma>'_is_ground_subst:
      "term_subst.is_ground_subst (\<mu> \<odot> \<gamma>')"
      using term.is_ground_subst_comp_right[OF \<gamma>'_is_ground_subst].

    have \<mu>_is_welltyped:
      "is_welltyped_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<mu>"
      using resolutionI(9)
      by blast

    have D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D"
      using resolution_preserves_typing_D[OF
          resolution[unfolded resolutionI(1-3)]
          R_is_welltyped].

    have C_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 C"
      using resolution_preserves_typing_C[OF
          resolution[unfolded resolutionI(1-3)]
          R_is_welltyped].

    have is_welltyped_\<mu>_\<gamma>:
      "is_welltyped_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
      using \<gamma>'_is_welltyped \<mu>_is_welltyped
      by (simp add: term.typed_subst_compose)

    note is_welltyped_\<rho>_\<mu>_\<gamma> = term.renaming_ground_subst[OF _ _ _ \<mu>_\<gamma>'_is_ground_subst]

    have "?C\<^sub>G \<in> clause.welltyped_ground_instances (C, \<V>\<^sub>1)"
      proof(
        unfold clause.welltyped_ground_instances_def mem_Collect_eq fst_conv snd_conv,
        intro exI, intro conjI C_is_welltyped resolutionI)

      show "clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next
      show "clause.is_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next
      show "is_welltyped_on (clause.vars C) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')"
        using
          is_welltyped_\<mu>_\<gamma>
          is_welltyped_\<rho>_\<mu>_\<gamma>[OF  resolutionI(6) _ resolutionI(16, 14)]
        by (simp add: subst_compose_assoc clause.vars_subst)
    next
      show "Ex (clause.welltyped \<V>\<^sub>1 C)"
        using C_is_welltyped
        by simp
    qed

    then have entails_C\<^sub>G: "?I \<TTurnstile> ?C\<^sub>G"
      using C_entails_ground_instances
      by blast

    have "?D\<^sub>G \<in> clause.welltyped_ground_instances (D, \<V>\<^sub>2)"
    proof(
        unfold clause.welltyped_ground_instances_def mem_Collect_eq fst_conv snd_conv,
        intro exI, intro conjI D_is_welltyped resolutionI)

      show "clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        by simp
    next
      show "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next

      show "is_welltyped_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
        using
          is_welltyped_\<mu>_\<gamma>
          is_welltyped_\<rho>_\<mu>_\<gamma>[OF resolutionI(7) _ resolutionI(17, 15)]
        by (simp add: subst_compose_assoc clause.vars_subst)
    next
      show "Ex (clause.welltyped \<V>\<^sub>2 D)"
        using D_is_welltyped
        by blast
    qed

    then have entails_D\<^sub>G: "?I \<TTurnstile> ?D\<^sub>G"
      using D_entails_ground_instances
      by blast

    have "?I \<TTurnstile> clause.to_ground (R \<cdot> \<gamma>')"
    proof -
      have [simp]: "?t\<^sub>G\<^sub>1 = ?t\<^sub>G\<^sub>2"
        using resolutionI(9) term_subst.is_imgu_unifies_pair
        by metis

      have [simp]: "?l\<^sub>G\<^sub>1 = Neg ?t\<^sub>G\<^sub>1"
        unfolding resolutionI
        by simp

      have [simp]: "?l\<^sub>G\<^sub>2 = Pos ?t\<^sub>G\<^sub>2"
        unfolding resolutionI
        by simp

      have [simp]: "?C\<^sub>G = add_mset ?l\<^sub>G\<^sub>1 ?C\<^sub>G'"
        unfolding resolutionI
        by simp

      have [simp]: "?D\<^sub>G = add_mset ?l\<^sub>G\<^sub>2 ?D\<^sub>G'"
        unfolding resolutionI
        by simp

      have "(\<not> ?I \<TTurnstile>l ?l\<^sub>G\<^sub>1) \<or> (\<not> ?I \<TTurnstile>l ?l\<^sub>G\<^sub>2)"
        by simp

      then have "(?I \<TTurnstile> ?C\<^sub>G') \<or> (?I \<TTurnstile> ?D\<^sub>G')"
        using entails_C\<^sub>G entails_D\<^sub>G
        by force

      have "?R\<^sub>G = ?C\<^sub>G' + ?D\<^sub>G'"
        unfolding resolutionI
        by simp

      then show ?thesis
        using `(?I \<TTurnstile> ?C\<^sub>G') \<or> (?I \<TTurnstile> ?D\<^sub>G')`
        by auto
    qed

    then have "?I \<TTurnstile> clause.to_ground (R \<cdot> \<gamma>)"
      by (metis \<gamma>'_\<gamma> clause.subst_eq)
  }

  then show ?thesis
    unfolding
      ground.G_entails_def clause.welltyped_ground_instances_def true_clss_def resolutionI(1-3)
    by auto   
qed

end

sublocale grounded_resolution_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" "(\<TTurnstile>\<^sub>F)"
proof unfold_locales
fix \<iota>

  assume "\<iota> \<in> inferences"

  then show "set (prems_of \<iota>) \<TTurnstile>\<^sub>F {concl_of \<iota>}"
    using
      factoring_sound
      resolution_sound
    unfolding inferences_def ground.G_entails_def
    by auto
qed

sublocale resolution_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" entails_\<G>
proof unfold_locales
  obtain select\<^sub>G where select\<^sub>G: "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    using Q_nonempty by blast

  then interpret grounded_resolution_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  fix \<iota>
  assume "\<iota> \<in> inferences"

  then show "entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding entails_def
    using sound
    by blast
qed
end