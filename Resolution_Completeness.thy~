theory Resolution_Completeness
  imports
    Grounded_Resolution
    Ground_Order_Resolution_Completeness

    First_Order_Clause.Nonground_Entailment
begin

section \<open>Completeness\<close>

context grounded_resolution_calculus
begin

subsection \<open>Liftings\<close>

lemma factoring_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'f gterm clause" and
    D C :: "('f, 'v) term clause" and
    \<gamma> :: "('f, 'v) subst"
  defines
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
  assumes
    ground_factoring: "ground.factoring D\<^sub>G C\<^sub>G" and
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<gamma>" and
    D_is_welltyped: "clause.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C'
  where
    "factoring (D, \<V>) (C', \<V>)"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_ground_instances (Infer [(D, \<V>)] (C', \<V>))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_factoring
proof(cases D\<^sub>G C\<^sub>G rule: ground.factoring.cases)
  case ground_factoringI: (factoringI L\<^sub>G D\<^sub>G' t\<^sub>G)

  have "D \<noteq> {#}"
    using ground_factoringI(1)
    by auto

  then obtain l\<^sub>1 where
    l\<^sub>1_is_maximal: "is_maximal l\<^sub>1 D" and
    l\<^sub>1_\<gamma>_is_maximal: "is_maximal (l\<^sub>1 \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
    using that obtain_maximal_literal D_grounding
    by blast

  obtain t\<^sub>1 where
    l\<^sub>1: "l\<^sub>1 = (Pos t\<^sub>1)" and
    l\<^sub>1_\<gamma>: "l\<^sub>1 \<cdot>l \<gamma> = (Pos (term.from_ground t\<^sub>G))" and
    t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<gamma> = term.from_ground t\<^sub>G"
  proof-
    have "is_maximal (literal.from_ground L\<^sub>G) (D \<cdot> \<gamma>)"
      using D_grounding ground_factoringI(4)
      by auto

    then have "l\<^sub>1 \<cdot>l \<gamma> = (Pos (term.from_ground t\<^sub>G))"
      unfolding ground_factoringI(2)
      using unique_maximal_in_ground_clause[OF D_grounding l\<^sub>1_\<gamma>_is_maximal]
      by simp

    then show ?thesis
      using that
      unfolding ground_factoringI(2)
      by (metis Neg_atm_of_iff clause_safe_unfolds(9) literal.collapse(1) literal.sel(1)
          subst_polarity_stable(2))
  qed

  obtain l\<^sub>2 D' where
    l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<gamma> = Pos (term.from_ground t\<^sub>G)" and
    D: "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D')"
  proof-
    obtain D'' where D: "D = add_mset l\<^sub>1 D''"
      using maximal_in_clause[OF l\<^sub>1_is_maximal]
      by (meson multi_member_split)

    moreover have "D \<cdot> \<gamma> = clause.from_ground (add_mset L\<^sub>G ( add_mset L\<^sub>G D\<^sub>G'))"
      using ground_factoringI(1) C\<^sub>G_def
      by (metis D\<^sub>G_def D_grounding clause.to_ground_inverse)

    ultimately have "D'' \<cdot> \<gamma> = add_mset (literal.from_ground L\<^sub>G) (clause.from_ground D\<^sub>G')"
      using l\<^sub>1_\<gamma>
      by (simp add: ground_factoringI(2))

    then obtain l\<^sub>2 where "l\<^sub>2 \<cdot>l \<gamma> = Pos (term.from_ground t\<^sub>G)" "l\<^sub>2 \<in># D''"
      unfolding clause.subst_def ground_factoringI
      using msed_map_invR
      by force

    then show ?thesis
      using that
      unfolding D
      by (metis mset_add)
  qed

  then obtain t\<^sub>2 where
    l\<^sub>2: "l\<^sub>2 = (Pos t\<^sub>2)" and
    t\<^sub>2_\<gamma>: "t\<^sub>2 \<cdot>t \<gamma> = term.from_ground t\<^sub>G"
    unfolding ground_factoringI(2)
    by (metis clause_safe_unfolds(9) is_pos_def literal.sel(1) subst_polarity_stable(2))
   

  have D'_\<gamma>: "D' \<cdot> \<gamma> = clause.from_ground D\<^sub>G'"
    using D D_grounding ground_factoringI(1,2,3) l\<^sub>1_\<gamma> l\<^sub>2_\<gamma>
    by force

  obtain \<mu> \<sigma> where \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and imgu: "welltyped_imgu_on (clause.vars D) \<V> t\<^sub>1 t\<^sub>2 \<mu>"
  proof-
    have unified: "t\<^sub>1 \<cdot>t \<gamma> = t\<^sub>2 \<cdot>t \<gamma>"
      unfolding t\<^sub>1_\<gamma> t\<^sub>2_\<gamma> ..

    then obtain \<tau> where "welltyped \<V> (t\<^sub>1 \<cdot>t \<gamma>) \<tau>" "welltyped \<V> (t\<^sub>2 \<cdot>t \<gamma>) \<tau>"
      using D_is_welltyped \<gamma>_is_welltyped
      unfolding D l\<^sub>1 l\<^sub>2
      apply auto
      by (meson literal.is_welltyped_def literal.set_intros(1))

    then have welltyped: "welltyped \<V> t\<^sub>1 \<tau>" "welltyped \<V> t\<^sub>2 \<tau>"
      using \<gamma>_is_welltyped
      unfolding D l\<^sub>1 l\<^sub>2
      by simp_all

    then show ?thesis
      using obtain_welltyped_imgu_on[OF unified welltyped] that
      by metis
  qed

  let ?C'' = "add_mset l\<^sub>1 D'"
  let ?C' = "?C'' \<cdot> \<mu>"

  show ?thesis
  proof(rule that)

    show factoring: "factoring (D, \<V>) (?C', \<V>)"
      sorry
(*
    proof (rule factoringI; (rule D l\<^sub>1 l\<^sub>2 imgu refl \<V>)?)
      show "select D = {#}"
        using ground_factoringI(3) select
        by simp
    next
      have "l\<^sub>1 \<cdot>l \<mu> \<in># D \<cdot> \<mu>"
        using l\<^sub>1_is_maximal clause.subst_in_to_set_subst maximal_in_clause
        by blast

      then have "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
        using is_maximal_if_grounding_is_maximal D_grounding l\<^sub>1_\<gamma>_is_maximal
        unfolding \<gamma>
        by auto
    next
      have "(\<exists>\<tau>. welltyped \<V> t\<^sub>1 \<tau>) \<and> is_welltyped_on (clause.vars D) \<V> \<mu> \<and> term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>1}}"
        sorry
    next
      show "D = add_mset l\<^sub>1 (add_mset l\<^sub>1 D')"
      proof-
        have "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D')"
          by (rule D)
        moreover have "l\<^sub>1 = l\<^sub>2"
        proof-
          have "t\<^sub>1 \<cdot>t \<mu> = t\<^sub>2 \<cdot>t \<mu>"
            using imgu term.subst_imgu_eq_subst_imgu 
            by blast
          moreover have "l\<^sub>1 = Pos t\<^sub>1" "l\<^sub>2 = Pos t\<^sub>2"
            by (rule l\<^sub>1, rule l\<^sub>2)
          ultimately show ?thesis
            sorry   
        qed
        ultimately show ?thesis
          sorry
      qed
    qed*)

    show C'_\<gamma>: "?C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    proof-
      have "term.is_idem \<mu>"
        using imgu
        unfolding term_subst.is_imgu_iff_is_idem_and_is_mgu
        by blast

      then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
        unfolding \<gamma> term_subst.is_idem_def subst_compose_assoc[symmetric]
        by argo

      have "C \<cdot> \<gamma> = clause.from_ground (add_mset (Pos t\<^sub>G) D\<^sub>G')"
        using ground_factoringI(5) clause.to_ground_eq[OF C_grounding clause.ground_is_ground]
        unfolding C\<^sub>G_def
        by (metis clause.from_ground_inverse ground_factoringI(2))

      also have "... = ?C'' \<cdot> \<gamma>"
        using t\<^sub>1_\<gamma> D'_\<gamma> l\<^sub>1_\<gamma>
        by auto

      also have "... = ?C' \<cdot> \<gamma>"
        unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma> ..

      finally show ?thesis ..
    qed

    show "Infer [D\<^sub>G] C\<^sub>G \<in> inference_ground_instances (Infer [(D, \<V>)] (?C', \<V>))"
    proof (rule is_inference_ground_instance_one_premise)
      show "is_inference_ground_instance_one_premise (D, \<V>) (?C', \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
      proof(unfold split, intro conjI; (rule D_is_welltyped refl \<V>)?)

        show "inference.is_ground (Infer [D] ?C' \<cdot>\<iota> \<gamma>)"
          using C_grounding D_grounding C'_\<gamma>
          by auto
      next

        show "Infer [D\<^sub>G] C\<^sub>G = inference.to_ground (Infer [D] ?C' \<cdot>\<iota> \<gamma>)"
          using C'_\<gamma>
          by simp
      next

        have imgu: "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
          using imgu
          by blast

        have "clause.vars ?C' \<subseteq> clause.vars D"
          using clause.variables_in_base_imgu[OF imgu, of ?C'']
          unfolding D l\<^sub>1 l\<^sub>2
          by auto

        then show "is_welltyped_on (clause.vars ?C') \<V> \<gamma>"
          using D_is_welltyped \<gamma>_is_welltyped
          by blast
      next
        (* use factoring_preserves_typing here later *)
        show "clause.is_welltyped \<V> ?C'"
          using D_is_welltyped factoring
          by (simp add: D imgu)
      qed

      show "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_factoring
        by blast
    qed
  qed
qed
      
lemma resolution_lifting:
  fixes 
    C\<^sub>G D\<^sub>G R\<^sub>G :: "'f gterm clause" and
    C D R :: "('f, 'v) term clause" and
    \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" and
    \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  defines
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    [simp]: "R\<^sub>G \<equiv> clause.to_ground (R \<cdot> \<gamma>)" and
    [simp]: "N\<^sub>G \<equiv> clause.welltyped_ground_instances (C, \<V>\<^sub>1) \<union>
                    clause.welltyped_ground_instances (D, \<V>\<^sub>2)" and
    [simp]: "\<iota>\<^sub>G \<equiv> Infer [C\<^sub>G, D\<^sub>G] R\<^sub>G"
  assumes
    ground_resolution: "ground.resolution C\<^sub>G D\<^sub>G R\<^sub>G" and
    \<rho>\<^sub>1: "term_subst.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term_subst.is_renaming \<rho>\<^sub>2" and
    C_grounding: "clause.is_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    R_grounding: "clause.is_ground (R \<cdot> \<gamma>)" and
    select_from_C: "clause.from_ground (select\<^sub>G C\<^sub>G) = (select C) \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>" and
    select_from_D: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>" and
    C_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 C" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    \<rho>\<^sub>1_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars C) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)" and
    \<rho>\<^sub>2_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)" and
    \<rho>\<^sub>1_is_welltyped: "is_welltyped_on (clause.vars C) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    not_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I N\<^sub>G"
  obtains R' \<V>\<^sub>3
  where
    "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R', \<V>\<^sub>3)"
    "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(C, \<V>\<^sub>1), (D, \<V>\<^sub>2)] (R', \<V>\<^sub>3))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_resolution
proof(cases C\<^sub>G D\<^sub>G R\<^sub>G rule: ground.resolution.cases)
  case ground_resolutionI: (resolutionI L\<^sub>G\<^sub>C C\<^sub>G' L\<^sub>G\<^sub>D D\<^sub>G' t\<^sub>G)

  have C_\<gamma>: "C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground (add_mset L\<^sub>G\<^sub>C C\<^sub>G')"
    using ground_resolutionI(1)
    unfolding C\<^sub>G_def
    by (metis C_grounding clause.to_ground_inverse)

  have D_\<gamma>: "D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground (add_mset L\<^sub>G\<^sub>D  D\<^sub>G')"
    using ground_resolutionI(2) D\<^sub>G_def
    by (metis D_grounding clause.to_ground_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) \<noteq> {#}"

  obtain l\<^sub>C where
    l\<^sub>C_\<gamma>: "l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground L\<^sub>G\<^sub>C" and
    l\<^sub>C_in_C: "l\<^sub>C \<in># C" and
    l\<^sub>C_selected: "?select\<^sub>G_not_empty \<Longrightarrow> l\<^sub>C \<in># (select C)" and
    l\<^sub>C_\<gamma>_selected: "?select\<^sub>G_not_empty \<Longrightarrow> (l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) \<in># (select (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>))" and
    l\<^sub>C_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal l\<^sub>C C" and
    l\<^sub>C_\<gamma>_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal (l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
  proof-
    obtain max_l\<^sub>C where
      "is_maximal max_l\<^sub>C C" and
      is_max_in_C_\<gamma>: "is_maximal (max_l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    proof-
      have C_not_empty: "C \<noteq> {#}"
      using ground_resolutionI(1)
      by auto

    then show ?thesis
      using that C_grounding obtain_maximal_literal
      by blast
  qed

  moreover then have "max_l\<^sub>C \<in># C"
    unfolding is_maximal_def
    by blast

  moreover have "max_l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = (Neg (term.from_ground t\<^sub>G))" if ?select\<^sub>G_empty
  proof(rule unique_maximal_in_ground_clause[OF C_grounding is_max_in_C_\<gamma>])
    have "ground_is_maximal L\<^sub>G\<^sub>C C\<^sub>G"
      using ground_resolutionI(3) ground_resolutionI(6) that
      unfolding is_maximal_def
      by simp

    then show "is_maximal (Neg (term.from_ground t\<^sub>G)) (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
        using C_grounding
        unfolding ground_resolutionI(3)
        by simp
    qed

    moreover obtain selected_l\<^sub>C where
qed
end
end