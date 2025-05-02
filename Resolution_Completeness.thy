theory Resolution_Completeness
  imports
    Grounded_Resolution
    Ground_Order_Resolution_Completeness
    Resolution_Welltypedness_Preservation

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
      by auto

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
    proof (rule factoringI; (rule D imgu refl \<V>)?)
      show "select D = {#}"
        using ground_factoringI(3) select
        by simp
    next
      have "l\<^sub>1 \<cdot>l \<mu> \<in># D \<cdot> \<mu>"
        using l\<^sub>1_is_maximal clause.subst_in_to_set_subst maximal_in_clause
        by blast

      then show "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
        using is_maximal_if_grounding_is_maximal D_grounding l\<^sub>1_\<gamma>_is_maximal
        unfolding \<gamma>
        by auto       
    next
      show "D = add_mset l\<^sub>1 (add_mset (Pos t\<^sub>2) D')"
        unfolding D l\<^sub>2 ..
    next
      show "l\<^sub>1 = Pos t\<^sub>1"
        using l\<^sub>1 .
    qed

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
    [simp]: "\<iota>\<^sub>G \<equiv> Infer [D\<^sub>G, C\<^sub>G] R\<^sub>G"
  assumes
    ground_resolution: "ground.resolution C\<^sub>G D\<^sub>G R\<^sub>G" and
    \<rho>\<^sub>1: "term_subst.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term_subst.is_renaming \<rho>\<^sub>2" and
    rename_apart: "clause.vars (C \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}" and
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
    "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(D, \<V>\<^sub>2), (C, \<V>\<^sub>1)] (R', \<V>\<^sub>3))"
    "R' \<cdot> \<gamma> = R \<cdot> \<gamma>"
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
    l\<^sub>C_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal l\<^sub>C C" and
    l\<^sub>C_\<gamma>_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal (l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    l\<^sub>C_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal l\<^sub>C (select C)" and
    l\<^sub>C_\<gamma>_selected: "?select\<^sub>G_not_empty \<Longrightarrow>is_maximal (l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) ((select C) \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and   
    l\<^sub>C_in_C: "l\<^sub>C \<in># C"
  proof-
    have C_not_empty: "C \<noteq> {#}"
      using ground_resolutionI(1)
      by auto

    then obtain max_l where
      "is_maximal max_l C" and
      is_max_in_C_\<gamma>: "is_maximal (max_l \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
      using that C_grounding obtain_maximal_literal C_not_empty
      by blast

    moreover then have "max_l \<in># C" 
      unfolding is_maximal_def
      by blast

    moreover have "max_l \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground L\<^sub>G\<^sub>C" if ?select\<^sub>G_empty
    proof-
      have "ground_is_maximal L\<^sub>G\<^sub>C C\<^sub>G"
        using ground_resolutionI(6) that
        unfolding is_maximal_def
        by simp

      then show ?thesis
        using unique_maximal_in_ground_clause[OF C_grounding is_max_in_C_\<gamma>] C_grounding
        unfolding ground_resolutionI(3)
        by simp
    qed

    then obtain selected_l where
      "is_maximal selected_l (select C)"
      "is_maximal (selected_l \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) ((select C) \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
      "selected_l \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground L\<^sub>G\<^sub>C"
    if ?select\<^sub>G_not_empty
    proof-
      have "is_maximal (literal.from_ground L\<^sub>G\<^sub>C) ((select C) \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
        if ?select\<^sub>G_not_empty
        using ground_resolutionI(6) that
        unfolding ground_resolutionI(3)
        by (metis C\<^sub>G_def select_from_C)

      then show ?thesis
        using
          that
          obtain_maximal_literal[OF _ select_ground_subst[OF C_grounding]]
          unique_maximal_in_ground_clause[OF select_ground_subst[OF C_grounding]]
        by (metis (no_types, lifting) clause.magma_subst_empty(1) is_maximal_not_empty)
     qed

    moreover then have "selected_l \<in># C" if ?select\<^sub>G_not_empty
      using that maximal_in_clause mset_subset_eqD select_subset
      by meson

    ultimately show ?thesis
      using that ground_resolutionI
      using \<open>select\<^sub>G (clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) = {#} \<Longrightarrow> max_l \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground L\<^sub>G\<^sub>C\<close> 
      by blast
    qed

  obtain C' where C: "C = add_mset l\<^sub>C C'"
    by (meson l\<^sub>C_in_C multi_member_split)

  then have C'_\<gamma>: "C' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground C\<^sub>G'"
    using l\<^sub>C_\<gamma> C_\<gamma>
    by auto

  obtain t\<^sub>C where 
    l\<^sub>C: "l\<^sub>C = Neg t\<^sub>C" and
    t\<^sub>C_\<gamma>: "t\<^sub>C \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G"
    using l\<^sub>C_\<gamma> 
    by (metis Neg_atm_of_iff literal_from_ground_atom_from_ground(1) clause_safe_unfolds(9)
        ground_resolutionI(3) literal.sel(2) subst_polarity_stable(2))

  obtain l\<^sub>D where
    l\<^sub>D_\<gamma>: "l\<^sub>D \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = literal.from_ground L\<^sub>G\<^sub>D" and
    l\<^sub>D_is_strictly_maximal: "is_strictly_maximal l\<^sub>D D"
  proof-
    have "is_strictly_maximal (literal.from_ground L\<^sub>G\<^sub>D) (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
      using ground_resolutionI(8) D_grounding
      by simp

    then show ?thesis
      using obtain_strictly_maximal_literal[OF D_grounding] that
      by force
  qed

  then have l\<^sub>D_in_D: "l\<^sub>D \<in># D"
    using strictly_maximal_in_clause
    by blast

  from l\<^sub>D_\<gamma> have l\<^sub>D_\<gamma>: "l\<^sub>D \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = (Pos (term.from_ground t\<^sub>G))"
    unfolding ground_resolutionI
    by simp

  then obtain t\<^sub>D where
    l\<^sub>D: "l\<^sub>D = Pos t\<^sub>D" and
    t\<^sub>D_\<gamma>: "t\<^sub>D \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G"
    by (metis clause_safe_unfolds(9) literal.collapse(1) literal.disc(1) literal.sel(1) subst_polarity_stable(2))

  obtain D' where D: "D = add_mset l\<^sub>D D'"
    by (meson l\<^sub>D_in_D multi_member_split)

  then have D'_\<gamma>: "D' \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground D\<^sub>G'"
    using D_\<gamma> l\<^sub>D_\<gamma>
    unfolding ground_resolutionI
    by auto

  obtain \<V>\<^sub>3 where
    \<V>\<^sub>3: "infinite_variables_per_type \<V>\<^sub>3" and
    \<V>\<^sub>1_\<V>\<^sub>3: "\<forall>x\<in>clause.vars C. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x)" and
    \<V>\<^sub>2_\<V>\<^sub>3: "\<forall>x\<in>clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x)"
    using clause.obtain_merged_\<V>[OF \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart clause.finite_vars clause.finite_vars 
                                 infinite_UNIV] .
  have \<gamma>_is_welltyped: "is_welltyped_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
  proof(unfold Set.ball_Un, intro conjI)

    show "is_welltyped_on (clause.vars (C \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<gamma>"
      using clause.renaming_grounding[OF \<rho>\<^sub>1 \<rho>\<^sub>1_\<gamma>_is_welltyped C_grounding \<V>\<^sub>1_\<V>\<^sub>3] .
  next

    show "is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
      using clause.renaming_grounding[OF \<rho>\<^sub>2 \<rho>\<^sub>2_\<gamma>_is_welltyped D_grounding \<V>\<^sub>2_\<V>\<^sub>3] .
  qed

  obtain \<mu> \<sigma> where
    \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and
    imgu: "welltyped_imgu_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>C \<cdot>t \<rho>\<^sub>1) (t\<^sub>D \<cdot>t \<rho>\<^sub>2) \<mu>"
  proof-

    have unified: "t\<^sub>C \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = t\<^sub>D \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>"
      using t\<^sub>C_\<gamma> t\<^sub>D_\<gamma>
      by simp

    obtain \<tau> where welltyped: "welltyped \<V>\<^sub>3 (t\<^sub>C \<cdot>t \<rho>\<^sub>1) \<tau>" "welltyped \<V>\<^sub>3 (t\<^sub>D \<cdot>t \<rho>\<^sub>2) \<tau>"
    proof-
      have "clause.is_welltyped \<V>\<^sub>2 (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
        using \<rho>\<^sub>2_\<gamma>_is_welltyped D_is_welltyped
        by (metis clause.welltyped_subst_stability)

      then obtain \<tau> where
        "welltyped \<V>\<^sub>2 (term.from_ground t\<^sub>G) \<tau>"
        unfolding D_\<gamma> ground_resolutionI
        by auto

      then have "welltyped \<V>\<^sub>3 (term.from_ground t\<^sub>G) \<tau>"
        using term.is_ground_typed
        by (meson term.ground_is_ground term.is_ground_typed)

      then have "welltyped \<V>\<^sub>3 (t\<^sub>C \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) \<tau>" "welltyped \<V>\<^sub>3 (t\<^sub>D \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma>) \<tau>"
        using t\<^sub>C_\<gamma> t\<^sub>D_\<gamma>
        by presburger+

      moreover have
        "term.vars (t\<^sub>C \<cdot>t \<rho>\<^sub>1) \<subseteq> clause.vars (C \<cdot> \<rho>\<^sub>1)"
        "term.vars (t\<^sub>D \<cdot>t \<rho>\<^sub>2) \<subseteq> clause.vars (D \<cdot> \<rho>\<^sub>2)"
        unfolding C l\<^sub>C clause.add_subst D l\<^sub>D
        by auto

      ultimately have "welltyped \<V>\<^sub>3 (t\<^sub>C \<cdot>t \<rho>\<^sub>1) \<tau>" "welltyped \<V>\<^sub>3 (t\<^sub>D \<cdot>t \<rho>\<^sub>2) \<tau>"
        using \<gamma>_is_welltyped
        by (simp_all add: subsetD)

      then show ?thesis
        using that
        by blast
    qed

    show ?thesis
      using obtain_welltyped_imgu_on[OF unified welltyped] that
      by metis
  qed

  define R' where
    R': "R' = (C' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"

  show ?thesis
  proof(rule that)

    show resolution: "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R', \<V>\<^sub>3)"
    proof(rule resolutionI;
          ((rule \<rho>\<^sub>1 \<rho>\<^sub>2 C D l\<^sub>C l\<^sub>D imgu rename_apart \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped \<V>\<^sub>1 \<V>\<^sub>2 R'
               \<V>\<^sub>1_\<V>\<^sub>3 \<V>\<^sub>2_\<V>\<^sub>3)+)?)
      show "clause.vars (D \<cdot> \<rho>\<^sub>2) \<inter> clause.vars (C \<cdot> \<rho>\<^sub>1) = {}"
        using rename_apart
        by blast
    next
      show "(\<exists>\<tau>. welltyped \<V>\<^sub>3 (t\<^sub>C \<cdot>t \<rho>\<^sub>1) \<tau> \<and> welltyped \<V>\<^sub>3 (t\<^sub>D \<cdot>t \<rho>\<^sub>2) \<tau>) \<and>
      is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2) \<union> clause.vars (C \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<mu> \<and> term.is_imgu \<mu> {{t\<^sub>C \<cdot>t \<rho>\<^sub>1, t\<^sub>D \<cdot>t \<rho>\<^sub>2}}"
        using imgu
        by blast
    next
      show "\<not> C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>"
      proof(rule clause.order.ground_less_not_less_eq)

        show "clause.vars (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>) = {}"
          using D_grounding
          unfolding \<gamma>
          by simp

        show "clause.vars (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>) = {}"
          using C_grounding
          unfolding \<gamma>
          by simp

        show "D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma> \<prec>\<^sub>c C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>"
          using ground_resolutionI(5) D_grounding C_grounding
          unfolding C\<^sub>G_def D\<^sub>G_def clause.order.less\<^sub>G_def \<gamma>
          by simp
      qed
    next
      show "select C = {#} \<and> is_maximal (l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or> is_maximal (l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (select C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
      proof(cases "select C = {#}")
        case True
        then have "?select\<^sub>G_empty"
          using is_maximal_not_empty l\<^sub>C_selected 
          by blast

        moreover have "l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
          using l\<^sub>C_in_C
          by blast

        ultimately show ?thesis
          using l\<^sub>C_\<gamma>_is_maximal is_maximal_if_grounding_is_maximal C_grounding True
          unfolding \<gamma>
          by force
      next
        case False
        then have "\<not>?select\<^sub>G_empty"
          using is_maximal_not_empty l\<^sub>C_selected select_from_C 
          by auto

        moreover have "l\<^sub>C \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># select C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
          using l\<^sub>C_selected maximal_in_clause calculation 
          by blast

        ultimately show ?thesis
          using select_ground_subst[OF C_grounding]
            l\<^sub>C_selected is_maximal_if_grounding_is_maximal
          unfolding \<gamma>
          by (metis (no_types, lifting) C\<^sub>G_def \<gamma> clause.comp_subst.left.monoid_action_compatibility ground_resolutionI(6) l\<^sub>C_\<gamma>
              literal.comp_subst.left.monoid_action_compatibility select_from_C)
      qed
    next
      show "select D = {#}"
        using ground_resolutionI(7) select_from_D 
        by fastforce
    next
      show "is_strictly_maximal (l\<^sub>D \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
      proof(rule is_strictly_maximal_if_grounding_is_strictly_maximal)

        show "l\<^sub>D \<cdot>l \<rho>\<^sub>2 \<odot> \<mu> \<in># D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>"
          using l\<^sub>D_in_D
          by blast

        show "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>)"
          using D_grounding[unfolded \<gamma>]
          by simp

        show "is_strictly_maximal (l\<^sub>D \<cdot>l \<rho>\<^sub>2 \<odot> \<mu> \<cdot>l \<sigma>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>)"
          using l\<^sub>D_\<gamma> D_\<gamma> ground_resolutionI(8)
          unfolding \<gamma> ground_resolutionI
          by fastforce
      qed
    qed
  
    show R'_\<gamma>: "R' \<cdot> \<gamma> = R \<cdot> \<gamma>"
    proof-

      have "term_subst.is_idem \<mu>"
        using imgu term.is_imgu_iff_is_idem_and_is_mgu
        by blast

      then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
        unfolding \<gamma> term_subst.is_idem_def
        by (metis subst_compose_assoc)

      have "R \<cdot> \<gamma> = (clause.from_ground C\<^sub>G' + clause.from_ground D\<^sub>G')"
        using ground_resolutionI(8, 9) clause.to_ground_inverse[OF R_grounding]
        by auto

      then show ?thesis
        unfolding
          R'
          C'_\<gamma>[symmetric]
          D'_\<gamma>[symmetric]
          clause.subst_comp_subst[symmetric]
          \<mu>_\<gamma>
        by simp
    qed

    show "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(D, \<V>\<^sub>2), (C, \<V>\<^sub>1)] (R', \<V>\<^sub>3))"
    proof (rule is_inference_ground_instance_two_premises)

      show "is_inference_ground_instance_two_premises (D, \<V>\<^sub>2) (C, \<V>\<^sub>1) (R', \<V>\<^sub>3) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      proof(unfold split, intro conjI;
            (rule \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart D_is_welltyped C_is_welltyped refl \<V>\<^sub>1 \<V>\<^sub>2 \<V>\<^sub>3)?)

        show "inference.is_ground (Infer [D \<cdot> \<rho>\<^sub>2, C \<cdot> \<rho>\<^sub>1] R' \<cdot>\<iota> \<gamma>)"
          using  D_grounding C_grounding R_grounding R'_\<gamma>
          by auto
      next

        show "\<iota>\<^sub>G = inference.to_ground (Infer [D \<cdot> \<rho>\<^sub>2, C \<cdot> \<rho>\<^sub>1] R' \<cdot>\<iota> \<gamma>)"
          using R'_\<gamma>
          by simp
      next
        show "clause.is_welltyped \<V>\<^sub>3 R'"
          using resolution C_is_welltyped D_is_welltyped resolution_preserves_typing 
          by fastforce
      next
        show "is_welltyped_on (clause.vars R') \<V>\<^sub>3 \<gamma>"
        proof(rule is_welltyped_on_subset[OF \<gamma>_is_welltyped])

          show "clause.vars R' \<subseteq> clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
          proof (unfold subset_eq, intro ballI)
            fix x

            have is_imgu: "term.is_imgu \<mu> {{t\<^sub>C \<cdot>t \<rho>\<^sub>1, t\<^sub>D \<cdot>t \<rho>\<^sub>2}}"
              using imgu
              by blast

            assume "x \<in> clause.vars R'"

            then consider
              (C') "x \<in> clause.vars (C' \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)" |
              (D') "x \<in> clause.vars (D' \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
              unfolding R'
              by auto

            then show "x \<in> clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
            proof cases
              case C'

              then show ?thesis
                using clause.variables_in_base_imgu[OF is_imgu]
                unfolding C l\<^sub>C D l\<^sub>D
                by auto
            next
              case D'

              then show ?thesis
                using clause.variables_in_base_imgu[OF is_imgu]
                unfolding C l\<^sub>C D l\<^sub>D
                by auto
            qed
          qed
        qed
      qed
        show "\<iota>\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_resolution
        by simp
    qed
  qed
qed

subsection \<open>Ground instances\<close>

context
  fixes \<iota>\<^sub>G N
  assumes
    subst_stability: "subst_stability_on N" and
    \<iota>\<^sub>G_Inf_from: "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause.welltyped_ground_instances ` N))"
begin

lemma single_premise_ground_instance:
  assumes
    ground_inference: "\<iota>\<^sub>G \<in>  {Infer [D] C | D C. ground_inference D C}" and
    lifting: "\<And>D \<gamma> C \<V> thesis. \<lbrakk>
    ground_inference (clause.to_ground (D \<cdot> \<gamma>)) (clause.to_ground (C \<cdot> \<gamma>));
    clause.is_ground (D \<cdot> \<gamma>);
    clause.is_ground (C \<cdot> \<gamma>);
    clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<gamma>))) = select D \<cdot> \<gamma>;
    clause.is_welltyped \<V> D; 
    is_welltyped_on (clause.vars D) \<V> \<gamma>;
    infinite_variables_per_type \<V>;
    \<And>C'. \<lbrakk>
        inference (D, \<V>) (C', \<V>);
        Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C \<cdot> \<gamma>))
        \<in> inference_ground_instances (Infer [(D, \<V>)] (C', \<V>));
        C' \<cdot> \<gamma> = C \<cdot> \<gamma>\<rbrakk> \<Longrightarrow> thesis\<rbrakk>
       \<Longrightarrow> thesis" and
    inference_eq: "inference = factoring"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
proof-
  obtain D\<^sub>G C\<^sub>G where
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer [D\<^sub>G] C\<^sub>G" and
    ground_inference: "ground_inference D\<^sub>G C\<^sub>G"
    using ground_inference
    by blast

  have D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union>(clause.welltyped_ground_instances ` N)"
    using \<iota>\<^sub>G_Inf_from
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain D \<gamma> \<V> where
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    D_is_welltyped: "clause.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>" and
    D_in_N: "(D, \<V>)\<in>N" and
    "select\<^sub>G D\<^sub>G = clause.to_ground (select D \<cdot> \<gamma>)"
    "D \<cdot> \<gamma> = clause.from_ground D\<^sub>G"
    using subst_stability[rule_format, OF D\<^sub>G_in_groundings]
    by blast

  then have
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>"
    by (simp_all add: select_ground_subst)

  obtain C where
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)"
    by (metis clause.all_subst_ident_iff_ground clause.from_ground_inverse
        clause.ground_is_ground)

  obtain C' where
    inference: "inference (D, \<V>) (C', \<V>)" and
    inference_ground_instances: "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(D, \<V>)] (C', \<V>))" and
    C'_C: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using
      lifting[OF
        ground_inference[unfolded D\<^sub>G C\<^sub>G]
        D_grounding
        C_grounding
        select[unfolded D\<^sub>G]
        D_is_welltyped
        \<gamma>_is_welltyped
        \<V>]
    unfolding D\<^sub>G C\<^sub>G \<iota>\<^sub>G.

  let ?\<iota> = "Infer [(D, \<V>)] (C', \<V>)"

  show ?thesis
  proof(rule that[OF _ inference_ground_instances])

    show "?\<iota> \<in> Inf_from N"
      using D_in_N inference inference_eq
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto
  qed
qed

lemma factoring_ground_instance:
  assumes ground_factoring: "\<iota>\<^sub>G \<in> ground.factoring_inferences"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
  using factoring_lifting single_premise_ground_instance[OF ground_factoring]
  by blast

lemma resolution_ground_instance:
  assumes
    ground_resolution: "\<iota>\<^sub>G \<in> ground.resolution_inferences" and
    not_redundant: "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (clause.welltyped_ground_instances ` N))"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
proof-
obtain C\<^sub>G D\<^sub>G R\<^sub>G where
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [C\<^sub>G, D\<^sub>G] R\<^sub>G" and
    ground_resolution: "ground.resolution C\<^sub>G D\<^sub>G R\<^sub>G"
    using assms(1)
    by blast

  have
    C\<^sub>G_in_groundings: "C\<^sub>G \<in> \<Union> (clause.welltyped_ground_instances ` N)" and
    D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union> (clause.welltyped_ground_instances ` N)"
    using \<iota>\<^sub>G_Inf_from
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain C \<V>\<^sub>1 \<gamma>\<^sub>1 where
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>\<^sub>1)" and
    C_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 C" and
    \<gamma>\<^sub>1_is_welltyped: "is_welltyped_on (clause.vars C) \<V>\<^sub>1 \<gamma>\<^sub>1" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    C_in_N: "(C, \<V>\<^sub>1)\<in>N" and
    "select\<^sub>G C\<^sub>G = clause.to_ground (select C \<cdot> \<gamma>\<^sub>1)"
    "C \<cdot> \<gamma>\<^sub>1 = clause.from_ground C\<^sub>G"
    using subst_stability[rule_format, OF C\<^sub>G_in_groundings]
    by blast

  then have
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>\<^sub>1)" and
    select_from_C: "clause.from_ground (select\<^sub>G C\<^sub>G) = select C \<cdot> \<gamma>\<^sub>1"
    by (simp_all add: select_ground_subst)

  obtain D \<V>\<^sub>2 \<gamma>\<^sub>2 where
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>\<^sub>2)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    \<gamma>\<^sub>2_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<gamma>\<^sub>2" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    D_in_N: "(D, \<V>\<^sub>2)\<in>N" and
    "select\<^sub>G D\<^sub>G = clause.to_ground (select D \<cdot> \<gamma>\<^sub>2)"
    "D \<cdot> \<gamma>\<^sub>2 = clause.from_ground D\<^sub>G"
    using subst_stability[rule_format, OF D\<^sub>G_in_groundings]
    by blast

  then have
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>\<^sub>2)" and
    select_from_D: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>\<^sub>2"
    by (simp_all add: select_ground_subst)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 \<gamma> :: "('f, 'v) subst" where
    \<rho>\<^sub>1: "term_subst.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term_subst.is_renaming \<rho>\<^sub>2" and
    rename_apart: "clause.vars (C \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}" and
    \<rho>\<^sub>1_is_welltyped: "is_welltyped_on (clause.vars C) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2" and
    \<gamma>\<^sub>1_\<gamma>: "\<forall>x \<in> clause.vars C. \<gamma>\<^sub>1 x = (\<rho>\<^sub>1 \<odot> \<gamma>) x" and
    \<gamma>\<^sub>2_\<gamma>: "\<forall>x \<in> clause.vars D. \<gamma>\<^sub>2 x = (\<rho>\<^sub>2 \<odot> \<gamma>) x"
    using clause.obtain_merged_grounding[OF
            \<gamma>\<^sub>1_is_welltyped \<gamma>\<^sub>2_is_welltyped C_grounding D_grounding \<V>\<^sub>2 clause.finite_vars].

  have C_grounding: "clause.is_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>1_\<gamma> C_grounding
    by fastforce

  have C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>1_\<gamma> C\<^sub>G
    by fastforce

  have D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>2_\<gamma> D_grounding
    by fastforce

  have D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using clause.subst_eq \<gamma>\<^sub>2_\<gamma> D\<^sub>G
    by fastforce

  have \<rho>\<^sub>1_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars C) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    using \<gamma>\<^sub>1_is_welltyped \<gamma>\<^sub>1_\<gamma>
    by fastforce

  have \<rho>\<^sub>2_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    using \<gamma>\<^sub>2_is_welltyped \<gamma>\<^sub>2_\<gamma>
    by fastforce

  have select_from_C:
    "clause.from_ground (select\<^sub>G (clause.to_ground (C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>))) = select C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
  proof-
    have "C \<cdot> \<gamma>\<^sub>1 = C \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
      using \<gamma>\<^sub>1_\<gamma> clause.subst_eq
      by fast

    moreover have "select C \<cdot> \<gamma>\<^sub>1 = select C \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
      using clause.subst_eq \<gamma>\<^sub>1_\<gamma> select_vars_subset
      by (metis (no_types, lifting) clause.comp_subst.left.monoid_action_compatibility in_mono)

    ultimately show ?thesis
      using select_from_C
      unfolding C\<^sub>G
      by simp
  qed

  have select_from_D:
    "clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>))) = select D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
  proof-
    have "D \<cdot> \<gamma>\<^sub>2 = D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
      using \<gamma>\<^sub>2_\<gamma> clause.subst_eq
      by fast

    moreover have "select D \<cdot> \<gamma>\<^sub>2 = select D \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>"
      using clause.subst_eq \<gamma>\<^sub>2_\<gamma> select_vars_subset[of D]
      by (metis (no_types, lifting) clause.comp_subst.left.monoid_action_compatibility in_mono)

    ultimately show ?thesis
      using select_from_D
      unfolding D\<^sub>G
      by simp
  qed

  obtain R where
    R_grounding: "clause.is_ground (R \<cdot> \<gamma>)" and
    R\<^sub>G: "R\<^sub>G = clause.to_ground (R \<cdot> \<gamma>)"
    by (metis clause.all_subst_ident_if_ground clause.from_ground_inverse clause.ground_is_ground)

  have "clause.welltyped_ground_instances (C, \<V>\<^sub>1) \<union> clause.welltyped_ground_instances (D, \<V>\<^sub>2) \<subseteq>
          \<Union> (clause.welltyped_ground_instances ` N)"
    using C_in_N D_in_N
    by blast

  then have \<iota>\<^sub>G_not_redundant:
    "\<iota>\<^sub>G \<notin> ground.GRed_I
          (clause.welltyped_ground_instances (C, \<V>\<^sub>1) \<union> clause.welltyped_ground_instances (D, \<V>\<^sub>2))"
    using not_redundant ground.Red_I_of_subset
    by blast

  obtain R' \<V>\<^sub>3 where
    resolution: "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R', \<V>\<^sub>3)" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_ground_instances (Infer [(C, \<V>\<^sub>1), (D, \<V>\<^sub>2)] (R', \<V>\<^sub>3))" and
    R'_\<gamma>_R_\<gamma>: "R' \<cdot> \<gamma> = R \<cdot> \<gamma>"
    sorry
    (*using
      resolution_lifting[OF
        ground_resolution[unfolded C\<^sub>G D\<^sub>G R\<^sub>G]
        \<rho>\<^sub>1 \<rho>\<^sub>2
        rename_apart
        C_grounding D_grounding R_grounding
        select_from_C select_from_D
        C_is_welltyped D_is_welltyped
        \<rho>\<^sub>1_\<gamma>_is_welltyped \<rho>\<^sub>2_\<gamma>_is_welltyped
        \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped
        \<V>\<^sub>1 \<V>\<^sub>2
        \<iota>\<^sub>G_not_redundant[unfolded \<iota>\<^sub>G C\<^sub>G D\<^sub>G R\<^sub>G]]
    unfolding \<iota>\<^sub>G R\<^sub>G C\<^sub>G D\<^sub>G .*)

  let ?\<iota> = "Infer [(C, \<V>\<^sub>1), (D, \<V>\<^sub>2)] (R', \<V>\<^sub>3)"
  show ?thesis
  proof(rule that[OF _ inference_groundings])

    show "?\<iota> \<in> Inf_from N"
      using C_in_N D_in_N resolution
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto
  qed
qed

lemma ground_instances:
  assumes not_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I (\<Union> (clause.welltyped_ground_instances ` N))"
  obtains \<iota> where
    "\<iota> \<in> Inf_from N"
    "\<iota>\<^sub>G \<in> inference_ground_instances \<iota>"
proof-
  consider
    (resolution) "\<iota>\<^sub>G \<in> ground.resolution_inferences" |
    (factoring) "\<iota>\<^sub>G \<in> ground.factoring_inferences"
    using \<iota>\<^sub>G_Inf_from
    unfolding
      ground.Inf_from_q_def
      ground.G_Inf_def
      inference_system.Inf_from_def
    sorry

  then show ?thesis
  proof cases
    case resolution

    then show ?thesis
      using that resolution_ground_instance not_redundant
      by blast
  next
    case factoring

    then show ?thesis
      using that factoring_ground_instance
      by blast
  qed
qed

end
end

context resolution_calculus
begin

lemma overapproximation:
  obtains select\<^sub>G where
    "ground_Inf_overapproximated select\<^sub>G premises"
    "is_grounding select\<^sub>G"
proof-
  obtain select\<^sub>G where
    subst_stability: "select_subst_stability_on select select\<^sub>G premises" and
    "is_grounding select\<^sub>G"
    using obtain_subst_stable_on_select_grounding
    by blast

  then interpret grounded_resolution_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales

  show thesis
  proof(rule that[OF _ select\<^sub>G])

    show "ground_Inf_overapproximated select\<^sub>G premises"
      using ground_instances[OF subst_stability]
      by auto
  qed
qed

sublocale statically_complete_calculus "\<bottom>\<^sub>F" inferences entails_\<G> Red_I_\<G> Red_F_\<G>
proof (unfold static_empty_ord_inter_equiv_static_inter,
    rule stat_ref_comp_to_non_ground_fam_inter,
    rule ballI)
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"

  then interpret grounded_resolution_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "statically_complete_calculus
          ground.G_Bot
          ground.G_Inf
          ground.G_entails
          ground.Red_I
          ground.Red_F"
    by unfold_locales
next

  show "\<And>N. \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G N"
    using overapproximation
    unfolding select\<^sub>G\<^sub>s_def
    by (smt (verit, best) mem_Collect_eq)
qed
end
end