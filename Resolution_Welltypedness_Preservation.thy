theory Resolution_Welltypedness_Preservation
  imports Resolution
begin

context resolution_calculus
begin

lemma factoring_preserves_typing_C:
  assumes 
  factoring: "factoring (C, \<V>) (D, \<V>)" and
  D_is_welltyped: "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using factoring
proof (cases "(C, \<V>)" "(D, \<V>)" rule: factoring.cases)
  case (factoringI L\<^sub>1 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>2 C')
  
  have "clause.is_welltyped \<V> ((add_mset L\<^sub>1 C') \<cdot> \<mu>)"
    using D_is_welltyped
    unfolding factoringI .

  then have "clause.is_welltyped \<V> (add_mset L\<^sub>1 C')"
    using factoringI(3)
    unfolding factoringI
    by simp

  moreover have "literal.is_welltyped \<V> L\<^sub>2"
    using factoringI(3) literal.is_welltyped_def
    unfolding factoringI
    by fastforce

  ultimately show ?thesis
    unfolding factoringI
    by simp
qed

lemma factoring_preserves_typing_D:
  assumes 
  factoring: "factoring (C, \<V>) (D, \<V>)" and
  C_is_welltyped: "clause.is_welltyped \<V> C"
  shows "clause.is_welltyped \<V> D"
  using factoring
proof (cases "(C, \<V>)" "(D, \<V>)" rule: factoring.cases)
  case (factoringI L\<^sub>1 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>2 C')

  have "clause.is_welltyped \<V> C'" "literal.is_welltyped \<V> L\<^sub>1"
    using C_is_welltyped
    unfolding factoringI
    by simp_all

  then have "clause.is_welltyped \<V> (C' \<cdot> \<mu>)" "literal.is_welltyped \<V> (L\<^sub>1 \<cdot>l \<mu>)"
    using factoringI(3)
    unfolding factoringI
    apply fastforce
    by (metis Un_iff \<open>literal.is_welltyped \<V> L\<^sub>1\<close> clause.vars_add literal.welltyped_subst_stability
        local.factoringI(3,4,5))

  then show ?thesis
    unfolding factoringI
    by simp
qed

lemma factoring_preserves_typing:
  assumes 
  factoring: "factoring (C, \<V>) (D, \<V>)"
  shows "clause.is_welltyped \<V> C \<longleftrightarrow> clause.is_welltyped \<V> D"
  using 
    factoring_preserves_typing_C
    factoring_preserves_typing_D
    assms
  by fast


lemma resolution_preserves_typing_R:
  assumes
    resolution: "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R, \<V>\<^sub>3)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    C_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 C"
  shows "clause.is_welltyped \<V>\<^sub>3 R"
  using resolution
proof (cases "(C, \<V>\<^sub>1)" "(D, \<V>\<^sub>2)" "(R, \<V>\<^sub>3)" rule: resolution.cases)
  case (resolutionI \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 t\<^sub>2 \<mu> L\<^sub>1 L\<^sub>2 C' D')
 
  then have welltyped_\<mu>:
    "is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2) \<union> clause.vars (C \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<mu>"
    by meson

  have "clause.is_welltyped \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1)"
    using C_is_welltyped clause.welltyped_renaming[OF resolutionI(3, 12)]
    by blast

  then have C\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
    using welltyped_\<mu>
    by simp

  have "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2)"
    using D_is_welltyped clause.welltyped_renaming[OF resolutionI(4, 11)]
    by blast

  then have D\<mu>_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
    using welltyped_\<mu>
    by simp

  have imgu: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> = t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>"
    using resolutionI(6) term.is_imgu_unifies_pair
    by auto

  from C\<mu>_is_welltyped D\<mu>_is_welltyped imgu
  show ?thesis
    unfolding resolutionI
    by cases auto
qed

lemma resolution_preserves_typing_D:
  assumes
    resolution: "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R, \<V>\<^sub>3)" and
    R_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 R"
  shows "clause.is_welltyped \<V>\<^sub>2 D"
  using resolution
proof (cases "(C, \<V>\<^sub>1)" "(D, \<V>\<^sub>2)" "(R, \<V>\<^sub>3)" rule: resolution.cases)
  case (resolutionI \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 t\<^sub>2 \<mu> L\<^sub>1 L\<^sub>2 C' D')

   have \<mu>_is_welltyped:
    "is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2) \<union> clause.vars (C \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<mu>"
     using resolutionI(6)
     by meson

   show ?thesis
   proof-
     have "clause.is_welltyped \<V>\<^sub>2 D'"
     proof-
        have "clause.is_welltyped \<V>\<^sub>3 (D' \<cdot> \<rho>\<^sub>2)"
          using R_is_welltyped \<mu>_is_welltyped
          unfolding resolutionI
          by auto
  
        moreover have "\<forall>x\<in>clause.vars D'. \<V>\<^sub>2 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>2 x)"
          using resolutionI(11)
          unfolding resolutionI
          by simp
  
        ultimately show ?thesis
          using clause.welltyped_renaming[OF resolutionI(4)]
          unfolding resolutionI
          by blast
      qed

     moreover have "literal.is_welltyped \<V>\<^sub>2 L\<^sub>2"
     proof-

      have \<V>\<^sub>2_\<V>\<^sub>3: "\<forall>x \<in> literal.vars L\<^sub>2. \<V>\<^sub>2 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>2 x)"
        using resolutionI(11)
        unfolding resolutionI
        by auto

      have "literal.is_welltyped \<V>\<^sub>3 (L\<^sub>2 \<cdot>l \<rho>\<^sub>2)"
      proof-
        obtain \<tau> where \<tau>: "welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
          using resolutionI(6)
          by force

        moreover have "welltyped \<V>\<^sub>2 t\<^sub>2 \<tau>"
            using
              \<tau>
              resolutionI(11)
              term.welltyped_renaming[OF resolutionI(4)]
            unfolding resolutionI
            by(auto simp: Set.ball_Un)


        then show ?thesis
          using literal.welltyped_renaming[OF resolutionI(4) \<V>\<^sub>2_\<V>\<^sub>3] literal.is_welltyped_def
          unfolding resolutionI by force
      qed

     then show ?thesis
        using literal.welltyped_renaming[OF resolutionI(4) \<V>\<^sub>2_\<V>\<^sub>3]
        unfolding resolutionI
        by simp
    qed

    ultimately show ?thesis
      unfolding resolutionI
      by simp
  qed
qed


lemma resolution_preserves_typing_C:
  assumes
    resolution: "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R, \<V>\<^sub>3)" and
    R_is_welltyped: "clause.is_welltyped \<V>\<^sub>3 R"
  shows "clause.is_welltyped \<V>\<^sub>1 C"
  using resolution
proof (cases "(C, \<V>\<^sub>1)" "(D, \<V>\<^sub>2)" "(R, \<V>\<^sub>3)" rule: resolution.cases)
  case (resolutionI \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 t\<^sub>2 \<mu> L\<^sub>1 L\<^sub>2 C' D')

  have \<mu>_is_welltyped:
    "is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2) \<union> clause.vars (C \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<mu>"
     using resolutionI(6)
     by meson

   show ?thesis
   proof-
    have "clause.is_welltyped \<V>\<^sub>1 C'"
    proof-
      have "clause.is_welltyped \<V>\<^sub>3 (C' \<cdot> \<rho>\<^sub>1)"
        using R_is_welltyped \<mu>_is_welltyped
        unfolding resolutionI
        by auto

      moreover have "\<forall>x\<in>clause.vars C'. \<V>\<^sub>1 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>1 x)"
        using resolutionI(12)
        unfolding resolutionI
        by simp

      ultimately show ?thesis
        using clause.welltyped_renaming[OF resolutionI(3)]
        unfolding resolutionI
        by blast
    qed

    moreover have "literal.is_welltyped \<V>\<^sub>1 L\<^sub>1"
    proof-

      have \<V>\<^sub>1_\<V>\<^sub>3: "\<forall>x \<in> literal.vars L\<^sub>1. \<V>\<^sub>1 x = \<V>\<^sub>3 (clause.rename \<rho>\<^sub>1 x)"
        using resolutionI(12)
        unfolding resolutionI
        by auto

      have "literal.is_welltyped \<V>\<^sub>3 (Pos (t\<^sub>1 \<cdot>t \<rho>\<^sub>1))"
        by (metis literal.is_welltyped_def literal.simps(15) local.resolutionI(6) singleton_iff)

      then show ?thesis
        using literal.welltyped_renaming[OF resolutionI(3) \<V>\<^sub>1_\<V>\<^sub>3]
        unfolding resolutionI
        by (simp add: literal.is_welltyped_def)
    qed

    ultimately show ?thesis
      unfolding resolutionI
      by simp
  qed
qed

lemma resolution_preserves_typing:
  assumes "resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R, \<V>\<^sub>3)"
  shows "clause.is_welltyped \<V>\<^sub>2 D \<and> clause.is_welltyped \<V>\<^sub>1 C \<longleftrightarrow> clause.is_welltyped \<V>\<^sub>3 R"
  using
    resolution_preserves_typing_R
    resolution_preserves_typing_D
    resolution_preserves_typing_C
    assms
  by fast

end
end