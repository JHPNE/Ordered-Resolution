theory Resolution_Welltypedness_Preservation
  imports Resolution
begin

context resolution_calculus
begin

lemma factoring_preserves_typing:
  assumes 
  factoring: "factoring (C, \<V>) (D, \<V>)"
  shows "clause.is_welltyped \<V> C \<longleftrightarrow> clause.is_welltyped \<V> D"
  using assms
proof (cases "(C, \<V>)" "(D, \<V>)" rule: factoring.cases)
  case (factoringI L\<^sub>1 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>2 C')
  then show ?thesis sorry
qed
(*
  case (factoringI L\<^sub>1 \<mu> t\<^sub>1 t\<^sub>2 L\<^sub>2 C')

  have "clause.is_welltyped \<V> C \<longleftrightarrow> (clause.is_welltyped \<V> (add_mset L\<^sub>1 C') \<and> 
         welltyped_imgu_on (clause.vars C) \<V> t\<^sub>1 t\<^sub>2 \<mu>)"
    using literal.is_welltyped_def literal.simps(15) local.factoringI(3,4,6) by force

  also have "clause.is_welltyped \<V> (add_mset L\<^sub>1 C') \<longleftrightarrow> clause.is_welltyped \<V> (add_mset L\<^sub>1 C' \<cdot> \<mu>)"
    sledgehammer
qed
*)



end
end