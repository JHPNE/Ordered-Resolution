theory Ground_Order_Resolution_Lifting
  imports
    Ground_Order_Resolution
    Abstract_Substitution.Functional_Substitution
    Abstract_Substitution.Functional_Substitution_Lifting
    Typing
begin

type_synonym 'f ground_atom = "'f gterm uprod"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"


context ground_order_resolution_calculus
begin

lemma resolution_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'f ground_atom clause" and
    D C :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines
    D\<^sub>G [simp]: "D\<^sub>G \<equiv> grounding_lifting.to_ground (functional_substitution_lifting.subst D \<gamma>)" and
    C\<^sub>G [simp]: "C\<^sub>G \<equiv> grounding_lifting.to_ground (functional_substitution_lifting.subst C \<gamma>)"
  assumes
    ground_resolution: "ground_order_resolution_calculus.resolution D\<^sub>G C\<^sub>G" and
    D_grounding: "functional_substitution.is_ground (functional_substitution_lifting.subst D \<gamma>)" and 
    C_grounding: "functional_substitution.is_ground (functional_substitution_lifting.subst C \<gamma>)" and
    select: "grounding_lifting.from_ground (select\<^sub>G D\<^sub>G) = functional_substitution_lifting.subst (select D) \<gamma>" and
    D_is_welltyped: "typing_lifting.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C'
  where
    "resolution (D, \<V>) (C', \<V>)"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))"
    "functional_substitution_lifting.subst C' \<gamma> = functional_substitution_lifting.subst C  \<gamma>"
  using ground_resolution
end