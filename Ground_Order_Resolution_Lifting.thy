theory Ground_Order_Resolution_Lifting
  imports
    Ground_Order_Resolution
begin

type_synonym 'f ground_atom = "'f gterm uprod"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

locale grounding_lifting =
  functional_substitution_lifting where sub_vars = sub_vars and sub_subst = sub_subst and
  map = map +
  sub: grounding where vars = sub_vars and subst = sub_subst and to_ground = sub_to_ground and
  from_ground = sub_from_ground +
  natural_functor_conversion where map = map and map_to = to_ground_map and
  map_from = from_ground_map and map' = ground_map and to_set' = to_set_ground
  for
    sub_to_ground :: "'sub \<Rightarrow> 'sub\<^sub>G" and
    sub_from_ground :: "'sub\<^sub>G \<Rightarrow> 'sub" and
    sub_vars :: "'sub \<Rightarrow> 'var set" and
    sub_subst :: "'sub \<Rightarrow> ('var \<Rightarrow> 'base) \<Rightarrow> 'sub" and
    map :: "('sub \<Rightarrow> 'sub) \<Rightarrow> 'expr \<Rightarrow> 'expr" and
    to_ground_map :: "('sub \<Rightarrow> 'sub\<^sub>G) \<Rightarrow> 'expr \<Rightarrow> 'expr\<^sub>G" and
    from_ground_map :: "('sub\<^sub>G \<Rightarrow> 'sub) \<Rightarrow> 'expr\<^sub>G \<Rightarrow> 'expr" and
    ground_map :: "('sub\<^sub>G \<Rightarrow> 'sub\<^sub>G) \<Rightarrow> 'expr\<^sub>G \<Rightarrow> 'expr\<^sub>G" and
    to_set_ground :: "'expr\<^sub>G \<Rightarrow> 'sub\<^sub>G set"
begin

definition to_ground :: "'expr \<Rightarrow> 'expr\<^sub>G" where
  "to_ground expr \<equiv> to_ground_map sub_to_ground expr"

end

context ground_order_resolution_calculus
begin

lemma (in grounding_lifting) resolution_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'f gterm clause" and
    D C :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines
    D\<^sub>G [simp]: "D\<^sub>G \<equiv> to_ground (D \<cdot> \<gamma>)" and
    C\<^sub>G [simp]: "C\<^sub>G \<equiv> to_ground (C \<cdot> \<gamma>)"
  assumes
    ground_resolution: "ground_order_resolution_calculus.resolution D\<^sub>G C\<^sub>G" and
    D_grounding: "is_ground (D \<cdot> \<gamma>)" and 
    C_grounding: "is_ground (C \<cdot> \<gamma>)" and
    select: "from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<gamma>" and
    D_is_welltyped: "is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C'
  where
    "eq_resolution (D, \<V>) (C', \<V>)"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_resolution
end