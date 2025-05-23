theory Resolution
  imports
    First_Order_Clause.Nonground_Order
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Nonground_Typing
    First_Order_Clause.Typed_Tiebreakers
    First_Order_Clause.Welltyped_IMGU
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
  
    Ground_Ordered_Resolution
begin

locale resolution_calculus =
  nonground_inhabited_typing \<F> +
  nonground_order less\<^sub>t +
  nonground_selection_function where select = select and
  atom_subst = "(\<cdot>t)" and
  atom_vars = "term.vars" and
  atom_from_ground = "term.from_ground" and
  atom_to_ground = "term.to_ground"
 +
  tiebreakers: tiebreakers tiebreakers
for
  select :: "('f, 'v :: infinite) term select" and
  less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" and
  \<F> :: "('f, 'ty) fun_types" and
  tiebreakers :: "('f gterm, ('f, 'v) term) tiebreakers"
begin

inductive factoring ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  factoringI: "
  C = add_mset L\<^sub>1 (add_mset L\<^sub>2 C') \<Longrightarrow>
  L\<^sub>1 = (Pos t\<^sub>1) \<Longrightarrow>
  L\<^sub>2 = (Pos t\<^sub>2) \<Longrightarrow>
  D = (add_mset L\<^sub>1 C') \<cdot> \<mu> \<Longrightarrow>
  factoring (C, \<V>) (D, \<V>)"
if
  "select C = {#}"
  "is_maximal (L\<^sub>1 \<cdot>l \<mu>) (C \<cdot> \<mu>)"
  "welltyped_imgu_on (clause.vars C) \<V> t\<^sub>1 t\<^sub>2 \<mu>"

inductive resolution ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  resolutionI: "
    C = add_mset L\<^sub>1 C' \<Longrightarrow>
    D = add_mset L\<^sub>2 D' \<Longrightarrow>
    L\<^sub>1 = (Neg t\<^sub>1) \<Longrightarrow>
    L\<^sub>2 = (Pos t\<^sub>2) \<Longrightarrow>
    R = (C' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    resolution (D, \<V>\<^sub>2) (C, \<V>\<^sub>1) (R, \<V>\<^sub>3)"
if
  "infinite_variables_per_type \<V>\<^sub>1"
  "infinite_variables_per_type \<V>\<^sub>2"
  "term_subst.is_renaming \<rho>\<^sub>1"
  "term_subst.is_renaming \<rho>\<^sub>2"
  "clause.vars (C \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
  "welltyped_imgu_on (clause.vars (C \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
  "\<not> (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "select C = {#} \<and> is_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or> is_maximal ( L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select C) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
  "select D = {#}"
  "is_strictly_maximal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "\<forall>x \<in> clause.vars C. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x)"
  "\<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x)"
  "is_welltyped_on (clause.vars C) \<V>\<^sub>1 \<rho>\<^sub>1"
  "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"

abbreviation factoring_inferences where
"factoring_inferences \<equiv> { Infer [C] D | C D. factoring C D}"

abbreviation resolution_inferences where
"resolution_inferences \<equiv> { Infer [D, C] R | D C R. resolution D C R}"

definition inferences :: "('f, 'v, 'ty) typed_clause inference set" where
"inferences \<equiv> resolution_inferences \<union> factoring_inferences"

abbreviation bottom\<^sub>F :: "('f, 'v, 'ty) typed_clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {({#}, \<V>) | \<V>. infinite_variables_per_type \<V> }"
end

end