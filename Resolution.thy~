theory Resolution
  imports
    First_Order_Clause.Nonground_Order
    First_Order_Clause.Nonground_Selection_Function
    First_Order_Clause.Nonground_Typing
    First_Order_Clause.Typed_Tiebreakers
    First_Order_Clause.Welltyped_IMGU

    Ground_Order_Resolution
begin

(* Nonground clause without equality *)
locale nonground_clause = nonground_term_with_context
begin

subsection \<open>Nonground Literals\<close>

sublocale literal: term_based_lifting where
  sub_subst = subst_apply_term and sub_vars = term.vars and map = map_literal and
  to_set = set_literal and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_literal and
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

notation literal.subst (infixl "\<cdot>l" 66)

lemma vars_literal [simp]:
  "literal.vars (Pos t) = term.vars t"
  "literal.vars (Neg t) = term.vars t"
  "literal.vars ((if b then Pos else Neg) t) = term.vars t"
  by (simp_all add: literal.vars_def)

lemma subst_literal [simp]:
  "Pos t \<cdot>l \<sigma> = Pos (t \<cdot>t \<sigma>)"
  "Neg t \<cdot>l \<sigma> = Neg (t \<cdot>t \<sigma>)"
  "atm_of (l \<cdot>l \<sigma>) = atm_of l \<cdot>t \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

lemma subst_literal_if [simp]:
  "(if b then Pos else Neg) a \<cdot>l \<rho> = (if b then Pos else Neg) (a \<cdot>t \<rho>)"
  by simp

lemma subst_polarity_stable:
  shows
    subst_neg_stable [simp]: "is_neg (l \<cdot>l \<sigma>) \<longleftrightarrow> is_neg l" and
    subst_pos_stable [simp]: "is_pos (l \<cdot>l \<sigma>) \<longleftrightarrow> is_pos l"
  by (simp_all add: literal.subst_def)

declare literal.discI [intro]

lemma literal_from_ground_atom_from_ground [simp]:
  "literal.from_ground (Neg t\<^sub>G) = Neg (term.from_ground t\<^sub>G)"
  "literal.from_ground (Pos t\<^sub>G) = Pos (term.from_ground t\<^sub>G)"
  by (simp_all add: literal.from_ground_def)

lemma literal_from_ground_polarity_stable [simp]:
  shows
    neg_literal_from_ground_stable: "is_neg (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_neg l\<^sub>G" and
    pos_literal_from_ground_stable: "is_pos (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_pos l\<^sub>G"
  by (simp_all add: literal.from_ground_def)

lemma literal_to_ground_atom_to_ground [simp]:
  "literal.to_ground (Pos t) = Pos (term.to_ground t)"
  "literal.to_ground (Neg t) = Neg (term.to_ground t)"
  by (simp_all add: literal.to_ground_def)

lemma literal_is_ground_atom_is_ground [intro]:
  "literal.is_ground l \<longleftrightarrow> term.is_ground (atm_of l)"
  by (simp add: literal.vars_def set_literal_atm_of)


subsection \<open>Nonground Clauses\<close>

sublocale clause: term_based_multiset_lifting where
  sub_subst = literal.subst and sub_vars = literal.vars and sub_to_ground = literal.to_ground and
  sub_from_ground = literal.from_ground
  by unfold_locales

notation clause.subst (infixl "\<cdot>" 67)

lemmas clause_submset_vars_clause_subset [intro] =
  clause.to_set_subset_vars_subset[OF set_mset_mono]

lemmas sub_ground_clause = clause.to_set_subset_is_ground[OF set_mset_mono]

lemma subst_clause_remove1_mset [simp]:
  assumes "l \<in># C"
  shows "remove1_mset l C \<cdot> \<sigma> = remove1_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemma clause_from_ground_remove1_mset [simp]:
  "clause.from_ground (remove1_mset l\<^sub>G C\<^sub>G) =
    remove1_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

lemmas clause_safe_unfolds =
  literal_to_ground_atom_to_ground
  literal_from_ground_atom_from_ground
  literal_from_ground_polarity_stable
  subst_literal
  vars_literal
end

(* Nonground Order without equality *)

locale nonground_order =
  nonground_clause +
  "term": nonground_term_order
begin

sublocale restricted_term_order_lifting where
  restriction = "range term.from_ground" and literal_to_mset = mset_lit
  by unfold_locales (rule inj_mset_lit)

(* TODO: Find way to not have this twice *)
notation term.order.less\<^sub>G (infix "\<prec>\<^sub>t\<^sub>G" 50)
notation term.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>t\<^sub>G" 50)


sublocale literal: nonground_term_based_order_lifting where
  less = less\<^sub>t and sub_subst = "(\<cdot>t)" and sub_vars = term.vars and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and map = map_literal and to_set = set_literal and
  to_ground_map = map_literal and from_ground_map = map_literal and
  ground_map = map_literal and to_set_ground = set_literal and to_mset = mset_lit
proof unfold_locales
  fix l :: "('f, 'v) term literal"
  show "set_mset (mset_lit l) = set_literal l"
    apply (cases l)
    by auto
next
  fix f :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"  and l :: "('f, 'v) term literal"
  show "mset_lit (map_literal f l) = image_mset f (mset_lit l)"
    apply (cases l)
    by auto
next
  show "inj mset_lit"
    using inj_mset_lit .
qed

  

notation literal.order.less\<^sub>G (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation literal.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>l\<^sub>G" 50)

sublocale clause: nonground_term_based_order_lifting where
  less = "(\<prec>\<^sub>l)" and sub_subst = literal.subst and sub_vars = literal.vars and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  map = image_mset and to_set = set_mset and to_ground_map = image_mset and
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset and
  to_mset = "\<lambda>x. x"
  by unfold_locales simp_all

notation clause.order.less\<^sub>G (infix "\<prec>\<^sub>c\<^sub>G" 50)
notation clause.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemma obtain_maximal_literal:
  assumes
    not_empty: "C \<noteq> {#}" and
    grounding: "clause.is_ground (C \<cdot> \<gamma>)"
  obtains l
  where "is_maximal l C" "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
proof-

  have grounding_not_empty: "C \<cdot> \<gamma> \<noteq> {#}"
    using not_empty
    by simp

  obtain l where
    l_in_C: "l \<in># C" and
    l_grounding_is_maximal: "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
    using
      ex_maximal_in_mset_wrt[OF
        literal.order.transp_on_less literal.order.asymp_on_less grounding_not_empty]
      maximal_in_clause
    unfolding clause.subst_def
    by (metis (mono_tags, lifting) image_iff multiset.set_map)

  show ?thesis
  proof(cases "is_maximal l C")
    case True

    with l_grounding_is_maximal that
    show ?thesis
      by blast
  next
    case False
    then obtain l' where
      l'_in_C: "l' \<in># C" and
      l_less_l': "l \<prec>\<^sub>l l'"
      unfolding is_maximal_def
      using l_in_C
      by blast

    note literals_in_C = l_in_C l'_in_C
    note literals_grounding = literals_in_C[THEN clause.to_set_is_ground_subst[OF _ grounding]]

    have "l \<cdot>l \<gamma> \<prec>\<^sub>l l' \<cdot>l \<gamma>"
      using literal.order.ground_subst_stability[OF literals_grounding l_less_l'].

    then have False
     using
       l_grounding_is_maximal
       clause.subst_in_to_set_subst[OF l'_in_C]
     unfolding is_maximal_def
     by force

    then show ?thesis..
  qed
qed

lemma obtain_strictly_maximal_literal:
  assumes
   grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   ground_strictly_maximal: "is_strictly_maximal l\<^sub>G (C \<cdot> \<gamma>)"
 obtains l where
   "is_strictly_maximal l C" "l\<^sub>G = l \<cdot>l \<gamma>"
proof-

  have grounding_not_empty: "C \<cdot> \<gamma> \<noteq> {#}"
    using is_strictly_maximal_not_empty[OF ground_strictly_maximal].

  have l\<^sub>G_in_grounding: "l\<^sub>G \<in># C \<cdot> \<gamma>"
    using strictly_maximal_in_clause[OF ground_strictly_maximal].

  obtain l where
    l_in_C: "l \<in># C" and
    l\<^sub>G [simp]: "l\<^sub>G = l \<cdot>l \<gamma>"
    using l\<^sub>G_in_grounding
    unfolding clause.subst_def
    by blast

  show ?thesis
  proof(cases "is_strictly_maximal l C")
    case True
    show ?thesis
      using that[OF True l\<^sub>G].
  next
    case False

    then obtain l' where
      l'_in_C: "l' \<in># C - {# l #}" and
      l_less_eq_l': "l \<preceq>\<^sub>l l'"
      unfolding is_strictly_maximal_def
      using l_in_C
      by blast

    note l_grounding =
       clause.to_set_is_ground_subst[OF l_in_C grounding]

    have l'_grounding: "literal.is_ground (l' \<cdot>l \<gamma>)"
      using l'_in_C grounding
      by (meson clause.to_set_is_ground_subst in_diffD)

    have "l \<cdot>l \<gamma> \<preceq>\<^sub>l l' \<cdot>l \<gamma>"
      using literal.order.less_eq.ground_subst_stability[OF l_grounding l'_grounding l_less_eq_l'].

    then have False
      using clause.subst_in_to_set_subst[OF l'_in_C] ground_strictly_maximal
      unfolding is_strictly_maximal_def subst_clause_remove1_mset[OF l_in_C]
      by simp

    then show ?thesis..
  qed
qed

lemma is_maximal_if_grounding_is_maximal:
  assumes
   l_in_C: "l \<in># C" and
   C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   l_grounding_is_maximal: "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
 shows
   "is_maximal l C"
proof(rule ccontr)
  assume "\<not> is_maximal l C"

  then obtain l' where l_less_l': "l \<prec>\<^sub>l l'" and l'_in_C: "l' \<in># C"
    using l_in_C
    unfolding is_maximal_def
    by blast

  have l'_grounding: "literal.is_ground (l' \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF l'_in_C C_grounding].

  have l_grounding: "literal.is_ground (l \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF l_in_C C_grounding].

  have l'_\<gamma>_in_C_\<gamma>: "l' \<cdot>l \<gamma> \<in># C \<cdot> \<gamma>"
    using clause.subst_in_to_set_subst[OF l'_in_C].

  have "l \<cdot>l \<gamma> \<prec>\<^sub>l l' \<cdot>l \<gamma>"
    using literal.order.ground_subst_stability[OF l_grounding l'_grounding l_less_l'].

  then have "\<not> is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
    using l'_\<gamma>_in_C_\<gamma>
    unfolding is_maximal_def literal.subst_comp_subst
    by fastforce

  then show False
    using l_grounding_is_maximal..
qed

lemma is_strictly_maximal_if_grounding_is_strictly_maximal:
  assumes
   l_in_C: "l \<in># C" and
   grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   grounding_strictly_maximal: "is_strictly_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
 shows
   "is_strictly_maximal l C"
  using
    is_maximal_if_grounding_is_maximal[OF
      l_in_C
      grounding
      is_maximal_if_is_strictly_maximal[OF grounding_strictly_maximal]
    ]
    grounding_strictly_maximal
  unfolding
    is_strictly_maximal_def is_maximal_def
    subst_clause_remove1_mset[OF l_in_C, symmetric]
    reflclp_iff
  by (metis in_diffD clause.subst_in_to_set_subst)

lemma unique_maximal_in_ground_clause:
  assumes
    "clause.is_ground C"
    "is_maximal l C"
    "is_maximal l' C"
  shows
    "l = l'"
  using assms clause.to_set_is_ground literal.order.not_less_eq
  unfolding is_maximal_def reflclp_iff
  by meson

lemma unique_strictly_maximal_in_ground_clause:
  assumes
    "clause.is_ground C"
    "is_strictly_maximal l C"
    "is_strictly_maximal l' C"
  shows
    "l = l'"
  using assms unique_maximal_in_ground_clause
  by blast

 (* TODO: order.order *)
thm literal.order.order.strict_iff_order

abbreviation ground_is_maximal where
  "ground_is_maximal l\<^sub>G C\<^sub>G \<equiv> is_maximal (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"

abbreviation ground_is_strictly_maximal where
  "ground_is_strictly_maximal l\<^sub>G C\<^sub>G \<equiv>
     is_strictly_maximal (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"

sublocale ground: ground_order_base where
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)"
rewrites
  less\<^sub>l\<^sub>G_rewrite [simp]: "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) mset_lit = (\<prec>\<^sub>l\<^sub>G)" and
  less\<^sub>c\<^sub>G_rewrite [simp]: "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)" and
  is_maximal_rewrite [simp]: "\<And>l\<^sub>G C\<^sub>G. ground.is_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_maximal l\<^sub>G C\<^sub>G" and
  is_strictly_maximal_rewrite [simp]: 
    "\<And>l\<^sub>G C\<^sub>G. ground.is_strictly_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_strictly_maximal l\<^sub>G C\<^sub>G"
proof unfold_locales

  interpret multiset_extension "(\<prec>\<^sub>t\<^sub>G)" mset_lit
    by unfold_locales

  interpret relation_restriction
    "(\<lambda>b1 b2. multp (\<prec>\<^sub>t) (mset_lit b1) (mset_lit b2))" literal.from_ground
    by unfold_locales

  {
    fix l1 l2
  have "(multp (\<lambda>b b'. term.from_ground b \<prec>\<^sub>t term.from_ground b') (mset_lit l1) (mset_lit l2)) =
    (multp (\<prec>\<^sub>t) (mset_lit (map_literal term.from_ground l1)) (mset_lit (map_literal term.from_ground l2)))"
    apply (cases l1; cases l2)
    apply auto
    sorry
  }

  show less\<^sub>l\<^sub>G_rewrite: "(\<prec>\<^sub>m) = (\<prec>\<^sub>l\<^sub>G)"
    unfolding multiset_extension_def literal.order.multiset_extension_def R\<^sub>r_def
    unfolding term.order.less\<^sub>G_def literal.from_ground_def
    using multp_image_mset_image_msetI
    sorry

  fix l\<^sub>G C\<^sub>G
  show "is_maximal_in_mset C\<^sub>G l\<^sub>G \<longleftrightarrow> ground_is_maximal l\<^sub>G C\<^sub>G"
    unfolding is_maximal_in_mset_iff 
    by (simp add: clause.to_set_from_ground image_iff is_maximal_def less\<^sub>l\<^sub>G_rewrite 
          literal.order.less\<^sub>r_def)

  then show "is_strictly_maximal_in_mset C\<^sub>G l\<^sub>G \<longleftrightarrow> ground_is_strictly_maximal l\<^sub>G C\<^sub>G"
    unfolding 
      is_strictly_maximal_def is_strictly_maximal_in_mset_iff reflclp_iff
      is_maximal_def is_maximal_in_mset_iff
    by (smt (verit, ccfv_SIG) clause.ground_sub_in_ground clause_from_ground_remove1_mset 
        in_remove1_mset_neq)
next

  interpret multiset_extension "(\<prec>\<^sub>l\<^sub>G)" "\<lambda>x. x"
    by unfold_locales

  interpret relation_restriction "multp (\<prec>\<^sub>l)" clause.from_ground
    by unfold_locales

  show less\<^sub>c\<^sub>G_rewrite: "(\<prec>\<^sub>m) = (\<prec>\<^sub>c\<^sub>G)"
    unfolding multiset_extension_def clause.order.multiset_extension_def R\<^sub>r_def
    unfolding literal.order.less\<^sub>G_def clause.from_ground_def
    by (metis literal.inj_from_ground literal.order.transp multp_image_mset_image_msetD
        multp_image_mset_image_msetI)
qed


lemma less\<^sub>c_add_mset:
  assumes "l \<prec>\<^sub>l l'" "C \<preceq>\<^sub>c C'"
  shows "add_mset l C \<prec>\<^sub>c add_mset l' C'"
  using assms multp_add_mset_reflclp[OF literal.order.asymp literal.order.transp]
  unfolding less\<^sub>c_def
  by blast

lemmas less\<^sub>c_add_same [simp] =
  multp_add_same[OF literal.order.asymp literal.order.transp, folded less\<^sub>c_def]

end

(* clause typing *)

locale clause_typing = "term": typing term_welltyped
  for term_welltyped
begin


sublocale literal: typing_lifting where
  sub_welltyped = term_welltyped and to_set = set_literal
  by unfold_locales

sublocale clause: mulitset_typing_lifting where 
  sub_welltyped = literal.welltyped
  by unfold_locales

end

(* Nonground typing *)

locale nonground_typing =
  nonground_clause +
  nonground_term_typing \<F>
  for \<F> :: "('f, 'ty) fun_types"
begin

sublocale clause_typing "welltyped \<V>"
  by unfold_locales


sublocale literal: term_based_nonground_typing_lifting where
  base_welltyped = welltyped and sub_vars = term.vars and sub_subst = "(\<cdot>t)" and
  map = map_literal and to_set = set_literal and sub_welltyped = welltyped and
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and
  to_ground_map = map_literal and from_ground_map = map_literal and ground_map = map_literal and
  to_set_ground = set_literal
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where
  base_welltyped = welltyped and sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and
  map = image_mset and to_set = set_mset and sub_welltyped = literal.welltyped and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset
  by unfold_locales

end

locale nonground_inhabited_typing =
  nonground_typing \<F> +
  nonground_term_inhabited_typing \<F>
  for \<F> :: "('f, 'ty) fun_types"
begin

sublocale literal: term_based_nonground_inhabited_typing_lifting where
  base_welltyped = welltyped and sub_vars = term.vars and 
  sub_subst = "(\<cdot>t)" and map = map_literal and to_set = set_literal and
  sub_welltyped = welltyped and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_literal and
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

sublocale clause: term_based_nonground_inhabited_typing_lifting where
  base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_welltyped = literal.welltyped and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and
  to_set_ground = set_mset
  by unfold_locales

end

type_synonym 'f ground_select = "'f gterm clause \<Rightarrow> 'f gterm clause"
type_synonym ('f, 'v) select = "('f, 'v) term clause \<Rightarrow> ('f, 'v) term clause"

context nonground_clause
begin

definition is_select_grounding :: "('f, 'v) select \<Rightarrow> 'f ground_select \<Rightarrow> bool" where
  "is_select_grounding select select\<^sub>G \<equiv> \<forall>C\<^sub>G. \<exists>C \<gamma>.
    clause.is_ground (C \<cdot> \<gamma>) \<and>
    C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>) \<and>
    select\<^sub>G C\<^sub>G = clause.to_ground ((select C) \<cdot> \<gamma>)"

end

locale nonground_selection_function =
  nonground_clause +
  selection_function select
  for select :: "('f, 'v) term clause \<Rightarrow> ('f, 'v) term clause"
begin

abbreviation is_grounding :: "'f ground_select \<Rightarrow> bool" where
  "is_grounding select\<^sub>G \<equiv> is_select_grounding select select\<^sub>G"

definition select\<^sub>G\<^sub>s where
  "select\<^sub>G\<^sub>s = { select\<^sub>G. is_grounding select\<^sub>G }"

definition select\<^sub>G_simple where
  "select\<^sub>G_simple C = clause.to_ground (select (clause.from_ground C))"

lemma select\<^sub>G_simple: "is_grounding select\<^sub>G_simple"
  unfolding is_select_grounding_def select\<^sub>G_simple_def
  by (metis clause.from_ground_inverse clause.ground_is_ground clause.subst_id_subst)

lemma select_is_ground:
  assumes "clause.is_ground C"
  shows "clause.is_ground (select C)"
  using select_subset sub_ground_clause assms
  by metis

lemma is_ground_in_selection:
  assumes "l \<in># select (clause.from_ground C)"
  shows "literal.is_ground l"
  using assms clause.sub_in_ground_is_ground select_subset
  by blast

lemma ground_literal_in_selection:
  assumes "clause.is_ground C" "l\<^sub>G \<in># clause.to_ground C"
  shows "literal.from_ground l\<^sub>G \<in># C"
  using assms
  by (metis clause.to_ground_inverse clause.ground_sub_in_ground)

lemma select_ground_subst:
  assumes "clause.is_ground (C \<cdot> \<gamma>)"
  shows "clause.is_ground (select C \<cdot> \<gamma>)"
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause clause.subst_def)

lemma select_neg_subst:
  assumes "l \<in># select C \<cdot> \<gamma>"
  shows "is_neg l"
  using assms subst_neg_stable select_negative_literals
  unfolding clause.subst_def
  by blast

lemma select_vars_subset: "\<And>C. clause.vars (select C) \<subseteq> clause.vars C"
  by (simp add: clause_submset_vars_clause_subset select_subset)

end

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) term clause \<times> ('v, 'ty) var_types"


locale resolution_calculus =
  nonground_inhabited_typing \<F> +
  nonground_order less\<^sub>t +
  nonground_selection_function select +
  tiebreakers: tiebreakers tiebreakers
for
  select :: "('f, 'v :: infinite) select" and
  less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" and
  \<F> :: "('f, 'ty) fun_types" and
  tiebreakers :: "('f, 'v) tiebreakers"
begin

inductive factoring ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  factoringI: "
  C = add_mset L\<^sub>1 (add_mset L\<^sub>2 C') \<Longrightarrow>
  L\<^sub>1 = (Pos t\<^sub>1) \<Longrightarrow>
  L\<^sub>2 = (Pos t\<^sub>2) \<Longrightarrow>
  D = add_mset L\<^sub>1 C' \<cdot> \<mu> \<Longrightarrow>
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
    resolution (C, \<V>\<^sub>1) (D, \<V>\<^sub>2) (R, \<V>\<^sub>3)"
if
  "infinite_variables_per_type \<V>\<^sub>1"
  "infinite_variables_per_type \<V>\<^sub>2"
  "term_subst.is_renaming \<rho>\<^sub>1"
  "term_subst.is_renaming \<rho>\<^sub>2"
  "clause.vars (D \<cdot> \<rho>\<^sub>2) \<inter> clause.vars (C \<cdot> \<rho>\<^sub>1) = {}"
  "welltyped_imgu_on (clause.vars (D \<cdot> \<rho>\<^sub>2) \<union> clause.vars (C \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
  "\<not> (C \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "select C = {#} \<and> is_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (C\<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or> ( L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># (select C))"
  "select D = {#}"
  "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
  "\<forall>x \<in> clause.vars D. \<V>\<^sub>2 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>2 x)"
  "\<forall>x \<in> clause.vars C. \<V>\<^sub>1 x = \<V>\<^sub>3 (term.rename \<rho>\<^sub>1 x)"
  "is_welltyped_on (clause.vars C) \<V>\<^sub>1 \<rho>\<^sub>1"
  "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"

end