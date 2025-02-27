theory Ground_Order_Base
  imports
  First_Order_Clause.Ground_Order
begin

primrec mset_lit :: "'a literal \<Rightarrow> 'a multiset" where
  "mset_lit (Pos A) = {#A#}" |
  "mset_lit (Neg A) = {#A, A#}"

lemma add_mset_eq_self: "{#a, a#} = {#b, b#} \<Longrightarrow> a = b"
  by (metis add_mset_eq_single add_mset_remove_trivial diff_union_swap)


lemma inj_mset_lit: "inj mset_lit"
proof(unfold inj_def, intro allI impI)
  fix l l' :: "'a literal"
  assume mset_lit: "mset_lit l = mset_lit l'"

  show "l = l'"
  proof(cases l)
    case l: (Pos a)
    show ?thesis
    proof(cases l')
      case l': (Pos a')

      show ?thesis
        using mset_lit l l'
        by simp
    next
      case l': (Neg a')
      show ?thesis
        using mset_lit l l'
        by simp
    qed
  next
    case l: (Neg a)
    then show ?thesis
    proof(cases l')
      case l': (Pos a')
      show ?thesis
        using mset_lit l l'
        by simp
    next
      case l': (Neg a')
      show ?thesis
        using mset_lit l l' add_mset_eq_self
        by simp
    qed
  qed
qed

locale ground_order_base =
  term.order: ground_term_order
begin

sublocale ground_order
  where literal_to_mset = mset_lit
  by unfold_locales (rule inj_mset_lit)
end
  
end