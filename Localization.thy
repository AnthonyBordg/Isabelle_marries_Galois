theory Localization
  imports Main "HOL-Algebra.Group" Ring
begin

locale submonoid = monoid M for M (structure) +
  fixes S (structure)
  assumes subset : "S \<subseteq> carrier M"
    and m_closed [intro, simp] : "\<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> S"
    and one_closed [simp] : "1 \<in> S"

lemma (in submonoid) is_submonoid: "submonoid M S"
  by (rule submonoid_axioms)

locale mult_submonoid = ring R + submonoid R S for R and S (structure)

locale mult_subset = cring R + mult_submonoid R S for R and S (structure)




