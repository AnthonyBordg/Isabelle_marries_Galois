theory Localization
  imports Main "HOL-Algebra.Group" "HOL-Algebra.Ring"
begin

locale submonoid = monoid M for M (structure) +
  fixes S
  assumes subset : "S \<subseteq> carrier M"
    and m_closed [intro, simp] : "\<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> S"
    and one_closed [simp] : "\<one> \<in> S"

lemma (in submonoid) is_submonoid: "submonoid M S"
  by (rule submonoid_axioms)

locale mult_submonoid_of_rng = ring R + submonoid R S for R and S

locale mult_submonoid_of_crng = cring R + mult_submonoid_of_rng R S for R and S

locale eq_obj_rng_of_frac = cring R + mult_submonoid_of_crng R S for R (structure) and S +
  fixes rel
  defines "rel \<equiv> \<lparr>carrier = carrier R \<times> S, eq = \<lambda>(r,s) (r',s'). \<exists>t\<in>S. t \<otimes> ((s'\<otimes> r) \<ominus> (s \<otimes> r')) = \<zero>\<rparr>"

lemma (in abelian_group) minus_to_eq :
  assumes "abelian_group G" and "x \<in> carrier G" and "y \<in> carrier G" and "x \<ominus> y = \<zero>"
  shows "x = y"
  by (metis add.inv_solve_right assms(2) assms(3) assms(4) l_zero minus_eq zero_closed)

lemma (in eq_obj_rng_of_frac) equiv_obj_rng_of_frac:
  shows "equivalence rel"
proof
  show "\<And>x. x \<in> carrier rel \<Longrightarrow> x .=\<^bsub>rel\<^esub> x"
  proof-
    fix x
    assume "x \<in> carrier rel"
    then have f1:"\<one> \<otimes> ((snd x \<otimes> fst x) \<ominus> (snd x \<otimes> fst x)) = \<zero>"
      using rel_def subset l_one minus_eq add.r_inv set_rev_mp by auto
    moreover have "x = (fst x, snd x)"
      by simp
    thus "x .=\<^bsub>rel\<^esub> x" 
      using rel_def one_closed f1 by auto
  qed
  show "\<And>x y. x .=\<^bsub>rel\<^esub> y \<Longrightarrow> x \<in> carrier rel \<Longrightarrow> y \<in> carrier rel \<Longrightarrow> y .=\<^bsub>rel\<^esub> x"
  proof-
    fix x y
    assume a1:"x .=\<^bsub>rel\<^esub> y" and a2:"x \<in> carrier rel" and a3:"y \<in> carrier rel"
    then obtain t where f1:"t \<in> S" and f2:"t \<otimes> ((snd y \<otimes> fst x) \<ominus> (snd x \<otimes> fst y)) = \<zero>"
      using rel_def by fastforce
    then have "(snd x \<otimes> fst y) \<ominus> (snd y \<otimes> fst x) = \<ominus> ((snd y \<otimes> fst x) \<ominus> (snd x \<otimes> fst y))"
      using abelian_group.minus_add abelian_group.minus_minus
      by (smt a2 a3 a_minus_def abelian_group.a_inv_closed add.inv_mult_group is_abelian_group mem_Sigma_iff monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse rel_def set_rev_mp subset)
    then have "t \<otimes> ((snd x \<otimes> fst y) \<ominus> (snd y \<otimes> fst x)) = \<zero>"
      using minus_zero r_minus f2
      by (smt a2 a3 f1 mem_Sigma_iff minus_closed partial_object.select_convs(1) prod.collapse rel_def semiring_simprules(3) set_rev_mp subset)
    thus "y .=\<^bsub>rel\<^esub> x"
      using f1 rel_def by auto
  qed
  show "\<And>x y z. x .=\<^bsub>rel\<^esub> y \<Longrightarrow> y .=\<^bsub>rel\<^esub> z \<Longrightarrow> x \<in> carrier rel \<Longrightarrow> y \<in> carrier rel \<Longrightarrow> z \<in> carrier rel \<Longrightarrow> x .=\<^bsub>rel\<^esub> z"
  proof-
    fix x y z
    assume a1:"x .=\<^bsub>rel\<^esub> y" and a2:"y .=\<^bsub>rel\<^esub> z" and a3:"x \<in> carrier rel" and a4:"y \<in> carrier rel" and a5:"z \<in> carrier rel"
    then obtain t where f1:"t \<in> S" and f2:"t \<otimes> ((snd y \<otimes> fst x) \<ominus> (snd x \<otimes> fst y)) = \<zero>"
      using rel_def by fastforce
    then obtain t' where f3:"t' \<in> S" and f4:"t' \<otimes> ((snd z \<otimes> fst y) \<ominus> (snd y \<otimes> fst z)) = \<zero>"
      using rel_def a2 by fastforce
    then have "t \<otimes> (snd y \<otimes> fst x) \<ominus> t \<otimes> (snd x \<otimes> fst y) = \<zero>"
      using f1 subset r_distr f2
      by (smt a3 a4 a_minus_def abelian_group.a_inv_closed is_abelian_group mem_Sigma_iff monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse r_minus rel_def subset_iff)
    then have "t' \<otimes> (t \<otimes> (snd y \<otimes> fst x)) \<ominus> t' \<otimes> (t \<otimes> (snd x \<otimes> fst y)) = \<zero>"
      using f3 subset r_distr
      by (smt a3 a4 a_minus_def f1 is_abelian_group mem_Sigma_iff minus_to_eq partial_object.select_convs(1) prod.collapse r_neg rel_def semiring_simprules(3) subset_iff)
    then have f5:"snd z \<otimes> (t' \<otimes> (t \<otimes> (snd y \<otimes> fst x))) \<ominus> snd z \<otimes> (t' \<otimes> (t \<otimes> (snd x \<otimes> fst y))) = \<zero>"
      using a5 rel_def r_distr
      by (smt a3 a4 a_minus_def f1 f3 is_abelian_group mem_Sigma_iff minus_to_eq monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse r_neg subset subset_iff)
    have "t' \<otimes> (snd z \<otimes> fst y) \<ominus> t' \<otimes> (snd y \<otimes> fst z) = \<zero>"
      using f3 f4 subset r_distr
      by (smt a4 a5 a_minus_def abelian_group.a_inv_closed is_abelian_group mem_Sigma_iff monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse r_minus rel_def set_rev_mp)
    then have "t \<otimes> (t' \<otimes> (snd z \<otimes> fst y)) \<ominus> t \<otimes> (t' \<otimes> (snd y \<otimes> fst z)) = \<zero>"
      using f1 subset r_distr
      by (smt a4 a5 a_minus_def f3 is_abelian_group mem_Sigma_iff minus_to_eq monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse r_neg rel_def subset_iff)
    then have f6:"snd x \<otimes> (t \<otimes> (t' \<otimes> (snd z \<otimes> fst y))) \<ominus> snd x \<otimes> (t \<otimes> (t' \<otimes> (snd y \<otimes> fst z))) = \<zero>"
      using a3 rel_def r_distr
      by (smt a4 a5 a_minus_def f1 f3 is_abelian_group mem_Sigma_iff minus_to_eq monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse r_neg subset subset_iff)
    have "snd z \<otimes> (t' \<otimes> (t \<otimes> (snd x \<otimes> fst y))) = snd x \<otimes> (t \<otimes> (t' \<otimes> (snd z \<otimes> fst y)))"
      using comm_monoid_axioms_def[of R] f1 f3 subset a3 a4 a5 m_assoc
      by (smt m_lcomm mem_Sigma_iff partial_object.select_convs(1) partial_object_ext_def rel_def semiring_simprules(3) set_rev_mp surjective_pairing)
    then have "snd z \<otimes> (t' \<otimes> (t \<otimes> (snd y \<otimes> fst x))) \<ominus> snd z \<otimes> (t' \<otimes> (t \<otimes> (snd x \<otimes> fst y))) \<oplus> 
      snd x \<otimes> (t \<otimes> (t' \<otimes> (snd z \<otimes> fst y))) \<ominus> snd x \<otimes> (t \<otimes> (t' \<otimes> (snd y \<otimes> fst z))) = 
      snd z \<otimes> (t' \<otimes> (t \<otimes> (snd y \<otimes> fst x))) \<ominus> snd x \<otimes> (t \<otimes> (t' \<otimes> (snd y \<otimes> fst z)))"
        using add.l_inv
        by (smt a3 a4 a5 f1 f3 f5 is_abelian_group local.semiring_axioms mem_Sigma_iff minus_to_eq monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.collapse rel_def semiring.semiring_simprules(6) subset subset_iff)
    then have f7:"snd z \<otimes> (t' \<otimes> (t \<otimes> (snd y \<otimes> fst x))) \<ominus> snd x \<otimes> (t \<otimes> (t' \<otimes> (snd y \<otimes> fst z))) = \<zero>"
      using f5 f6
      by (smt \<open>snd z \<otimes> (t' \<otimes> (t \<otimes> (snd x \<otimes> fst y))) = snd x \<otimes> (t \<otimes> (t' \<otimes> (snd z \<otimes> fst y)))\<close> \<open>t' \<otimes> (snd z \<otimes> fst y) \<ominus> t' \<otimes> (snd y \<otimes> fst z) = \<zero>\<close> a4 a5 f3 is_abelian_group mem_Sigma_iff minus_to_eq partial_object.select_convs(1) prod.collapse rel_def semiring_simprules(3) subset subset_iff)
    moreover have "(t \<otimes> t' \<otimes> snd y) \<otimes> ((snd z \<otimes> fst x) \<ominus> (snd x \<otimes> fst z)) = ((t \<otimes> t' \<otimes> snd y) \<otimes> (snd z \<otimes> fst x)) \<ominus> ((t \<otimes> t' \<otimes> snd y) \<otimes> (snd x \<otimes> fst z))"
      using r_distr f1 f3 subset a3 a4 a5 rel_def a_minus_def r_minus
      by (smt SigmaE abelian_group.a_inv_closed is_abelian_group monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.sel(1) prod.sel(2) subset_iff)
    moreover have f8:"(t \<otimes> t' \<otimes> snd y) \<otimes> (snd z \<otimes> fst x) = snd z \<otimes> (t' \<otimes> (t \<otimes> (snd y \<otimes> fst x)))"
      using m_assoc comm_monoid_axioms_def[of R] f1 f3 subset a3 a4 a5 rel_def set_rev_mp
      by (smt SigmaE local.semiring_axioms m_lcomm partial_object.select_convs(1) prod.sel(1) prod.sel(2) semiring.semiring_simprules(3))
    moreover have f9:"(t \<otimes> t' \<otimes> snd y) \<otimes> (snd x \<otimes> fst z) = snd x \<otimes> (t \<otimes> (t' \<otimes> (snd y \<otimes> fst z)))"
      using m_assoc comm_monoid_axioms_def[of R] f1 f3 subset a3 a4 a5 rel_def set_rev_mp
      by (smt SigmaE m_comm monoid.m_closed monoid_axioms partial_object.select_convs(1) prod.sel(1) prod.sel(2))
    then have f10:"(t \<otimes> t' \<otimes> snd y) \<otimes> (snd z \<otimes> fst x) \<ominus> (t \<otimes> t' \<otimes> snd y) \<otimes> (snd x \<otimes> fst z) = \<zero>"
      using f7 f8 f9 by simp
    moreover have "t \<otimes> t' \<otimes> snd y \<in> S"
      using f1 f3 a4 rel_def m_closed
      by (simp add: mem_Times_iff)
    then have "(t \<otimes> t' \<otimes> snd y) \<otimes> (snd z \<otimes> fst x \<ominus> snd x \<otimes> fst z) = \<zero>"
      using r_distr subset set_rev_mp f10 calculation(2) by auto
    thus " x .=\<^bsub>rel\<^esub> z"
      using rel_def \<open>t \<otimes> t' \<otimes> snd y \<in> S\<close> by auto
  qed
qed