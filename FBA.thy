section "Definition of a Federated Byzantine Agreement System"

theory FBA
imports Main
begin

definition project where 
  "project slices S n \<equiv> {Sl \<inter> S | Sl . Sl \<in> slices n}"

locale FBAS =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>the well-behaved nodes\<close>
  assumes slices_ne:"\<And>p . p \<in> W \<Longrightarrow> slices p \<noteq> {}"
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . (\<exists> Sl \<in> slices p . Sl \<subseteq> Q)"

definition quorum_of where
  "quorum_of p Q \<equiv> p \<in> Q \<and> quorum Q"

end

section \<open>The Cascade Theorem\<close>

locale intact = \<comment> \<open>Here we fix an intact set @{term I} and prove the cascade theorem.\<close>
  orig:FBAS slices W 
  + proj:FBAS "project slices I" W \<comment> \<open>We consider the projection of the system on @{term I}\<close>
  for slices W I +
  assumes "I \<subseteq> W" 
    and q_avail:"orig.quorum I"
    and q_inter:"\<And> Q Q' . \<lbrakk>proj.quorum Q; proj.quorum Q'; Q \<inter> I \<noteq> {}; Q' \<inter> I \<noteq> {}\<rbrakk>  \<Longrightarrow> Q \<inter> Q' \<inter> I \<noteq> {}"
begin

theorem cascade:
  fixes U S
  assumes "orig.quorum U" and "U \<inter> I \<noteq> {}" and "U \<subseteq> S"
  obtains "I \<subseteq> S" | "\<exists> n \<in> I - S . \<forall> Sl \<in> slices n . Sl \<inter> S \<inter> I \<noteq> {}"
proof -
  have False if "\<forall> n \<in> I - S . \<exists> Sl \<in> slices n . Sl \<inter> S \<inter> I = {}" and "\<not>I \<subseteq> S"
  proof -
    text \<open>First we show that @{term \<open>I-S\<close>} is a quorum in the projected system:\<close>
    have "proj.quorum (I-S)" using that(1)
      unfolding proj.quorum_def project_def 
      by (auto; smt DiffI Diff_Compl Diff_Int_distrib Diff_eq Diff_eq_empty_iff Int_commute)
    text \<open>Then we show that U is also a quorum in the projected system:\<close>
    moreover have "proj.quorum U" using \<open>orig.quorum U\<close> 
      unfolding proj.quorum_def orig.quorum_def project_def 
      by (simp; meson Int_commute inf.coboundedI2)
    text \<open>Since quorums of @{term I} must intersect, we get a contradiction:\<close>
    ultimately show False using \<open>U \<subseteq> S\<close> \<open>U \<inter> I \<noteq> {}\<close> \<open>\<not>I\<subseteq>S\<close> q_inter by auto
  qed
  thus ?thesis using that by blast
qed

end

section "The Union Theorem"

text \<open>Here we prove that the union of two intact sets that intersect is intact.
This implies that maximal intact sets are disjoint.\<close>

locale intersecting_intact = 
  i1:intact slices W I\<^sub>1 + i2:intact slices W I\<^sub>2 \<comment> \<open>We fix two intersecting intact sets @{term I\<^sub>1} and @{term I\<^sub>2}.\<close>
  + proj:FBAS "project slices (I\<^sub>1\<union>I\<^sub>2)" W \<comment> \<open>We consider the projection of the system on @{term \<open>I\<^sub>1\<union>I\<^sub>2\<close>}.\<close>
  for slices W I\<^sub>1 I\<^sub>2 +
assumes inter:"I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
begin

theorem union_quorum: "i1.orig.quorum (I\<^sub>1\<union>I\<^sub>2)"
  using i1.intact_axioms i2.intact_axioms
  unfolding  intact_def FBAS_def intact_axioms_def i1.orig.quorum_def
  by (metis Int_iff Un_iff le_supI1 le_supI2)

theorem union_quorum_intersection: 
  assumes "proj.quorum Q\<^sub>1" and "proj.quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" and "Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}"
  shows "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}"
proof -
  text \<open>First we show that @{term Q\<^sub>1} and @{term Q\<^sub>2} are quorums in the projections on @{term I\<^sub>1} and @{term I\<^sub>2}.\<close>
  have "i1.proj.quorum Q\<^sub>1" using \<open>proj.quorum Q\<^sub>1\<close> 
    unfolding i1.proj.quorum_def proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  moreover have "i2.proj.quorum Q\<^sub>2" using \<open>proj.quorum Q\<^sub>2\<close> 
    unfolding i2.proj.quorum_def proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  moreover have "i2.proj.quorum Q\<^sub>1" using \<open>proj.quorum Q\<^sub>1\<close>
    unfolding proj.quorum_def i2.proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  moreover have "i1.proj.quorum Q\<^sub>2" using \<open>proj.quorum Q\<^sub>2\<close>
    unfolding proj.quorum_def i1.proj.quorum_def project_def
    by auto (metis Int_Un_distrib Int_iff Un_subset_iff) 
  text \<open>Next we show that @{term Q\<^sub>1} and @{term Q\<^sub>2} intersect if they are quorums of, respectively, @{term I\<^sub>1} and @{term I\<^sub>2}. 
This is the only interesting part of the proof.\<close> 
  moreover have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" 
    if "i1.proj.quorum Q\<^sub>1" and "i2.proj.quorum Q\<^sub>2" and "i2.proj.quorum Q\<^sub>1"
      and "Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}"
    for Q\<^sub>1 Q\<^sub>2
  proof -
    obtain n where "n \<in> I\<^sub>1\<inter>I\<^sub>2" using inter by blast
    have "i1.proj.quorum I\<^sub>2" 
    proof -
      have "i1.orig.quorum I\<^sub>2" by (simp add: i2.q_avail)
      thus ?thesis unfolding i1.orig.quorum_def i1.proj.quorum_def project_def
        by auto (meson Int_commute Int_iff inf_le2 subset_trans)
    qed
    moreover note \<open>i1.proj.quorum Q\<^sub>1\<close>
    ultimately have "Q\<^sub>1 \<inter> I\<^sub>2 \<inter> I\<^sub>1 \<noteq> {}" using i1.q_inter inter \<open>Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}\<close> by blast
    moreover note \<open>i2.proj.quorum Q\<^sub>2\<close>  
    moreover note \<open>i2.proj.quorum Q\<^sub>1\<close>
    ultimately have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}" using i2.q_inter \<open>Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}\<close> by blast 
    thus ?thesis by (simp add: inf_sup_distrib1)
  qed
  text \<open>Next  we show that @{term Q\<^sub>1} and @{term Q\<^sub>2} intersect if they are quorums of the same intact set. This is obvious.\<close>
  moreover
  have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" 
    if "i1.proj.quorum Q\<^sub>1" and "i1.proj.quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>1 \<noteq> {}"
    for Q\<^sub>1 Q\<^sub>2
    by (simp add: Int_Un_distrib i1.q_inter that(1) that(2) that(3) that(4))  
  moreover
  have "Q\<^sub>1 \<inter> Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}"
    if "i2.proj.quorum Q\<^sub>1" and "i2.proj.quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}"
    for Q\<^sub>1 Q\<^sub>2
    by (simp add: Int_Un_distrib i2.q_inter that)
  text \<open>Finally we have covered all the cases and get the final result:\<close>
  ultimately
  show ?thesis
    by (smt Int_Un_distrib Int_commute assms(3,4) sup_bot.right_neutral) 
qed

end

end