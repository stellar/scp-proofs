theory FBA
  imports Main 
begin

section "Personal Byzantine quorum systems"

text \<open>We start by proving some facts about an abstraction of FBA called a personal Byzantine quorum system (PBQS).
For more details about PBQSs see the paper "Stellar Consensus by Instantiation", to appear at DISC 2019.\<close>

locale pbqs =
  fixes quorum_of :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  fixes W::"'node set"
  assumes quorum_assm:"\<And> p p' . \<lbrakk>p \<in> W; quorum_of p Q; p' \<in> Q\<inter>W\<rbrakk> \<Longrightarrow> \<exists> Q' . quorum_of p' Q' \<and> Q'\<subseteq>Q"
    \<comment> \<open>In other words, a quorum (of some participant) must contain a quorum of each of its members.\<close>
begin

definition blocks where
  \<comment> \<open>Set @{term R} blocks participant @{term p}.\<close>
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"

abbreviation blocked_by where "blocked_by R \<equiv> {p . blocks R p}"

abbreviation B where "B \<equiv> -W"
  \<comment> \<open>@{term B} is the set of malicious nodes.\<close>

definition quorum_of_set where "quorum_of_set S Q \<equiv> \<exists> p \<in> S . quorum_of p Q"

subsection "The set of participants not blocked by malicious participants"

definition L where "L \<equiv> W - (blocked_by B)"

lemma l2: "p \<in> L \<Longrightarrow> \<exists> Q  \<subseteq> W. quorum_of p Q" 
  unfolding L_def blocks_def using DiffD2 by auto
 
lemma l3:
\<comment>  \<open>If a participant is not blocked by the malicious participants, then it has a quorum consisting exclusively of correct 
participants which are not blocked by the malicious participants.\<close>
  assumes "p \<in> L" shows "\<exists> Q \<subseteq> L . quorum_of p Q"
proof -
  have False if 1:"\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> (-L) \<noteq> {}"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> W" 
      using l2 \<open>p \<in> L\<close> by auto 
    obtain p' where "p' \<in> Q \<inter> (-L)"  using 1 \<open>quorum_of p Q\<close> by auto
    then obtain Q' where "quorum_of p' Q'" and "Q' \<subseteq> Q"  using \<open>quorum_of p Q\<close> quorum_assm assms
      by (metis DiffD1 IntD1 L_def \<open>Q \<subseteq> W\<close> inf.orderE)

    from \<open>quorum_of p' Q'\<close> and \<open> p' \<in> Q \<inter> (-L)\<close>  \<open>Q \<subseteq> W\<close> have "Q' \<inter> B \<noteq> {}" unfolding L_def blocks_def by auto
    thus False using \<open>Q \<subseteq> W\<close> \<open>Q' \<subseteq> Q\<close> by auto
  qed 
  thus ?thesis by (metis disjoint_eq_subset_Compl double_complement)
qed

subsection "Intact sets"

definition is_intertwined where
  "is_intertwined S \<equiv> S \<subseteq> W 
    \<and> (\<forall> Q Q' . quorum_of_set S Q \<and> quorum_of_set S Q' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition is_intact where
  \<comment> \<open>NOTE: This is weaker than the notion of intact set presented in the Stellar Whitepaper~\cite{MazieresStellarConsensusProtocol2015}.\<close>
  "is_intact I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<subseteq> I . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set I Q \<and> quorum_of_set I Q' \<longrightarrow> I \<inter> Q \<inter> Q' \<noteq> {})"

text \<open>Next we show that the union of two intact sets that intersect is an intact set.\<close>

lemma intact_union:
  assumes "is_intact I\<^sub>1" and "is_intact I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_intact (I\<^sub>1\<union> I\<^sub>2)"
proof -
  have "I\<^sub>1 \<union> I\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_intact_def by auto
  moreover

  text \<open>Next, we prove quorum availability (this is trivial):\<close>
  have "\<forall> p \<in> (I\<^sub>1\<union>I\<^sub>2) . \<exists> Q \<subseteq> (I\<^sub>1\<union>I\<^sub>2) . quorum_of p Q" 
    using \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> unfolding is_intact_def
    by (meson UnE le_supI1 le_supI2)
  moreover

  text \<open>Finally, we prove quorum intersection, which is a little harder:\<close>
  have "(I\<^sub>1\<union>I\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}"
    if "quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>1" and "quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>2" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    text \<open>First we generalize to avoid repeating the argument twice:\<close>
    have \<open>(I\<^sub>1\<union>I\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "is_intact I\<^sub>1" and "is_intact I\<^sub>2"
      and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "quorum_of_set I\<^sub>1 Q\<^sub>1" and "quorum_of_set I\<^sub>2 Q\<^sub>2"
    for I\<^sub>1 I\<^sub>2
    proof -
      obtain p Q where "quorum_of p Q" and "p \<in> I\<^sub>1 \<inter> I\<^sub>2" and "Q \<subseteq> I\<^sub>2"
        using \<open>I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}\<close> \<open>is_intact I\<^sub>2\<close> unfolding is_intact_def by blast
      moreover
      obtain p\<^sub>1 where "quorum_of p\<^sub>1 Q\<^sub>1" and "p\<^sub>1 \<in> I\<^sub>1"
        using \<open>quorum_of_set I\<^sub>1 Q\<^sub>1\<close> quorum_of_set_def by auto
      obtain p' where "p' \<in> Q \<inter> Q\<^sub>1" using \<open>is_intact I\<^sub>1\<close> \<open>quorum_of_set I\<^sub>1 Q\<^sub>1\<close> \<open>quorum_of p Q\<close> \<open>p \<in> I\<^sub>1 \<inter> I\<^sub>2\<close>
        unfolding is_intact_def quorum_of_set_def
        by (metis Int_iff all_not_in_conv)
      moreover have "p' \<in> W" and "p\<^sub>1 \<in> W" and "p' \<in> I\<^sub>2" sorry
      ultimately obtain Q' where "quorum_of p' Q'" and "Q' \<subseteq> Q\<^sub>1"
        using quorum_assm[of p\<^sub>1 Q\<^sub>1] \<open>quorum_of p\<^sub>1 Q\<^sub>1\<close>
        by (meson Int_iff)
      hence "Q' \<inter> Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}" using \<open>is_intact I\<^sub>2\<close> \<open>quorum_of_set I\<^sub>2 Q\<^sub>2\<close> \<open>p' \<in> I\<^sub>2\<close> 
        unfolding quorum_of_set_def is_intact_def
        by (metis inf_assoc inf_sup_aci(1))
      thus "(I\<^sub>1\<union>I\<^sub>2) \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}"
        using \<open>Q' \<subseteq> Q\<^sub>1\<close> by blast 
    qed
    thus ?thesis using assms that unfolding quorum_of_set_def by auto 
  qed

  text \<open>Now we have all the properties of intact sets:\<close>
  ultimately show ?thesis using assms
    unfolding is_intact_def by simp
qed

end

section "Stellar quorum systems"

text \<open>We now show that FBA gives rise to a PBQS, and thus that the properties of PBQSs hold in FBA, and we prove the cascade theorem.\<close>

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>the well-behaved nodes\<close>
  assumes slices_ne:"\<And>p . p \<in> W \<Longrightarrow> slices p \<noteq> {}"
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . (\<exists> Sl \<in> slices p . Sl \<subseteq> Q)"

definition quorum_of where "quorum_of p Q \<equiv> quorum Q \<and> (p \<notin> W \<or> (\<exists> Sl \<in> slices p . Sl \<subseteq> Q))"

lemma quorum_union:"quorum Q \<Longrightarrow> quorum Q' \<Longrightarrow> quorum (Q \<union> Q')"
  unfolding quorum_def
  by (metis IntE Int_iff UnE inf_sup_aci(1) sup.coboundedI1 sup.coboundedI2)

lemma l1:
  assumes "\<And> p . p \<in> S \<Longrightarrow> \<exists> Q \<subseteq> S . quorum_of p Q" and "p\<in> S"
  shows "quorum_of p S" using assms unfolding quorum_of_def quorum_def
  by (meson Int_iff subset_trans)

lemma is_pbqs:
  assumes "quorum_of p Q" and "p' \<in> Q"
  shows "quorum_of p' Q" 
  \<comment> \<open>This is the property required of a PBQS.\<close>
  using assms
  by (simp add: quorum_def quorum_of_def)

interpretation pbqs quorum_of 
  \<comment> \<open>Stellar quorums form a personal quorum system.\<close>
  unfolding pbqs_def quorum_def quorum_of_def by blast 

lemma quorum_is_quorum_of_some_slice:
  assumes "quorum_of p Q" and "p \<in> W"
  obtains S where "S \<in> slices p" and "S \<subseteq> Q"
    and "\<And> p' . p' \<in> S \<inter> W \<Longrightarrow> quorum_of p' Q"
  using assms unfolding quorum_def quorum_of_def by fastforce

lemma "is_intact C \<Longrightarrow> quorum C" 
  \<comment> \<open>Every intact set is a quorum.\<close> 
  unfolding is_intact_def quorum_of_def quorum_def
  by fastforce

lemma in_quorum:"quorum Q \<Longrightarrow> p \<in> Q \<Longrightarrow> quorum_of p Q"
  by (simp add: quorum_def quorum_of_def)

subsection \<open>Properties of blocking sets\<close>

inductive blocking_max where
  \<comment> \<open>This is the set of participants that are eventually blocked by a set @{term R} when byzantine processors help epidemic propagation.\<close>
  "\<lbrakk>p \<in> W; \<forall> Sl \<in> slices p . \<exists> q \<in> Sl . q \<in> R\<union>B \<or> blocking_max R q\<rbrakk> \<Longrightarrow> blocking_max R p"
inductive_cases "blocking_max R p"

text \<open>Next we show that if @{term \<open>R\<close>} blocks @{term \<open>p\<close>} and @{term p} belongs to an intact set cluster @{term S}, then @{term \<open>R \<inter> S \<noteq> {}\<close>}.\<close>

text \<open>We first prove two auxiliary lemmas:\<close>

lemma intact_wb:"p \<in> I \<Longrightarrow> is_intact I \<Longrightarrow> p\<in>W"
  using is_intact_def  by fastforce 

lemma intact_has_ne_slices:
  assumes "is_intact I" and "p\<in>I"
    and "Sl \<in> slices p" 
  shows "Sl \<noteq> {}"
  using assms unfolding is_intact_def quorum_of_set_def quorum_of_def quorum_def
  by (metis empty_iff inf_bot_left inf_bot_right subset_refl)

lemma intact_has_intact_slice:
  assumes "is_intact I" and "p\<in>I"
  obtains Sl where "Sl \<in> slices p" and "Sl \<subseteq> I"
  using assms unfolding is_intact_def quorum_of_set_def quorum_of_def quorum_def
  by (metis Int_commute  empty_iff inf.order_iff  inf_bot_right le_infI1)

text \<open>Now the theorem:\<close>

theorem blocking_max_intersects_intact:
  \<comment> \<open>if @{term \<open>R\<close>} blocks @{term \<open>p\<close>} when malicious participants help epidemic propagation, 
and @{term p} belongs to an intact set @{term S}, then @{term \<open>R \<inter> S \<noteq> {}\<close>}\<close>
  assumes  "blocking_max R p" and "is_intact S" and "p \<in> S"
  shows "R \<inter> S \<noteq> {}" using assms
proof (induct)
  case (1 p R)
  obtain Sl where "Sl \<in> slices p" and "Sl \<subseteq> S" using intact_has_intact_slice
    using "1.prems" by blast
  moreover have "Sl \<subseteq> W" using assms(2) calculation(2) is_intact_def by auto 
  ultimately show ?case
    using "1.hyps" assms(2) by fastforce
qed

text \<open>Next we prove the cascade theorem\<close>

theorem cascade_thm:
  assumes "is_intact I" and "p \<in> I" and "quorum_of p Q" and "Q \<subseteq> S"
  obtains "I \<subseteq> S" | "\<exists> p' \<in> (W-S) . (\<forall> s \<in> slices p' . s \<inter> S \<inter> W \<noteq> {})"
    \<comment> \<open>Here we need potentially befouled nodes to help propagation...\<close>
  nitpick[card 'node=4, verbose, expect=none]
proof -
  have False if 1:"\<forall> p' \<in> (W-S) . (\<exists> s \<in> slices p' . s \<inter> S \<inter> W = {})" and 2:"\<not>I\<subseteq>S"
  proof -
    have "I \<subseteq> W" using assms(1) is_intact_def by auto 
    with 1 have "quorum ((-S)\<union>B)" unfolding quorum_def using Int_commute by fastforce
    with 2 obtain q where "q\<in>I" and "quorum_of q ((-S) \<union> B)" using in_quorum by fastforce 
    moreover have "((-S)\<union>B)\<inter>Q \<subseteq> B" using Compl_anti_mono \<open>Q\<subseteq>S\<close> by blast
    ultimately show False using \<open>p\<in>I\<close> and \<open>quorum_of p Q\<close>  and \<open>is_intact I\<close> 
      unfolding is_intact_def quorum_of_set_def by blast
  qed 
  thus ?thesis using that
    by auto
qed

end
