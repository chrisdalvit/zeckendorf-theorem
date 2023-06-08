theory Zeckendorf

imports 
  Main
  "HOL-Number_Theory.Number_Theory"

begin

definition is_fib :: "nat \<Rightarrow> bool" where
  "is_fib n = (\<exists> i. n = fib i)"

definition le_fib_idx_set :: "nat \<Rightarrow> nat set" where
  "le_fib_idx_set n = {i .fib i < n}"

definition inc_seq_on :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> bool" where
  "inc_seq_on f I = (\<forall> n \<in> I. f(n+1) > (f n)+1)"

definition fib_idx_set :: "nat \<Rightarrow> nat set" where
  "fib_idx_set n = {i. fib i = n}"

lemma fib_values[simp]:
  "fib 3 = 2"
  "fib 4 = 3"
  "fib 5 = 5"
  "fib 6 = 8"
  by(auto simp: numeral_Bit0 numeral_eq_Suc)

lemma fib_strict_mono: "i \<ge> 2 \<Longrightarrow> fib i < fib (Suc i)"
  using fib_mono by(induct i, simp, fastforce)

lemma fib_index_strict_mono : "i \<ge> 2 \<Longrightarrow> j > i \<Longrightarrow> fib j > fib i"
  by(induct i, simp, metis Suc_leI fib_mono fib_strict_mono nle_le nless_le)

lemma fib_implies_is_fib: "fib i = n \<Longrightarrow> is_fib n"
  using is_fib_def by auto


lemma zero_fib_unique_idx: "n = fib i \<Longrightarrow> n = fib 0 \<Longrightarrow> i = 0"
  using fib_neq_0_nat fib_idx_set_def by fastforce

lemma zero_fib_equiv: "fib i = 0 \<longleftrightarrow> i = 0"
  using zero_fib_unique_idx by auto

lemma one_fib_idxs: "fib i = Suc 0 \<Longrightarrow> i = Suc 0 \<or> i = Suc(Suc 0)"
  using Fib.fib0 One_nat_def Suc_1 eq_imp_le fib_2 fib_index_strict_mono less_2_cases nat_neq_iff by metis

lemma ge_two_eq_fib_implies_eq_idx: "n \<ge> 2 \<Longrightarrow> n = fib i \<Longrightarrow> n = fib j \<Longrightarrow> i = j"
  using fib_index_strict_mono fib_mono Suc_1 fib_2 nle_le nless_le not_less_eq by metis

lemma ge_two_fib_unique_idx: "fib i \<ge> 2 \<Longrightarrow> fib i = fib j \<Longrightarrow> i = j"
  using ge_two_eq_fib_implies_eq_idx by auto

lemma no_fib_lower_bound: "\<not> is_fib n \<Longrightarrow> n \<ge> 4"
proof(rule ccontr)
  assume "\<not> is_fib n" "\<not> 4 \<le> n"
  hence "n \<in> {0,1,2,3}" by auto
  have "is_fib 0" "is_fib 1" "is_fib 2" "is_fib 3"
    using fib0 fib1 fib_values fib_implies_is_fib by blast+
  then show False
    using \<open>\<not> is_fib n\<close> \<open>n \<in> {0,1,2,3}\<close> by blast
qed

lemma pos_fib_has_idx_ge_two: "n > 0 \<Longrightarrow> is_fib n \<Longrightarrow> (\<exists> i. i \<ge> 2 \<and> fib i = n)"
  unfolding is_fib_def by (metis One_nat_def fib_2 fib_mono less_eq_Suc_le nle_le)

lemma finite_fib0_idx: "finite({i. fib i = 0})"
  using zero_fib_unique_idx finite_nat_set_iff_bounded by auto

lemma finite_fib1_idx: "finite({i. fib i = 1})"
  using one_fib_idxs finite_nat_set_iff_bounded by auto

lemma finite_fib_ge_two_idx: "n \<ge> 2 \<Longrightarrow> finite({i. fib i = n})"
  using ge_two_fib_unique_idx finite_nat_set_iff_bounded by auto

lemma finite_fib_index: "finite({i. fib i = n})"
  using finite_fib0_idx finite_fib1_idx finite_fib_ge_two_idx by(rule nat_induct2, auto)

lemma no_fib_implies_le_fib_idx_set: "\<not> is_fib n \<Longrightarrow> {i. fib i < n} \<noteq> {}"
proof - 
  assume "\<not> is_fib n"
  hence "0 \<in> {i. fib i < n}" using no_fib_lower_bound by fastforce
  thus "{i. fib i < n} \<noteq> {}" by blast
qed

lemma finite_smaller_fibs: "finite({i. fib i < n})"
proof(induct n)
  case (Suc n)
  moreover have "{i. fib i < Suc n} = {i. fib i < n} \<union> {i. fib i = n}" by auto
  moreover have "finite({i. fib i = n})" using finite_fib_index by auto
  ultimately show ?case  by auto
qed simp

\<comment> \<open>AUX Lemma maybe simplify\<close>
lemma inc_seq_on_aux: "inc_seq_on c {0..k - 1} \<Longrightarrow> n - fib i < fib (i-1) \<Longrightarrow> fib (c k) < fib i \<Longrightarrow> 
                       (n - fib i) = (\<Sum> i=0..k. fib (c i)) \<Longrightarrow> Suc (c k) < i"
  by (metis fib_mono bot_nat_0.extremum diff_Suc_1 leD le_SucE linorder_le_less_linear not_add_less1 sum.last_plus)

lemma inc_seq_smaller_domain: "inc_seq_on f {0..Suc k} \<Longrightarrow> inc_seq_on f {0..k}"
  unfolding inc_seq_on_def by simp

lemma inc_seq_suc_greater: "inc_seq_on f I \<Longrightarrow> x \<in> I \<Longrightarrow> f(x+1) > f x"
  unfolding inc_seq_on_def by fastforce

lemma inc_seq_add_positive_geater: "inc_seq_on f {0..k} \<Longrightarrow> x \<in> {0..k} \<Longrightarrow> n > 0 \<Longrightarrow> x + n \<in> {0..k} \<Longrightarrow> f(x+n) > f x"
proof(induct n)
  case (Suc n)
  show ?case
  proof(cases "n = 0")
    case False
    hence "f x < f (x + n)" using Suc by auto
    moreover have "... < f (x + n + 1)" using Suc inc_seq_suc_greater by auto
    ultimately show ?thesis by simp
  qed(insert Suc inc_seq_suc_greater, auto)
qed auto

lemma inc_seq_strict_mono: "inc_seq_on f {0..k} \<Longrightarrow> x \<in> {0..k} \<Longrightarrow> y \<in> {0..k} \<Longrightarrow> y > x \<Longrightarrow> f y > f x"
  using inc_seq_add_positive_geater less_imp_add_positive by metis

lemma inc_seq_mono: "inc_seq_on f {0..k} \<Longrightarrow> x \<in> {0..k} \<Longrightarrow> y \<in> {0..k} \<Longrightarrow> y \<ge> x \<Longrightarrow> f y \<ge> f x"
  using inc_seq_strict_mono order_le_less unfolding inc_seq_on_def by metis

lemma inc_seq_upper_bound: "inc_seq_on f {0..k} \<Longrightarrow> x \<in> {0..k} \<Longrightarrow> f x < f(Suc k)"
proof(induct k)
  case (Suc k)
  then show ?case
  proof(cases "x \<in> {0..k}")
    case True
    then show ?thesis
      using Suc inc_seq_smaller_domain unfolding inc_seq_on_def by force
  next
    case False
    hence "x = Suc k" 
      using Suc by auto
    then show ?thesis
      using Suc unfolding inc_seq_on_def by fastforce
  qed
qed(simp add: inc_seq_on_def)

lemma inc_seq_inj_on: "inc_seq_on f {0..k} \<Longrightarrow> inj_on f {0..Suc k}"
proof -
  assume "inc_seq_on f {0..k}"
  hence "inj_on f {0..k}" unfolding inj_on_def using inc_seq_strict_mono nat_neq_iff by metis
  moreover have "\<forall> x\<in>{0..k}. f x = f (Suc k) \<longrightarrow> x = Suc k"
    using \<open>inc_seq_on f {0..k}\<close> inc_seq_upper_bound less_not_refl by metis
  ultimately show "inj_on f {0..Suc k}"
    using atLeastAtMost_iff le_Suc_eq unfolding inj_on_def by metis
qed

lemma inc_seq_bij_betw: "inc_seq_on f {0..k} \<Longrightarrow> bij_betw f {0..Suc k} (f ` {0..Suc k})"
  using inc_seq_inj_on inj_on_imp_bij_betw by blast

\<comment> \<open>-------------------------------------- PROOF -----------------------------------------\<close>

lemma fib_implies_zeckendorf:
  assumes "is_fib n" "n > 0"
  shows "\<exists> c k. n = (\<Sum> i=0..k. fib(c i)) \<and> inc_seq_on c {0..k-1} \<and> (\<forall> i\<in>{0..k}. c i \<ge> 2)" 
proof - 
  from assms obtain i where i_def: "fib i = n" "i \<ge> 2" using pos_fib_has_idx_ge_two by auto
  define c where c_def: "(c :: nat \<Rightarrow> nat) = (\<lambda> n::nat. if n = 0 then i else i + 3)"
  from i_def have "n = (\<Sum>i = 0..0. fib (c i))" by (simp add: c_def) 
  moreover have "inc_seq_on c {0..0}" by (simp add: c_def inc_seq_on_def)
  ultimately show "\<exists> c k. n = (\<Sum> i=0..k. fib(c i)) \<and> inc_seq_on c {0..k-1} \<and> (\<forall> i\<in>{0..k}. c i \<ge> 2)"
    using i_def c_def by fastforce
qed

lemma no_fib_betwn_fibs: "\<not> is_fib n \<Longrightarrow> \<exists> i. fib i < n \<and> n < fib (Suc i)"
proof - 
  assume "\<not> is_fib n"
  have finite_le_fib: "finite {i. fib i < n}" using finite_smaller_fibs by auto
  obtain i where max_def: "i = Max {i. fib i < n}" by blast
  show "\<exists> i. fib i < n \<and> n < fib (Suc i)"
  proof(intro exI conjI)
    have "(Suc i) \<notin> {i. fib i < n}" using max_def Max_ge Suc_n_not_le_n finite_le_fib by blast
    thus "fib (Suc i) > n" 
      using \<open>\<not> is_fib n\<close> fib_implies_is_fib linorder_less_linear by blast
  qed(insert max_def Max_in \<open>\<not> is_fib n\<close> finite_le_fib no_fib_implies_le_fib_idx_set, auto)
qed

theorem zeckendorfI:
  assumes "n > 0"
  shows "\<exists> c k. n = (\<Sum> i=0..k. fib (c i)) \<and> inc_seq_on c {0..k-1} \<and> (\<forall>i\<in>{0..k}. c i \<ge> 2)" 
  using assms
proof(induct n rule: nat_less_induct)
  case (1 n)
  then show ?case
  proof(cases "is_fib n")
    case False
    obtain i where bounds: "fib i < n" "n < fib (Suc i)" "i > 0"
      using no_fib_betwn_fibs 1(2) False by force
    then obtain c k where seq: "(n - fib i) = (\<Sum> i=0..k. fib (c i))" "inc_seq_on c {0..k-1}" "\<forall> i\<in>{0..k}. c i \<ge> 2"
      using 1 fib_neq_0_nat zero_less_diff diff_less by metis
    let ?c' = "(\<lambda> n. if n = k+1 then i else c n)"
    have diff_le_fib: "n - fib i < fib(i-1)"
      using bounds fib2 not0_implies_Suc[of i] by auto
    hence ck_lt_fib: "fib (c k) < fib i" 
      using fib_Suc_mono[of "i-1"] bounds by (simp add: sum.last_plus seq)
    have "inc_seq_on ?c' {0..k}"
      using inc_seq_on_aux[OF seq(2) diff_le_fib ck_lt_fib seq(1)] One_nat_def 
            inc_seq_on_def leI seq by force
    moreover have "n = (\<Sum> i=0..k+1. fib (?c' i))" 
      using bounds seq by simp
    moreover have "\<forall> i \<in> {0..k+1}. ?c' i \<ge> 2" 
      using seq bounds fib2 not0_implies_Suc[of i] atLeastAtMost_iff 
            diff_is_0_eq' less_nat_zero_code not_less_eq_eq by fastforce
    ultimately show ?thesis by fastforce
  qed(insert fib_implies_zeckendorf, auto)
qed


lemma zeckendorf_seq_to_set:
  assumes "n > 0"
  assumes "n = (\<Sum> i=0..k. fib (c i))" "inc_seq_on c {0..k-1}" "\<forall>i\<in>{0..k}. c i \<ge> 2"
  shows "n = (\<Sum> i\<in> c ` {0..k}. fib i)"
  using assms sum.reindex_bij_betw[OF inc_seq_bij_betw] by(cases k, auto)

theorem zeckendorf_setI: 
  assumes "n > 0"
  shows "\<exists> I. n = (\<Sum> i\<in>I. fib i) \<and> (\<forall> i\<in>I. i \<ge> 2)" 
  using zeckendorfI[OF assms(1)] zeckendorf_seq_to_set[OF assms(1)] by blast

\<comment> \<open>-------------------------------------- END PROOF -----------------------------------------\<close>

lemma fib_sum_zero_equiv: "(\<Sum> i=n..m::nat . fib (c i)) = 0 \<longleftrightarrow> (\<forall> i\<in>{n..m}. c i = 0)" 
  using finite_atLeastAtMost sum_eq_0_iff zero_fib_equiv by auto

lemma fib_idx_ge_two_fib_sum_not_zero: "n \<le> m \<Longrightarrow> \<forall>i\<in>{n..m::nat}. c i \<ge> 2 \<Longrightarrow> \<not> (\<Sum> i=n..m. fib (c i)) = 0"
  by (rule ccontr, simp add: fib_sum_zero_equiv)

lemma one_unique_fib_sum:
  assumes "inc_seq_on c {0..k-1}" "\<forall>i\<in>{0..k}. c i \<ge> 2"
  shows "(\<Sum> i=0..k. fib (c i)) = 1 \<longleftrightarrow> k = 0 \<and> c 0 = 2"
proof
  assume "(\<Sum>i = 0..k. fib (c i)) = 1"
  hence "fib (c 0) + (\<Sum>i = 1..k. fib (c i)) = 1" by (simp add: sum.atLeast_Suc_atMost)
  moreover have "fib (c 0) \<ge> 1" using assms(2) fib_neq_0_nat[of "c 0"] by force
  ultimately show "k = 0 \<and> c 0 = 2"
    using fib_idx_ge_two_fib_sum_not_zero[of 1 k c] assms add_is_1 one_fib_idxs by(cases "k=0", fastforce, auto)
qed simp

lemma smaller_index_implies_fib_le: "i < j \<Longrightarrow> fib(Suc i) \<le> fib j"
  using fib_mono by (induct j, auto)

lemma inc_seq_zero_at_start: "inc_seq_on c {0..k-1} \<Longrightarrow> c k = 0 \<Longrightarrow> k = 0"
  unfolding inc_seq_on_def
  by (metis One_nat_def Suc_eq_plus1 Suc_pred atLeast0AtMost atMost_iff less_nat_zero_code not_gr_zero order.refl)

lemma fib_sum_upper_bound:
  assumes "inc_seq_on c {0..k-1}" "\<forall>i\<in>{0..k}. c i \<ge> 2"
  shows "(\<Sum> i=0..k. fib (c i)) < fib (Suc (c k))"
  using assms
proof(induct "c k" arbitrary: k rule: nat_less_induct)
  case 1
  then show ?case
  proof(cases "c k")
    case (Suc nat)
    show ?thesis
    proof(cases k)
      case k_Suc: (Suc _)
      hence  ck_bounds: "c(k-1) + 1 < c k" "c(k-1) < c k"
        using 1(2) unfolding inc_seq_on_def by (force)+
      moreover have "(\<Sum>i = 0..k. fib (c i)) = fib(c k) + (\<Sum>i = 0..k-1. fib (c i))" 
        using k_Suc by simp
      moreover have "(\<Sum>i = 0..(k-1). fib (c i)) < fib (Suc (c (k-1)))" 
        using ck_bounds(2) 1 unfolding inc_seq_on_def by auto
      ultimately show ?thesis 
        using Suc smaller_index_implies_fib_le by fastforce
    qed(simp add: fib_index_strict_mono assms(2))
  qed(insert inc_seq_zero_at_start[OF 1(2)], auto)
qed

lemma nat_betw_fibs: "\<exists> i. fib i \<le> n \<and> fib(Suc i) > n"   
proof(cases "is_fib n")
  case True
  then obtain i where "fib i = n" unfolding is_fib_def by auto
  then show ?thesis
    using fib_Suc_mono leD 
    by (metis Fib.fib2 add_cancel_left_right le_refl linorder_neqE_nat old.nat.distinct(1) zero_fib_equiv)
qed(insert no_fib_betwn_fibs, force)
  

lemma nat_ge_2_fib_idx_bound: "2 \<le> n \<Longrightarrow> fib i \<le> n \<Longrightarrow> n < fib (Suc i) \<Longrightarrow> 2 \<le> i"
  by (metis One_nat_def fib_1 fib_2 le_Suc_eq less_2_cases linorder_not_le not_less_eq)

lemma last_fib_sum_index_constraint:
  assumes "n \<ge> 2" "n = (\<Sum> i=0..k. fib (c i))" "inc_seq_on c {0..k-1}" 
          "\<forall>i\<in>{0..k}. c i \<ge> 2" "fib i \<le> n" "fib(Suc i) > n"
  shows "c k = i"
proof -
  have "2 \<le> i" using assms(1,5,6) nat_ge_2_fib_idx_bound by simp 
  have "c k > i \<longrightarrow> False"
    using smaller_index_implies_fib_le assms 
    by (metis bot_nat_0.extremum leD sum.last_plus trans_le_add1)
  moreover have "c k < i \<longrightarrow> False"
  proof 
    assume "c k < i"
    have seq: "inc_seq_on c {0..k - 1 - 1}" "\<forall>i\<in>{0..k-1}. 2 \<le> c i"
      using assms unfolding inc_seq_on_def by simp+
    have "k > 0"
      by(rule ccontr, insert \<open>c k < i\<close> assms fib_index_strict_mono leD, auto)
    hence "c (k-1) + 1 < c k" "c (k-1) + 3 \<le> i"
      using \<open>c k < i\<close> assms unfolding inc_seq_on_def by force+
    have "(\<Sum>i = 0..k-1. fib (c i)) + fib (c k) = (\<Sum>i = 0..k. fib (c i))"
      using sum.atLeast0_atMost_Suc Suc_pred'[OF \<open>k > 0\<close>] by metis
    moreover have "fib (Suc (c (k-1))) \<le> fib (i-2)"
      using \<open>c k < i\<close> \<open>c (k-1) + 1 < c k\<close> by (simp add: fib_mono)
    moreover have "fib (c k) \<le> fib (i-1)"
      using \<open>c k < i\<close> fib_mono by fastforce
    ultimately have "(\<Sum>i = 0..k. fib (c i)) < fib (i-1) + fib (i-2)"
      using assms \<open>c k < i\<close> \<open>k > 0\<close> fib_sum_upper_bound[OF seq(1) seq(2)] by simp
    hence "(\<Sum>i = 0..k. fib (c i)) < fib i"
      using fib.simps(3)[of "i-2"] assms(4) \<open>c k < i\<close> 
      by (metis add_2_eq_Suc diff_Suc_1 \<open>2 \<le> i\<close> le_add_diff_inverse)
    then show False
      using assms by simp
    qed
    ultimately show ?thesis by simp
qed

lemma fib_unique_fib_sum:
  fixes k :: nat
  assumes "n \<ge> 2" "inc_seq_on c {0..k-1}" "\<forall>i\<in>{0..k}. c i \<ge> 2" 
  assumes "n = fib i"
  shows "n = (\<Sum>i=0..k. fib (c i)) \<longleftrightarrow> k = 0 \<and> c 0 = i"
proof
  assume ass: "n = (\<Sum>i = 0..k. fib (c i))"
  obtain j where bounds: "fib j \<le> n" "fib(Suc j) > n" "j \<ge> 2" 
    using nat_betw_fibs assms nat_ge_2_fib_idx_bound by blast
  have idx_eq: "c k = j"
    using last_fib_sum_index_constraint assms(1-3) ass bounds by simp
  have "i = j"
    using bounds ass assms by (metis Suc_leI fib_mono ge_two_fib_unique_idx le_neq_implies_less linorder_not_le)
  have "k > 0 \<longrightarrow> fib i = fib i + (\<Sum>i = 0..k-1. fib (c i))"
    using ass assms by (metis idx_eq One_nat_def Suc_pred \<open>i = j\<close> add.commute sum.atLeast0_atMost_Suc)
  hence "k > 0 \<longrightarrow> False"
    using fib_idx_ge_two_fib_sum_not_zero[of 0 "k-1" c] assms by auto
  then show "k = 0 \<and> c 0 = i" using \<open>i = j\<close> idx_eq by simp
qed(auto simp: assms)

lemma unique_zeckendorf:
  assumes "n > 0"
  assumes "n = (\<Sum> i=0..k. fib (c i))" "inc_seq_on c {0..k-1}" "\<forall>i\<in>{0..k}. c i \<ge> 2" 
  assumes "n = (\<Sum> i=0..k'. fib (c' i))" "inc_seq_on c' {0..k'-1}" "\<forall>i\<in>{0..k'}. c' i \<ge> 2"
  shows "k = k' \<and> (\<forall> i \<in> {0..k}. c i = c' i)"
  using assms
proof(induct n arbitrary: k k' rule: nat_less_induct)
  case IH: (1 n)
  consider "n = 0" | "n = 1" | "n \<ge> 2" by linarith
  then show ?case
  proof(cases)
    case 3
    obtain i where bounds: "fib i \<le> n" "fib(Suc i) > n" "2 \<le> i" 
      using nat_betw_fibs nat_ge_2_fib_idx_bound 3 by blast
    have last_idx_eq: "c' k' = i" "c k = i" "c' k' = c k"
      using last_fib_sum_index_constraint[OF 3] IH(6-8) IH(3-5) bounds by blast+
    then show ?thesis
    proof(cases "is_fib n")
      case True
      hence "fib i = n" 
        unfolding is_fib_def using bounds IH(2-8) fib_mono leD nle_le not_less_eq_eq by metis
      hence "k = 0" "c 0 = i" "k' = 0" "c' 0 = i"
        using fib_unique_fib_sum 3 IH(3-8) by metis+
        then show ?thesis by simp
    next
      case False
      have "k > 0" 
        using IH(3) False unfolding is_fib_def by fastforce
      have "k' > 0"
        using IH(6) False  unfolding is_fib_def by fastforce
      have "0 < n - fib (c k)" using False bounds last_idx_eq(2) unfolding is_fib_def by fastforce
      moreover have "n - fib (c k) < n" 
        using bounds last_idx_eq by (simp add: dual_order.strict_trans1 fib_neq_0_nat)
      moreover have "n - fib (c k) = (\<Sum>i = 0..k-1. fib (c i))" 
        using sum.atLeast0_atMost_Suc[of "\<lambda> i. fib (c i)" "k-1"] Suc_diff_1 \<open>k > 0\<close> IH(3) by simp
      moreover have "n - fib (c' k' ) = (\<Sum>i = 0..k'-1. fib (c' i))" 
        using sum.atLeast0_atMost_Suc[of "\<lambda> i. fib (c' i)" "k'-1"] Suc_diff_1 \<open>k' > 0\<close> IH(6) by simp
      moreover have "inc_seq_on c {0..k-1 - 1}" "\<forall>i\<in>{0..k-1}. 2 \<le> c i"
        using IH(4,5) unfolding inc_seq_on_def by auto
      moreover have "inc_seq_on c' {0..k'-1 - 1}" "\<forall>i\<in>{0..k'-1}. 2 \<le> c' i"
        using IH(7,8) unfolding inc_seq_on_def by auto
      ultimately have "k-1 = k'-1 \<and> (\<forall>i\<in>{0..k-1}. c i = c' i)"
        using IH(1) unfolding last_idx_eq by blast 
      then show ?thesis
        using IH(1) last_idx_eq by (metis One_nat_def Suc_pred \<open>0 < k'\<close> \<open>0 < k\<close> atLeastAtMost_iff le_Suc_eq)
    qed
  qed(insert IH one_unique_fib_sum, auto)
qed

definition non_consecutive :: "nat set \<Rightarrow> bool" where
"non_consecutive I = (\<forall> x \<in> I. Suc x \<notin> I)"
