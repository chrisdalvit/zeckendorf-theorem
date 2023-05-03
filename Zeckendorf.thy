theory Zeckendorf

imports 
  Main
  "HOL-Number_Theory.Number_Theory"

begin

definition is_fib :: "nat \<Rightarrow> bool" where
  "is_fib n = (\<exists> i. n = fib i)"

definition le_fibs_idx_set :: "nat \<Rightarrow> nat set" where
  "le_fibs_idx_set n = {i .fib i < n}"

definition inc_seq_on :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> bool" where
  "inc_seq_on f I = (\<forall> n \<in> I. f(n+1) > (f n)+1)"

definition fibs_idx_set :: "nat \<Rightarrow> nat set" where
  "fibs_idx_set n = {i. fib i = n}"

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

lemma no_fib_empty_index: "\<not> is_fib n \<Longrightarrow> fibs_idx_set n = {}"
  using is_fib_def fibs_idx_set_def by auto

\<comment> \<open>Deprecated ---> delete if not needed\<close>
lemma "\<not> is_fib n \<Longrightarrow> finite(fibs_idx_set n)"
  unfolding no_fib_empty_index by simp

lemma fib_implies_is_fib: "fib i = n \<Longrightarrow> is_fib n"
  using is_fib_def by auto

lemma ge_2_unique_fib_idx: "n \<ge> 2 \<Longrightarrow> n = fib i \<Longrightarrow> n = fib j \<Longrightarrow> i = j"
  using fib_index_strict_mono fib_mono Suc_1 fib_2 nle_le nless_le not_less_eq by metis

lemma zero_unique_fib_idx: "n = fib i \<Longrightarrow> n = fib 0  \<Longrightarrow> i = 0"
  using fib_neq_0_nat fibs_idx_set_def by fastforce

lemma one_fib_idx: "fib i = Suc 0 \<Longrightarrow> i = Suc 0 \<or> i = Suc(Suc 0)"
  using Fib.fib0 One_nat_def Suc_1 eq_imp_le fib_2 fib_index_strict_mono less_2_cases nat_neq_iff by metis

lemma zero_fib_idx_set: "fibs_idx_set 0 = {0}" 
  using zero_unique_fib_idx unfolding fibs_idx_set_def by auto 

lemma one_fib_idx_set: "fibs_idx_set 1 = {1,2}" 
  using one_fib_idx unfolding fibs_idx_set_def by fastforce

lemma ge_2_fib_idx_set: "fib i = n \<Longrightarrow> n \<ge> 2 \<Longrightarrow> fibs_idx_set n = {i}"
  using ge_2_unique_fib_idx[of n] unfolding fibs_idx_set_def is_fib_def by auto

lemma fib_implies_bounded_fib_idx_set: "is_fib n \<Longrightarrow> \<exists> m.\<forall> n\<in>fibs_idx_set n. n < m"
proof -
  assume "is_fib n"
  then obtain i where "fib i = n" unfolding is_fib_def by auto
  consider "n = 0" | "n = 1" | "n \<ge> 2" by linarith
  then show "\<exists> m.\<forall> n\<in>fibs_idx_set n. n < m"
    using zero_fib_idx_set one_fib_idx_set ge_2_fib_idx_set \<open>fib i = n\<close> by(cases, auto)
qed

lemma bounded_fib_index: "\<exists> m. \<forall> n \<in> fibs_idx_set n. n < m"
  using fib_implies_bounded_fib_idx_set no_fib_empty_index by auto

lemma finite_fib_index: "finite(fibs_idx_set n)"
  using bounded_nat_set_is_finite bounded_fib_index by presburger

lemma no_fib_lower_bound: "\<not> is_fib n \<Longrightarrow> n \<ge> 4"
proof(rule ccontr)
  assume "\<not> is_fib n" "\<not> 4 \<le> n"
  hence "n \<in> {0,1,2,3}" by auto
  have "is_fib 0" "is_fib 1" "is_fib 2" "is_fib 3"
    using fib0 fib1 fib_values fib_implies_is_fib by blast+
  then show False
    using \<open>\<not> is_fib n\<close> \<open>n \<in> {0,1,2,3}\<close> by blast
qed

lemma inc_seq_smaller_domain: "inc_seq_on f {0..Suc k} \<Longrightarrow> inc_seq_on f {0..k}"
  unfolding inc_seq_on_def by simp

lemma inc_seq_suc_greater: "inc_seq_on f {0..k} \<Longrightarrow> x \<in> {0..k} \<Longrightarrow> f(x+1) > f x"
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

\<comment> \<open>
  Use this lemma to show that if sequence contains 0 then it can later be obmitted for fibs
\<close>
lemma zero_starts_inc_seq: "inc_seq_on f {0..k} \<Longrightarrow> x \<in> {0..k} \<Longrightarrow> f x = 0 \<Longrightarrow> x = 0"
  using inc_seq_strict_mono[of f k 0 x] by auto

\<comment> \<open>
  Deprecated: maybe delete
\<close>
lemma inc_seq_inj_on_aux: "inc_seq_on f {0..k} \<Longrightarrow> inj_on f {0..k}"
  unfolding inj_on_def using inc_seq_strict_mono nat_neq_iff by metis

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

\<comment> \<open>
  Deprecated --> maybe delete
\<close>
lemma inc_seq_extension: "inc_seq_on c {0..k} \<Longrightarrow> c (k+1) + 2 \<le> c (k+2) \<Longrightarrow> inc_seq_on c {0..k+1}"
  by (simp add: atLeast0_atMost_Suc inc_seq_on_def)

lemma fib_implies_zeckendorf:
  assumes "is_fib n"
  shows "\<exists> c k. n = (\<Sum> i=0..k. fib(c i)) \<and> inc_seq_on c {0..k-1}" 
proof -
  from assms obtain idx where idx_def: "fib idx = n" 
    unfolding is_fib_def by auto
  hence "n = (\<Sum>i = 0..0. fib ((\<lambda> n::nat. if n = 0 then idx else idx + 3) i))" 
    by simp
  moreover have "inc_seq_on (\<lambda> n::nat. if n = 0 then idx else idx + 3) {0..0}" 
    unfolding inc_seq_on_def by simp
  ultimately show ?thesis 
    by fastforce
qed

lemma no_fib_implies_le_fibs_idx_set: "\<not> is_fib n \<Longrightarrow> le_fibs_idx_set n \<noteq> {}"
proof - 
  assume "\<not> is_fib n"
  hence "0 \<in> le_fibs_idx_set n" 
    using no_fib_lower_bound unfolding le_fibs_idx_set_def by fastforce
  thus "le_fibs_idx_set n \<noteq> {}" by blast
qed

lemma finite_smaller_fibs: "finite(le_fibs_idx_set n)"
proof(induct n)
  case (Suc n)
  moreover have "{i. fib i < Suc n} = {i. fib i < n} \<union> {i. fib i = n}" 
    by auto
  moreover have "finite({i. fib i = n})"
    using finite_fib_index fibs_idx_set_def by auto
  ultimately show ?case 
    unfolding le_fibs_idx_set_def by auto
qed (simp add: le_fibs_idx_set_def)

lemma no_fib_between_fibs: "\<not> is_fib n \<Longrightarrow> \<exists> i. fib i < n \<and> n < fib (Suc i)"
proof - 
  assume "\<not> is_fib n"
  obtain i where "i = Max(le_fibs_idx_set n)" by blast
  then show "\<exists> i. fib i < n \<and> n < fib (Suc i)"
  proof(intro exI conjI)
    assume "i = Max (le_fibs_idx_set n)"
    hence "(Suc i) \<notin> (le_fibs_idx_set n)" 
      by (metis Max_ge Suc_n_not_le_n finite_smaller_fibs)
    thus "fib (Suc i) > n" 
      using \<open>\<not> is_fib n\<close> fib_implies_is_fib order_le_imp_less_or_eq le_fibs_idx_set_def by fastforce
  qed(insert no_fib_implies_le_fibs_idx_set \<open>\<not> is_fib n\<close> finite_smaller_fibs Max_in le_fibs_idx_set_def, auto)
qed

lemma
  assumes "n > 0" "n = (\<Sum> i=0..k. fib (c i))" "inc_seq_on c {0..k-1}"
  shows "\<exists> k c. n = (\<Sum> i=0..k. fib (c i)) \<and> inc_seq_on c {0..k-1} \<and> (\<forall> i\<in>{0..k}. c i \<ge> 1)"
proof(cases k)
  case 0
  then show ?thesis
  proof(cases "c 0 = 0")
    case False
    show ?thesis using assms False zero_starts_inc_seq[OF assms(3)] 0 by fastforce
  qed(insert assms 0 fib0, auto)
next
  case (Suc nat)
  have c: "inc_seq_on c {0..nat-1}"
    using assms unfolding Suc inc_seq_on_def by simp 
  have "n = (\<Sum>i = 0..Suc nat. fib (c i))"
    using assms unfolding Suc by simp
  then show ?thesis
  proof(cases "c 0 = 0")
    case True
    let "?c'" = "(\<lambda> i. c (Suc i))"
    have "inc_seq_on c {0..nat}"
      using assms unfolding Suc inc_seq_on_def
      by auto
    hence c: "inc_seq_on ?c' {0..nat-1}"
      unfolding inc_seq_on_def 
      sorry
    have "n = fib (c 0) + (\<Sum> i=1..k. fib (c i))"
      using assms True by (simp add: sum_shift_lb_Suc0_0)
    hence s: "n = (\<Sum> i=1..Suc nat. fib (c i))"
      unfolding True fib0 Suc by simp
    have b:"\<forall> i \<in> {0..nat}. ?c' i \<ge> 1"
      using assms zero_starts_inc_seq Suc
      by (metis One_nat_def Suc_eq_plus1 Suc_le_mono bot_nat_0.extremum diff_Suc_1 inc_seq_on_def le_Suc_eq less_nat_zero_code)
    have a: "n = (\<Sum> i=0..nat. fib (?c' i))"
      using s sum.shift_bounds_cl_Suc_ivl unfolding One_nat_def by blast
    then show ?thesis
      using a b c by auto
  next
    case False
    have "\<forall> i\<in>{0..k}. c i \<ge> 1"
      using zero_starts_inc_seq[OF assms(3)] assms False Suc unfolding inc_seq_on_def
      apply auto
      apply (metis (no_types, opaque_lifting) Suc_le_D Suc_le_mono atLeastAtMost_iff bot_nat_0.extremum_strict le_simps(3) not_gr0)
      by (metis Suc_le_D atLeastAtMost_iff bot_nat_0.extremum_uniqueI less_nat_zero_code not_less_eq_eq)
    then show ?thesis
      using assms by auto
  qed
qed

\<comment> \<open>
  ----> Simplify
\<close>
theorem zeckendorfI:
  assumes "n > 0"
  shows "\<exists> c k. n = (\<Sum> i=0..k. fib (c i)) \<and> inc_seq_on c {0..k-1}" 
  using assms
proof(induct n rule: nat_less_induct)
  case (1 n)
  then show ?case
  proof(cases "is_fib n")
    case False
    obtain i where lower: "fib i < n" and upper: "n < fib (Suc i)" and ge_one: "i > 0"
      using no_fib_between_fibs 1(2) False by force
    then obtain c k where decomp: "(n - fib i) = (\<Sum> i=0..k. fib (c i))" and seq: "inc_seq_on c {0..k-1}" 
      using 1 fib_neq_0_nat zero_less_diff diff_less by metis
    from ge_one obtain m where "i = Suc m"
      using gr0_implies_Suc by auto
    let ?c' = "(\<lambda> n. if n = k+1 then i  else c n)"
    have "n - fib i < fib(i-1)"
      using upper lower fib2 \<open>i = Suc m\<close> by simp 
    have "n - fib i < fib i"
      using \<open>n - fib i < fib(i-1)\<close> \<open>i = Suc m\<close> fib_Suc_mono[of "i-1"] by simp
    hence "fib (c k) < fib i" 
      by (simp add: sum.last_plus decomp)
    have "inc_seq_on ?c' {0..k}"
      using seq unfolding inc_seq_on_def
      apply auto
      using \<open>n - fib i < fib (i-1)\<close> \<open>fib (c k) < fib i\<close> 
      using add_diff_cancel_left' bot_nat_0.extremum decomp fib_mono le_SucE le_add1 linorder_not_le plus_1_eq_Suc sum.last_plus
      by (metis add_diff_cancel_left' bot_nat_0.extremum decomp fib_mono le_SucE le_add1 linorder_not_le plus_1_eq_Suc sum.last_plus)
    moreover have "n = (\<Sum> i=0..k+1. fib (?c' i))" 
      using lower decomp by simp
    ultimately show ?thesis by fastforce
  qed(insert fib_implies_zeckendorf, auto)
qed

theorem zeckendorf_setI: 
  assumes "n > 0"
  shows "\<exists> I. n = (\<Sum> i\<in>I. fib i) \<and> I \<noteq> {}" 
proof - 
  from assms obtain c k where decomp: "n = (\<Sum> i=0..k::nat. fib(c i))" and inc: "inc_seq_on c {0..k-1}" 
    using zeckendorfI by blast
  then show "\<exists> I. n = (\<Sum> i\<in>I. fib i) \<and> I \<noteq> {}"
  proof(cases "k=0")
    case True
    hence "n = sum fib (c ` {0})" using decomp by simp
    then show ?thesis using decomp by blast
  next
    case False
    hence "n = (\<Sum> i \<in> c ` {0..k}. fib i)"
      using sum.reindex_bij_betw decomp inc inc_seq_bij_betw by fastforce
    then show ?thesis by auto
  qed
qed

theorem zeckendorf_unique:
  assumes "n > 0" "finite A" "finite B"
  assumes "n = (\<Sum> i\<in>A. fib i)" "n = (\<Sum> i\<in>B. fib i)"
  shows "A = B"
proof -   
  let ?I = "A - (A \<inter> B)"
  let ?I' = "B - (A \<inter>  B)"
  have "(\<Sum> i\<in>A. fib i) = (\<Sum> i\<in>B. fib i)" 
    using assms by blast
  hence "(\<Sum> i\<in>?I. fib i) = (\<Sum> i\<in>?I'. fib i)"
    using assms 
    by (simp add: sum_diff_nat)
  oops