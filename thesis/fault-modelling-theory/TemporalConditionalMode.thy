theory TemporalConditionalMode

imports Main

begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

type_synonym 'a tval = "'a list set"

definition var_condition :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "var_condition a ls \<equiv> distinct ls \<and> a \<in> set ls "

inductive_set
  ta :: "'a tval set"
where
  var: "{ ls . var_condition a ls } \<in> ta" |
  Compl: "S \<in> ta \<Longrightarrow> - S \<in> ta" |
  inter: "S \<in> ta \<Longrightarrow> T \<in> ta \<Longrightarrow> S \<inter> T \<in> ta"

lemma ta_Diff: 
  "S \<in> ta \<Longrightarrow> T \<in> ta \<Longrightarrow> S - T \<in> ta"
unfolding Diff_eq by (intro ta.inter ta.Compl)

lemma ta_union: "S \<in> ta \<Longrightarrow> T \<in> ta \<Longrightarrow> 
  S \<union> T \<in> ta"
proof -
  assume "S \<in> ta" and "T \<in> ta"
  hence "- (- S \<inter> - T) \<in> ta" by (intro ta.intros)
  thus "S \<union> T \<in> ta" by simp
qed

lemma ta_empty: "({} :: 'a tval) \<in> ta"
proof -
  obtain S :: "'a tval" where "S \<in> ta" 
    by (fast intro: ta.var)
  hence "S \<inter> -S \<in> ta" by (intro ta.intros)
  thus ?thesis by simp
qed

lemma ta_UNIV: "(UNIV :: 'a tval) \<in> ta"
proof -
  have "- {} \<in> ta" using ta_empty by (rule ta.Compl)
  thus "UNIV \<in> ta" by simp
qed

typedef 'a tformula = "ta :: 'a tval set" by (auto intro: ta_empty)

definition tvar :: "'a \<Rightarrow> 'a tformula"
where "tvar a = Abs_tformula { ls . var_condition a ls }"

lemma Rep_tformula_tvar : "Rep_tformula (tvar a) = { ls . var_condition a ls }"
unfolding tvar_def using ta.var by (rule Abs_tformula_inverse)

instantiation tformula :: (type) boolean_algebra
begin

definition
  "x \<sqinter> y = Abs_tformula (Rep_tformula x \<inter> Rep_tformula y)"

definition
  "x \<squnion> y = Abs_tformula (Rep_tformula x \<union> Rep_tformula y)"

definition
  "\<top> = Abs_tformula UNIV"

definition
  "\<bottom> = Abs_tformula {}"

definition
  "x \<le> y \<longleftrightarrow> Rep_tformula x \<subseteq> Rep_tformula y"

definition
  "x < y \<longleftrightarrow> Rep_tformula x \<subset> Rep_tformula y"

definition 
  "- x = Abs_tformula (- Rep_tformula x)"

definition
  "x - y = Abs_tformula (Rep_tformula x - Rep_tformula y)"

lemma Rep_tformula_inf:
  "Rep_tformula (x \<sqinter> y) = Rep_tformula x \<inter> Rep_tformula y"
unfolding inf_tformula_def
by (intro Abs_tformula_inverse ta.inter Rep_tformula)

lemma Rep_tformula_sup:
  "Rep_tformula (x \<squnion> y) = Rep_tformula x \<union> Rep_tformula y"
unfolding sup_tformula_def
by (intro Abs_tformula_inverse ta_union Rep_tformula)

lemma Rep_tformula_top: "Rep_tformula \<top> = UNIV"
unfolding top_tformula_def by (intro Abs_tformula_inverse ta_UNIV)

lemma Rep_tformula_bot: "Rep_tformula \<bottom> = {}"
unfolding bot_tformula_def by (intro Abs_tformula_inverse ta_empty)

lemma Rep_tformula_compl: "Rep_tformula (- x) = - Rep_tformula x"
unfolding uminus_tformula_def
by (intro Abs_tformula_inverse ta.Compl Rep_tformula)

lemma Rep_tformula_diff:
  "Rep_tformula (x - y) = Rep_tformula x - Rep_tformula y"
unfolding minus_tformula_def
by (intro Abs_tformula_inverse ta_Diff Rep_tformula)

lemmas eq_tformula_iff = Rep_tformula_inject [symmetric]

lemmas Rep_tformula_simps =
  less_eq_tformula_def less_tformula_def eq_tformula_iff
  Rep_tformula_sup Rep_tformula_inf Rep_tformula_top Rep_tformula_bot
  Rep_tformula_compl Rep_tformula_diff Rep_tformula_tvar

instance proof
qed (unfold Rep_tformula_simps, auto)

end

lemma bot_neq_top_tformula [simp]: "(\<bottom> :: 'a tformula) \<noteq> \<top>"
unfolding Rep_tformula_simps by auto

lemma top_neq_bot_tformula [simp]: "(\<top> :: 'a tformula) \<noteq> \<bottom>"
unfolding Rep_tformula_simps by auto

lemma var_le_tvar_simps [simp]:
  "tvar x \<le> tvar y \<longleftrightarrow> x = y"
  "\<not> tvar x \<le> - tvar y"
  "\<not> - tvar x \<le> tvar y "
apply (auto simp add: Rep_tformula_simps var_condition_def )
apply (auto simp add: subset_eq)
apply (auto simp add: distinct_conv_nth)
done

lemma var_eq_tvar_simps [simp]:
  "tvar x = tvar y \<longleftrightarrow> x = y"
  "tvar x \<noteq> - tvar y"
  "- tvar x \<noteq> tvar y"
unfolding Rep_tformula_simps set_eq_subset 
apply (auto)
end

end
