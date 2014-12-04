theory TemporalConditionalMode

imports Main

begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

type_synonym 'a tval = "'a list set"

inductive_set
  ta :: "'a tval set"
where
  tvar: "{ ls . distinct ls \<and> a \<in> set ls } \<in> ta" |
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
    by (fast intro: ta.tvar)
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
where "tvar a = Abs_tformula { ls . distinct ls \<and> a \<in> set ls }"

lemma Rep_tformula_tvar : "Rep_tformula (tvar a) = { ls . distinct ls \<and> a \<in> set ls }"
unfolding tvar_def using ta.tvar by (rule Abs_tformula_inverse)

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
apply (auto simp add: Rep_tformula_simps  )
apply (auto simp add: subset_eq)
apply (metis (no_types) distinct.simps(2) distinct_length_2_or_more distinct_singleton)
apply (metis List.set_insert distinct_remdups insertCI set_remdups)
proof -
  assume "\<forall>x\<in>- {ls. distinct ls \<and> x \<in> set ls}. distinct x \<and> y \<in> set x"
  assume a1: "\<forall>x\<in>- {ls. distinct ls \<and> x \<in> set ls}. distinct x \<and> y \<in> set x"
  have "\<And>b_y w. \<not> b_y (w\<Colon>'a list) \<longrightarrow> w \<in> - Collect b_y" by (metis Collect_neg_eq mem_Collect_eq)
  thus False using a1 by (metis (no_types) not_distinct_conv_prefix)
qed

(*
apply (metis List.finite_set empty_iff finite_distinct_list insertCI list.set(1) set_ConsD set_simps(2))
apply (metis List.finite_set distinct.simps(2) finite_distinct_list insertCI set_simps(2))
by (metis (mono_tags) Collect_mem_eq Collect_neg_eq Compl_iff UnCI append_Nil distinct.simps(2) double_compl empty_iff insertCI list.set(1) mem_Collect_eq set_append set_simps(2) subsetI subset_antisym uminus_set_def)
*)

lemma var_eq_tvar_simps [simp]:
  "tvar x = tvar y \<longleftrightarrow> x = y"
  "tvar x \<noteq> - tvar y"
  "- tvar x \<noteq> tvar y"
unfolding Rep_tformula_simps set_eq_subset 
sorry


lemma tformula_induct [case_names tvar compl inf, induct type: tformula]:
  fixes P :: "'a tformula \<Rightarrow> bool"
  assumes 1: "\<And>i. P (tvar i)"
  assumes 2: "\<And>x. P x \<Longrightarrow> P (- x)"
  assumes 3: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> P (x \<sqinter> y)"
  shows "P x"
proof (induct x rule: Abs_tformula_induct)
  fix y :: "'a list set"
  assume "y \<in> ta" thus "P (Abs_tformula y)"
  proof (induct rule: ta.induct)
    case (tvar i)
    have "P (tvar i)" by (rule 1)
    thus ?case unfolding tvar_def .
  next
    case (Compl S)
    from `P (Abs_tformula S)` have "P (- Abs_tformula S)" by (rule 2)
    with `S \<in> ta` show ?case
      unfolding uminus_tformula_def by (simp add: Abs_tformula_inverse)
  next
    case (inter S T)
    from `P (Abs_tformula S)` and `P (Abs_tformula T)`
    have "P (Abs_tformula S \<sqinter> Abs_tformula T)" by (rule 3)
    with `S \<in> ta` and `T \<in> ta` show ?case
      unfolding inf_tformula_def by (simp add: Abs_tformula_inverse)
  qed
qed

definition
  tformulas :: "'a set \<Rightarrow> 'a tformula set"
where
  "tformulas S =
    {x. \<forall>as bs. (\<forall>i\<in>S. i \<in> set as \<longleftrightarrow> i \<in> set bs) \<longrightarrow>
      as \<in> Rep_tformula x \<longleftrightarrow> bs \<in> Rep_tformula x}"

lemma tformulasI:
  assumes "\<And>as bs. \<forall>i\<in>S. i \<in> set as \<longleftrightarrow> i \<in> set bs
    \<Longrightarrow> as \<in> Rep_tformula x \<longleftrightarrow> bs \<in> Rep_tformula x"
  shows "x \<in> tformulas S"
using assms unfolding tformulas_def by simp

lemma tformulasD:
  assumes "x \<in> tformulas S"
  assumes "\<forall>i\<in>S. i \<in> set as \<longleftrightarrow> i \<in> set bs"
  shows "as \<in> Rep_tformula x \<longleftrightarrow> bs \<in> Rep_tformula x"
using assms unfolding tformulas_def by simp

lemma tformulas_mono: "S \<subseteq> T \<Longrightarrow> tformulas S \<subseteq> tformulas T"
by (fast intro!: tformulasI elim!: tformulasD)

lemma tformulas_insert: "x \<in> tformulas S \<Longrightarrow> x \<in> tformulas (insert a S)"
unfolding tformulas_def by simp

(* TODO: Problema! *)
(*
lemma tformulas_tvar: "i \<in> set S \<Longrightarrow> tvar i \<in> tformulas S"
unfolding tformulas_def by (simp add: Rep_tformula_simps)

lemma tformulas_tvar_iff: "tvar i \<in> tformulas S \<longleftrightarrow> i \<in> S"
unfolding tformulas_def by (simp add: Rep_tformula_simps, fast)
*)

lemma tformulas_bot: "\<bottom> \<in> tformulas S"
unfolding tformulas_def by (simp add: Rep_tformula_simps)

lemma tformulas_top: "\<top> \<in> tformulas S"
unfolding tformulas_def by (simp add: Rep_tformula_simps)

lemma tformulas_compl: "x \<in> tformulas S \<Longrightarrow> - x \<in> tformulas S"
unfolding tformulas_def by (simp add: Rep_tformula_simps)

lemma tformulas_inf:
  "x \<in> tformulas S \<Longrightarrow> y \<in> tformulas S \<Longrightarrow> x \<sqinter> y \<in> tformulas S"
unfolding tformulas_def by (auto simp add: Rep_tformula_simps)

lemma tformulas_sup:
  "x \<in> tformulas S \<Longrightarrow> y \<in> tformulas S \<Longrightarrow> x \<squnion> y \<in> tformulas S"
unfolding tformulas_def by (auto simp add: Rep_tformula_simps)

lemma tformulas_diff:
  "x \<in> tformulas S \<Longrightarrow> y \<in> tformulas S \<Longrightarrow> x - y \<in> tformulas S"
unfolding tformulas_def by (auto simp add: Rep_tformula_simps)

(* TODO: implementar ifte *)
(*
lemma tformulas_ifte:
  "a \<in> tformulas S \<Longrightarrow> x \<in> tformulas S \<Longrightarrow> y \<in> tformulas S \<Longrightarrow>
    ifte a x y \<in> tformulas S"
unfolding ifte_def
by (intro tformulas_sup tformulas_inf tformulas_compl)
*)

lemmas tformulas_intros =
  tformulas_tvar tformulas_bot tformulas_top tformulas_compl
  tformulas_inf tformulas_sup tformulas_diff tformulas_ifte

fun prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "prefix ls [] = False" |
  "prefix [] rs = True" |
  "prefix (a # ls) (b # rs) = ((a = b) \<and> prefix ls rs)"

definition tprefix :: "'a tval \<Rightarrow> 'a tval \<Rightarrow> 'a tformula"
where
  "tprefix l r \<equiv> Abs_tformula { rs | ls rs . ls \<in> l \<and> rs \<in> r \<and> (prefix ls rs) }"

datatype 'a TemporalFormula = 
  TTrue 
  | TFalse
  | TVar 'a
  | TAnd "'a TemporalFormula" "'a TemporalFormula"
  | TOr "'a TemporalFormula" "'a TemporalFormula"
  | TNot "'a TemporalFormula"
  | Before "'a TemporalFormula" "'a TemporalFormula"

primrec TF2tformula :: "'a TemporalFormula \<Rightarrow> 'a tformula"
where
  "TF2tformula TTrue = \<top>" |
  "TF2tformula TFalse = \<bottom>" |
  "TF2tformula (TVar a) = tvar a" |
  "TF2tformula (TAnd l r) = TF2tformula l \<sqinter> TF2tformula r" |
  "TF2tformula (TOr l r) = TF2tformula l \<squnion> TF2tformula r" |
  "TF2tformula (TNot f) = - TF2tformula f" |
  "TF2tformula (Before l r) = 
    tprefix (Rep_tformula (TF2tformula l)) (Rep_tformula (TF2tformula r))"

lemma "\<lbrakk> a \<noteq> b \<rbrakk> \<Longrightarrow> 
  TF2tformula (Before (TVar a) (TVar b)) = Abs_tformula { [a,b] }"
apply (auto simp add: tprefix_def Rep_tformula_simps)
done

end
