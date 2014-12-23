theory TemporalConditionalMode

imports Main Free_Boolean_Algebra 

begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

type_synonym 'a tval = "'a list set"

primrec before_op_list :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "before_op_list _ _ [] = False" |
  "before_op_list a b (x # xs) = ((a = x \<and> b \<in> set xs) \<or> (before_op_list a b xs))"

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

definition before :: "'a \<Rightarrow> 'a tformula"
where "before a = Abs_tformula { ls | ls b . distinct ls \<and> before_op_list a b ls }"

text {* @{term tformula } as a @{term boolean_algebra } *}

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
unfolding Rep_tformula_simps
apply (auto)
apply (auto simp add: subset_iff)
apply (metis distinct_remdups empty_iff in_set_member list.set(1) member_rec(1) set_remdups)
apply (metis distinct_remdups insertCI set_remdups set_simps(2))
apply (metis distinct.simps(2))
done

lemma var_eq_tvar_simps [simp]:
  "tvar x = tvar y \<longleftrightarrow> x = y"
  "tvar x \<noteq> - tvar y"
  "- tvar x \<noteq> tvar y"
unfolding Rep_tformula_simps
apply (metis (full_types) tvar_def var_le_tvar_simps(1))
apply (metis Rep_tformula_tvar tvar_def uminus_tformula_def var_le_tvar_simps(1) var_le_tvar_simps(3))
apply (metis Rep_tformula_tvar tvar_def uminus_tformula_def var_le_tvar_simps(1) var_le_tvar_simps(3))
done

(*  before: "{ ls | ls b . distinct ls \<and> before a b ls } \<in> ta" |
*)
lemma tformula_induct [case_names tvar compl inf , induct type: tformula]:
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
    {x. \<forall>as bs. (\<forall>p\<in>S.
      (distinct as \<and> p \<in> set as) \<longleftrightarrow> 
      (distinct bs \<and> p \<in> set bs)) \<longrightarrow>
      as \<in> Rep_tformula x \<longleftrightarrow> bs \<in> Rep_tformula x}"

lemma tformulasI:
  assumes "\<And>as bs. \<forall>p\<in>S.
    (distinct as \<and> p \<in> set as) \<longleftrightarrow> 
    (distinct bs \<and> p \<in> set bs)
    \<Longrightarrow> as \<in> Rep_tformula x \<longleftrightarrow> bs \<in> Rep_tformula x"
  shows "x \<in> tformulas S"
using assms unfolding tformulas_def by simp

lemma tformulasD:
  assumes "x \<in> tformulas S"
  assumes "\<forall>p\<in>S.
    (distinct as \<and> p \<in> set as) \<longleftrightarrow> 
    (distinct bs \<and> p \<in> set bs)"
  shows "as \<in> Rep_tformula x \<longleftrightarrow> bs \<in> Rep_tformula x"
using assms unfolding tformulas_def by simp

lemma tformulas_mono: "S \<subseteq> T \<Longrightarrow> tformulas S \<subseteq> tformulas T"
by (fast intro!: tformulasI elim!: tformulasD)

lemma tformulas_insert: "x \<in> tformulas S \<Longrightarrow> x \<in> tformulas (insert a S)"
unfolding tformulas_def by simp

lemma tformulas_tvar: "i \<in> S \<Longrightarrow> tvar i \<in> tformulas S"
unfolding tformulas_def 
apply (auto simp add: Rep_tformula_simps)
done

(* TODO: Problema! *)

(*lemma tformulas_before: "a \<in> S \<Longrightarrow> before a \<in> tformulas S"
unfolding tformulas_def 
apply (auto simp add: Rep_tformula_simps)
done*)

lemma tformulas_tvar_iff: "tvar i \<in> tformulas S \<longleftrightarrow> i \<in> S"
unfolding tformulas_def 
apply (auto simp add: Rep_tformula_simps)
apply (metis distinct_singleton empty_iff insert_iff list.set(1) set_simps(2))
done


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

lemma tformulas_ifte:
  "a \<in> tformulas S \<Longrightarrow> x \<in> tformulas S \<Longrightarrow> y \<in> tformulas S \<Longrightarrow>
    ifte a x y \<in> tformulas S"
unfolding ifte_def
by (intro tformulas_sup tformulas_inf tformulas_compl)

lemmas tformulas_intros =
  tformulas_tvar tformulas_bot tformulas_top tformulas_compl
  tformulas_inf tformulas_sup tformulas_diff tformulas_ifte

definition tinsert :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list set"
where
  "tinsert i ls \<equiv> { xs . distinct xs \<and> i \<in> set xs \<and> (\<forall> j \<in> set ls . j \<in> set xs)  }"

definition tdiff :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list set"
where
  "tdiff i ls \<equiv> { xs . distinct xs \<and> (\<forall> j \<in> set ls . j \<in> set xs \<and> j \<noteq> i)  }"

lemma t_ifte_inject:
  assumes "ifte (tvar i) x y = ifte (tvar i) x' y'" 
  assumes "i \<notin> S"
  assumes "x \<in> tformulas S" and "x' \<in> tformulas S"
  assumes "y \<in> tformulas S" and "y' \<in> tformulas S"
  shows "x = x' \<and> y = y'"
proof
  have 1: "\<And>ls. \<lbrakk> distinct ls \<and> i \<in> set ls \<rbrakk> \<Longrightarrow> ls \<in> Rep_tformula x \<longleftrightarrow> ls \<in> Rep_tformula x'"
    using assms(1)
    by (simp add: Rep_tformula_simps ifte_def set_eq_iff, fast)
  have 2: "\<And>ls. \<lbrakk> distinct ls \<and> i \<notin> set ls \<rbrakk> \<Longrightarrow> ls \<in> Rep_tformula y \<longleftrightarrow> ls \<in> Rep_tformula y'"
    using assms(1)
    by (simp add: Rep_tformula_simps ifte_def set_eq_iff, fast)

  show "x = x'"
  unfolding Rep_tformula_simps
  proof (rule set_eqI)
    fix ls
    have "ls \<in> Rep_tformula x \<longleftrightarrow> 
        (\<forall> xs . xs \<in> tinsert i ls \<and> xs \<in> Rep_tformula x)"
      using `x \<in> tformulas S` sorry (* by (rule formulasD, force simp add: `i \<notin> S`)*)
    also have "\<dots> \<longleftrightarrow> 
        (\<forall> xs . xs \<in> tinsert i ls \<and> xs \<in> Rep_tformula x')"
      sorry (*by (rule 1, simp)*)
    also have "\<dots> \<longleftrightarrow> ls \<in> Rep_tformula x'"
      using `x' \<in> tformulas S` sorry (*by (rule tformulasD, force simp add: `i \<notin> S`) *)
    finally show "ls \<in> Rep_tformula x \<longleftrightarrow> ls \<in> Rep_tformula x'" .
  qed
  show  "y = y'"
  unfolding Rep_tformula_simps
  proof (rule set_eqI)
    fix ls
    have "ls \<in> Rep_tformula y \<longleftrightarrow> (\<forall> xs . xs \<in> tdiff i ls \<and> xs \<in> Rep_tformula y)"
      using `y \<in> tformulas S` sorry (*by (rule tformulasD, force simp add: `i \<notin> S`)*)
    also have "\<dots> \<longleftrightarrow> (\<forall> xs . xs \<in> tdiff i ls \<and> xs \<in> Rep_tformula y')"
      sorry (*by (rule 2, simp)*)
    also have "\<dots> \<longleftrightarrow> ls \<in> Rep_tformula y'"
      using `y' \<in> tformulas S` sorry (*by (rule tformulasD, force simp add: `i \<notin> S`)*)
    finally show "ls \<in> Rep_tformula y \<longleftrightarrow> ls \<in> Rep_tformula y'" .
  qed
qed

inductive
  hom_graph_t ::
    "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> 'a set \<Rightarrow> 'a tformula \<Rightarrow> 'b \<Rightarrow> bool"
  for f :: "'a \<Rightarrow> 'b::boolean_algebra"
where
  bot: "hom_graph_t f {} bot bot"
| top: "hom_graph_t f {} top top"
| ifte: "i \<notin> S \<Longrightarrow> hom_graph_t f S x a \<Longrightarrow> hom_graph_t f S y b \<Longrightarrow>
  hom_graph_t f (insert i S) (ifte (tvar i) x y) (ifte (f i) a b)"

lemma hom_graph_t_dest:
  "hom_graph_t f S x a \<Longrightarrow> k \<in> S \<Longrightarrow> \<exists>y z b c.
    x = ifte (tvar k) y z \<and> a = ifte (f k) b c \<and>
    hom_graph_t f (S - {k}) y b \<and> hom_graph_t f (S - {k}) z c"
proof (induct set: hom_graph_t)
  case (ifte i S x a y b) show ?case
  proof (cases "i = k")
    assume "i = k" with ifte(1,2,4) show ?case by auto
  next
    assume "i \<noteq> k"
    with `k \<in> insert i S` have k: "k \<in> S" by simp
    have *: "insert i S - {k} = insert i (S - {k})"
      using `i \<noteq> k` by (simp add: insert_Diff_if)
    have **: "i \<notin> S - {k}" using `i \<notin> S` by simp
    from ifte(1) ifte(3) [OF k] ifte(5) [OF k]
    show ?case
      unfolding *
      apply clarify
      apply (simp only: ifte_ifte_distrib [of "tvar i"])
      apply (simp only: ifte_ifte_distrib [of "f i"])
      apply (fast intro: hom_graph_t.ifte [OF **])
      done
  qed
qed simp_all

lemma hom_graph_t_insert_elim:
  assumes "hom_graph_t f (insert i S) x a" and "i \<notin> S"
  obtains y z b c
  where "x = ifte (tvar i) y z"
    and "a = ifte (f i) b c"
    and "hom_graph_t f S y b"
    and "hom_graph_t f S z c"
using hom_graph_t_dest [OF assms(1) insertI1]
by (clarify, simp add: assms(2))

lemma hom_graph_t_imp_tformulas:
  "hom_graph_t f S x a \<Longrightarrow> x \<in> tformulas S"
by (induct set: hom_graph_t, simp_all add: tformulas_intros tformulas_insert)

lemma hom_graph_t_unique:
  "hom_graph_t f S x a \<Longrightarrow> hom_graph_t f S x a' \<Longrightarrow> a = a'"
proof (induct arbitrary: a' set: hom_graph_t)
  case (ifte i S y b z c a')
  from ifte(6,1) obtain y' z' b' c'
    where 1: "ifte (tvar i) y z = ifte (tvar i) y' z'"
      and 2: "a' = ifte (f i) b' c'"
      and 3: "hom_graph_t f S y' b'"
      and 4: "hom_graph_t f S z' c'"
    by (rule hom_graph_t_insert_elim)
  from 1 3 4 ifte(1,2,4) have "y = y' \<and> z = z'"
    by (intro t_ifte_inject hom_graph_t_imp_tformulas)
  with 2 3 4 ifte(3,5) show "ifte (f i) b c = a'"
    by simp
qed (erule hom_graph_t.cases, simp_all)+

lemma hom_graph_t_insert:
  assumes "hom_graph_t f S x a"
  shows "hom_graph_t f (insert i S) x a"
proof (cases "i \<in> S")
  assume "i \<in> S" with assms show ?thesis by (simp add: insert_absorb)
next
  assume "i \<notin> S"
  hence "hom_graph_t f (insert i S) (ifte (tvar i) x x) (ifte (f i) a a)"
    by (intro hom_graph_t.ifte assms)
  thus "hom_graph_t f (insert i S) x a"
    by (simp only: ifte_same)
qed

lemma hom_graph_t_finite_superset:
  assumes "hom_graph_t f S x a" and "finite T" and "S \<subseteq> T"
  shows "hom_graph_t f T x a"
proof -
  from `finite T` have "hom_graph_t f (S \<union> T) x a"
    by (induct set: finite, simp add: assms, simp add: hom_graph_t_insert)
  with `S \<subseteq> T` show "hom_graph_t f T x a"
    by (simp only: subset_Un_eq)
qed

lemma hom_graph_t_imp_finite:
  "hom_graph_t f S x a \<Longrightarrow> finite S"
by (induct set: hom_graph_t) simp_all

lemma hom_graph_t_unique':
  assumes "hom_graph_t f S x a" and "hom_graph_t f T x a'"
  shows "a = a'"
proof (rule hom_graph_t_unique)
  have fin: "finite (S \<union> T)"
    using assms by (intro finite_UnI hom_graph_t_imp_finite)
  show "hom_graph_t f (S \<union> T) x a"
    using assms(1) fin Un_upper1 by (rule hom_graph_t_finite_superset)
  show "hom_graph_t f (S \<union> T) x a'"
    using assms(2) fin Un_upper2 by (rule hom_graph_t_finite_superset)
qed

lemma hom_graph_t_tvar: "hom_graph_t f {i} (tvar i) (f i)"
proof -
  have "hom_graph_t f {i} (ifte (tvar i) top bot) (ifte (f i) top bot)"
    by (simp add: hom_graph_t.intros)
  thus "hom_graph_t f {i} (tvar i) (f i)"
    unfolding ifte_def by simp
qed

lemma hom_graph_t_compl:
  "hom_graph_t f S x a \<Longrightarrow> hom_graph_t f S (- x) (- a)"
by (induct set: hom_graph_t, simp_all add: hom_graph_t.intros compl_ifte)

lemma hom_graph_t_inf:
  "hom_graph_t f S x a \<Longrightarrow> hom_graph_t f S y b \<Longrightarrow>
   hom_graph_t f S (x \<sqinter> y) (a \<sqinter> b)"
 apply (induct arbitrary: y b set: hom_graph_t)
   apply (simp add: hom_graph_t.bot)
  apply simp
 apply (erule (1) hom_graph_t_insert_elim)
 apply (auto simp add: inf_ifte_distrib hom_graph_t.ifte)
done

lemma hom_graph_t_union_inf:
  assumes "hom_graph_t f S x a" and "hom_graph_t f T y b"
  shows "hom_graph_t f (S \<union> T) (x \<sqinter> y) (a \<sqinter> b)"
proof (rule hom_graph_t_inf)
  have fin: "finite (S \<union> T)"
    using assms by (intro finite_UnI hom_graph_t_imp_finite)
  show "hom_graph_t f (S \<union> T) x a"
    using assms(1) fin Un_upper1 by (rule hom_graph_t_finite_superset)
  show "hom_graph_t f (S \<union> T) y b"
    using assms(2) fin Un_upper2 by (rule hom_graph_t_finite_superset)
qed

lemma hom_graph_t_exists: "\<exists>a S. hom_graph_t f S x a"
by (induct x)                               
   (auto intro: hom_graph_t_tvar hom_graph_t_compl hom_graph_t_union_inf)

definition
  hom_t :: "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> 'a tformula \<Rightarrow> 'b"
where
  "hom_t f x = (THE a. \<exists>S. hom_graph_t f S x a)"

lemma hom_graph_t_hom_t: "\<exists>S. hom_graph_t f S x (hom_t f x)"
unfolding hom_t_def
apply (rule theI')
apply (rule ex_ex1I)
apply (rule hom_graph_t_exists)
apply (fast elim: hom_graph_t_unique')
done

lemma hom_t_equality:
  "hom_graph_t f S x a \<Longrightarrow> hom_t f x = a"
unfolding hom_t_def
apply (rule the_equality)
apply (erule exI)
apply (erule exE)
apply (erule (1) hom_graph_t_unique')
done

lemma hom_t_var [simp]: "hom_t f (tvar i) = f i"
by (rule hom_t_equality, rule hom_graph_t_tvar)

lemma hom_t_bot [simp]: "hom_t f \<bottom> = \<bottom>"
by (rule hom_t_equality, rule hom_graph_t.bot)

lemma hom_t_top [simp]: "hom_t f \<top> = \<top>"
by (rule hom_t_equality, rule hom_graph_t.top)

lemma hom_t_compl [simp]: "hom_t f (- x) = - hom_t f x"
proof -
  obtain S where "hom_graph_t f S x (hom_t f x)"
    using hom_graph_t_hom_t ..
  hence "hom_graph_t f S (- x) (- hom_t f x)"
    by (rule hom_graph_t_compl)
  thus "hom_t f (- x) = - hom_t f x"
    by (rule hom_t_equality)
qed

lemma hom_t_inf [simp]: "hom_t f (x \<sqinter> y) = hom_t f x \<sqinter> hom_t f y"
proof -
  obtain S where S: "hom_graph_t f S x (hom_t f x)"
    using hom_graph_t_hom_t ..
  obtain T where T: "hom_graph_t f T y (hom_t f y)"
    using hom_graph_t_hom_t ..
  have "hom_graph_t f (S \<union> T) (x \<sqinter> y) (hom_t f x \<sqinter> hom_t f y)"
    using S T by (rule hom_graph_t_union_inf)
  thus ?thesis by (rule hom_t_equality)
qed

lemma hom_t_sup [simp]: "hom_t f (x \<squnion> y) = hom_t f x \<squnion> hom_t f y"
unfolding sup_conv_inf by (simp only: hom_t_compl hom_t_inf)

lemma hom_t_diff [simp]: "hom_t f (x - y) = hom_t f x - hom_t f y"
unfolding diff_eq by (simp only: hom_t_compl hom_t_inf)

lemma hom_t_ifte [simp]:
  "hom_t f (ifte x y z) = ifte (hom_t f x) (hom_t f y) (hom_t f z)"
unfolding ifte_def by (simp only: hom_t_compl hom_t_inf hom_t_sup)

lemmas hom_t_simps =
  hom_t_var hom_t_bot hom_t_top hom_t_compl
  hom_t_inf hom_t_sup hom_t_diff hom_t_ifte

lemma hom_t_tvar_eq_id: "hom_t tvar x = x"
by (induct x) simp_all

lemma hom_t_hom_t: "hom_t f (hom_t g x) = hom_t (\<lambda>i. hom_t f (g i)) x"
by (induct x) simp_all

definition
  fmap_t :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tformula \<Rightarrow> 'b tformula"
where
  "fmap_t f = hom_t (\<lambda>i. tvar (f i))"

lemma fmap_t_tvar [simp]: "fmap_t f (tvar i) = tvar (f i)"
unfolding fmap_t_def by simp

lemma fmap_t_bot [simp]: "fmap_t f \<bottom> = \<bottom>"
unfolding fmap_t_def by simp

lemma fmap_t_top [simp]: "fmap_t f \<top> = \<top>"
unfolding fmap_t_def by simp

lemma fmap_t_compl [simp]: "fmap_t f (- x) = - fmap_t f x"
unfolding fmap_t_def by simp

lemma fmap_t_inf [simp]: "fmap_t f (x \<sqinter> y) = fmap_t f x \<sqinter> fmap_t f y"
unfolding fmap_t_def by simp

lemma fmap_t_sup [simp]: "fmap_t f (x \<squnion> y) = fmap_t f x \<squnion> fmap_t f y"
unfolding fmap_t_def by simp

lemma fmap_t_diff [simp]: "fmap_t f (x - y) = fmap_t f x - fmap_t f y"
unfolding fmap_t_def by simp

lemma fmap_t_ifte [simp]:
  "fmap_t f (ifte x y z) = ifte (fmap_t f x) (fmap_t f y) (fmap_t f z)"
unfolding fmap_t_def by simp

lemmas fmap_t_simps =
  fmap_t_tvar fmap_t_bot fmap_t_top fmap_t_compl
  fmap_t_inf fmap_t_sup fmap_t_diff fmap_t_ifte

lemma fmap_t_ident: "fmap_t (\<lambda>i. i) x = x"
by (induct x) simp_all

lemma fmap_t_fmap_t: "fmap_t f (fmap_t g x) = fmap_t (f \<circ> g) x"
by (induct x) simp_all

fun prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "prefix ls [] = False" |
  "prefix [] rs = True" |
  "prefix (a # ls) (b # rs) = ((a = b) \<and> prefix ls rs)"

definition tprefix :: "'a tformula \<Rightarrow> 'a tformula \<Rightarrow> 'a tformula"
where
  "tprefix L R \<equiv> Abs_tformula 
    { rs | ls rs . ls \<in> Rep_tformula L \<and> rs \<in> Rep_tformula R \<and> (prefix ls rs) }"

lemma "hom_t s (tvar A) \<or> hom_t s (- tvar A)"
apply (auto)
done

lemma "hom_t s (tprefix (tvar A) (tvar B)) \<or> hom_t s (- tprefix (tvar A) (tvar B))"
apply (auto)
done

lemma before_and: 
  "hom_t s (tprefix (tvar A) (tvar B)) \<or> hom_t s (tprefix (tvar B) (tvar A)) = 
  hom_t s (tvar A \<sqinter> tvar B)"
apply (auto)
done

lemma and_neg: "hom_t s (tvar A \<sqinter> tvar B) \<or> hom_t s (- tvar A) \<or> hom_t s (- tvar B)"
apply (auto)
done

lemma "hom_t s (tprefix (tvar A) (tvar B)) \<or> hom_t s (tprefix (tvar B) (tvar A)) \<or>
  hom_t s (- tvar A) \<or> hom_t s (- tvar B) "
apply (metis and_neg before_and)
done

datatype 'a TemporalFormula = 
  TTrue ("True")
  | TFalse ("False")
  | TVar 'a ("[_]")
  | TAnd "'a TemporalFormula" "'a TemporalFormula" (infixr "T\<and>" 40)
  | TOr "'a TemporalFormula" "'a TemporalFormula" (infixr "T\<or>" 50)
  | TNot "'a TemporalFormula" ("T\<not> _" 40)
  | Before "'a TemporalFormula" "'a TemporalFormula" (infixr "T<" 40)

primrec TF2tformula :: "'a TemporalFormula \<Rightarrow> 'a tformula"
where
  "TF2tformula TTrue = \<top>" |
  "TF2tformula TFalse = \<bottom>" |
  "TF2tformula (TVar a) = tvar a" |
  "TF2tformula (TAnd l r) = TF2tformula l \<sqinter> TF2tformula r" |
  "TF2tformula (TOr l r) = TF2tformula l \<squnion> TF2tformula r" |
  "TF2tformula (TNot f) = - TF2tformula f" |
  "TF2tformula (Before l r) = 
    tprefix (TF2tformula l) (TF2tformula r)"

lemma "\<lbrakk> a \<noteq> b \<rbrakk> \<Longrightarrow> 
  TF2tformula (Before (TVar a) (TVar b)) = Abs_tformula { [a,b] }"
apply (auto simp add: tprefix_def Rep_tformula_simps)
sorry

lemma "TF2tformula (T\<not> ((TVar a) T< (TVar a))) = \<top>"
sorry


end
