theory Temporal_Faults_Algebra_syntax

imports Temporal_Faults_Algebra_dlist

begin
subsection {* Syntax for the Algebra of Temporal Faults *}

inductive_set 
  formulas :: "'a set \<Rightarrow> 'a formula set"
  for G :: "'a set"
where
  step[intro!]: "\<forall> dl \<in> Rep_formula f. Dlist.set dl \<subseteq> G \<Longrightarrow> f \<in> formulas G"

lemma dlist_empty_in_formulas: "Abs_formula { Dlist.empty } \<in> formulas G"
apply (rule formulas.intros)
by (simp add: Abs_formula_inverse set.rep_eq)

lemma basic_cases_in_formulas: 
  "{ Abs_formula {}, Abs_formula  { Dlist.empty } } \<subseteq> formulas G"
by (simp add: Abs_formula_inverse dlist_empty_in_formulas formulas.intros)

lemma formula_formulas_UNIV: "f \<in> formulas UNIV"
by blast

datatype 'a formula_exp =
  tFalse | 
  tTrue |
  tNeutral |
  tVar 'a |
  tOR "'a formula_exp" "'a formula_exp" | 
  tAND "'a formula_exp" "'a formula_exp" |
  tNOT "'a formula_exp" | 
  tXB "'a formula_exp" "'a formula_exp"

typedef 'a formula_syn = "UNIV::'a formula_exp set" by simp

inductive_set formulas_exp :: "'a set \<Rightarrow> 'a formula_exp set" 
  for G :: "'a set"
where
  "tFalse \<in> formulas_exp G" |
  "tTrue \<in> formulas_exp G" |
  "tNeutral \<in> formulas_exp G" |
  "g \<in> G \<Longrightarrow> (tVar g) \<in> formulas_exp G" |
  "X \<in> formulas_exp G \<Longrightarrow> Y \<in> formulas_exp G \<Longrightarrow> tOR X Y \<in> formulas_exp G" |
  "X \<in> formulas_exp G \<Longrightarrow> Y \<in> formulas_exp G \<Longrightarrow> tAND X Y \<in> formulas_exp G" |
  "X \<in> formulas_exp G \<Longrightarrow> Y \<in> formulas_exp G \<Longrightarrow> tXB X Y \<in> formulas_exp G" |
  "X \<in> formulas_exp G \<Longrightarrow> tNOT X \<in> formulas_exp G"

definition remainder_complements :: "'a set \<Rightarrow> 'a formula_exp \<Rightarrow> 'a formula_exp" where
  "remainder_complements G base = 
    (Finite_Set.fold (\<lambda> x f\<^sub>2 . tAND (tNOT (tVar x)) f\<^sub>2) base G)"

fun tXB_of_list :: "'a list \<Rightarrow> 'a formula_exp" where
  "tXB_of_list [] = tNeutral" |
  "tXB_of_list [a] = tVar a" |
  "tXB_of_list (a # as) = tXB (tVar a) (tXB_of_list as)"

fun mk_minterm :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a formula_exp" where
  "mk_minterm [] G = tNeutral" |
  "mk_minterm as G = remainder_complements (G - set as) (tXB_of_list as)"

lemma unary_mk_minterm[simp]: "mk_minterm [g] {g} = tVar g"
by (simp add: "mk_minterm.cases" remainder_complements_def )

inductive normal_formula_exp :: "'a set \<Rightarrow> 'a formula_exp \<Rightarrow> bool"
  for G :: "'a set"
where
  "normal_formula_exp G tFalse" |
  "normal_formula_exp G tTrue" |
  [intro!]: "Dlist.set as \<subseteq> G \<Longrightarrow> 
    normal_formula_exp G (mk_minterm (list_of_dlist as) G)" |
  [intro!]: "normal_formula_exp G X \<Longrightarrow> normal_formula_exp G Y \<Longrightarrow>
    normal_formula_exp G (tOR X Y)"

lemma tNeutral_is_normal[simp]: "normal_formula_exp G tNeutral"
by (metis empty_subsetI list.set(1) mk_minterm.simps(1) normal_formula_exp.intros(3) set.rep_eq slice_right_zero_eq_empty)

lemma unary_tVar_is_normal: "normal_formula_exp {g} (tVar g)"
by (metis List.set_insert empty_set insert_Nil insert_absorb2 list_of_dlist_Dlist list_of_dlist_insert normal_formula_exp.simps remdups.simps(1) set.rep_eq subset_insertI unary_mk_minterm)

primrec 
    formula_exp_to_formula :: "'a formula_exp \<Rightarrow> 'a formula"
    where
  "formula_exp_to_formula tFalse = bot" | 
  "formula_exp_to_formula tNeutral = Abs_formula { Dlist [] }" |
  "formula_exp_to_formula tTrue = top" |
  "formula_exp_to_formula (tVar x) = Abs_formula { dl. Dlist.member dl x }" |
  "formula_exp_to_formula (tOR a b) = sup (formula_exp_to_formula a) (formula_exp_to_formula b)" |
  "formula_exp_to_formula (tAND a b) = inf (formula_exp_to_formula a) (formula_exp_to_formula b)" |
  "formula_exp_to_formula (tNOT a) = (- formula_exp_to_formula a)" |
  "formula_exp_to_formula (tXB a b) = (xbefore (formula_exp_to_formula a) (formula_exp_to_formula b))"
(* TODO rever a forma normal
fun formula_exp_to_NF :: "'a formula_exp \<Rightarrow> 'a formula_exp" where
  "formula_exp_to_NF f = f"
*)

lemma top_formula_not_less_eq_bot_formula: "\<not> ((top::'a formula) \<le> bot)"
by (metis Rep_formula_bot Rep_formula_top empty_not_UNIV top.extremum_unique)

lemma neutral_formula_not_less_eq_bot_formula: "\<not> ((neutral::'a formula) \<le> bot)"
unfolding neutral_formula_def
by (metis Abs_formula_inverse Rep_formula_bot UNIV_I bot.extremum_unique insert_not_empty)

abbreviation eval where "eval \<equiv> formula_exp_to_formula"

abbreviation empty_list_formula_exp :: "'a set \<Rightarrow> 'a formula_exp" where
  "empty_list_formula_exp V \<equiv> tNOT (Finite_Set.fold (\<lambda> x f\<^sub>2 . tOR (tVar x) f\<^sub>2) tFalse V)"

abbreviation dlist_to_formula_exp  where
  "dlist_to_formula_exp dl G \<equiv> mk_minterm (list_of_dlist dl) G"

fun dlist_set_to_formula_exp_rm_false :: 
  "'a set \<Rightarrow> 'a dlist \<Rightarrow> 'a formula_exp \<Rightarrow> 'a formula_exp" where
"dlist_set_to_formula_exp_rm_false G dl tFalse = dlist_to_formula_exp dl G" |
"dlist_set_to_formula_exp_rm_false G dl f\<^sub>2 = tOR (dlist_to_formula_exp dl G) f\<^sub>2"

abbreviation dlist_set_to_formula_exp where
  "dlist_set_to_formula_exp Dls G \<equiv> 
    Finite_Set.fold (dlist_set_to_formula_exp_rm_false G) tFalse Dls"

abbreviation formula_to_formula_exp where
  "formula_to_formula_exp f \<equiv> dlist_set_to_formula_exp (Rep_formula f)"

lemma formula_to_formula_exp_bot: 
  "eval (formula_to_formula_exp bot G) = bot"
by simp

abbreviation reduce :: "'a formula_exp \<Rightarrow> 'a set \<Rightarrow> 'a formula_exp" where
  "reduce \<equiv> formula_to_formula_exp \<circ> eval"

lemma reduce_tFalse[simp]: "reduce tFalse G = tFalse"
by simp

lemma normal_tFalse[simp]: "normal_formula_exp G tFalse" 
by (simp add: normal_formula_exp.intros(1))



lemma "f \<in> formulas_exp G \<Longrightarrow> normal_formula_exp G (reduce f G)"
apply (induct f, simp+)


(*<*)
notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)
(*>*)

instantiation formula_syn :: (type) boolean_algebra
begin

definition
  "x \<sqinter> y = Abs_formula_syn (tAND (Rep_formula_syn x) (Rep_formula_syn y))"

definition
  "x \<squnion> y = Abs_formula_syn (tOR (Rep_formula_syn x) (Rep_formula_syn y))"

definition
  "\<top> = Abs_formula_syn tTrue"

definition
  "\<bottom> = Abs_formula_syn tFalse"

definition
  "x \<le> y \<longleftrightarrow> (eval (Rep_formula_syn x)) \<le> (eval (Rep_formula_syn y))"

definition
  "x < y \<longleftrightarrow> (eval (Rep_formula_syn x)) < (eval (Rep_formula_syn y))"

definition
  "- x = Abs_formula_syn (tNOT (Rep_formula_syn x))"

definition
  "x - y = Abs_formula_syn (tAND (Rep_formula_syn x)  (tNOT (Rep_formula_syn y)))"

lemma Rep_formula_syn_inf:
  "Rep_formula_syn (x \<sqinter> y) = tAND (Rep_formula_syn x) (Rep_formula_syn y)"
unfolding inf_formula_syn_def
by (simp add: Abs_formula_syn_inverse)

lemma Rep_formula_syn_sup:
  "Rep_formula_syn (x \<squnion> y) = tOR (Rep_formula_syn x) (Rep_formula_syn y)"
unfolding sup_formula_syn_def
by (simp add: Abs_formula_syn_inverse)

lemma Rep_formula_syn_top[simp]: "Rep_formula_syn \<top> = tTrue"
unfolding top_formula_syn_def
by (simp add: Abs_formula_syn_inverse)

lemma Rep_formula_syn_bot[simp]: "Rep_formula_syn \<bottom> = tFalse"
unfolding bot_formula_syn_def 
by (simp add: Abs_formula_syn_inverse)

lemma Rep_formula_syn_compl: 
  "Rep_formula_syn (- x) = tNOT (Rep_formula_syn x)"
unfolding uminus_formula_syn_def
by (simp add: Abs_formula_syn_inverse Rep_formula_syn)

lemma Rep_formula_syn_diff:
  "Rep_formula_syn (x - y) = tAND (Rep_formula_syn x) (tNOT (Rep_formula_syn y))"
unfolding minus_formula_syn_def
by (simp add: Abs_formula_syn_inverse)

lemma Rep_formula_syn_eq:
  "x = y \<longleftrightarrow> (Rep_formula_syn x) = (Rep_formula_syn y)"
by (metis Rep_formula_syn_inverse)

lemmas eq_formula_syn_iff = Rep_formula_syn_inject [symmetric]

lemmas Rep_formula_syn_boolean_algebra_simps =
  less_eq_formula_syn_def less_formula_syn_def eq_formula_syn_iff
  Rep_formula_syn_sup Rep_formula_syn_inf Rep_formula_syn_top 
  Rep_formula_syn_bot Rep_formula_syn_compl Rep_formula_syn_diff 
  Rep_formula_syn_eq
  
instance proof
fix x y::"'a formula_syn"
show "(x < y) = (x \<le> y \<and> \<not> (y \<le> x))"
using less_eq_formula_syn_def less_formula_syn_def by auto
next
fix x::"'a formula_syn"
show "x \<le> x"
by (simp add: less_eq_formula_syn_def)
next
fix x y z:: "'a formula_syn"
assume "x \<le> y" "y \<le> z"
thus "x \<le> z"
using less_eq_formula_syn_def by auto
next
fix x::"'a formula_syn" and y::"'a formula_syn"
assume "x \<le> y" "y \<le> x"
thus "x = y"
unfolding less_eq_formula_syn_def eq_iff
apply simp
apply (simp add: iffE)





qed (unfold Rep_formula_syn_boolean_algebra_simps, auto)
end


(*<*)
no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)
(*>*)

(* TODO From a set of formulas to a formula syntactic 'a formula \<Rightarrow> 'a formula_exp \<Longrightarrow> 
  resolver com inductive? *) 
(*
inductive_set
  formula_syn :: "'a set \<Rightarrow> 'a formula_exp set"
  for "V"
where 
  "tFalse \<in> formula_syn V" |
  "tTrue \<in> formula_syn V" |
  "tNeutral \<in> formula_syn V" |
  "a \<in> V \<Longrightarrow> tVar a \<in> formula_syn V" |
  "f \<in> formula_syn V \<Longrightarrow> tNOT f \<in> formula_syn V" |
  "\<lbrakk> f\<^sub>1 \<in> formula_syn V; f\<^sub>2 \<in> formula_syn V \<rbrakk> \<Longrightarrow> tOR f\<^sub>1 f\<^sub>2 \<in> formula_syn V" |
  "\<lbrakk> f\<^sub>1 \<in> formula_syn V; f\<^sub>2 \<in> formula_syn V \<rbrakk> \<Longrightarrow> tAND f\<^sub>1 f\<^sub>2 \<in> formula_syn V" |
  "\<lbrakk> f\<^sub>1 \<in> formula_syn V; f\<^sub>2 \<in> formula_syn V \<rbrakk> \<Longrightarrow> tDIFF f\<^sub>1 f\<^sub>2 \<in> formula_syn V" |
  "\<lbrakk> f\<^sub>1 \<in> formula_syn V; f\<^sub>2 \<in> formula_syn V \<rbrakk> \<Longrightarrow> tXB f\<^sub>1 f\<^sub>2 \<in> formula_syn V" 
*)
subsection {* Tautology check *}

definition tautology :: "'a formula_exp \<Rightarrow> bool" where
  "tautology fexp = (eval(fexp) = top)"

subsubsection {* Algebra eval laws *}

lemma eval_tempo_tVar: 
  "tempo1 (eval (tVar a))"
  "tempo2 (eval (tVar a))"
  "tempo3 (eval (tVar a))"
  "tempo4 (eval (tVar a))"
by (auto simp add: tempo1_formula_def tempo2_formula_def tempo3_formula_def
  tempo4_formula_def Abs_formula_inverse dlist_tempo1_member dlist_tempo2_member
  dlist_tempo3_member dlist_tempo4_member)

lemma eval_xbefore_bot_step:
  "xbefore (eval tFalse) (eval (tVar a)) = bot"
  "xbefore (eval (tVar a)) (eval tFalse) = bot"
by (auto simp add: xbefore_formula_def Abs_formula_inverse dlist_xbefore_def 
  bot_formula_def)

corollary eval_xbefore_bot:
  "eval (tXB tFalse (tVar a)) = bot"
  "eval (tXB (tVar a) tFalse) = bot"
using eval_xbefore_bot_step by force+

lemma eval_xbefore_neutral_step:
  "xbefore (eval tNeutral) (eval (tVar a)) = Abs_formula {dl. Dlist.member dl a}"
  "xbefore (eval (tVar a)) (eval tNeutral) = Abs_formula {dl. Dlist.member dl a}"
proof-
  have "tempo1 (eval (tVar a))" using eval_tempo_tVar by simp
  thus "xbefore (eval tNeutral) (eval (tVar a)) = 
    Abs_formula {dl. Dlist.member dl a}" 
    "xbefore (eval (tVar a)) (eval tNeutral) = 
      Abs_formula {dl. Dlist.member dl a}"
    by (auto simp add: xbefore_formula_def Abs_formula_inverse 
      neutral_formula_def tempo1_formula_def dlistset_xbefore_neutral_1 
      dlistset_xbefore_neutral_2)
qed

corollary eval_xbefore_neutral:
  "eval (tXB tNeutral (tVar a)) = Abs_formula {dl. Dlist.member dl a}"
  "eval (tXB (tVar a) tNeutral) = Abs_formula {dl. Dlist.member dl a}"
using eval_xbefore_neutral_step by fastforce+

lemma eval_xbefore_not_idempotent_step:
  "xbefore (eval (tVar a)) (eval (tVar a)) = bot"
proof-
  have "tempo1 (eval (tVar a))" using eval_tempo_tVar by simp
  thus ?thesis by (simp add: xbefore_not_idempotent) 
qed

corollary eval_xbefore_not_idempotent:
  "eval (tXB (tVar a) (tVar a)) = bot"
using eval_xbefore_not_idempotent_step by simp

lemma eval_inf_tempo1_step: 
  "tempo1 (inf (eval (tVar a)) (eval (tVar b)))"
proof-
  have "tempo1 (eval (tVar a))" "tempo1 (eval (tVar b))" 
    using eval_tempo_tVar by auto
  thus ?thesis using inf_tempo1 by simp
qed

corollary eval_inf_tempo1:
  "tempo1 (eval (tAND (tVar a) (tVar b)))"
using eval_inf_tempo1_step by simp

lemma eval_xbefore_not_sym_step:
  "xbefore (eval (tVar a)) (eval (tVar b)) \<le> 
    - (xbefore (eval (tVar b)) (eval (tVar a)))"
proof-
  have "tempo1 (eval (tVar a))" "tempo1 (eval (tVar b))" 
    using eval_tempo_tVar by auto
  thus ?thesis using xbefore_not_sym by simp
qed

corollary eval_xbefore_not_sym:
  "eval (tXB (tVar a) (tVar b)) \<le> - eval (tXB (tVar b) (tVar a))"
using eval_xbefore_not_sym_step by simp

lemma eval_xbefore_assoc_step:
  "xbefore (xbefore (eval (tVar a)) (eval (tVar b))) (eval (tVar c)) = 
    xbefore (eval (tVar a)) (xbefore (eval (tVar b)) (eval (tVar c)))"
proof-
  have "tempo1 (eval (tVar a))" "tempo1 (eval (tVar b))" "tempo1 (eval (tVar c))" 
    using eval_tempo_tVar by auto
  thus ?thesis using xbefore_assoc by simp
qed

corollary eval_xbefore_assoc:
  "eval (tXB (tXB (tVar a) (tVar b)) (tVar c)) = 
  eval (tXB (tVar a) (tXB (tVar b) (tVar c)))"
using eval_xbefore_assoc_step by simp

lemma eval_independent_events_step: 
  "a \<noteq> b \<Longrightarrow> independent_events (eval (tVar a)) (eval (tVar b))"
by (auto simp add: independent_events_formula_def Abs_formula_inverse
  dlist_indepentent_events_member)

lemma eval_xbefore_inf_equiv_bot_step: 
  "inf 
    (xbefore (eval (tVar a)) (eval (tVar b))) 
    (xbefore (eval (tVar b)) (eval (tVar a))) = bot"
proof-
  have "tempo1 (eval (tVar a))" "tempo1 (eval (tVar b))" 
    using eval_tempo_tVar by auto
  thus ?thesis using xbefore_inf_equiv_bot by simp
qed

corollary eval_xbefore_inf_equiv_bot:
  "eval (tAND (tXB (tVar a) (tVar b)) (tXB (tVar b) (tVar a))) = bot"
using eval_xbefore_inf_equiv_bot_step by simp

lemma eval_xbefore_sup_equiv_inf_step: "a \<noteq> b \<Longrightarrow> sup 
  (xbefore (eval (tVar a)) (eval (tVar b))) 
  (xbefore (eval (tVar b)) (eval (tVar a))) = 
  inf (eval (tVar a)) (eval (tVar b))"
proof-
  assume "a \<noteq> b"
  hence "tempo1 (eval (tVar a))" "tempo2 (eval (tVar a))"
    "tempo3 (eval (tVar a))" "tempo4 (eval (tVar a))"
    "tempo1 (eval (tVar b))" "tempo2 (eval (tVar b))"
    "tempo3 (eval (tVar b))" "tempo4 (eval (tVar b))"
    "independent_events (eval (tVar a)) (eval (tVar b))"
    using eval_tempo_tVar eval_independent_events_step by fastforce+
  thus ?thesis by (simp add: xbefore_sup_equiv_inf)
qed

corollary eval_xbefore_sup_equiv_inf: "a \<noteq> b \<Longrightarrow> 
  eval (tOR (tXB (tVar a) (tVar b)) (tXB (tVar b) (tVar a))) = 
  eval (tAND (tVar a) (tVar b))"
using eval_xbefore_sup_equiv_inf_step by simp

lemma eval_xbefore_trans_step:
  "less_eq 
    (inf 
      (xbefore (eval (tVar a)) (eval (tVar b))) 
      (xbefore (eval (tVar b)) (eval (tVar c)))) 
    (xbefore (eval (tVar a)) (eval (tVar c)))"
proof-
  have "tempo1 (eval (tVar a))" "tempo1 (eval (tVar b))" "tempo1 (eval (tVar c))" 
    "tempo2 (eval (tVar a))" "tempo2 (eval (tVar b))" "tempo2 (eval (tVar c))" 
    using eval_tempo_tVar by auto
  thus ?thesis using xbefore_trans by simp
qed

corollary eval_xbefore_trans:
  "less_eq (eval (tAND (tXB (tVar a) (tVar b)) (tXB (tVar b) (tVar c))))
  (eval (tXB (tVar a) (tVar c)))"
using eval_xbefore_trans_step by simp

lemma eval_xbefore_sup_step:
  "xbefore (sup (eval (tVar a)) (eval (tVar b))) (eval (tVar c)) = 
    sup 
      (xbefore (eval (tVar a)) (eval (tVar c))) 
      (xbefore (eval (tVar b)) (eval (tVar c)))"
  "xbefore (eval (tVar a)) (sup (eval (tVar b)) (eval (tVar c))) = 
    sup 
      (xbefore (eval (tVar a)) (eval (tVar b))) 
      (xbefore (eval (tVar a)) (eval (tVar c)))"
by (simp add: xbefore_sup_1 xbefore_sup_2)+

corollary eval_xbefore_sup:
  "eval (tXB (tOR (tVar a) (tVar b)) (tVar c)) = 
    eval (tOR (tXB (tVar a) (tVar c)) (tXB (tVar b) (tVar c)))"
  "eval (tXB (tVar a) (tOR (tVar b) (tVar c))) = 
    eval (tOR (tXB (tVar a) (tVar b)) (tXB (tVar a) (tVar c)))"
by (simp add: xbefore_sup_1 xbefore_sup_2)+


lemma eval_not_xbefore_step:
  "a \<noteq> b \<Longrightarrow> - (xbefore (eval (tVar a)) (eval (tVar b))) = 
    sup 
      (sup (- (eval (tVar a))) (- (eval (tVar b)))) 
      (xbefore (eval (tVar b)) (eval (tVar a)))"
proof-
  assume "a \<noteq> b"
  hence "tempo1 (eval (tVar a))" "tempo1 (eval (tVar b))" 
    "tempo2 (eval (tVar a))" "tempo2 (eval (tVar b))" 
    "tempo3 (eval (tVar a))" "tempo3 (eval (tVar b))" 
    "tempo4 (eval (tVar a))" "tempo4 (eval (tVar b))" 
    "independent_events (eval (tVar a)) (eval (tVar b))"
    using eval_tempo_tVar eval_independent_events_step by fastforce+
  thus ?thesis using not_xbefore by simp
qed

corollary eval_not_xbefore: "a \<noteq> b \<Longrightarrow> 
  eval (tNOT (tXB (tVar a) (tVar b))) =
  eval (
    tOR 
      (tOR (tNOT (tVar a)) (tNOT (tVar b))) 
      (tXB (tVar b) (tVar a)))"
using eval_not_xbefore_step by simp

lemma eval_inf_xbefore_equiv_sups_xbefore_step: 
  "inf (eval (tVar a)) (xbefore (eval (tVar b)) (eval (tVar c))) = 
  sup 
    (xbefore (inf (eval (tVar a)) (eval (tVar b))) (eval (tVar c))) 
    (xbefore (eval (tVar b)) (inf (eval (tVar a)) (eval (tVar c))))"
proof-
  have "tempo2 (eval (tVar a))" using eval_tempo_tVar by simp
  thus ?thesis using inf_xbefore_equiv_sups_xbefore by simp
qed

corollary eval_inf_xbefore_equiv_sups_xbefore:
  "eval (tAND (tVar a) (tXB (tVar b) (tVar c))) =
  eval (tOR 
    (tXB (tAND (tVar a) (tVar b)) (tVar c)) 
    (tXB (tVar b) (tAND (tVar a) (tVar c))))"
using eval_inf_xbefore_equiv_sups_xbefore_step by simp

datatype MyVars = MyVarA | MyVarB

subsection {* Soundness and completeness on the syntactical constructors *}

primrec inc_nat_option :: "nat option \<Rightarrow> nat option" where
  "inc_nat_option None = None" |
  "inc_nat_option (Some i) = Some (Suc i)"

primrec list_index_of_aux :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat option" where
  "list_index_of_aux [] _ n = None" |
  "list_index_of_aux (x#xs) a n = 
    (if x = a then Some 0 else inc_nat_option (list_index_of_aux xs a (n-1)))"

definition list_index_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "list_index_of l a = list_index_of_aux l a (List.length l)"

definition dlist_index_of :: "'a dlist \<Rightarrow> 'a \<Rightarrow> nat option" where
  "dlist_index_of dl a = list_index_of_aux (list_of_dlist dl) a (Dlist.length dl)"

(*
lemma index_of_aux_member1: 
  "index_of_aux l v 0 \<noteq> None \<Longrightarrow> List.member l v"
unfolding index_of_def List.member_def 
apply (induct l, auto)
*)

lemma dlist_index_of_empty[simp]: "dlist_index_of Dlist.empty v = None"
by (simp add: dlist_index_of_def)

lemma dlist_index_of_insert_new[simp]: 
  "\<not> Dlist.member dl v \<Longrightarrow> dlist_index_of (Dlist.insert v dl) v = Some 0"
by (simp add: Dlist.member_def dlist_index_of_def member_def)

lemma dlist_index_of_insert: "\<not> Dlist.member dl x \<Longrightarrow> 
  dlist_index_of (Dlist.insert x dl) v = 
  (if x = v then Some 0 else inc_nat_option (dlist_index_of dl v))"
proof(cases "x = v")
  case True
  assume "\<not> Dlist.member dl x" "x = v"
  thus ?thesis by simp
  next
  assume "\<not> Dlist.member dl x" "x \<noteq> v"
  thus ?thesis
    by (simp add: Dlist.length_def Dlist.member_def dlist_index_of_def in_set_member) 
qed

lemma dlist_index_of_insert_existing:
  "\<lbrakk> \<not> Dlist.member dl x; Dlist.member dl v; dlist_index_of dl v \<noteq> None \<rbrakk> \<Longrightarrow> 
  dlist_index_of (Dlist.insert x dl) v \<noteq> None"
by (auto simp add: dlist_index_of_insert)

lemma dlist_index_of_member: "dlist_index_of dl v \<noteq> None \<Longrightarrow> Dlist.member dl v"
apply (induct dl, simp)
by (metis Dlist.member_def dlist_index_of_insert inc_nat_option.simps(1) 
  list_of_dlist_insert member_def member_rec(1) not_in_set_insert)

lemma dlist_index_of_member_iff: "dlist_index_of dl v \<noteq> None \<longleftrightarrow> Dlist.member dl v"
apply (rule iffI, simp add: dlist_index_of_member)
apply (induct dl, simp add: dlist_index_of_def)
by (metis Dlist.member_def dlist_index_of_insert dlist_index_of_insert_existing 
  in_set_member insert_code(1) insert_iff list_of_dlist_insert option.simps(3))


lemma dlist_index_of_slice_right: 
  "dlist_index_of dl v \<noteq> None \<Longrightarrow> (\<exists>i. Dlist.member (dl\<dagger>..i) v)"
apply (induct dl, simp)
by (metis dlist_index_of_member slice_none slice_right_def)

lemma dlist_index_of_slice_right_iff: 
  "dlist_index_of dl v \<noteq> None \<longleftrightarrow> (\<exists>i. Dlist.member (dl\<dagger>..i) v)"
proof (rule iffI)
  next
  assume "dlist_index_of dl v \<noteq> None"
  thus "\<exists>i. Dlist.member (dl\<dagger>..i) v" by (simp add: dlist_index_of_slice_right)
  next
  assume "\<exists>i. Dlist.member (dl\<dagger>..i) v"
  hence "Dlist.member dl v" by (simp add: dlist_member_slice_right_member_dlist)
  thus "dlist_index_of dl v \<noteq> None" by (meson dlist_index_of_member_iff) 
qed

lemma dlist_index_of_slice_left:
  "dlist_index_of dl v \<noteq> None \<Longrightarrow> (\<exists>i. Dlist.member (dl\<dagger>i..) v)"
apply (induct dl, simp)
by (metis dlist_index_of_member slice_none slice_left_def)

lemma dlist_index_of_slice_left_iff: 
  "dlist_index_of dl v \<noteq> None \<longleftrightarrow> (\<exists>i. Dlist.member (dl\<dagger>i..) v)"
proof (rule iffI)
  next
  assume "dlist_index_of dl v \<noteq> None"
  thus "\<exists>i. Dlist.member (dl\<dagger>i..) v" by (simp add: dlist_index_of_slice_left)
  next
  assume "\<exists>i. Dlist.member (dl\<dagger>i..) v"
  hence "Dlist.member dl v" by (simp add: dlist_member_slice_left_member_dlist)
  thus "dlist_index_of dl v \<noteq> None" by (meson dlist_index_of_member_iff) 
qed

corollary dlist_index_of_slice:
  "dlist_index_of dl v \<noteq> None \<Longrightarrow> (\<exists>i. Dlist.member (dl\<dagger>..i) v \<or> Dlist.member (dl\<dagger>i..) v)"
by (meson dlist_index_of_slice_right)

corollary dlist_index_of_slice_iff: 
  "dlist_index_of dl v \<noteq> None \<longleftrightarrow> (\<exists>i. Dlist.member (dl\<dagger>..i) v \<or> Dlist.member (dl\<dagger>i..) v)"
by (meson dlist_index_of_slice_left_iff dlist_index_of_slice_right_iff)

lemma dlist_index_of_not_member_slice: 
  "\<not> Dlist.member dl v \<Longrightarrow> dlist_index_of dl v = dlist_index_of (dl\<dagger>i..j) v"
by (metis dlist_index_of_member dlist_member_slice_member_dlist)

corollary dlist_index_of_not_member_slice_right: 
  "\<not> Dlist.member dl v \<Longrightarrow> dlist_index_of dl v = dlist_index_of (dl\<dagger>..j) v"
unfolding slice_right_def
by (simp add: dlist_index_of_not_member_slice)

corollary dlist_index_of_not_member_slice_left: 
  "\<not> Dlist.member dl v \<Longrightarrow> dlist_index_of dl v = dlist_index_of (dl\<dagger>i..) v"
unfolding slice_left_def
by (simp add: dlist_index_of_not_member_slice)

lemma dlist_index_of_length: 
  "Dlist.member dl v \<Longrightarrow> the (dlist_index_of dl v) < Dlist.length dl"
apply (induct dl, simp)
by (smt Dlist.length_def Dlist.member_def Suc_lessI add_eq_self_zero 
  dlist_index_of_insert dlist_index_of_member_iff inc_nat_option.simps(1) 
  inc_nat_option.simps(2) le_add1 length_greater_0_conv lessI less_trans 
  list.size(4) list_of_dlist_insert member_def not_in_set_insert not_less 
  not_less_iff_gr_or_eq option.collapse option.inject)
(*
lemma dlist_index_length_iff: 
  "Dlist.member dl v \<longleftrightarrow> the (dlist_index_of dl v) < Dlist.length dl"
apply (rule iffI, simp add: dlist_index_of_length)
*)

lemma dlist_index_of_dlist_nth:
  "dlist_index_of dl v = Some i \<Longrightarrow> dlist_nth dl i = v"
apply (induct dl, simp)
apply (simp add: dlist_index_of_insert)
sorry

lemma dlist_index_of_sliceable_nth:
  "dlist_index_of dl v = Some i \<Longrightarrow> Dlist.member (sliceable_nth dl i) v"
apply (induct dl, simp)
apply (simp add: dlist_index_of_insert)
sorry

lemma dlist_index_of_slice_right_equiv: 
  "Dlist.member (dl\<dagger>..i) v \<Longrightarrow> 
  dlist_index_of (dl\<dagger>..i) v = dlist_index_of dl v"
sorry

lemma dlist_index_of_slice_left_equiv: 
  "Dlist.member (dl\<dagger>i..) v \<Longrightarrow> 
  i + the (dlist_index_of (dl\<dagger>i..) v) = the (dlist_index_of dl v)"
sorry

(*
lemma slice_right_member_index_of: 
  "Dlist.member (dl\<dagger>..i) v \<longleftrightarrow> 
    (case (index_of (list_of_dlist dl) v) of None \<Rightarrow> False | Some x \<Rightarrow> x < i)"
apply (induct dl, simp add: slice_right_def slice_dlist_def Dlist.member_def 
  List.member_def)
sorry
*)

(*
lemma slice_left_member_index_of:
  "\<exists>i. v \<in> Dlist.set (dl\<dagger>i..) \<longleftrightarrow> index_of (list_of_dlist dl) v \<ge> i \<and> i < Dlist.length dl"
apply (induct dl, 
  simp add: index_of_def Dlist.length_def Dlist.member_def Dlist.empty_def slice_left_def 
  slice_dlist_def List.member_def Dlist.set_def)
by (metis Dlist.length_def cancel_comm_monoid_add_class.diff_cancel empty_iff empty_set 
  linorder_not_less list_of_dlist_Dlist list_of_dlist_simps(3) list_of_dlist_simps(4) 
  max_0L order_refl set.rep_eq set_remdups slice_left_def take_0)


lemma dlist_index_of_member: 
  "index_of (list_of_dlist dl) v < Dlist.length dl \<longleftrightarrow> Dlist.member dl v"
unfolding index_of_def Dlist.length_def Dlist.member_def
by (metis index_of_def index_of_member)
*)
(*
lemma dlist_singleton_sliceable_nth_member1: 
  "\<exists>i. Dlist [v] = sliceable_nth dl i \<Longrightarrow> Dlist.member dl v"
by (metis Dlist.member_def distinct_remdups_id distinct_singleton dlist_member_suc_nth1 
  drop_all in_set_conv_nth list.set_intros(1) list_of_dlist_Dlist list_of_dlist_slice 
  member_def not_Cons_self2 not_le take_eq_Nil)

lemma dlist_singleton_sliceable_nth_member: 
  "(\<exists>i. Dlist [v] = sliceable_nth dl i) \<longleftrightarrow> Dlist.member dl v"
apply (rule iffI, simp add: dlist_singleton_sliceable_nth_member1)
by (metis Dlist.member_def One_nat_def Suc_diff_le diff_is_0_eq' drop_Nil drop_eq_Nil 
  in_set_conv_nth in_set_member max_0L not_less order_refl slice_dlist_def 
  take_one_drop_n_singleton_nth)
*)

definition formulas :: "'a set \<Rightarrow> 'a formula set" where
"formulas V = { f . \<forall> dl \<in> Rep_formula f. (set (list_of_dlist dl)) \<subseteq> V  }"

lemma formulasI:
  assumes "\<forall> dl \<in> Rep_formula f. (set (list_of_dlist dl)) \<subseteq> V"
  shows "f \<in> formulas V"
using assms unfolding formulas_def by simp

lemma formulasD:
  assumes "f \<in> formulas V"
  shows "\<forall> dl \<in> Rep_formula f. (set (list_of_dlist dl)) \<subseteq> V"
using assms unfolding formulas_def by simp

lemma formulas_mono: "S \<subseteq> T \<Longrightarrow> formulas S \<subseteq> formulas T"
by (meson contra_subsetD formulasD formulasI subsetI)

lemma formulas_insert: "x \<in> formulas S \<Longrightarrow> x \<in> formulas (insert a S)"
unfolding formulas_def by auto

lemma in_set_conv_member: "List.member l v \<longleftrightarrow> (\<exists> i < length l. l ! i = v )"
by (simp add: in_set_conv_nth member_def)

lemma in_set_conv_member_dlist: 
  "Dlist.member dl v \<longleftrightarrow> (\<exists>i. Dlist.member (sliceable_nth dl i) v)"
by (metis Dlist.member_def dlist_member_suc_nth1 dlist_member_suc_nth2 drop_eq_Nil 
  empty_iff empty_set in_set_conv_member in_set_member linorder_not_less 
  list_of_dlist_simps(4) list_of_dlist_slice take_eq_Nil)

lemma formulas_var: "v \<in> V \<Longrightarrow> Abs_formula {dl. Dlist.member dl v} \<in> formulas V"



lemma formulas_var_iff: "v \<in> V \<longleftrightarrow> Abs_formula {ls. Dlist.member ls v} \<in> formulas V"
apply (rule iffI, simp add: formulas_var)
apply (simp add: Abs_formula_inverse formulas_def)
by (metis Dlist.member_def dlist_index_of_member empty_iff empty_set list_of_dlist_Dlist 
  member_rec(1) member_rec(2) remdups.simps(1) remdups.simps(2))

(*
definition formulas ::"'a set \<Rightarrow> 'a formula set" where
  "formulas V = { f. \<forall> dl\<^sub>1 dl\<^sub>2 . 
    (\<forall>v\<in>V. dlist_index_of dl\<^sub>1 v = dlist_index_of dl\<^sub>2 v) \<longrightarrow>
    dl\<^sub>1 \<in> Rep_formula f \<longleftrightarrow> dl\<^sub>2 \<in> Rep_formula f }"
*)
(*  
  "formulas V = { f. \<forall> dl\<^sub>1 dl\<^sub>2 . (\<forall>v\<in>V. Dlist.member dl\<^sub>1 v \<longleftrightarrow> Dlist.member dl\<^sub>2 v) \<longrightarrow>
    dl\<^sub>1 \<in> Rep_formula f \<longleftrightarrow> dl\<^sub>2 \<in> Rep_formula f }"
*)
(*
lemma formulasI:
  assumes "\<And>dl\<^sub>1 dl\<^sub>2. 
    (\<forall>v\<in>V. dlist_index_of dl\<^sub>1 v = dlist_index_of dl\<^sub>2 v)
    \<Longrightarrow> dl\<^sub>1 \<in> Rep_formula f \<longleftrightarrow> dl\<^sub>2 \<in> Rep_formula f"
  shows "f \<in> formulas V"
using assms unfolding formulas_def by simp

lemma formulasD:
  assumes "f \<in> formulas V"
  assumes "\<forall>v\<in>V. dlist_index_of dl\<^sub>1 v = dlist_index_of dl\<^sub>2 v"
  shows "dl\<^sub>1 \<in> Rep_formula f \<longleftrightarrow> dl\<^sub>2 \<in> Rep_formula f"
using assms unfolding formulas_def by simp

lemma formulas_mono: "S \<subseteq> T \<Longrightarrow> formulas S \<subseteq> formulas T"
by (fast intro!: formulasI elim!: formulasD)

lemma formulas_insert: "x \<in> formulas S \<Longrightarrow> x \<in> formulas (insert a S)"
unfolding formulas_def by simp

lemma in_set_conv_member: "List.member l v \<longleftrightarrow> (\<exists> i < length l. l ! i = v )"
by (simp add: in_set_conv_nth member_def)

lemma in_set_conv_member_dlist: 
  "Dlist.member dl v \<longleftrightarrow> (\<exists>i. Dlist.member (sliceable_nth dl i) v)"
by (metis Dlist.member_def dlist_member_suc_nth1 dlist_member_suc_nth2 drop_eq_Nil 
  empty_iff empty_set in_set_conv_member in_set_member linorder_not_less 
  list_of_dlist_simps(4) list_of_dlist_slice take_eq_Nil)

lemma formulas_var: "v \<in> V \<Longrightarrow> Abs_formula {dl. Dlist.member dl v} \<in> formulas V"
apply (simp add: formulas_def Abs_formula_inverse)
by (simp add: dlist_index_of_member_iff[symmetric])


lemma formulas_var_iff: "v \<in> V \<longleftrightarrow> Abs_formula {ls. Dlist.member ls v} \<in> formulas V"
apply (rule iffI, simp add: formulas_var)
apply (simp add: Abs_formula_inverse formulas_def)
by (metis Dlist.member_def dlist_index_of_member empty_iff empty_set list_of_dlist_Dlist 
  member_rec(1) member_rec(2) remdups.simps(1) remdups.simps(2))

(*
by (metis (mono_tags, hide_lams) Dlist.member_def empty_iff in_set_member list.set(1) 
  list_of_dlist_Dlist member_rec(1) remdups.simps(1) remdups.simps(2))
*)

lemma formulas_bot: "bot \<in> formulas S"
unfolding formulas_def by simp

lemma formulas_top: "top \<in> formulas S"
unfolding formulas_def by simp

lemma formulas_compl: "x \<in> formulas S \<Longrightarrow> - x \<in> formulas S"
unfolding formulas_def by (simp add: Rep_formula_boolean_algebra_simps)

lemma formulas_inf:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> inf x y \<in> formulas S"
unfolding formulas_def by (auto simp add: Rep_formula_boolean_algebra_simps)

lemma formulas_sup:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> sup x y \<in> formulas S"
unfolding formulas_def by (auto simp add: Rep_formula_boolean_algebra_simps)

lemma formulas_diff:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> x - y \<in> formulas S"
unfolding formulas_def by (auto simp add: Rep_formula_boolean_algebra_simps)
*)
(*
lemma formulas_xbefore:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> xbefore x y \<in> formulas S"
unfolding formulas_def 
*)
(*
lemma formulas_neutral: "neutral \<in> formulas S"
unfolding formulas_def neutral_formula_def
*)


(*lemma formulas_xbefore: "\<lbrakk> f1 \<in> formulas V; f2 \<in> formulas V \<rbrakk> \<Longrightarrow> 
  xbefore f1 f2 \<in> formulas V"*)
(*
unfolding formulas_def 
apply (simp add: formulas_def Rep_formula_xbefore_to_dlist_xbefore dlist_xbefore_def)

apply (simp add: slice_left_def slice_right_def slice_dlist_def size_dlist_def 
  )
*)


(*
lemma finite_formula : "finite V \<Longrightarrow> finite (formulas V)"
*)


theorem soundness: 
  "fexp \<in> formula_syn V \<Longrightarrow> formula_exp_to_formula fexp \<in> formulas V"
apply (induct fexp, auto)
apply (simp add: formulas_bot)
apply (simp add: formulas_top)
(*
apply (metis formula_exp.distinct(1) formula_exp.distinct(11) formula_exp.distinct(13) 
  formula_exp.distinct(9) formula_exp_to_formula.simps(2) formula_syn.simps formulas_var)
apply (metis formula_exp.distinct(15) formula_exp.distinct(17) formula_exp.distinct(3) 
  formula_exp.distinct(9) formula_exp.inject(2) formula_exp_to_formula.simps(3) formula_syn.simps formulas_sup)
apply (metis formula_exp.distinct(11) formula_exp.distinct(15) formula_exp.distinct(19) 
  formula_exp.distinct(5) formula_exp.inject(3) formula_exp_to_formula.simps(4) 
  formula_syn.simps formulas_compl)
by (metis formula_exp.distinct(13) formula_exp.distinct(17) formula_exp.distinct(19) formula_exp.distinct(7) formula_exp.inject(4) formula_exp_to_formula.simps(5) formula_syn.simps formulas_xbefore)
*)

lemma completeness_tNOT:
  "finite V \<Longrightarrow> - f \<in> formulas V \<Longrightarrow> tNOT (formula_to_formula_exp f) \<in> formula_syn V"
sorry

theorem completeness: 
  "\<forall> V. finite V \<and> fsem \<in> formulas V \<longrightarrow> formula_to_formula_exp fsem \<in> formula_syn V"
by (metis completeness_tNOT formula_exp.distinct(11) formula_exp.distinct(15) 
  formula_exp.distinct(19) formula_exp.distinct(5) formula_exp.inject(3) formula_syn.cases 
  formulas_compl)



end