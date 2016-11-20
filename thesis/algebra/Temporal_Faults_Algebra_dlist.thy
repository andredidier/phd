section {* Denotational semantics for \ac{algebra} *}

text {*
\label{sec:theory-algebra-dlist}
In the following we present the denotation semantics for \ac{algebra} in terms of sets of distinct lists.
*}

(*<*)
theory Temporal_Faults_Algebra_dlist
imports 
  Temporal_Faults_Algebra Sliceable_dlist Dlist_finiteness Enum
  "~~/src/HOL/Library/Dlist"
  "~~/src/HOL/Library/Permutation" 
  "~~/src/HOL/Library/Sublist_Order" 
  "~~/src/HOL/Library/LaTeXsugar"
  "~~/src/HOL/Library/OptionalSugar"
begin
(*>*)

subsection {* Formula: distinct lists *}

text{* 
The definition of a formula in the \ac{algebra} is a set of sets of distinct lists (dlist).
*}

typedef 'a formula = "UNIV::'a dlist set set" by simp

subsubsection {* Formula as Boolean algebra*}

(*<*)
notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)
(*
notation (latex output) 
  xbefore ("_\<rightarrow>_" [80,80] 80) and
  slice ("(3_\<^bsub>[_.._]\<^esub>)"  [80,80,80] 80) and
  slice_left ("(2_\<^bsub>[_..]\<^esub>)" [80,80] 80) and
  slice_right ("(2_\<^bsub>[.._]\<^esub>)" [80,80] 80) and  
  tempo1 ("vremya\<^sub>1 _" 80) and
  tempo2 ("vremya\<^sub>2 _" 80) and
  tempo3 ("vremya\<^sub>3 _" 80) and
  tempo4 ("vremya\<^sub>4 _" 80) and 
  Abs_formula ("_\<^bsub>formula\<^esub>") and
  Rep_formula ("_\<^bsub>dlist set\<^esub>") and
  list_of_dlist ("_\<^bsub>list\<^esub>" 80)
  *)
(*>*)

text{* In the following we instantiate the formula as a Boolean algebra and prove that Boolean operators are valid. *}

instantiation formula :: (type) boolean_algebra
begin

definition
  "x \<sqinter> y = Abs_formula (Rep_formula x \<inter> Rep_formula y)"

definition
  "x \<squnion> y = Abs_formula (Rep_formula x \<union> Rep_formula y)"

definition
  "\<top> = Abs_formula UNIV"

definition
  "\<bottom> = Abs_formula {}"

definition
  "x \<le> y \<longleftrightarrow> Rep_formula x \<subseteq> Rep_formula y"

definition
  "x < y \<longleftrightarrow> Rep_formula x \<subset> Rep_formula y"

definition
  "- x = Abs_formula (- (Rep_formula x))"

definition
  "x - y = Abs_formula (Rep_formula x - Rep_formula y)"

lemma Rep_formula_inf:
  "Rep_formula (x \<sqinter> y) = Rep_formula x \<inter> Rep_formula y"
unfolding inf_formula_def
by (simp add: Abs_formula_inverse Rep_formula)

lemma Rep_formula_sup:
  "Rep_formula (x \<squnion> y) = Rep_formula x \<union> Rep_formula y"
unfolding sup_formula_def
by (simp add: Abs_formula_inverse Rep_formula)

lemma Rep_formula_top[simp]: "Rep_formula \<top> = UNIV"
unfolding top_formula_def
by (simp add: Abs_formula_inverse)

lemma Rep_formula_bot[simp]: "Rep_formula \<bottom> = {}"
unfolding bot_formula_def 
by (simp add: Abs_formula_inverse)

lemma Rep_formula_compl: "Rep_formula (- x) = - Rep_formula x"
unfolding uminus_formula_def
by (simp add: Abs_formula_inverse Rep_formula)

lemma Rep_formula_diff:
  "Rep_formula (x - y) = Rep_formula x - Rep_formula y"
unfolding minus_formula_def
by (simp add: Abs_formula_inverse Rep_formula)

lemmas eq_formula_iff = Rep_formula_inject [symmetric]

lemmas Rep_formula_boolean_algebra_simps =
  less_eq_formula_def less_formula_def eq_formula_iff
  Rep_formula_sup Rep_formula_inf Rep_formula_top Rep_formula_bot
  Rep_formula_compl Rep_formula_diff 
  
instance proof
qed (unfold Rep_formula_boolean_algebra_simps, auto)
end

(*<*)
no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)
(*>*)

subsubsection {* Tempo properties *}

text {* In this section we define the tempo properties. *}

text {* Tempo1: disjoint split *}
definition dlist_tempo1 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo1 S \<equiv> \<forall>i j l. i \<le> j \<longrightarrow> \<not> ((S (l\<dagger>..i) \<and> S (l\<dagger>j..)))"

text {* Tempo2: belonging iff *}
definition dlist_tempo2 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo2 S \<equiv> \<forall>i l. S l \<longleftrightarrow> (S (l\<dagger>..i) \<or> S (l\<dagger>i..))"

definition dlist_tempo3 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo3 S \<equiv> \<forall>i j l. j < i \<longrightarrow> (S (l\<dagger>j..i) \<longleftrightarrow> 
  (S (l\<dagger>..i) \<and> S (l\<dagger>j..)))"

definition dlist_tempo4 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo4 S \<equiv> \<forall> l. S l \<longleftrightarrow> (\<exists>i. S (l\<dagger>i..(Suc i)))"

definition dlist_tempo5 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo5 S \<equiv> 
  \<forall> i j l. (i \<noteq> j \<and> i < (#l) \<and> j < (#l)) \<longrightarrow> 
    \<not>(S (l\<dagger>i..(Suc i)) \<and> S (l\<dagger>j..(Suc j)))"

definition dlist_tempo6 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo6 S \<equiv> \<forall>l. (\<forall> i j. \<not> S (l\<dagger>i..j)) \<longleftrightarrow> \<not> S l"

definition dlist_tempo7 :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo7 S \<equiv> \<forall>l. (\<exists> i j. i < j \<and> S (l\<dagger>i..j)) \<longleftrightarrow> S l"

definition dlist_tempo :: "('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_tempo S \<equiv> dlist_tempo1 S \<and> dlist_tempo2 S \<and> 
  dlist_tempo3 S \<and> dlist_tempo5 S \<and> dlist_tempo4 S \<and> dlist_tempo6 S \<and> 
  dlist_tempo7 S"
  
lemmas tempo_defs = dlist_tempo_def dlist_tempo1_def dlist_tempo2_def 
  dlist_tempo3_def dlist_tempo5_def dlist_tempo4_def dlist_tempo6_def 
  dlist_tempo7_def

lemma dlist_tempo_1_no_gap:
  "dlist_tempo1 S \<Longrightarrow> \<forall>i l. \<not> ((S (l\<dagger>..i) \<and> S (l\<dagger>i..)))"
unfolding dlist_tempo1_def
by auto

corollary dlist_tempo_1_no_gap_append: 
  "dlist_tempo1 S \<Longrightarrow> 
    \<forall>zs xs ys. list_of_dlist zs = list_of_dlist xs @ list_of_dlist ys \<longrightarrow> 
    \<not> ((S xs \<and> S ys))"
using dlist_tempo_1_no_gap  
by (metis Dlist_list_of_dlist append_eq_conv_conj slice_left_drop 
  take_slice_right)

subsubsection {* Tempo properties for list member *}

text {*
We use the naming convention of variable, but in fact, a variable is equivalent to a list membership: 
@{term "var a = {xs . a \<in> set (list_of_dlist xs)}"}.
*}
                                                      
lemma dlist_tempo1_member: "dlist_tempo1 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo1_def Dlist.member_def List.member_def
by (meson distinct_in_set_slice1_not_in_slice2)

lemma dlist_tempo2_member: "dlist_tempo2 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo2_def Dlist.member_def List.member_def
by (metis (no_types, lifting) Un_iff set_slice )

lemma dlist_tempo3_member: "dlist_tempo3 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo3_def Dlist.member_def List.member_def
by (metis DiffD2 Un_iff distinct_slice_diff2 dlist_append_extreme_left 
  dlist_append_extreme_right less_imp_le_nat set_append)

lemma dlist_tempo5_member: "dlist_tempo5 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo5_def Dlist.member_def List.member_def
by (metis Dlist_list_of_dlist Suc_leI disjoint_dlist_def disjoint_slice_suc 
  distinct_list_of_dlist dlist_empty_slice dlist_member_suc_nth1 empty_slice 
  less_Suc_eq_0_disj not_less_eq slice_singleton)

lemma dlist_tempo4_member: "dlist_tempo4 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo4_def Dlist.member_def List.member_def
(*by (metis Un_iff length_pos_if_in_set set_slice size_dlist_def slice_none 
  slice_right_slice_left_absorb)*)
by (metis dlist_member_suc_nth in_set_conv_nth in_set_dropD in_set_takeD 
  list_of_dlist_Dlist set_remdups size_dlist_def slice_dlist_def)

lemma dlist_tempo6_member: "dlist_tempo6 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo6_def Dlist.member_def List.member_def
by (metis append_Nil in_set_conv_decomp in_set_conv_nth in_set_dropD 
  in_set_takeD length_pos_if_in_set list_of_dlist_slice take_drop_suc)

lemma dlist_tempo7_member: "dlist_tempo7 (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo7_def Dlist.member_def List.member_def
by (metis Un_iff dlist_append_extreme_left dlist_member_suc_nth2 
  in_set_conv_nth lessI less_imp_le_nat set_append set_slice size_dlist_def)

theorem dlist_tempo_member: "dlist_tempo (\<lambda>xs. Dlist.member xs a)"
unfolding dlist_tempo_def 
by (simp add: dlist_tempo1_member dlist_tempo2_member dlist_tempo3_member 
  dlist_tempo5_member dlist_tempo4_member dlist_tempo6_member 
  dlist_tempo7_member)

subsubsection {* Tempo properties for other operators *}

lemma dlist_tempo1_inf: "\<lbrakk>dlist_tempo1 a; dlist_tempo1 b\<rbrakk> \<Longrightarrow> 
  dlist_tempo1 (\<lambda>zs. a zs \<and> b zs)"
unfolding dlist_tempo1_def
by simp

lemma dlist_tempo3_inf: "\<lbrakk>dlist_tempo3 a; dlist_tempo3 b\<rbrakk> \<Longrightarrow> 
  dlist_tempo3 (\<lambda>zs. a zs \<and> b zs)"
unfolding dlist_tempo3_def
by auto

lemma dlist_tempo2_sup: "\<lbrakk>dlist_tempo2 a; dlist_tempo2 b\<rbrakk> \<Longrightarrow> 
  dlist_tempo2 (\<lambda>zs. a zs \<or> b zs)"
unfolding dlist_tempo2_def
by auto

lemma dlist_tempo4_sup: "\<lbrakk>dlist_tempo4 a; dlist_tempo4 b\<rbrakk> \<Longrightarrow> 
  dlist_tempo4 (\<lambda>zs. a zs \<or> b zs)"
unfolding dlist_tempo4_def
by blast

subsection {* \acs*{XBefore} of distinct lists *}

definition dlist_xbefore :: "('a dlist \<Rightarrow> bool) \<Rightarrow> ('a dlist \<Rightarrow> bool) \<Rightarrow> 
  'a dlist \<Rightarrow> bool"
where
"dlist_xbefore a b xs \<equiv> \<exists>i. a (xs\<dagger>..i) \<and> b (xs\<dagger>i..)"
(*<*)
notation (latex output)
  dlist_xbefore ("_\<rightarrow>_ (_)" [80,80,80] 80) 
(*>*)

subsubsection {* \acs*{XBefore} and temporal properties *}

lemma dlist_tempo1_xbefore: "\<lbrakk>dlist_tempo1 a; dlist_tempo1 b\<rbrakk> \<Longrightarrow> 
  dlist_tempo1 (dlist_xbefore a b)"
unfolding dlist_tempo1_def dlist_xbefore_def slice_slice_simps
by (smt le_add1 min.absorb2 min.cobounded1 slice_right_slice_left_absorb 
  slice_right_slice_right_absorb)

subsubsection {* \acs*{XBefore} and appending *}

lemma Rep_slice_append: 
  "list_of_dlist zs = (list_of_dlist (zs\<dagger>..i)) @ (list_of_dlist (zs\<dagger>i..))"
by (metis distinct_append distinct_list_of_dlist distinct_slice_inter_empty 
  list_of_dlist_Dlist remdups_id_iff_distinct slice_append)

lemma dlist_xbefore_append: 
  "dlist_xbefore a b zs \<longleftrightarrow> 
  (\<exists>xs ys. set (list_of_dlist xs) \<inter> set (list_of_dlist ys) = 
    {} \<and> a xs \<and> b ys \<and> 
    list_of_dlist zs = ((list_of_dlist xs) @ (list_of_dlist ys)))"
unfolding dlist_xbefore_def
by (metis Rep_slice_append append_Nil2 append_eq_conv_conj 
  distinct_slice_inter_empty dlist_xbefore_def drop_take max_0L 
  size_dlist_def slice_append slice_dlist_def slice_left_def slice_right_def 
  take_slice_right)

subsubsection {* \acs*{XBefore}, bot, top and idempotency *}

lemma dlist_xbefore_bot_1: "dlist_xbefore (\<lambda>xs. False) b zs = False"
unfolding dlist_xbefore_def
by simp

corollary dlistset_xbefore_bot_1: 
  "Collect (dlist_xbefore (\<lambda>xs. False) b) = {}"
by (simp add: dlist_xbefore_bot_1)

(*
unfolding dlist_xbefore_def dlist_tempo_def dlist_tempo1_def dlist_tempo2_def
  dlist_tempo3_def dlist_tempo4_def dlist_tempo5_def dlist_tempo6_def dlist_tempo7_def
by auto*)

lemma dlist_xbefore_bot_2: "dlist_xbefore a (\<lambda>xs. False) zs = False"
unfolding dlist_xbefore_def
by simp

lemma dlistset_xbefore_bot_2: 
  "Collect (dlist_xbefore a (\<lambda>xs. False)) = {}"
by (simp add: dlist_xbefore_bot_2)

lemma dlist_xbefore_idem: 
  "dlist_tempo1 a \<Longrightarrow> dlist_xbefore a a zs = False"
unfolding dlist_xbefore_def dlist_tempo1_def
by blast

lemma dlistset_xbefore_idem: 
  "dlist_tempo1 a \<Longrightarrow> Collect (dlist_xbefore a a) = {}"
by (simp add: dlist_xbefore_idem)

lemma dlist_xbefore_implies_idem: 
  "\<forall>xs. b xs \<longrightarrow> a xs \<Longrightarrow> dlist_tempo1 a \<Longrightarrow> dlist_xbefore a b zs = False"
unfolding dlist_tempo1_def dlist_xbefore_def
by blast

subsubsection {* \acs*{XBefore} neutral*}

lemma dlist_xbefore_neutral_1: 
  "dlist_tempo1 a \<Longrightarrow> dlist_xbefore (\<lambda>xs. xs = dlist_of_list []) a zs = a zs"
by (metis (full_types) Dlist_list_of_dlist Rep_slice_append append.simps(1) 
  dlist_of_list dlist_xbefore_def take_0 take_slice_right)

corollary dlistset_xbefore_neutral_1: 
  "dlist_tempo1 a \<Longrightarrow> Collect (dlist_xbefore (\<lambda>xs. xs = Dlist []) a) = Collect a"
using dlist_xbefore_neutral_1 by auto

lemma dlist_xbefore_neutral_2: 
  "dlist_tempo1 a \<Longrightarrow> dlist_xbefore a (\<lambda>xs. xs = Dlist []) zs = a zs"
by (smt Dlist_list_of_dlist append_Nil2 distinct_append distinct_list_of_dlist dlist_of_list 
  dlist_xbefore_append list_of_dlist_empty)

corollary dlistset_xbefore_neutral_2: 
  "dlist_tempo1 a \<Longrightarrow> Collect (dlist_xbefore a (\<lambda>xs. xs = Dlist [])) = Collect a"
using dlist_xbefore_neutral_2 by auto

subsubsection {* \acs*{XBefore} associativity*}

theorem dlist_xbefore_assoc1: 
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow> dlist_tempo1 U \<Longrightarrow> 
  (dlist_xbefore (dlist_xbefore S T) U zs) \<longleftrightarrow> 
    (dlist_xbefore S (dlist_xbefore T U) zs)"
unfolding dlist_xbefore_def slice_slice_simps dlist_tempo_def
apply auto
apply (metis diff_is_0_eq less_imp_le max_0L min_def not_le 
  ordered_cancel_comm_monoid_diff_class.le_iff_add slice_dlist_def 
  take_eq_Nil)
by (metis le_add1 min.absorb2)

corollary dlist_xbefore_assoc:
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow> dlist_tempo1 U \<Longrightarrow> 
  (dlist_xbefore (dlist_xbefore S T) U) = 
    (dlist_xbefore S (dlist_xbefore T U))"
using dlist_xbefore_assoc1 by blast

corollary dlistset_xbefore_assoc:
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow> dlist_tempo1 U \<Longrightarrow>
  Collect (dlist_xbefore (dlist_xbefore S T) U) = 
    Collect (dlist_xbefore S (dlist_xbefore T U))"
by (simp add: dlist_xbefore_assoc)

subsubsection {* \acs*{XBefore} equivalences *}

lemma dlist_tempo1_le_uniqueness: 
  "dlist_tempo1 S \<Longrightarrow> S (l\<dagger>..i) \<Longrightarrow> i \<le> j \<Longrightarrow> \<not> S (l\<dagger>j..)" and
  "dlist_tempo1 S \<Longrightarrow> S (l\<dagger>j..) \<Longrightarrow> i \<le> j \<Longrightarrow> \<not> S (l\<dagger>..i)"
unfolding dlist_tempo1_def
by auto

lemma dlist_xbefore_not_sym: 
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow> dlist_xbefore S T xs \<Longrightarrow> 
  dlist_xbefore T S xs \<Longrightarrow> False"
by (metis dlist_xbefore_def le_cases dlist_tempo1_le_uniqueness)

corollary dlist_xbefore_and: 
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow> 
    ((dlist_xbefore S T zs) \<and> (dlist_xbefore T S zs)) = False"
using dlist_xbefore_not_sym by blast


corollary dlistset_xbefore_and:
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow>
  (Collect (dlist_xbefore S T)) \<inter> (Collect (dlist_xbefore T S)) = {}"
using dlist_xbefore_and
by auto

lemma dlist_tempo2_left_absorb: "dlist_tempo2 S \<Longrightarrow> S (l\<dagger>i..) \<Longrightarrow> S l"
unfolding dlist_tempo2_def
by auto

lemma dlist_tempo2_right_absorb: "dlist_tempo2 S \<Longrightarrow> S (l\<dagger>..i) \<Longrightarrow> S l"
unfolding dlist_tempo2_def
by auto

lemma dlist_xbefore_implies_member1[simp]: 
  "dlist_tempo2 S \<Longrightarrow> dlist_xbefore S T l \<Longrightarrow> S l"
by (meson dlist_xbefore_def dlist_tempo2_right_absorb)

lemma dlist_xbefore_implies_member2[simp]: 
  "dlist_tempo2 T \<Longrightarrow> dlist_xbefore S T l \<Longrightarrow> T l"
by (meson dlist_xbefore_def dlist_tempo2_left_absorb)

lemma dlist_xbefore_or1:
  "dlist_tempo2 S \<Longrightarrow> dlist_tempo2 T \<Longrightarrow>
  dlist_xbefore S T l \<or> dlist_xbefore T S l \<Longrightarrow> S l \<and> T l"
using dlist_xbefore_implies_member1 dlist_xbefore_implies_member2 by blast

(*TODO: review independent events definition*)
definition dlist_independent_events :: 
  "('a dlist \<Rightarrow> bool) \<Rightarrow> ('a dlist \<Rightarrow> bool) \<Rightarrow> bool"
where
"dlist_independent_events S T \<equiv> 
  (\<forall>i l. \<not> (S (l\<dagger>i..(Suc i)) \<and> T (l\<dagger>i..(Suc i))))"

lemma dlist_indepentent_events_member: "a \<noteq> b \<Longrightarrow> 
  dlist_independent_events (\<lambda> dl. Dlist.member dl a) (\<lambda> dl. Dlist.member dl b)"
apply (simp add: dlist_independent_events_def Dlist.member_def List.member_def)
by (metis dlist_member_suc_nth1)


(*Verificar se faz sentido a regra abaixo. *)
(*
lemma "dlist_independent_events a b \<Longrightarrow> \<forall>xs. b xs \<longrightarrow> a xs \<Longrightarrow> False"
unfolding dlist_independent_events_def
sorry
*)

(*TODO: try to remove all these requirements*)
lemma dlist_and_split9:
  "dlist_independent_events S T \<Longrightarrow> 
    dlist_tempo2 S \<Longrightarrow> dlist_tempo2 T \<Longrightarrow>
    dlist_tempo3 S \<Longrightarrow> dlist_tempo3 T \<Longrightarrow>
    dlist_tempo4 S \<Longrightarrow> dlist_tempo4 T \<Longrightarrow>
  S l \<and> T l \<longleftrightarrow> (\<exists>i j. i \<le> j \<and>
    ((S (l\<dagger>..i) \<and> T (l\<dagger>j..)) \<or> (S (l\<dagger>j..) \<and> T (l\<dagger>..i))))"
unfolding dlist_independent_events_def  
  dlist_tempo2_def dlist_tempo3_def dlist_tempo4_def
by (metis le_refl not_less not_less_eq_eq)

lemma dlist_tempo_equiv_xor: 
  "dlist_tempo1 S \<Longrightarrow> dlist_tempo2 S \<Longrightarrow>  
  \<forall>l. S l \<longleftrightarrow> (\<forall>i. (S (l\<dagger>..i) \<and> \<not> S (l\<dagger>i..)) \<or> (\<not> S (l\<dagger>..i) \<and> S (l\<dagger>i..)))"
unfolding tempo_defs
by (meson order_refl)

corollary dlist_tempo_equiv_not_eq: "dlist_tempo1 S \<Longrightarrow> dlist_tempo2 S \<Longrightarrow> 
  \<forall>l. S l \<longleftrightarrow> (\<forall>i. S (l\<dagger>..i) \<noteq> S (l\<dagger>i..))"
using dlist_tempo_equiv_xor
by auto

lemma dlists_xbefore_or2:
  "dlist_independent_events S T \<Longrightarrow> 
  dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow>
  dlist_tempo2 S \<Longrightarrow> dlist_tempo2 T \<Longrightarrow>
  dlist_tempo3 S \<Longrightarrow> dlist_tempo3 T \<Longrightarrow>
  dlist_tempo4 S \<Longrightarrow> dlist_tempo4 T \<Longrightarrow>
  S l \<and> T l \<Longrightarrow> dlist_xbefore S T l \<or> dlist_xbefore T S l"
unfolding dlist_xbefore_def dlist_tempo_def
by (metis dlist_and_split9 dlist_tempo_equiv_not_eq 
  dlist_tempo1_le_uniqueness)

theorem dlist_xbefore_or_one_list:
  "dlist_independent_events S T \<Longrightarrow> 
  dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow>
  dlist_tempo2 S \<Longrightarrow> dlist_tempo2 T \<Longrightarrow>
  dlist_tempo3 S \<Longrightarrow> dlist_tempo3 T \<Longrightarrow>
  dlist_tempo4 S \<Longrightarrow> dlist_tempo4 T \<Longrightarrow>
  dlist_xbefore S T l \<or> dlist_xbefore T S l \<longleftrightarrow> S l \<and> T l"
using dlist_xbefore_or1 dlists_xbefore_or2 dlist_tempo_def
by blast

corollary dlist_xbefore_or: 
  "dlist_independent_events S T \<Longrightarrow> 
  dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow>
  dlist_tempo2 S \<Longrightarrow> dlist_tempo2 T \<Longrightarrow>
  dlist_tempo3 S \<Longrightarrow> dlist_tempo3 T \<Longrightarrow>
  dlist_tempo4 S \<Longrightarrow> dlist_tempo4 T \<Longrightarrow>
  (\<lambda>zs. (dlist_xbefore S T zs) \<or> (dlist_xbefore T S zs)) = 
    (\<lambda>zs. S zs \<and> T zs)"
using dlist_xbefore_or_one_list 
by blast

corollary dlistset_xbefore_or:
  "dlist_independent_events S T \<Longrightarrow> 
  dlist_tempo1 S \<Longrightarrow> dlist_tempo1 T \<Longrightarrow>
  dlist_tempo2 S \<Longrightarrow> dlist_tempo2 T \<Longrightarrow>
  dlist_tempo3 S \<Longrightarrow> dlist_tempo3 T \<Longrightarrow>
  dlist_tempo4 S \<Longrightarrow> dlist_tempo4 T \<Longrightarrow>
  (Collect (dlist_xbefore S T)) \<union> (Collect (dlist_xbefore T S)) = 
    Collect S \<inter> Collect T"
using dlist_xbefore_or
by (smt Collect_cong Collect_conj_eq Collect_disj_eq)

subsubsection {* \acs*{XBefore} transitivity *}

theorem dlist_xbefore_trans: "
  \<lbrakk>dlist_tempo1 a; dlist_tempo1 b; dlist_tempo1 c\<rbrakk> \<Longrightarrow>
  \<lbrakk>dlist_tempo2 a; dlist_tempo2 b; dlist_tempo2 c\<rbrakk> \<Longrightarrow>   
  dlist_xbefore a b zs \<and> dlist_xbefore b c zs \<Longrightarrow> 
  dlist_xbefore a c zs"
using dlist_xbefore_not_sym 
by (metis dlist_tempo2_def dlist_xbefore_def)

corollary dlistset_xbefore_trans: "
  \<lbrakk>dlist_tempo1 a; dlist_tempo1 b; dlist_tempo1 c\<rbrakk> \<Longrightarrow>
  \<lbrakk>dlist_tempo2 a; dlist_tempo2 b; dlist_tempo2 c\<rbrakk> \<Longrightarrow>
  (Collect (dlist_xbefore a b) \<inter> Collect (dlist_xbefore b c)) \<subseteq> 
    Collect (dlist_xbefore a c)"
using dlist_xbefore_trans
by auto

subsubsection {* Boolean operators mixed with \acs*{XBefore} *}

theorem mixed_dlist_xbefore_or1: "  
  dlist_xbefore (\<lambda>xs. a xs \<or> b xs) c zs =
  ((dlist_xbefore a c zs) \<or> (dlist_xbefore b c zs))"
unfolding dlist_xbefore_def by auto

corollary mixed_dlistset_xbefore_or1: "
  Collect (dlist_xbefore (\<lambda>xs. a xs \<or> b xs) c) = 
  Collect (dlist_xbefore a c) \<union> Collect (dlist_xbefore b c)"
proof-
  have "Collect (\<lambda>zs. (dlist_xbefore a c zs) \<or> (dlist_xbefore b c zs)) =
    (Collect (dlist_xbefore a c) \<union> Collect (dlist_xbefore b c))"
    by (simp add: Collect_disj_eq)
  thus ?thesis using mixed_dlist_xbefore_or1 by blast
qed
 
theorem mixed_dlist_xbefore_or2: "
  dlist_xbefore a (\<lambda>xs. b xs \<or> c xs) zs =
  ((dlist_xbefore a b zs) \<or> (dlist_xbefore a c zs))"
unfolding dlist_xbefore_def by auto

corollary mixed_dlistset_xbefore_or2: "
  Collect (dlist_xbefore a (\<lambda>xs. b xs \<or> c xs)) =
  Collect (dlist_xbefore a b) \<union> Collect (dlist_xbefore a c)"
proof-
  have "Collect (\<lambda>zs. (dlist_xbefore a b zs) \<or> (dlist_xbefore a c zs)) =
    Collect (dlist_xbefore a b) \<union> Collect (dlist_xbefore a c)"
    by (simp add: Collect_disj_eq)
  thus ?thesis using mixed_dlist_xbefore_or2 by blast
qed

lemma and_dlist_xbefore_equiv_or_dlist_xbefore: 
  "dlist_tempo2 a \<Longrightarrow>
  (a zs \<and> dlist_xbefore b c zs) \<longleftrightarrow> 
    (dlist_xbefore (\<lambda> xs. a xs \<and> b xs) c zs \<or>
      dlist_xbefore b (\<lambda>xs. a xs \<and> c xs) zs)"
proof-
  assume "dlist_tempo2 a"
  hence 0: "\<forall>i xs. a xs \<longleftrightarrow> (a (xs\<dagger>..i) \<or> a (xs\<dagger>i..))" 
    using dlist_tempo2_def by auto
  have "a zs \<and> dlist_xbefore b c zs \<longleftrightarrow> 
    a zs \<and> (\<exists>i. b (zs\<dagger>..i) \<and> c (zs\<dagger>i..))"
    by (auto simp add: dlist_xbefore_def)
  thus ?thesis using 0 by (auto simp add: dlist_xbefore_def)  
qed

corollary and_dlistset_xbefore_equiv_or_dlistset_xbefore: 
  "dlist_tempo2 a \<Longrightarrow>
  ((Collect a) \<inter> (Collect (dlist_xbefore b c)))= 
    (Collect (dlist_xbefore (\<lambda> xs. a xs \<and> b xs) c) \<union>
      Collect (dlist_xbefore b (\<lambda>xs. a xs \<and> c xs)))"
by (smt Collect_cong Collect_conj_eq Collect_disj_eq dlist_tempo2_def 
  dlist_xbefore_def)

lemma dlist_xbefore_implies_not_sym_dlist_xbefore: " 
  \<lbrakk>dlist_tempo1 a; dlist_tempo1 b\<rbrakk> \<Longrightarrow> 
  dlist_xbefore a b zs \<Longrightarrow> \<not> dlist_xbefore b a zs"
unfolding dlist_xbefore_def dlist_tempo1_def 
by (meson nat_le_linear)
  
corollary dlistset_xbefore_implies_not_sym_dlistset_xbefore:
  "\<lbrakk>dlist_tempo1 a; dlist_tempo1 b\<rbrakk> \<Longrightarrow>
  Collect (dlist_xbefore a b) \<subseteq> - Collect (dlist_xbefore b a)"
using dlist_xbefore_implies_not_sym_dlist_xbefore 
by (metis (mono_tags, lifting) CollectD ComplI subsetI)

theorem mixed_not_dlist_xbefore: "dlist_independent_events a b \<Longrightarrow> 
  \<lbrakk>dlist_tempo1 a; dlist_tempo1 b\<rbrakk> \<Longrightarrow> 
  \<lbrakk>dlist_tempo2 a; dlist_tempo2 b\<rbrakk> \<Longrightarrow>
  \<lbrakk>dlist_tempo3 a; dlist_tempo3 b\<rbrakk> \<Longrightarrow>
  \<lbrakk>dlist_tempo4 a; dlist_tempo4 b\<rbrakk> \<Longrightarrow>
  (\<not> (dlist_xbefore a b zs)) = 
  ((\<not> a zs) \<or> (\<not> b zs) \<or> (dlist_xbefore b a zs))"
using dlist_xbefore_implies_not_sym_dlist_xbefore dlist_xbefore_or_one_list 
by blast

corollary mixed_not_dlistset_xbefore: "dlist_independent_events a b \<Longrightarrow> 
  \<lbrakk>dlist_tempo1 a; dlist_tempo1 b\<rbrakk> \<Longrightarrow> 
  \<lbrakk>dlist_tempo2 a; dlist_tempo2 b\<rbrakk> \<Longrightarrow>
  \<lbrakk>dlist_tempo3 a; dlist_tempo3 b\<rbrakk> \<Longrightarrow>
  \<lbrakk>dlist_tempo4 a; dlist_tempo4 b\<rbrakk> \<Longrightarrow>
  (- Collect (dlist_xbefore a b)) = 
  ((- Collect a) \<union> (- Collect b) \<union> Collect (dlist_xbefore b a))"
proof-
  assume 0: "dlist_independent_events a b" "dlist_tempo1 a" "dlist_tempo1 b" 
  "dlist_tempo2 a" "dlist_tempo2 b" "dlist_tempo3 a" "dlist_tempo3 b" 
  "dlist_tempo4 a" "dlist_tempo4 b"
  have "((- Collect a) \<union> (- Collect b) \<union> Collect (dlist_xbefore b a)) =
    ((Collect (\<lambda>zs. \<not> a zs \<or> \<not> b zs)) \<union> Collect (dlist_xbefore b a))"
    by blast
  also have "... = (Collect (\<lambda>zs. \<not> a zs \<or> \<not> b zs \<or> dlist_xbefore b a zs))"
    by blast
  hence "Collect (\<lambda>zs. (\<not> a zs) \<or> (\<not> b zs) \<or> (dlist_xbefore b a zs)) =
    ((- Collect a) \<union> (- Collect b) \<union> Collect (dlist_xbefore b a))" 
    "Collect (\<lambda>zs. \<not> (dlist_xbefore a b zs)) = 
      - Collect (dlist_xbefore a b)"
    by blast+
  thus ?thesis using 0 mixed_not_dlist_xbefore by blast
qed 

theorem not_1_dlist_xbefore: 
  "\<lbrakk> dlist_tempo1 a;  dlist_tempo2 b\<rbrakk> \<Longrightarrow> 
    dlist_xbefore (\<lambda>xs. \<not> a xs) b zs = b zs"
by (metis Dlist_list_of_dlist dlist_tempo_1_no_gap dlist_xbefore_def dlist_xbefore_implies_member2 drop_0 slice_left_drop slice_right_take take_0)

corollary not_1_dlistset_xbefore: 
  "\<lbrakk> dlist_tempo1 a;  dlist_tempo2 b\<rbrakk> \<Longrightarrow> 
    Collect (dlist_xbefore (\<lambda>xs. \<not> a xs) b) = Collect b"
using not_1_dlist_xbefore by blast

theorem not_2_dlist_xbefore: 
  "\<lbrakk> dlist_tempo1 b; dlist_tempo2 a \<rbrakk> \<Longrightarrow> dlist_xbefore a (\<lambda>xs. \<not> b xs) zs = a zs"
by (metis Dlist.empty_def append_Nil2 dlist_tempo_1_no_gap 
  dlist_xbefore_append dlist_xbefore_implies_member1 drop_0 inf.commute 
  inf_bot_left list.set(1) list_of_dlist_empty slice_left_drop 
  slice_right_take take_0)

corollary not_2_dlistset_xbefore: 
  "\<lbrakk> dlist_tempo1 b; dlist_tempo2 a \<rbrakk> \<Longrightarrow> 
  Collect (dlist_xbefore a (\<lambda>xs. \<not> b xs)) = Collect a"
using not_2_dlist_xbefore by blast

lemma empty_dlist_implies_false[simp]: 
  "\<lbrakk> dlist_tempo1 a; dlist_tempo2 a \<rbrakk> \<Longrightarrow> a (Dlist []) \<Longrightarrow> False"
unfolding dlist_tempo1_def dlist_tempo2_def dlist_tempo3_def dlist_tempo4_def
  slice_left_def slice_right_def size_dlist_def slice_dlist_def
by (metis Dlist.empty_def list.size(3) list_of_dlist_empty nat_le_linear)


lemma dlist_inf_xbefore_trans:
  "\<lbrakk> dlist_tempo1 b; dlist_tempo3 b \<rbrakk> \<Longrightarrow> ((dlist_xbefore a b zs) \<and> (dlist_xbefore b c zs)) \<longleftrightarrow> 
    (dlist_xbefore (dlist_xbefore a b) c) zs"
proof-
  assume 0: "dlist_tempo1 b" "dlist_tempo3 b" 
  hence 1: "\<exists> i. (\<exists> j. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..) \<and> b (zs\<dagger>..j) \<and> c (zs\<dagger>j..) \<longleftrightarrow>
      a (zs\<dagger>..i) \<and> b (zs\<dagger>i..j) \<and> c (zs\<dagger>j..))"
    by (metis slice_left_def slice_right_def)
  have 2: "(\<exists> x y. a (zs\<dagger>..x) \<and> b (zs\<dagger>x..) \<and> b (zs\<dagger>..y) \<and> c (zs\<dagger>y..)) \<longleftrightarrow>
      (\<exists> x y. a (zs\<dagger>..x) \<and> b (zs\<dagger>x..y) \<and> c (zs\<dagger>y..))"
    using 0
    by (metis (no_types, hide_lams) diff_zero dlist_empty_slice dlist_tempo1_le_uniqueness dlist_tempo3_def dlist_tempo_1_no_gap drop_0 list_of_dlist_empty list_of_dlist_simps(3) max_0L not_le slice_left_drop slice_right_def take_0)
  have 3: "((\<exists>i. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..)) \<and> (\<exists>j. b (zs\<dagger>..j) \<and> c (zs\<dagger>j..))) \<longleftrightarrow> 
    (\<exists> i j. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..) \<and> b (zs\<dagger>..j) \<and> c (zs\<dagger>j..))"
    "(\<exists>i. (\<exists>j. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>j..i)) \<and> c (zs\<dagger>i..)) \<longleftrightarrow> 
      (\<exists>i j. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>j..i) \<and> c (zs\<dagger>i..))"
    by auto
  have 4: "(\<exists> x y. a (zs\<dagger>..min x y) \<and> b (zs\<dagger>x..y) \<and> c (zs\<dagger>y..)) \<longleftrightarrow>
    (\<exists> x y. a (zs\<dagger>..x) \<and> b (zs\<dagger>x..y) \<and> c (zs\<dagger>y..))"
    using 0
    by (metis (no_types, lifting) Dlist.empty_def append_Nil2 dlist_empty_slice dlist_tempo_1_no_gap_append list_of_dlist_empty min.cobounded1 min_def)
  have "(\<exists>i j. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..j) \<and> c (zs\<dagger>j..)) \<longleftrightarrow> 
    (\<exists>i j. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>i..j) \<and> c (zs\<dagger>j..))"
    using 4 by simp
  hence "(\<exists>i j. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..) \<and> b (zs\<dagger>..j) \<and> c (zs\<dagger>j..)) \<longleftrightarrow> 
    (\<exists>i j. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>i..j) \<and> c (zs\<dagger>j..))"
    using 0 2 by simp
  hence "((\<exists>i. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..)) \<and> (\<exists>j. b (zs\<dagger>..j) \<and> c (zs\<dagger>j..))) \<longleftrightarrow> 
    (\<exists>i j. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>i..j) \<and> c (zs\<dagger>j..))"
    using 0 3 by simp
  hence "((\<exists>i. a (zs\<dagger>..i) \<and> b (zs\<dagger>i..)) \<and> (\<exists>j. b (zs\<dagger>..j) \<and> c (zs\<dagger>j..))) \<longleftrightarrow> 
    (\<exists>j. (\<exists>i. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>i..j)) \<and> c (zs\<dagger>j..))"
    using 3 by auto
  hence "(dlist_xbefore a b zs \<and> dlist_xbefore b c zs) \<longleftrightarrow> 
    (\<exists>j. (\<exists>i. a (zs\<dagger>..min i j) \<and> b (zs\<dagger>i..j)) \<and> c (zs\<dagger>j..))"
    using dlist_xbefore_def by auto
  hence "(dlist_xbefore a b zs \<and> dlist_xbefore b c zs) \<longleftrightarrow> 
    (\<exists>j. (\<exists>i. a ((zs\<dagger>..j)\<dagger>..i) \<and> b ((zs\<dagger>..j)\<dagger>i..)) \<and> c (zs\<dagger>j..))"
    by (simp add: min.commute slice_right_slice_left_absorb slice_right_slice_right_absorb)
  thus ?thesis unfolding dlist_xbefore_def by simp
qed

lemma dlistset_inf_xbefore_trans:
  "\<lbrakk> dlist_tempo1 b; dlist_tempo3 b \<rbrakk> \<Longrightarrow> (Collect  (dlist_xbefore a b) \<inter> Collect (dlist_xbefore b c)) = 
    Collect (dlist_xbefore (dlist_xbefore a b) c)"
using dlist_inf_xbefore_trans
using Collect_cong Collect_conj_eq by blast

subsection {* Formulas as \ac{algebra} *}

text {*
In the following we prove that a formula is a valid type instantation for all \ac{algebra} classes.
*}

subsubsection {* Basic properties of \ac{algebra} *}

instantiation formula :: (type) temporal_faults_algebra_basic
begin

definition
  "neutral = Abs_formula { dlist_of_list [] }"

definition
  "xbefore a b = Abs_formula { zs . 
    dlist_xbefore (\<lambda>xs. xs \<in> Rep_formula a) (\<lambda>ys. ys \<in> Rep_formula b) zs }"

definition 
  "tempo1 a = dlist_tempo1 (\<lambda>xs. xs \<in> Rep_formula a)"
    
lemma Rep_formula_xbefore_to_dlist_xbefore: 
  "Rep_formula (xbefore a b) = 
  Collect (dlist_xbefore (\<lambda>x. x \<in> Rep_formula a) (\<lambda>y. y \<in> Rep_formula b))"
unfolding dlist_xbefore_def xbefore_formula_def
by (simp add: Abs_formula_inverse)

lemma Rep_formula_xbefore_bot_1: "Rep_formula (xbefore bot a) = 
  Rep_formula bot"
unfolding xbefore_formula_def 
by (simp add: Abs_formula_inverse dlist_xbefore_bot_1)

lemma Rep_formula_xbefore_bot_2: "Rep_formula (xbefore a bot) = 
  Rep_formula bot"
unfolding xbefore_formula_def
by (simp add: Abs_formula_inverse dlist_xbefore_bot_2)

lemma Rep_formula_xbefore_neutral_1: "tempo1 a \<Longrightarrow> Rep_formula (xbefore neutral a) = Rep_formula a"
unfolding xbefore_formula_def neutral_formula_def tempo1_formula_def 
apply (simp add: Abs_formula_inverse)
using dlistset_xbefore_neutral_1 by auto

lemma Rep_formula_xbefore_neutral_2: "tempo1 a \<Longrightarrow> Rep_formula (xbefore a neutral) = Rep_formula a"
unfolding xbefore_formula_def neutral_formula_def tempo1_formula_def
apply (simp add: Abs_formula_inverse)
using dlistset_xbefore_neutral_2 by auto

lemma Rep_formula_xbefore_not_idempotent: 
  "tempo1 a \<Longrightarrow> Rep_formula (xbefore a a) = Rep_formula bot"
unfolding xbefore_formula_def tempo1_formula_def 
by (simp add: Abs_formula_inverse dlist_xbefore_idem)

lemma Rep_formula_xbefore_not_sym:
  "\<lbrakk> tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    Rep_formula (xbefore a b) \<subseteq> Rep_formula (-xbefore b a)"
unfolding xbefore_formula_def tempo1_formula_def uminus_formula_def
by (simp add: Abs_formula_inverse 
  dlistset_xbefore_implies_not_sym_dlistset_xbefore)

instance proof
  fix a::"'a formula"
  show "xbefore bot a = bot"
  unfolding eq_formula_iff Rep_formula_xbefore_bot_1 by auto
  next
  fix a::"'a formula"
  show "xbefore a bot = bot"
  unfolding eq_formula_iff Rep_formula_xbefore_bot_2 by auto
  next
  fix a::"'a formula"
  assume "tempo1 a"
  thus "xbefore neutral a = a"
  unfolding eq_formula_iff
  using Rep_formula_xbefore_neutral_1 by auto
  next
  fix a::"'a formula"
  assume "tempo1 a"
  thus "xbefore a neutral = a"
  unfolding eq_formula_iff
  using Rep_formula_xbefore_neutral_2 by auto
  next
  fix a::"'a formula"
  assume "tempo1 a"
  thus "xbefore a a = bot"
  unfolding eq_formula_iff
  using Rep_formula_xbefore_not_idempotent by auto
  next
  fix a::"'a formula" and b::"'a formula"
  assume "tempo1 a" "tempo1 b"
  thus "xbefore a b \<le> - xbefore b a"
  unfolding eq_formula_iff less_eq_formula_def
  using Rep_formula_xbefore_not_sym by simp 
  fix a::"'a formula" and b::"'a formula"
  assume "tempo1 a" "tempo1 b"
  thus "tempo1 (inf a b)"
  unfolding tempo1_formula_def 
  by (simp add: dlist_tempo1_inf Rep_formula_inf)
qed

end

subsubsection {* Associativity of \ac{algebra} *}

instantiation formula :: (type) temporal_faults_algebra_assoc
begin

instance proof
  fix a::"'a formula" and b::"'a formula" and c::"'a formula"
  assume "tempo1 a" "tempo1 b" "tempo1 c"
  thus "xbefore (xbefore a b) c = xbefore a (xbefore b c)"
  unfolding xbefore_formula_def tempo1_formula_def
  by (simp add: Abs_formula_inverse dlist_xbefore_assoc)
qed

end

subsubsection {* Equivalences in \ac{algebra} *}

instantiation formula :: (type) temporal_faults_algebra_equivs
begin

definition 
  "independent_events a b = 
    dlist_independent_events 
      (\<lambda>xs. xs \<in> Rep_formula a) (\<lambda>xs. xs \<in> Rep_formula b)"

definition 
  "tempo2 a = dlist_tempo2 (\<lambda>xs. xs \<in> Rep_formula a)"

definition 
  "tempo3 a = dlist_tempo3 (\<lambda>xs. xs \<in> Rep_formula a)"

definition 
  "tempo4 a = dlist_tempo4 (\<lambda>xs. xs \<in> Rep_formula a)"

instance proof
  fix a::"'a formula" and b::"'a formula"
  assume "tempo1 a" "tempo1 b" 
  thus "inf (xbefore a b) (xbefore b a) = bot"
  unfolding xbefore_formula_def tempo1_formula_def bot_formula_def 
    inf_formula_def
  by (simp add: dlistset_xbefore_and Abs_formula_inverse)
  next
  fix a::"'a formula" and b::"'a formula"
  assume "independent_events a b" "tempo1 a" "tempo1 b" "tempo2 a" "tempo2 b"
    "tempo3 a" "tempo3 b" "tempo4 a" "tempo4 b"
  thus "sup (xbefore a b) (xbefore b a) = inf a b"
  unfolding xbefore_formula_def tempo1_formula_def tempo2_formula_def 
    tempo3_formula_def tempo4_formula_def independent_events_formula_def 
    sup_formula_def inf_formula_def
  by (simp add: dlistset_xbefore_or Abs_formula_inverse)
  next
  fix a::"'a formula" and b::"'a formula"
  assume "tempo2 a" "tempo2 b"
  thus "tempo2 (sup a b)"
  unfolding tempo2_formula_def 
  by (simp add: dlist_tempo2_sup Rep_formula_sup)
  next
  fix a::"'a formula" and b::"'a formula"
  assume "tempo3 a" "tempo3 b"
  thus "tempo3 (inf a b)"
  unfolding tempo3_formula_def
  by (simp add: dlist_tempo3_inf Rep_formula_inf)
  next
  fix a::"'a formula" and b::"'a formula"
  assume "tempo4 a" "tempo4 b"
  thus "tempo4 (sup a b)"
  unfolding tempo4_formula_def 
  by (simp add: dlist_tempo4_sup Rep_formula_sup)
qed

end

subsubsection {* Transitivity in \ac{algebra} *}

instantiation formula :: (type) temporal_faults_algebra_trans
begin
instance proof
  fix a::"'a formula" and b::"'a formula" and c::"'a formula"
  assume "tempo1 a" "tempo1 b" "tempo1 c" "tempo2 a" "tempo2 b" "tempo2 c"
  thus "inf (xbefore a b) (xbefore b c) \<le> xbefore a c"
  unfolding tempo1_formula_def tempo2_formula_def xbefore_formula_def 
    less_eq_formula_def inf_formula_def
  by (simp add: dlistset_xbefore_trans Abs_formula_inverse)
  next
  fix a::"'a formula" and b::"'a formula" and c::"'a formula"
  assume "tempo1 b" "tempo3 b"
  thus "inf (xbefore a b) (xbefore b c) = xbefore (xbefore a b) c"
  unfolding xbefore_formula_def inf_formula_def tempo1_formula_def 
    tempo3_formula_def
  by (simp add: Abs_formula_inverse dlistset_inf_xbefore_trans)
qed
end

subsubsection {* Mixed operators in \ac{algebra} *}

instantiation formula :: (type) temporal_faults_algebra_mixed_ops
begin
instance proof
  fix a::"'a formula" and b::"'a formula" and c::"'a formula"
  show "xbefore (sup a b) c = sup (xbefore a c) (xbefore b c)"
  unfolding xbefore_formula_def sup_formula_def
  by (simp add: mixed_dlistset_xbefore_or1 Abs_formula_inverse)
  next
  fix a::"'a formula" and b::"'a formula" and c::"'a formula"
  show "xbefore a (sup b c) = sup (xbefore a b) (xbefore a c)"
  unfolding xbefore_formula_def sup_formula_def
  by (simp add: mixed_dlistset_xbefore_or2 Abs_formula_inverse)
  next 
  fix a::"'a formula" and b::"'a formula"
  assume "independent_events a b" "tempo1 a" "tempo1 b" "tempo2 a" "tempo2 b"
    "tempo3 a" "tempo3 b" "tempo4 a" "tempo4 b"
  thus "(- xbefore a b) = (sup (sup (- a) (- b)) (xbefore b a))"
  by (simp add: Abs_formula_inverse xbefore_formula_def uminus_formula_def 
    sup_formula_def independent_events_formula_def tempo1_formula_def 
    tempo2_formula_def tempo3_formula_def tempo4_formula_def  
    mixed_not_dlistset_xbefore)
  next
  fix a::"'a formula" and b::"'a formula" and c::"'a formula"
  assume "tempo2 a"
  thus "inf a (xbefore b c) = 
    sup (xbefore (inf a b) c) (xbefore b (inf a c))"
  apply (auto simp add: xbefore_formula_def sup_formula_def inf_formula_def 
    tempo2_formula_def Abs_formula_inverse)
  using and_dlistset_xbefore_equiv_or_dlistset_xbefore Abs_formula_inverse
  by fastforce
  next
  fix a::"'a formula" and b::"'a formula"
  assume "tempo1 a" "tempo2 b"
  thus "xbefore (- a) b = b"
  unfolding xbefore_formula_def tempo1_formula_def tempo2_formula_def
    uminus_formula_def 
  by (auto simp add: Abs_formula_inverse not_1_dlistset_xbefore 
    Rep_formula_inverse)
  next
  fix a::"'a formula" and b::"'a formula"
  assume "tempo1 b" "tempo2 a"
  thus "xbefore a (- b) = a"
  unfolding xbefore_formula_def tempo1_formula_def tempo2_formula_def
    uminus_formula_def 
  by (auto simp add: Abs_formula_inverse not_2_dlistset_xbefore 
    Rep_formula_inverse)
qed
end

subsection {* Equivalence of the new definition of \acs*{XBefore} with the old one *}

definition old_dlist_xbefore
where
"old_dlist_xbefore S T zs \<equiv> 
  (\<exists> xs ys. S xs \<and> \<not> T xs \<and> T ys \<and> \<not> S ys \<and> 
    set (list_of_dlist xs) \<inter> set (list_of_dlist ys) = {} \<and> 
    list_of_dlist zs = (list_of_dlist xs) @ (list_of_dlist ys))"

theorem old_dlist_xbefore_equals_new_xbefore:
  "\<lbrakk> dlist_tempo1 S; dlist_tempo1 T \<rbrakk> \<Longrightarrow> 
    dlist_xbefore S T zs = old_dlist_xbefore S T zs"
unfolding dlist_xbefore_append old_dlist_xbefore_def 
using dlist_tempo_1_no_gap_append
by blast

subsection {* Soundness and completeness on the mapping rules*}

theorem temporal_faults_algebra_mapping_soundness: 
    "\<forall> (f\<^sub>1::'a formula) (f\<^sub>2::'a formula). \<exists> S. ((Rep_formula f\<^sub>1 = S \<and> Rep_formula f\<^sub>2 = S) \<longleftrightarrow> f\<^sub>1 = f\<^sub>2)"
by blast

theorem temporal_faults_algebra_mapping_completeness: 
    "\<forall> (S::'a dlist set). \<exists> f::'a formula. Rep_formula f = S"
using Abs_formula_inverse by auto

subsection {* Syntax for the Algebra of Temporal Faults *}

datatype 'a formula_exp =
  tFalse | 
  tTrue |
  tNeutral |
  tVar 'a |
  tOR "'a formula_exp" "'a formula_exp" | 
  tAND "'a formula_exp" "'a formula_exp" |
  tNOT "'a formula_exp" | 
  tXB "'a formula_exp" "'a formula_exp" |
  tDIFF "'a formula_exp" "'a formula_exp"

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
  "formula_exp_to_formula (tXB a b) = (xbefore (formula_exp_to_formula a) (formula_exp_to_formula b))" |
  "formula_exp_to_formula (tDIFF a b) = 
    Abs_formula 
    ((Rep_formula (formula_exp_to_formula a)) - 
    (Rep_formula (formula_exp_to_formula b)))"
(* TODO rever a forma normal
fun formula_exp_to_NF :: "'a formula_exp \<Rightarrow> 'a formula_exp" where
  "formula_exp_to_NF f = f"
*)

abbreviation eval where "eval \<equiv> formula_exp_to_formula"

abbreviation empty_list_formula_exp :: "'a set \<Rightarrow> 'a formula_exp" where
  "empty_list_formula_exp V \<equiv> tNOT (Finite_Set.fold (\<lambda> x f\<^sub>2 . tOR (tVar x) f\<^sub>2) tFalse V)"

primrec list_to_formula_exp :: "'a list \<Rightarrow> 'a formula_exp" where
 "list_to_formula_exp [] = (empty_list_formula_exp UNIV)" |
 "list_to_formula_exp (x # xs) = tXB (tVar x) (list_to_formula_exp xs)"

abbreviation dlist_to_formula_exp  where
  "dlist_to_formula_exp dl \<equiv> list_to_formula_exp (list_of_dlist dl)"

abbreviation dlist_set_to_formula_exp where
  "dlist_set_to_formula_exp Dls \<equiv> Finite_Set.fold (\<lambda> dl f\<^sub>2 . tOR (dlist_to_formula_exp dl) f\<^sub>2  ) tFalse Dls"

abbreviation formula_to_formula_exp where
  "formula_to_formula_exp f \<equiv> dlist_set_to_formula_exp (Rep_formula f)"

typedef 'a formula_syn = "UNIV::'a formula_exp set" by simp

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
  "x - y = Abs_formula_syn (tDIFF (Rep_formula_syn x)  (Rep_formula_syn y))"

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
  "Rep_formula_syn (x - y) = tDIFF (Rep_formula_syn x) (Rep_formula_syn y)"
unfolding minus_formula_syn_def
by (simp add: Abs_formula_syn_inverse)

lemmas eq_formula_syn_iff = Rep_formula_syn_inject [symmetric]

lemmas Rep_formula_syn_boolean_algebra_simps =
  less_eq_formula_syn_def less_formula_syn_def eq_formula_syn_iff
  Rep_formula_syn_sup Rep_formula_syn_inf Rep_formula_syn_top 
  Rep_formula_syn_bot Rep_formula_syn_compl Rep_formula_syn_diff 
  
instance proof
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
inductive_set
  formula_syn :: "'a set \<Rightarrow> 'a formula_exp set"
  for "V"
where 
  "tFalse \<in> formula_syn V" |
  "a \<in> V \<Longrightarrow> tVar a \<in> formula_syn V" |
  "f \<in> formula_syn V \<Longrightarrow> tNOT f \<in> formula_syn V" |
  "\<lbrakk> f\<^sub>1 \<in> formula_syn V; f\<^sub>2 \<in> formula_syn V \<rbrakk> \<Longrightarrow> tOR f\<^sub>1 f\<^sub>2 \<in> formula_syn V" |
  "\<lbrakk> f\<^sub>1 \<in> formula_syn V; f\<^sub>2 \<in> formula_syn V \<rbrakk> \<Longrightarrow> tXB f\<^sub>1 f\<^sub>2 \<in> formula_syn V" 

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

lemma "tautology (tOR 
  (tNOT (tVar MyVarA))
  (tOR 
    (tNOT (tVar MyVarB))
    (tOR (tXB (tVar MyVarA) (tVar MyVarB)) (tXB (tVar MyVarB) (tVar MyVarA)))))"
proof-
  have 0: "MyVarA \<noteq> MyVarB" by simp
  hence "eval (tOR (tXB (tVar MyVarA) (tVar MyVarB)) (tXB (tVar MyVarB) (tVar  
    MyVarA))) = eval (tAND (tVar MyVarA) (tVar MyVarB))"
    using eval_xbefore_sup_equiv_inf by force
  hence "eval (tOR 
    (tNOT (tVar MyVarA))
    (tOR 
      (tNOT (tVar MyVarB))
      (tOR (tXB (tVar MyVarA) (tVar MyVarB)) 
        (tXB (tVar MyVarB) (tVar MyVarA))))) =
    eval (tOR 
    (tNOT (tVar MyVarA))
    (tOR 
      (tNOT (tVar MyVarB))
      (tAND (tVar MyVarA) (tVar MyVarB))))" by simp
  thus ?thesis using 0 unfolding tautology_def

proof-
  have "tempo1 (eval (tVar MyVarA))" "tempo2 (eval (tVar MyVarA))"
    "tempo3 (eval (tVar MyVarA))" "tempo4 (eval (tVar MyVarA))"
    "tempo1 (eval (tVar MyVarB))" "tempo2 (eval (tVar MyVarB))"
    "tempo3 (eval (tVar MyVarB))" "tempo4 (eval (tVar MyVarB))"
    "independent_events (eval (tVar MyVarA)) (eval (tVar MyVarB))"
    using tempo_eval_tVar independent_events_eval_tVar by fastforce+
  hence "eval (tOR (tXB (tVar MyVarA) (tVar MyVarB)) (tXB (tVar MyVarB) (tVar MyVarA))) =
    eval (tAND (tVar MyVarA) (tVar MyVarB))"
    "sup 
      (eval (tOR (tNOT (tVar MyVarA)) (tNOT (tVar MyVarB))))
      (eval (tAND (tVar MyVarA) (tVar MyVarB))) = top"
    apply (simp add: xbefore_sup_equiv_inf)
    by (metis compl_inf compl_sup_top formula_exp_to_formula.simps(4) 
      formula_exp_to_formula.simps(5) formula_exp_to_formula.simps(6))
  hence "eval (tOR 
    (tNOT (tVar MyVarA))
    (tOR 
      (tNOT (tVar MyVarB))
      (tOR (tXB (tVar MyVarA) (tVar MyVarB)) (tXB (tVar MyVarB) (tVar MyVarA))))) =
    top"
    by (simp add: sup_assoc)
  thus ?thesis unfolding tautology_def by simp
qed


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


definition formulas ::"'a set \<Rightarrow> 'a formula set" where
  "formulas V = { f. \<forall> dl\<^sub>1 dl\<^sub>2 . 
    (\<forall>v\<in>V. dlist_index_of dl\<^sub>1 v = dlist_index_of dl\<^sub>2 v) \<longrightarrow>
    dl\<^sub>1 \<in> Rep_formula f \<longleftrightarrow> dl\<^sub>2 \<in> Rep_formula f }"
(*  
  "formulas V = { f. \<forall> dl\<^sub>1 dl\<^sub>2 . (\<forall>v\<in>V. Dlist.member dl\<^sub>1 v \<longleftrightarrow> Dlist.member dl\<^sub>2 v) \<longrightarrow>
    dl\<^sub>1 \<in> Rep_formula f \<longleftrightarrow> dl\<^sub>2 \<in> Rep_formula f }"
*)

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

lemma formulas_xbefore: "\<lbrakk> f\<^sub>1 \<in> formulas V; f\<^sub>2 \<in> formulas V \<rbrakk> \<Longrightarrow> 
  xbefore f\<^sub>1 f\<^sub>2 \<in> formulas V"
unfolding formulas_def 
apply (simp add: formulas_def Rep_formula_xbefore_to_dlist_xbefore dlist_xbefore_def)

apply (simp add: slice_left_def slice_right_def slice_dlist_def size_dlist_def 
  )




lemma finite_formula : "finite V \<Longrightarrow> finite (formulas V)"



theorem soundness: 
  "\<forall> V. finite V \<and> fexp \<in> formula_syn V \<longrightarrow> formula_exp_to_formula fexp \<in> formulas V"
apply (induct fexp)
apply (simp add: formulas_bot)
apply (metis formula_exp.distinct(1) formula_exp.distinct(11) formula_exp.distinct(13) 
  formula_exp.distinct(9) formula_exp_to_formula.simps(2) formula_syn.simps formulas_var)
apply (metis formula_exp.distinct(15) formula_exp.distinct(17) formula_exp.distinct(3) 
  formula_exp.distinct(9) formula_exp.inject(2) formula_exp_to_formula.simps(3) formula_syn.simps formulas_sup)
apply (metis formula_exp.distinct(11) formula_exp.distinct(15) formula_exp.distinct(19) 
  formula_exp.distinct(5) formula_exp.inject(3) formula_exp_to_formula.simps(4) 
  formula_syn.simps formulas_compl)
by (metis formula_exp.distinct(13) formula_exp.distinct(17) formula_exp.distinct(19) formula_exp.distinct(7) formula_exp.inject(4) formula_exp_to_formula.simps(5) formula_syn.simps formulas_xbefore)

lemma completeness_tNOT:
  "finite V \<Longrightarrow> - f \<in> formulas V \<Longrightarrow> tNOT (formula_to_formula_exp f) \<in> formula_syn V"
sorry

theorem completeness: 
  "\<forall> V. finite V \<and> fsem \<in> formulas V \<longrightarrow> formula_to_formula_exp fsem \<in> formula_syn V"
by (metis completeness_tNOT formula_exp.distinct(11) formula_exp.distinct(15) 
  formula_exp.distinct(19) formula_exp.distinct(5) formula_exp.inject(3) formula_syn.cases 
  formulas_compl)



(*<*)
end
(*>*)
