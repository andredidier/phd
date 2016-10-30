theory Dlist_finiteness

imports Main 
  "~~/src/HOL/Library/Dlist"
begin
(*TODO
lemma finite_dlists_length_le: 
  "finite A \<Longrightarrow> finite { dl. set (list_of_dlist dl) \<subseteq> A \<and> Dlist.length dl \<le> n }"
using  finite_lists_length_le Dlist.length_def 
sorry
*)

definition dlists :: "'a set \<Rightarrow> 'a dlist set" where
  "dlists A \<equiv> { dl . Dlist.set dl \<subseteq> A  }"

definition lists_of_dlists :: "'a dlist set \<Rightarrow> 'a list set" where
  "lists_of_dlists dls \<equiv> { list_of_dlist dl | dl . dl \<in> dls  }"

definition dlists_of_lists :: "'a list set \<Rightarrow> 'a dlist set" where
  "dlists_of_lists ls \<equiv> { dlist_of_list l | l . distinct l \<and> l \<in> ls  }"

lemma dlists_lists_equiv: "lists_of_dlists (dlists_of_lists ls) = ls"
  "dlists_of_lists (lists_of_dlists dls) = dls"

lemma finite_lists_finite_distincts: "finite {xs. P xs} \<Longrightarrow> finite {xs. distinct xs \<and> P xs}"
by auto

lemma distinct_list_limit: "\<lbrakk> finite A; distinct l; set l \<subseteq> A \<rbrakk> \<Longrightarrow> length l \<le> card A"
by (metis card_mono distinct_card)

lemma dlist_limit: "\<lbrakk> finite A; Dlist.set dl \<subseteq> A \<rbrakk> \<Longrightarrow> Dlist.length dl \<le> card A"
by (simp add: Dlist.length_def distinct_list_limit set.rep_eq)

lemma distinct_list_finiteness: "finite A \<Longrightarrow> finite { l. distinct l \<and> set l \<subseteq> A }"
proof-
  assume 0: "finite A"
  hence "finite { l. set l \<subseteq> A \<and> length l \<le> card A }" by (simp add: finite_lists_length_le) 
  hence "finite { l. distinct l \<and> set l \<subseteq> A \<and> length l \<le> card A }" 
    using finite_lists_finite_distincts by simp
  hence "finite { l. distinct l \<and> set l \<subseteq> A \<and> length l \<le> card A }" 
    using finite_lists_finite_distincts by simp
  thus ?thesis using 0 distinct_list_limit by (metis (no_types, lifting) Collect_cong) 
qed

lemma dlists_finiteness_1: "finite A \<Longrightarrow> finite { list_of_dlist dl | dl. Dlist.set dl \<subseteq> A }"
proof-
  have 0: "{ list_of_dlist dl | dl. Dlist.set dl \<subseteq> A } = { l. distinct l \<and> set l \<subseteq> A }"
    by (metis distinct_list_of_dlist list_of_dlist_Dlist remdups_id_iff_distinct set.rep_eq) 
  have 1: "{ dl . Dlist.set dl \<subseteq> A } = { dl. distinct (list_of_dlist dl) \<and> set (list_of_dlist dl) \<subseteq> A }"
    by (simp add: set.rep_eq)
  assume 1: "finite A"
  hence "finite { l. distinct l \<and> set l \<subseteq> A }" by (simp add: distinct_list_finiteness)
  thus ?thesis by (simp add: "0") 
qed

lemma list_of_dlist_pred: 
  "{list_of_dlist dl | dl. P (list_of_dlist dl)} = { l. distinct l \<and> P l }"
  "{ dl . P (list_of_dlist dl) } = { dlist_of_list l | l. distinct l \<and> P l }"
  "distinct l \<and> P l \<Longrightarrow> \<exists> dl. dl = dlist_of_list l \<and> P (list_of_dlist dl)"
apply (metis distinct_list_of_dlist list_of_dlist_Dlist remdups_id_iff_distinct)
apply (metis Dlist_list_of_dlist dlist_of_list list_of_dlist_Dlist remdups_id_iff_distinct)
by (metis dlist_of_list list_of_dlist_Dlist remdups_id_iff_distinct)

lemma "P ls \<Longrightarrow> \<exists> dls. dls = dlists_of_lists ls \<and> P (lists_of_dlists dls)"

lemma dlists_finiteness: "finite A \<Longrightarrow> finite { dl. Dlist.set dl \<subseteq> A }"
proof-
  assume "finite A"
  hence "finite { list_of_dlist dl | dl. Dlist.set dl \<subseteq> A }" using dlists_finiteness_1 by blast 
  hence "finite {}"
qed

lemma "{ list_of_dlist dl | dl. Dlist.set dl \<subseteq> A } \<subseteq> lists A"
using set.rep_eq by fastforce



lemma dlist_limit: "\<lbrakk> finite A; set (list_of_dlist dl) \<subseteq> A \<rbrakk> \<Longrightarrow> Dlist.length dl \<le> card A"
by (metis card_mono distinct_card distinct_list_of_dlist Dlist.length_def)

inductive_set
  dlists :: "'a set \<Rightarrow> 'a list set"
  for A :: "'a set"
where
  Nil [intro!, simp]: "[] \<in> dlists A" | 
  Cons [intro!, simp]: "\<lbrakk> a \<in> A; dl \<in> dlists A; a \<notin> set dl \<rbrakk> \<Longrightarrow> a # dl \<in> dlists A"

lemma dlists_subseteq_lists: "dlists A \<subseteq> lists A"



lemma dlists_distinct: "l \<in> dlists A \<Longrightarrow> distinct l"
apply (induct l)
apply simp
by (metis (no_types) distinct.simps(2) dlists.cases list.distinct(2) list.inject)

lemma dlists_empty_set: "dlists {} = {[]}"
using dlists.simps by blast

lemma dlists_singleton_aux: "\<forall>x \<in> dlists {a} . x = [] \<or> x = [a]"
using dlists.simps
by (metis list.set_intros(1) singletonD)

lemma dlists_singleton: "dlists {a} = {[], [a]}"
by (simp add: dlists_singleton_aux subsetI subset_antisym)

lemma singleton_list_in_dlists: "n \<in> A \<Longrightarrow> [n] \<in> dlists A"
by simp

lemma singleton_subseteq: "n \<in> A \<Longrightarrow> dlists {n} \<subseteq> dlists A"
unfolding dlists_singleton
by simp

lemma "n \<in> A \<Longrightarrow> \<forall>l \<in> dlists A. (remove1 n l) \<in> dlists A"


(*
lemma dlists_insert_remove1: "\<lbrakk> l \<in> dlists (insert n A); n \<notin> set l \<rbrakk> \<Longrightarrow> remove1 n l \<in> dlists A"
apply (induct l)
apply simp
by (metis dlists.simps insertE list.inject list.set_intros(2) remove1.simps(2) remove1_idem)

lemma dlists_insert_remove2: "\<lbrakk> l \<in> dlists (insert n A); n \<in> set l \<rbrakk> \<Longrightarrow> remove1 n l \<in> dlists A"
apply (induct l)
apply simp
by (metis dlists.simps dlists_insert_remove1 in_set_remove1 insertE list.distinct(1) list.inject 
  remove1.simps(2) remove1_idem)

lemma dlists_insert_remove: "l \<in> dlists (insert n A) \<Longrightarrow> remove1 n l \<in> dlists A"
by (meson dlists_insert_remove1 dlists_insert_remove2)
*)

lemma dlists_insert_partition: "dlists (insert n A) = dlists {n} \<union> dlists A \<union> 
  { l. set l \<subseteq> insert n A \<and> remove1 n l \<in> dlists A }"
proof (cases "n \<in> A")
  case True
  show ?thesis 
qed


definition dlists_insert:: "'a \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
  "dlists_insert n A \<equiv> { l. l \<in> dlists (insert n A) \<and> n \<in> set l \<longrightarrow> (remove1 n l) \<in> dlists A }"

lemma finite_dlists_insert: "finite A \<Longrightarrow> finite (dlists_insert n A)"
unfolding dlists_insert_def
sorry

lemma dlists_insert_equiv: "dlists_insert n A = dlists (insert n A)"
unfolding dlists_insert_def
using dlists_insert_remove
sorry

lemma dlists_insert_finite: "finite (dlists_insert n1 (insert n2 A)) \<Longrightarrow> finite (dlists_insert n1 A)"
unfolding dlists_insert_def
by (simp add: dlists_insert_remove2)

lemma dlists_insert_finite_2: "finite (dlists (insert n1 (insert n2 A))) \<Longrightarrow> finite (dlists (insert n1 A))"
using dlists_insert_equiv
by (metis dlists_insert_finite)

lemma finite_dlist_set: "finite A \<Longrightarrow> finite (dlists A)"
proof-
  fix n1 n2
  assume 0: "finite A"
  hence "finite (insert n1 (insert n2 A))" by simp
  hence "finite (dlists_insert n1 (insert n2 A))" by (simp add: finite_dlists_insert)
  hence "finite (dlists (insert n1 (insert n2 A)))" by (simp add: dlists_insert_equiv)
  hence "finite (dlists (insert n1 A))" by (meson dlists_insert_finite_2) 
  thus ?thesis using 0
  by (metis Zero_neq_Suc card.insert card_eq_0_iff dlists_empty_set dlists_insert_finite_2 
    empty_iff finite.cases finite.emptyI insert_commute)
qed



(*
proof-
  assume 1: "finite A"
  hence "finite { dl. Dlist.set dl \<subseteq> A \<and> Dlist.length dl \<le> card A }" 
    using 1 finite_dlists_length_le by blast
  thus ?thesis using 1
    by (metis (mono_tags, lifting) Collect_cong dlist_limit) 
qed
*)

end