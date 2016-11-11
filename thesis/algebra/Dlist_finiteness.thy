theory Dlist_finiteness

imports Main Enum
  "~~/src/HOL/Library/Dlist"
begin




(*TODO
lemma finite_dlists_length_le: 
  "finite A \<Longrightarrow> finite { dl. set (list_of_dlist dl) \<subseteq> A \<and> Dlist.length dl \<le> n }"
using  finite_lists_length_le Dlist.length_def 
sorry
*)

(*
definition
  formulas :: "'a set \<Rightarrow> 'a formula set"
where
  "formulas S =
    {x. \<forall>A B. (\<forall>i\<in>S. i \<in> A \<longleftrightarrow> i \<in> B) \<longrightarrow>
      A \<in> Rep_formula x \<longleftrightarrow> B \<in> Rep_formula x}"
*)


definition dlists2_pred :: "'a set \<Rightarrow> 'a dlist \<Rightarrow> bool" where
  "dlists2_pred A dl = (\<forall>X. (Dlist.set dl \<subseteq> X \<longrightarrow> X \<subseteq> A) \<longleftrightarrow> (Dlist.set dl \<subseteq> A ))"
(*
  "dlists2_pred A dl = (Dlist.set dl \<subseteq> A)"
*)
(*
  "dlists2_pred A dl = (\<forall> X Y. (\<forall> a \<in> A. a \<in> X \<longleftrightarrow> a \<in> Y) \<longrightarrow> 
      Dlist.set dl \<subseteq> X \<longleftrightarrow> Dlist.set dl \<subseteq> Y)"
*)

definition dlists2 :: "'a set \<Rightarrow> 'a dlist set" where
  "dlists2 A \<equiv> Collect (dlists2_pred A)"

lemma "dlists2_pred A dl \<Longrightarrow> Dlist.set dl \<subseteq> A"
by (auto simp add: dlists2_pred_def)
(*
lemma "\<not> dlists2_pred A dl \<Longrightarrow> Dlist.set dl \<subseteq> A"
by (auto simp add: dlists2_pred_def)
*)

definition dlists :: "'a set \<Rightarrow> 'a dlist set" where
  "dlists A \<equiv> { dl . Dlist.set dl \<subseteq> A  }"

(*
lemma "dls \<subseteq> dlists2 A \<Longrightarrow> -dls \<subseteq> dlists2 A"
unfolding dlists2_def
apply auto
*)

definition lists_of_dlists :: "'a dlist set \<Rightarrow> 'a list set" where
  "lists_of_dlists dls \<equiv> { list_of_dlist dl | dl . dl \<in> dls  }"

definition dlists_of_lists :: "'a list set \<Rightarrow> 'a dlist set" where
  "dlists_of_lists ls \<equiv> { dlist_of_list l | l . distinct l \<and> l \<in> ls  }"

lemma dlists_all_distinct: "\<forall>dl \<in> dlists_of_lists ls. distinct (list_of_dlist l)"
by simp


lemma lists_and_dlists_belongs: 
  "l \<in> lists_of_dlists dls \<Longrightarrow> distinct l \<and> dlist_of_list l \<in> dls"
  "distinct l \<and> dlist_of_list l \<in> dls \<Longrightarrow> l \<in> lists_of_dlists dls"
  "\<lbrakk> \<forall>l \<in> ls. distinct l ; dl \<in> dlists_of_lists ls \<rbrakk> \<Longrightarrow> list_of_dlist dl \<in> ls"
  "\<lbrakk> \<forall>l \<in> ls. distinct l ; list_of_dlist dl \<in> ls \<rbrakk> \<Longrightarrow> dl \<in> dlists_of_lists ls"
unfolding lists_of_dlists_def dlists_of_lists_def
apply auto
apply (metis list_of_dlist_Dlist remdups_id_iff_distinct)
apply (metis remdups_id_iff_distinct)
by force

lemma lists_and_dlists_inverse: 
  "\<lbrakk> \<forall>l \<in> ls. distinct l; l \<in> lists_of_dlists (dlists_of_lists ls) \<rbrakk> \<Longrightarrow> l \<in> ls"
  "dl \<in> dlists_of_lists (lists_of_dlists dls) \<Longrightarrow> dl \<in> dls"
apply (metis dlist_of_list list_of_dlist_Dlist lists_and_dlists_belongs(1) 
  lists_and_dlists_belongs(3) remdups_id_iff_distinct)
by (metis Dlist_list_of_dlist dlist_of_list lists_and_dlists_belongs(1) 
  lists_and_dlists_belongs(3))

lemma lists_and_dlists_equiv_1: 
  "dlists_of_lists (lists_of_dlists dls) = dls"
proof-
   have "dlists_of_lists (lists_of_dlists dls) =
    { dlist_of_list l | l. distinct l \<and> l \<in> lists_of_dlists dls}"
    unfolding dlists_of_lists_def  by simp
  moreover have "... = { dlist_of_list l | l. dlist_of_list l \<in> dls}"
    by (metis Dlist_list_of_dlist distinct_list_of_dlist dlist_of_list 
       lists_and_dlists_belongs(1) lists_and_dlists_belongs(2))
  moreover have "... = { dl . dl \<in> dls }" by (metis Dlist_list_of_dlist dlist_of_list) 
  ultimately show ?thesis by simp
qed

lemma lists_and_dlists_equiv_2: 
  "\<forall>l \<in> ls. distinct l \<Longrightarrow> lists_of_dlists (dlists_of_lists ls) = ls"
proof-
  assume "\<forall>l \<in> ls. distinct l"
  moreover have "lists_of_dlists (dlists_of_lists ls) = 
    { list_of_dlist dl | dl . dl \<in> dlists_of_lists ls }"
    unfolding dlists_of_lists_def lists_of_dlists_def by simp+
  moreover have "... = { list_of_dlist dl | dl . list_of_dlist dl \<in> ls  }"
    by (meson calculation(1) lists_and_dlists_belongs(3) lists_and_dlists_belongs(4))
  moreover have "... = { l . l \<in> ls }"
    by (metis Abs_dlist_inverse CollectI calculation(1))  
  ultimately show ?thesis by simp
qed

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

lemma dlists_finiteness_2: "finite A \<Longrightarrow> finite (lists_of_dlists (dlists A))"
proof-
  assume "finite A"
  moreover hence "finite { list_of_dlist dl | dl. Dlist.set dl \<subseteq> A }" 
    by (simp add: dlists_finiteness_1)
  moreover hence "finite { list_of_dlist dl | dl. dl \<in> { dl . Dlist.set dl \<subseteq> A } }"
    using CollectD CollectI Collect_cong by auto
  thus ?thesis by (simp add: dlists_def lists_of_dlists_def)
qed

lemma list_of_dlist_pred: 
  "{list_of_dlist dl | dl. P (list_of_dlist dl)} = { l. distinct l \<and> P l }"
  "{ dl . P (list_of_dlist dl) } = { dlist_of_list l | l. distinct l \<and> P l }"
  "distinct l \<and> P l \<Longrightarrow> \<exists> dl. dl = dlist_of_list l \<and> P (list_of_dlist dl)"
apply (metis distinct_list_of_dlist list_of_dlist_Dlist remdups_id_iff_distinct)
apply (metis Dlist_list_of_dlist dlist_of_list list_of_dlist_Dlist remdups_id_iff_distinct)
by (metis dlist_of_list list_of_dlist_Dlist remdups_id_iff_distinct)

lemma lists_and_dlists_equiv_pred: 
  "\<lbrakk> P ls ; \<forall> l\<in>ls. distinct l \<rbrakk> \<Longrightarrow> P (lists_of_dlists (dlists_of_lists ls))"
by (simp add: lists_and_dlists_equiv_2)

(* { l. distinct l \<and> set l \<subseteq> A } *)

lemma finite_over_pred_lists_and_dlists:
  "finite { l . distinct l \<and> P l } \<Longrightarrow> finite { dl . P (list_of_dlist dl) }"
by (simp add: list_of_dlist_pred(2))

lemma dlists_finiteness: "finite A \<Longrightarrow> finite (dlists A)"
proof-
  obtain P where 1: "P = (\<lambda>l. set l \<subseteq> A)" by simp
  assume 0: "finite A"
  hence "finite { l. distinct l \<and> P l }" by (simp add: 1 distinct_list_finiteness)
  hence "finite { dl . P (list_of_dlist dl) }" using finite_over_pred_lists_and_dlists by blast
  hence "finite { dl . Dlist.set dl \<subseteq> A }" by (metis "1" Collect_cong set.rep_eq)
  thus ?thesis by (simp add: dlists_def)  
qed

lemma dlists_in_lists: "dlists A \<subseteq> dlists_of_lists (lists A)"
by (smt Dlist_list_of_dlist distinct_list_of_dlist dlist_of_list dlists_def dlists_of_lists_def 
  lists_eq_set mem_Collect_eq set.rep_eq subsetI)

lemma lists_in_dlists: "\<forall>l \<in> lists A. distinct l \<Longrightarrow> dlists_of_lists (lists A) \<subseteq> dlists A"
by (smt Collect_mono dlist_of_list dlists_def dlists_of_lists_def in_listsD list_of_dlist_Dlist 
  remdups_id_iff_distinct set.rep_eq subsetI)

lemma lists_equiv_dlists: "\<forall>l \<in> lists A. distinct l \<Longrightarrow> dlists_of_lists (lists A) = dlists A"
by (simp add: dlists_in_lists eq_iff lists_in_dlists)

lemma dlists_empty_set: "dlists {} = dlists_of_lists {[]}"
by (metis distinct.simps(1) lists_empty lists_equiv_dlists singletonD)

lemma singleton_in_lists_singleton: "[a] \<in> lists {a}"
by simp

(*
lemma dlists_singleton: "dlists {a} = dlists_of_lists {[], [a]}"
proof-
  have 0: "\<forall>l \<in> {[], [a]}. distinct l" by auto 
  hence "\<forall>x \<in> dlists {a} . x = (dlist_of_list []) \<or> x = (dlist_of_list [a])" sorry
  thus ?thesis 
qed


lemma singleton_list_in_dlists: "n \<in> A \<Longrightarrow> [n] \<in> dlists A"
by simp

lemma singleton_subseteq: "n \<in> A \<Longrightarrow> dlists {n} \<subseteq> dlists A"
unfolding dlists_singleton
by simp

lemma "n \<in> A \<Longrightarrow> \<forall>l \<in> dlists A. (remove1 n l) \<in> dlists A"

*)

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

(*
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
*)


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