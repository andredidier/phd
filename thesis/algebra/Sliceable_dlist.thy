section {* Sliceable distinct lists *}
text {* \label{sec:theory-sliceable-dlist}*}

(*<*)
theory Sliceable_dlist

imports 
  Sliceable
  "~~/src/HOL/Library/Dlist"

begin
(*>*)

(*<*)
lemma take1_drop_nth: "i < length xs \<Longrightarrow> take 1 (drop i xs) = [xs!i]"
by (simp add: take_Suc_conv_app_nth)

lemma "(\<forall>i. xs!i = ys!i) \<and> length xs = length ys \<longleftrightarrow> xs = ys"
using list_eq_iff_nth_eq
by blast
(*>*)

text {* The following is the instantiation of the sliceable class for the dlist type. *}

instantiation dlist :: (type) sliceable
begin

definition
  "l\<dagger>i..f = Dlist (take (max 0 (f-i)) (drop i (list_of_dlist l)))"

definition 
  "size l = length (list_of_dlist l)"

definition
  "empty_inter l k = 
  ((set (list_of_dlist l)) \<inter> (set (list_of_dlist k)) = {})"

definition
  "disjoint l = distinct (list_of_dlist l)"

lemma list_of_dlist_slice : 
  "list_of_dlist (l\<dagger>i..f) = take (max 0 (f-i)) (drop i (list_of_dlist l))"
unfolding slice_dlist_def 
by simp

lemma Dlist_slice_inverse : 
  "list_of_dlist (Dlist (take (max 0 (c-i)) (drop i (list_of_dlist x)))) 
  = (take (max 0 (c-i)) (drop i (list_of_dlist x)))"
by simp

lemma Dlist_empty_seq_inter: "c \<le> k \<Longrightarrow> 
  (
  set (take c (list_of_dlist x)) \<inter>
  set (drop k (list_of_dlist x))
  ) = {}"
by (simp add: set_take_disj_set_drop_if_distinct)

lemma Dlist_forall_slice_eq1: 
  "(\<forall>i f. (Dlist (take (max 0 (f-i)) (drop i (list_of_dlist l1))) = 
  Dlist (take (max 0 (f-i)) (drop i (list_of_dlist l2))))) \<Longrightarrow> 
  l1 = l2"
by (metis (mono_tags, hide_lams) Dlist_list_of_dlist 
  Sliceable_dlist.list_of_dlist_slice drop_0 drop_take max_0L take_equalityI)

lemma Dlist_forall_slice_eq: 
  "l1 = l2 \<longleftrightarrow>  
  (\<forall>i f. (Dlist (take (max 0 (f-i)) (drop i (list_of_dlist l1))) = 
  Dlist (take (max 0 (f-i)) (drop i (list_of_dlist l2)))))"
using Dlist_forall_slice_eq1 by blast

lemma distinct_list_take_1_uniqueness:
  "distinct l \<Longrightarrow> i\<noteq>j \<Longrightarrow> i < length l \<Longrightarrow> j < length l \<Longrightarrow>
    take 1 (drop i l) \<noteq> take 1 (drop j l)"
by (simp add: hd_drop_conv_nth nth_eq_iff_index_eq take_Suc)

lemmas list_of_dlist_simps = slice_left_def slice_right_def slice_dlist_def 
  size_dlist_def disjoint_dlist_def empty_inter_dlist_def Dlist_slice_inverse 

instance proof
  fix l::"'a dlist"
  show "l\<dagger>0..(#l) = l" by (simp add: dlist_eqI list_of_dlist_slice size_dlist_def) 
  fix l::"'a dlist"
  show "disjoint l" by (simp add: disjoint_dlist_def)
  next
  fix l::"'a dlist" and c::nat and k
  assume "c \<le> k"
  thus "empty_inter (l\<dagger>0..c) (l\<dagger>k..(#l))" 
  by (simp add: size_dlist_def empty_inter_dlist_def 
    set_take_disj_set_drop_if_distinct list_of_dlist_slice )
  next
  fix l::"'a dlist" and i and j and a and b 
  show "size (l\<dagger>i..j) = max 0 (min j (#l) - i)"
  proof (cases "j \<le> #l")
    case True
    assume "j \<le> #l"
    thus ?thesis
      by (metis (no_types, hide_lams) list_of_dlist_simps(7) size_dlist_def 
        drop_take length_drop length_take list_of_dlist_simps(3) max_0L 
        min.commute) 
    next
    case False
    assume "\<not> (j \<le> #l)"
    hence "j > #l" by simp
    thus ?thesis 
      by (metis (no_types, lifting) list_of_dlist_simps(3) 
        list_of_dlist_simps(7) size_dlist_def length_drop length_take max_0L 
        min.commute min_diff)
  qed
  next
  fix l::"'a dlist" and i and j and a and b
  show "(l\<dagger>i..j)\<dagger>a..b = l\<dagger>(i + a)..(min j (i + b))"
    proof -
      have f1: "\<forall>n. max (0::nat) n = n"
        by (meson max_0L)
      hence "take b (take (max 0 (j - i)) (drop i (list_of_dlist l))) = drop i (take (i + b) (take j (list_of_dlist l)))"
        by (metis (no_types) diff_add_inverse drop_take)
      hence "take (max 0 (b - a)) (drop a (list_of_dlist (l\<dagger>i..j))) = drop a (drop i (take (min (i + b) j) (list_of_dlist l)))"
        using f1 by (metis Sliceable_dlist.list_of_dlist_slice drop_take take_take)
      thus ?thesis
        using f1 by (metis (no_types) add.commute drop_drop drop_take list_of_dlist_simps(3) min.commute)
    qed
  next
  fix l::"'a dlist" and i and j
  assume "disjoint l" "i\<noteq>j" "i < (#l)" "j < (#l)"
  hence "take 1 (drop i (list_of_dlist l)) \<noteq> 
    take 1 (drop j (list_of_dlist l))"
    using distinct_list_take_1_uniqueness size_dlist_def by auto
  hence "take (Suc i - i) (drop i (list_of_dlist l)) \<noteq> 
    take (Suc j - j) (drop j (list_of_dlist l))"
    by simp
  hence "take (max 0 (Suc i - i)) (drop i (list_of_dlist l)) \<noteq> 
    take (max 0 (Suc j - j)) (drop j (list_of_dlist l))"
    by simp
  thus "l\<dagger>i..Suc i \<noteq> l\<dagger>j..Suc j" 
  by (metis list_of_dlist_slice)
  next
  fix l1::"'a dlist" and l2::"'a dlist"
  show "(#l1) = (#l2) \<and> (\<forall>i j. l1\<dagger>i..j = l2\<dagger>i..j) \<longleftrightarrow> (l1 = l2)" 
    using Dlist_forall_slice_eq
    by (metis Sliceable_dlist.list_of_dlist_slice)
qed

end

subsection {* Properties of sliceable distinct lists *}

text {* In the following we present lemmas, corollaries and theorems about sliceable distinct lists.*}

abbreviation dlist_nth :: "'a dlist \<Rightarrow> nat \<Rightarrow> 'a"
where
"dlist_nth l i \<equiv> (list_of_dlist (sliceable_nth l i))!0"

theorem set_slice : 
  "set (list_of_dlist l) = 
    set (list_of_dlist (l\<dagger>..i)) \<union> set (list_of_dlist (l\<dagger>i..))"
unfolding slice_dlist_def slice_right_def slice_left_def size_dlist_def
apply (simp add: list_of_dlist_inject)
by (metis append_take_drop_id set_append)

theorem take_slice_right: "take n (list_of_dlist l) = list_of_dlist (l\<dagger>..n)"
unfolding slice_right_def slice_dlist_def 
by (metis Dlist_slice_inverse drop_0 max_0L minus_nat.diff_0)

theorem slice_right_cons: "distinct (x # xs) \<Longrightarrow> 
  (Dlist (x # xs))\<dagger>..(Suc n) = Dlist (x # (list_of_dlist ((Dlist xs)\<dagger>..n)))"
unfolding slice_right_def slice_dlist_def
by (simp add: distinct_remdups_id)

theorem slice_append: 
  "\<forall>n. Dlist ((list_of_dlist (l\<dagger>..n)) @ (list_of_dlist (l\<dagger>n..))) = l"
unfolding size_dlist_def slice_left_def slice_right_def
by (simp add: list_of_dlist_inverse list_of_dlist_slice )

theorem slice_append_mid: 
"\<forall>i s e. s \<le> i \<and> i \<le> e \<longrightarrow> 
  ((list_of_dlist (l\<dagger>s..i)) @ (list_of_dlist (l\<dagger>i..e))) = 
    list_of_dlist (l\<dagger>s..e)"
unfolding size_dlist_def slice_left_def slice_right_def list_of_dlist_slice 
by (smt Nat.diff_add_assoc2 drop_drop le_add_diff_inverse 
  le_add_diff_inverse2 max_0L take_add)

theorem slice_append_3: 
"\<forall>i j. i \<le> j \<longrightarrow> 
  ((list_of_dlist (l\<dagger>..i)) @ 
    (list_of_dlist (l\<dagger>i..j)) @ (list_of_dlist (l\<dagger>j..))) = list_of_dlist l"
unfolding size_dlist_def slice_left_def slice_right_def list_of_dlist_slice 
by (metis append_assoc append_take_drop_id drop_0 le_add_diff_inverse 
  length_drop max.cobounded2 max_0L minus_nat.diff_0 take_add take_all)

theorem distinct_slice_lte_inter_empty[simp]: 
  "i \<le> j \<Longrightarrow> set (list_of_dlist (l\<dagger>..i)) \<inter> set (list_of_dlist (l\<dagger>j..)) = {}"
unfolding size_dlist_def slice_left_def slice_right_def
by (simp add: Dlist_empty_seq_inter list_of_dlist_slice )

corollary distinct_slice_inter_empty [simp]: 
  "set (list_of_dlist (l\<dagger>..i)) \<inter> set (list_of_dlist (l\<dagger>i..)) = {}"
by simp

corollary distinct_slice_lt_inter_empty [simp]: 
  "i < j \<Longrightarrow> set (list_of_dlist (l\<dagger>..i)) \<inter> set (list_of_dlist (l\<dagger>j..)) = {}"
by simp

corollary distinct_slice_diff1: 
  "set (list_of_dlist (l\<dagger>..i)) - set (list_of_dlist (l\<dagger>i..)) = 
    set (list_of_dlist (l\<dagger>..i))"
by (simp add: Diff_triv)

corollary distinct_slice_diff2: 
  "set (list_of_dlist (l\<dagger>i..)) - set (list_of_dlist (l\<dagger>..i)) = 
    set (list_of_dlist (l\<dagger>i..))"
using distinct_slice_diff1 by fastforce

(*
lemma Dlist_slice_inverse[simp]:
  "list_of_dlist (Dlist ((list_of_dlist l)\<dagger>i..f)) = (list_of_dlist l)\<dagger>i..f"
by (simp add: Dlist_inverse distinct_dlist distinct_slice)
*)

theorem distinct_in_set_slice1_not_in_slice2: 
  "i \<le> j \<Longrightarrow> 
  x \<in> set (list_of_dlist (l\<dagger>..i)) \<and> x \<in> set (list_of_dlist (l\<dagger>j..)) \<Longrightarrow> 
  False"
using distinct_slice_lte_inter_empty by fastforce

corollary distinct_in_set_slice1_implies_not_in_slice2: 
  "i \<le> j \<Longrightarrow> x \<in> set (list_of_dlist (l\<dagger>..i)) \<Longrightarrow> 
  x \<in> set (list_of_dlist (l\<dagger>j..)) \<Longrightarrow> False"
by (meson distinct_in_set_slice1_not_in_slice2)

lemma exists_sublist_or_not_sublist [simp]: "\<exists>i. l\<dagger>..i \<in> T \<or> l\<dagger>i.. \<notin> T"
unfolding slice_right_def slice_left_def
by auto

lemma forall_slice_left_implies_exists [simp]: 
  "\<forall> i . l\<dagger>i.. \<in> S \<Longrightarrow> \<exists> i . l\<dagger>(Suc i).. \<in> S"
unfolding slice_right_def slice_left_def 
by (simp add: slice_dlist_def)

lemma forall_slice_right_implies_exists [simp]: 
  "\<forall> i . l\<dagger>..i \<in> S \<Longrightarrow> \<exists> i . l\<dagger>..(i-1) \<in> S"
unfolding slice_right_def slice_left_def 
by auto

(*lemma take_Suc_Cons [simp]: "take (Suc n) (xDlist_inverse # xs) = x # take n xs"*)

lemma take_Suc_Cons_hd_tl: "length l > 0 \<Longrightarrow> 
  take (Suc n) l = hd l # (take n (tl l))"
apply (induct l)
by auto

corollary take_Suc_Cons_hd_tl_singleton: 
  "length l > 0 \<Longrightarrow> take (Suc 0) l = [hd l]"
apply (induct l)
by auto

lemma take_drop_suc: "i < length l \<Longrightarrow> length l > 0 \<Longrightarrow> 
  take (max 0 ((Suc i) - i)) (drop i l) = [l!i]"
by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1_left add.commute 
  append_eq_append_conv cancel_comm_monoid_add_class.diff_cancel 
  hd_drop_conv_nth lessI max_0L numeral_1_eq_Suc_0 numeral_One take_add 
  take_hd_drop)

lemma slice_right_take:"l\<dagger>..i = Dlist (take i (list_of_dlist l))"
unfolding slice_right_def slice_dlist_def
by auto

lemma slice_left_drop: "l\<dagger>i.. = Dlist (drop i (list_of_dlist l))"
unfolding slice_left_def slice_dlist_def size_dlist_def
by auto

lemma take_one_singleton_hd: "l \<noteq> [] \<Longrightarrow> take (Suc 0) l = [hd l]"
apply (induct l, simp)
by auto

lemma take_one_singleton_nth: "l \<noteq> [] \<Longrightarrow> take (Suc 0) l = [l!0]"
apply (induct l, simp)
by auto

lemma take_one_drop_n_append_singleton_nth: 
  "ys \<noteq> [] \<Longrightarrow> take 1 (drop (length xs) (xs @ ys)) = 
  [(xs @ ys)!(length xs)]"
by (induct xs, auto simp add: take_one_singleton_nth)

lemma append_length_nth_hd: "ys \<noteq> [] \<Longrightarrow> [(xs @ ys)!(length xs)] = [hd ys]"
by (induct ys, auto)

lemma take_one_drop_n_singleton_nth: "l \<noteq> [] \<Longrightarrow> n < length l \<Longrightarrow> 
  take 1 (drop n l) = [l!n]"
proof-
  assume 0: "l \<noteq> []"
  assume 1: "n < length l"
  obtain xs where "xs = take n l" by simp
  obtain ys where "ys = drop n l" by simp
  have "take 1 (drop n l) = take 1 (drop (length xs) (xs @ ys))" using 0 1 
    by (simp add: `ys = drop n l`)
  also have "... = [(xs @ ys)!(length xs)]" using 0 1
    by (metis `ys = drop n l` drop_eq_Nil not_le 
      take_one_drop_n_append_singleton_nth)
  also have "... = [l!(length xs)]" 
    by (simp add: `xs = take n l` `ys = drop n l`)
  finally show ?thesis using 0 1
    by (simp add: hd_drop_conv_nth take_one_singleton_hd)
qed

lemma slice_singleton: "(list_of_dlist l) \<noteq> [] \<Longrightarrow> i < (#l) \<Longrightarrow> 
  list_of_dlist (l\<dagger>i..(Suc i)) = [(list_of_dlist l)!i]"
by (metis list_of_dlist_slice length_greater_0_conv size_dlist_def 
  take_drop_suc)

lemma slice_right_zero_eq_empty: "list_of_dlist (l\<dagger>..0) = []"
by (simp add: slice_right_def slice_dlist_def)

lemma slice_left_size_eq_empty: "list_of_dlist (l\<dagger>(#l)..) = []"
by (simp add: slice_left_def slice_dlist_def )

lemma slice_right_singleton_eq_element: "list_of_dlist l \<noteq> [] \<Longrightarrow> 
  list_of_dlist (l\<dagger>..1) = [(list_of_dlist l)!0]"
by (metis One_nat_def take_one_singleton_nth take_slice_right)

lemma slice_left_singleton_eq_element: "list_of_dlist l \<noteq> [] \<Longrightarrow> 
  list_of_dlist (l\<dagger>((#l)-1)..) = [(list_of_dlist l)!((#l)-1)]"
by (metis (no_types, lifting) Cons_nth_drop_Suc list_of_dlist_slice 
  Suc_diff_Suc Suc_leI diff_Suc_eq_diff_pred diff_less drop_0 drop_all 
  drop_take length_greater_0_conv max_0L minus_nat.diff_0 size_dlist_def 
  slice_left_def slice_none zero_less_one)

lemma dlist_empty_slice[simp]: "i \<le> j \<Longrightarrow> (l\<dagger>j..i) = Dlist []"
by (simp add: slice_dlist_def)

lemma dlist_append_extreme_left: 
  "i\<le>j \<Longrightarrow> list_of_dlist (l\<dagger>..j) = 
  (list_of_dlist (l\<dagger>..i)) @ (list_of_dlist (l\<dagger>i..j))"
by (metis list_of_dlist_slice le_add_diff_inverse max_0L take_add 
  take_slice_right)

lemma dlist_append_extreme_right: 
  "i\<le>j \<Longrightarrow> list_of_dlist (l\<dagger>i..) = 
  (list_of_dlist (l\<dagger>i..j)) @ (list_of_dlist (l\<dagger>j..))"
unfolding list_of_dlist_slice slice_left_def slice_right_def
by (metis append_take_drop_id drop_drop le_add_diff_inverse2 length_drop 
  max.cobounded2 max_0L size_dlist_def take_all)

lemma dlist_disjoint[simp]: "disjoint (l::'a dlist)"
by (simp add: disjoint_dlist_def)

lemma dlist_member_suc_nth1: 
  "x \<in> set (list_of_dlist(l\<dagger>i..(Suc i))) \<Longrightarrow> x = (list_of_dlist l)!i"
proof-
  assume 0: "x \<in> set (list_of_dlist (l\<dagger>i..(Suc i)))"
  obtain rl where 1:"rl = list_of_dlist l" by blast
  hence "x \<in> set (take (max 0 (Suc i - i)) (drop i rl))" 
    using 0 by (metis list_of_dlist_slice )
  hence "x \<in> set (take 1 (drop i rl))" by simp
  hence "x = rl!i" 
    by (metis drop_Nil drop_all empty_iff list.inject list.set(1) 
      list.set_cases not_less take_Nil take_one_drop_n_singleton_nth)
  thus ?thesis using 1 by simp
qed

lemma dlist_member_suc_nth2: 
  "i < (#l) \<Longrightarrow> x = (list_of_dlist l)!i \<Longrightarrow> 
  x \<in> set (list_of_dlist (l\<dagger>i..(Suc i)))"
unfolding size_dlist_def slice_dlist_def
by (metis Dlist_slice_inverse drop_Nil drop_eq_Nil leD length_greater_0_conv 
  list.set_intros(1) take_drop_suc)

lemma dlist_member_suc_nth: "i < (#l) \<Longrightarrow> 
  (x = (list_of_dlist l)!i) \<longleftrightarrow> (x \<in> set (list_of_dlist (l\<dagger>i..(Suc i))))"
using dlist_member_suc_nth1 dlist_member_suc_nth2
by fastforce

corollary not_dlist_member_empty[simp]: 
  "\<not> Dlist.member (Dlist.empty) v"
  "\<not> (Dlist.member (Dlist []) v)"
by (simp add: Dlist.member_def Dlist.empty_def List.member_def)+

lemma dlist_empty_slice_none: "(Dlist.empty\<dagger>i..j) = Dlist.empty"
by (simp add: Dlist.empty_def slice_dlist_def)

corollary dlist_empty_slice_right_none: "(Dlist.empty\<dagger>..j) = Dlist.empty"
by (simp add: dlist_empty_slice_none slice_right_def)

corollary dlist_empty_slice_left_none: "(Dlist.empty\<dagger>i..) = Dlist.empty"
by (simp add: dlist_empty_slice_none slice_left_def)

lemma dlist_member_slice_empty_none: 
  "\<not> (Dlist.member (Dlist.empty\<dagger>i..j) v)"
by (auto simp add: slice_dlist_def)

corollary dlist_member_slice_right_empty_none[simp]: 
  "\<not> (Dlist.member (Dlist.empty\<dagger>..j) v)"
by (simp add: slice_right_def dlist_empty_slice_none)

corollary dlist_member_slice_left_empty_none[simp]: 
  "\<not> (Dlist.member (Dlist.empty\<dagger>i..) v)"
by (simp add: slice_left_def dlist_empty_slice_none)

lemma dlist_member_slice_member_dlist:
  "\<exists> i j. Dlist.member (dl\<dagger>i..j) v \<Longrightarrow> Dlist.member dl v"
unfolding Dlist.member_def List.member_def slice_dlist_def
using in_set_dropD in_set_takeD by fastforce

corollary dlist_member_slice_right_member_dlist:
  "\<exists>j. Dlist.member (dl\<dagger>..j) v \<Longrightarrow> Dlist.member dl v"
by (metis dlist_member_slice_member_dlist slice_right_def)

corollary dlist_member_slice_left_member_dlist:
  "\<exists>i. Dlist.member (dl\<dagger>i..) v \<Longrightarrow> Dlist.member dl v"
by (metis dlist_member_slice_member_dlist slice_left_def)

lemma sliceable_nth_member1: 
  "sliceable_nth dl i = Dlist [v] \<Longrightarrow> Dlist.member dl v"
by (metis Dlist.member_def distinct_remdups_id distinct_singleton 
  dlist_member_slice_member_dlist in_set_member list.set_intros(1) list_of_dlist_Dlist)

corollary sliceable_nth_member: 
  "\<exists>i. sliceable_nth dl i = Dlist [v] \<Longrightarrow> Dlist.member dl v"
by (auto simp add: sliceable_nth_member1)

lemma sliceable_nth_member_iff: 
  "(\<exists>i. sliceable_nth dl i = Dlist [v]) \<longleftrightarrow> Dlist.member dl v"
apply (rule iffI, simp add: sliceable_nth_member)
by (metis Dlist.member_def empty_iff empty_set in_set_conv_nth in_set_member 
  list_of_dlist_slice size_dlist_def slice_dlist_def slice_singleton)


(*<*)
end
(*>*)