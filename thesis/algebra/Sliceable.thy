theory Sliceable

imports Main 

begin

class sliceable = 
  fixes slice :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" ("(3_\<dagger>_.._)"  [80,80,80] 80)
  fixes size :: "'a \<Rightarrow> nat" ("(1#_)" 65)
  fixes empty_inter :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes disjoint :: "'a \<Rightarrow> bool"
  (*assumes disjoint_simp [simp]: "disjoint x"*)
  assumes slice_none: "x\<dagger>0..(#x) = x"
  assumes empty_seq_inter [simp]: "disjoint x \<Longrightarrow> c \<le> k \<Longrightarrow> empty_inter (x\<dagger>0..c) (x\<dagger>k..(#x))"
  assumes size_slice: "size (x\<dagger>i..j) = max 0 ((min j (size x))-i)"
  assumes slice_slice: "(x\<dagger>i..j)\<dagger>a..b = x\<dagger>(i+a)..(min j (i+b))"
  assumes disjoint_slice_suc: 
    "disjoint x \<Longrightarrow> i\<noteq>j \<Longrightarrow> i < (#x) \<Longrightarrow> j < (#x) \<Longrightarrow> x\<dagger>i..(Suc i) \<noteq> x\<dagger>j..(Suc j)"
  assumes disjoint_slice[simp]: "disjoint x \<Longrightarrow> disjoint (x\<dagger>i..j)"
  assumes forall_slice_implies_eq: "(#x) = (#y) \<and> (\<forall>i j. (x\<dagger>i..j) = (y\<dagger>i..j)) \<longleftrightarrow> (x = y)"
  (*
  assumes forall_slice_Suc_implies_eq: 
    "(#x) = (#y) \<and> (\<forall>i. x\<dagger>i..(Suc i) = y\<dagger>i..(Suc i)) \<longleftrightarrow> (x = y)"
  *)

definition slice_right :: "'a::sliceable \<Rightarrow> nat \<Rightarrow> 'a" ("(2_\<dagger>.._)" [80,80] 80)
where "x\<dagger>..i = x\<dagger>0..i"

definition slice_left :: "'a::sliceable \<Rightarrow> nat \<Rightarrow> 'a" ("(2_\<dagger>_..)" [80,80] 80)
where "x\<dagger>i.. = x\<dagger>i..(# x)"

lemma (in sliceable) slice_right_disjoint[simp]: "disjoint xs \<Longrightarrow> disjoint (xs\<dagger>..i)"
unfolding slice_right_def
by simp

lemma (in sliceable) slice_left_disjoint[simp]: "disjoint xs \<Longrightarrow> disjoint (xs\<dagger>i..)"
unfolding slice_left_def
by simp

abbreviation sliceable_nth :: "'a::sliceable \<Rightarrow> nat \<Rightarrow> 'a"
where
"sliceable_nth l i \<equiv> l\<dagger>i..(Suc i)"

theorem (in sliceable) empty_seq_inter_eq [simp]: 
  "disjoint x \<Longrightarrow> empty_inter (x\<dagger>..i) (x\<dagger>i..)"
by (simp add: slice_right_def slice_left_def)

theorem (in sliceable) empty_seq_sliced_inter [simp]: 
  "disjoint x \<Longrightarrow> b \<le> i \<Longrightarrow> j \<le> a \<Longrightarrow> i \<le> j \<Longrightarrow> a \<le> size x \<Longrightarrow> empty_inter (x\<dagger>b..i) (x\<dagger>j..a)"
proof-
  let ?l = "x\<dagger>b..a"
  assume lt0: "i \<le> j"
  assume lt1: "j \<le> a"
  assume lt2: "b \<le> i"
  assume lt3: "a \<le> size x"
  assume lt4: "disjoint x"
  have blta: "b \<le> a" using lt0 lt1 lt2 by simp
  have ilta: "i \<le> a" using lt0 lt1 by simp
  hence 2: "empty_inter (?l\<dagger>0..(i-b)) (?l\<dagger>(j-b)..(#?l))" using lt0 lt4 disjoint_slice by simp
  hence "empty_inter ((x\<dagger>b..a)\<dagger>0..(i-b)) ((x\<dagger>b..a)\<dagger>(j-b)..(#?l))" by simp
  hence 3: "empty_inter (x\<dagger>b..i) ((x\<dagger>b..a)\<dagger>(j-b)..(#(x\<dagger>b..a)))" using ilta lt2
    by (simp add: slice_slice min_absorb2)
  hence 3: "empty_inter (x\<dagger>b..i) (x\<dagger>j..a)"  
    using blta lt0 lt2 lt3 
    by (auto simp add: size_slice slice_slice min_def)
  thus ?thesis by simp
qed

theorem distinct_slice_lte_inter_empty[simp]: 
  "distinct l \<Longrightarrow> i \<le> j \<Longrightarrow> 
    set (take i (drop 0 l)) 
    \<inter> set (take (length l-i) (drop i l)) = {}"
by (simp add: set_take_disj_set_drop_if_distinct )

lemma (in sliceable) size_slice_right_absorb: "(#(l\<dagger>..i)) = min i (#l)"
by (simp add: slice_right_def sliceable_class.size_slice)

lemma (in sliceable) size_slice_left_absorb: "(#(l\<dagger>i..)) = (#l)-i"
by (simp add: slice_left_def sliceable_class.size_slice)

corollary (in sliceable) slice_right_slice_left_absorb: "(l\<dagger>..i)\<dagger>j.. = l\<dagger>j..i"
unfolding slice_left_def slice_right_def
by (metis (mono_tags, hide_lams) add.left_neutral add.right_neutral max_0L min.left_idem 
  size_slice_right_absorb slice_right_def sliceable_class.size_slice sliceable_class.slice_none 
  sliceable_class.slice_slice)

corollary (in sliceable) slice_right_slice_left_absorb_empty: 
  "i \<le> j \<Longrightarrow> (#((l\<dagger>..i)\<dagger>j..)) = 0"
by (simp add: size_slice_left_absorb size_slice_right_absorb)

corollary (in sliceable) slice_left_slice_right_absorb: "(l\<dagger>i..)\<dagger>..j = l\<dagger>i..(i+j)"
unfolding slice_left_def slice_right_def
proof -
  have "(l\<dagger>i..(#l))\<dagger>0..j = (l\<dagger>0..(#l))\<dagger>i..(i + j)"
    by (simp add: sliceable_class.slice_slice)
  thus "(l\<dagger>i..(#l))\<dagger>0..j = l\<dagger>i..(i + j)"
    by (simp add: sliceable_class.slice_none)
qed

corollary (in sliceable) slice_right_slice_right_absorb: "(l\<dagger>..i)\<dagger>..j = (l\<dagger>..(min i j))"
unfolding slice_left_def slice_right_def
by (simp add: sliceable_class.slice_slice)

corollary (in sliceable) slice_left_slice_left_absorb: "(l\<dagger>i..)\<dagger>j.. = l\<dagger>(i+j).."
unfolding slice_left_def slice_right_def
by (simp add: sliceable_class.slice_slice sliceable_class.size_slice min_absorb1)

corollary (in sliceable) slice_slice_right_absorb: "(l\<dagger>i..j)\<dagger>..b = l\<dagger>i..(min j (i+b))"
unfolding slice_left_def slice_right_def
by (simp add: add.commute sliceable_class.slice_slice)

corollary (in sliceable) slice_slice_left_absorb: 
  "(l\<dagger>i..j)\<dagger>a.. = l\<dagger>(i+a)..j"
unfolding slice_left_def slice_right_def
by (metis (mono_tags, hide_lams) add.assoc diff_diff_left max_0L slice_left_def 
  slice_left_slice_right_absorb slice_right_def slice_slice_right_absorb 
  sliceable_class.size_slice sliceable_class.slice_none sliceable_class.slice_slice)

corollary (in sliceable) slice_left_slice_absorb: 
  "(l\<dagger>i..)\<dagger>a..b = l\<dagger>(i+a)..(i+b)"
unfolding slice_left_def slice_right_def
by (metis (mono_tags, lifting) slice_left_slice_right_absorb slice_right_def 
  slice_right_slice_left_absorb slice_slice_left_absorb sliceable_class.slice_none)

corollary (in sliceable) slice_right_slice_absorb: 
  "(l\<dagger>..j)\<dagger>a..b = l\<dagger>a..(min j b)"
unfolding slice_left_def slice_right_def
by (simp add: sliceable_class.slice_slice)


lemmas (in sliceable) slice_slice_simps = slice_left_slice_left_absorb slice_left_slice_right_absorb
  slice_right_slice_left_absorb slice_right_slice_right_absorb slice_slice
  slice_slice_right_absorb slice_slice_left_absorb slice_left_slice_absorb slice_right_slice_absorb

lemmas (in sliceable) size_slice_defs = size_slice size_slice_left_absorb size_slice_right_absorb

lemma (in sliceable) slice_f_min_neutral: "(P (l\<dagger>i..(min f k)) \<and> f \<le> k) \<longleftrightarrow> (P (l\<dagger>i..f) \<and> f \<le> k)"
by linarith

lemma (in sliceable) slice_i_min_neutral: "(P (l\<dagger>(min i k)..f) \<and> i \<le> k) \<longleftrightarrow> (P (l\<dagger>i..f) \<and> i \<le> k)"
by linarith

lemma (in sliceable) slice_i_min_neutral_lt: "(P (l\<dagger>(min k i)..f) \<and> i < k) \<longleftrightarrow> 
  (P (l\<dagger>i..f) \<and> i < k)"
by linarith

lemma (in sliceable) slice_foral_i_min_neutral: 
  "(\<forall> i f . P (l\<dagger>(min i k)..f) \<and> i \<le> k) \<longleftrightarrow> (\<forall> i f . P (l\<dagger>i..f) \<and> i \<le> k)"
using not_less by auto

lemma (in sliceable) slice_f_max_neutral: "(P (l\<dagger>i..(max f k)) \<and> f \<ge> k) \<longleftrightarrow> (P (l\<dagger>i..f) \<and> f \<ge> k)"
by (metis max.orderE)

lemma (in sliceable) slice_i_max_neutral: "(P (l\<dagger>(max i k)..f) \<and> i \<ge> k) \<longleftrightarrow> (P (l\<dagger>i..f) \<and> i \<ge> k)"
by (metis max.orderE)

lemma (in sliceable) empty_slice[simp]: "i \<le> j \<Longrightarrow> (#(l\<dagger>j..i)) = 0"
using local.size_slice by auto

corollary (in sliceable) forall_disjoint_slice_suc:
  "\<forall> i j . (disjoint x \<and> i\<noteq>j \<and> i < (#x) \<and> j < (#x)) \<longrightarrow> (x\<dagger>i..(Suc i) \<noteq> x\<dagger>j..(Suc j))"
by (simp add: local.disjoint_slice_suc)

end