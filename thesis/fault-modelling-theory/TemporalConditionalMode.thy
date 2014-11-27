theory TemporalConditionalMode

imports ConditionalMode

begin

datatype_new 'a temporal_exp = 
  Top_temporal_exp
  | Bot_temporal_exp
  | Atom_temporal_exp 'a
  | Before_temporal_exp "'a temporal_exp" "'a temporal_exp"
  | Or_temporal_exp "'a temporal_exp" "'a temporal_exp"

abbreviation And_temporal_exp :: "'a temporal_exp binop"
where
  "And_temporal_exp t1 t2 \<equiv> 
    Or_temporal_exp 
      (Before_temporal_exp t1 t2) 
      (Before_temporal_exp t2 t1)"

fun is_ordered_sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_ordered_sublist (a1 # ls1) (a2 # ls2) = ((a1 = a2) \<and> is_ordered_sublist ls1 ls2)" |
  "is_ordered_sublist [] _ = True" |
  "is_ordered_sublist _ [] = False"

definition unpile_temporal_exp :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
where
  "unpile_temporal_exp ls A \<equiv> { t . t \<in> A \<and> is_ordered_sublist ls t} "

inductive_set
  ta :: "'a list set set"
where
  var: "{ls. a \<in> set ls} \<in> ta"
| Compl: "S \<in> ta \<Longrightarrow> - S \<in> ta"
| inter: "S \<in> ta \<Longrightarrow> T \<in> ta \<Longrightarrow> S \<inter> T \<in> ta"

lemma ta_empty: "({} :: 'a list set) \<in> ta"
proof -
  obtain S :: "'a list set" where "S \<in> ta" by (fast intro: ta.var)
  hence "S \<inter> - S \<in> ta" by (intro ta.intros)
  thus ?thesis by simp
qed

typedef 'a temporal_formula = "ta :: 'a list set set"
apply (auto intro: ta_empty)
done

definition var :: "'a \<Rightarrow> 'a temporal_formula"
where "var a = Abs_temporal_formula {ls. a \<in> set ls}"

lemma Rep_formula_var: "Rep_temporal_formula (var a) = {ls . a \<in> set ls}"
unfolding var_def using ta.var by (rule Abs_temporal_formula_inverse)

instantiation temporal_formula :: (type) temporal_exp
begin
end

primrec set_temporal_exp :: "'a temporal_exp \<Rightarrow> 'a list set"
where
  "set_temporal_exp Top_temporal_exp = lists UNIV" |
  "set_temporal_exp Bot_temporal_exp = { [] }" |
  "set_temporal_exp (Atom_temporal_exp a) = unpile_temporal_exp [a] UNIV" |
  "set_temporal_exp (Before_temporal_exp t1 t2) = 
    { l1 @ l2 | l1 l2 . l1 \<in> set_temporal_exp t1 \<and> l2 \<in> set_temporal_exp t2  }" |
  "set_temporal_exp (Or_temporal_exp t1 t2) = (set_temporal_exp t1) \<union> (set_temporal_exp t2)"

datatype Test = Test_a | Test_b | Test_c

lemma "set_temporal_exp (Before_temporal_exp (Atom_temporal_exp Test_a) (Atom_temporal_exp Test_b))
  = {[Test_a, Test_b],[Test_a,Test_b,Test_c],[Test_a,Test_c,Test_b],[Test_c,Test_a,Test_b]}"
apply (auto simp add: unpile_temporal_exp_def is_ordered_sublist_def)
done


definition val_temporal_exp :: "'a temporal_exp \<Rightarrow> 'a list set \<Rightarrow> bool"
where
  "val_temporal_exp t s = (set_temporal_exp t \<subseteq> s)"

lemma "val_temporal_exp (Before_temporal_exp (Atom_temporal_exp A) (Atom_temporal_exp B))"

type_synonym ('a, 'FMode, 'vv) TemporalConditionalMode =
  "('a list set, 'FMode, 'vv) ConditionalMode"

lemma temporal_and: "CVIF {[A,B], [B,A]} t1 t2"

end
