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

primrec set_temporal_exp :: "'a temporal_exp \<Rightarrow> 'a list set"
where
  "set_temporal_exp Top_temporal_exp = lists UNIV" |
  "set_temporal_exp Bot_temporal_exp = { [] }" |
  "set_temporal_exp (Atom_temporal_exp a) = {[a]}" |
  "set_temporal_exp (Before_temporal_exp t1 t2) = 
    { l1 @ l2 | l1 l2 . l1 \<in> set_temporal_exp t1 \<and> l2 \<in> set_temporal_exp t2  }" |
  "set_temporal_exp (Or_temporal_exp t1 t2) = (set_temporal_exp t1) \<union> (set_temporal_exp t2)"


definition val_temporal_exp :: "'a temporal_exp \<Rightarrow> 'a list set \<Rightarrow> bool"
where
  "val_temporal_exp t s = (set_temporal_exp t \<subseteq> s)"

lemma "val_temporal_exp (Before_temporal_exp (Atom_temporal_exp A) (Atom_temporal_exp B))"

type_synonym ('a, 'FMode, 'vv) TemporalConditionalMode =
  "('a list set, 'FMode, 'vv) ConditionalMode"

lemma temporal_and: "CVIF {[A,B], [B,A]} t1 t2"

end
