theory FaultModellingTypes

imports Main

begin

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

definition apply_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'c)"
where
  "apply_map m f \<equiv> (\<lambda> x. case (m x) of None \<Rightarrow> None | (Some mx) \<Rightarrow> Some (f mx))"

primrec apply_f_list :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b list"
where
  "apply_f_list [] f = []" |
  "apply_f_list (l # ls) f = (f l) # (apply_f_list ls f)"

end
