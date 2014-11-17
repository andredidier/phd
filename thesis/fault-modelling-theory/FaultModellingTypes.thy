theory FaultModellingTypes

imports Main

begin

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

definition apply_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'c)"
where
  "apply_map m f \<equiv> (\<lambda> x. case (m x) of None \<Rightarrow> None | (Some mx) \<Rightarrow> Some (f mx))"

definition merge_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  "merge_map m1 m2 f = 
  (
    \<lambda> x. 
      case (m1 x) of
        None \<Rightarrow> 
        (
          case (m2 x) of
            None \<Rightarrow> None | Some b2 \<Rightarrow> Some b2
        ) |
        Some b1 \<Rightarrow> 
        (
          case (m2 x) of
            None \<Rightarrow> Some b1 | Some b2 \<Rightarrow> Some (f b1 b2)
        )
  )"

primrec apply_f_list :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b list"
where
  "apply_f_list [] f = []" |
  "apply_f_list (l # ls) f = (f l) # (apply_f_list ls f)"

end
