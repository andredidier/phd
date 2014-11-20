(*<*)
theory ValueCondition

imports Main FaultModellingTypes Boolean_Expression_Checkers

begin
(*>*)

(*<*)
datatype 'vb ValueCondition = 
  VCConst bool
  | VCVar 'vb 
  | VCNot "'vb ValueCondition" 
  | VCAnd "'vb ValueCondition" "'vb ValueCondition" 

notation (output) VCConst  ("_" 60)
notation (output) VCVar ("_" 60)
notation (output) VCNot ("\<not>_" 80)
notation (output) VCAnd (infixr "\<and>" 75)

abbreviation VCOr :: "'vb ValueCondition \<Rightarrow> 'vb ValueCondition \<Rightarrow> 'vb ValueCondition"
where "VCOr b1 b2 \<equiv> VCNot (VCAnd (VCNot b1) (VCNot b2))"

notation (output) VCOr (infixr "\<or>" 70)

abbreviation VCNand :: "'vb ValueCondition \<Rightarrow> 'vb ValueCondition \<Rightarrow> 'vb ValueCondition"
where "VCNand b1 b2 \<equiv> (VCNot (VCAnd b1 b2))"

notation (output) VCNand (infixr "\<^sup>\<not>\<and>" 70)

abbreviation VCXor :: "'vb ValueCondition \<Rightarrow> 'vb ValueCondition \<Rightarrow> 'vb ValueCondition"
where "VCXor b1 b2 \<equiv> (VCAnd (VCNand b1 b2) (VCOr b1 b2))"

notation (output) VCXor (infixr "\<otimes>" 70)

(*>*)

primrec ValueCondition_eval :: "'vb ValueCondition \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ValueCondition_eval (VCConst c) _ = c" |
  "ValueCondition_eval (VCVar v) env = (env v)" |
  "ValueCondition_eval (VCNot b) env = (\<not> ValueCondition_eval b env)" |
  "ValueCondition_eval (VCAnd b1 b2) env = 
    ((ValueCondition_eval b1 env) \<and> (ValueCondition_eval b2 env))"

primrec ValueCondition_to_bool_expr :: "'vb ValueCondition \<Rightarrow> 'vb bool_expr"
where
  "ValueCondition_to_bool_expr (VCConst c) = Const_bool_expr c" |
  "ValueCondition_to_bool_expr (VCVar v) = Atom_bool_expr v" |
  "ValueCondition_to_bool_expr (VCNot b) = Neg_bool_expr (ValueCondition_to_bool_expr b)" |
  "ValueCondition_to_bool_expr (VCAnd b1 b2) = 
    And_bool_expr (ValueCondition_to_bool_expr b1) (ValueCondition_to_bool_expr b2)"

lemma value_preservation: 
  "val_bool_expr (ValueCondition_to_bool_expr b) s = ValueCondition_eval b s"
apply (induction b)
apply (auto)
done

definition ValueCondition_Tautology :: "'vb ValueCondition \<Rightarrow> bool"
where "ValueCondition_Tautology \<equiv> taut_test \<circ> ValueCondition_to_bool_expr"

corollary Tautology_eval: "ValueCondition_Tautology b = (\<forall> env. ValueCondition_eval b env)"
apply (simp add: ValueCondition_Tautology_def value_preservation taut_test)
done

definition ValueCondition_Sat :: "'vb ValueCondition \<Rightarrow> bool"
where "ValueCondition_Sat \<equiv> sat_test \<circ> ValueCondition_to_bool_expr"

corollary Sat_eval: "ValueCondition_Sat b = (\<exists> env. ValueCondition_eval b env)"
apply (simp add: ValueCondition_Sat_def value_preservation sat_test)
done

end
