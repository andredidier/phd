(*<*)
theory ValueCondition

imports Main FaultModellingTypes Boolean_Expression_Checkers

begin
(*>*)

(*<*)
datatype 'vb ValueCondition = 
  VCConstOp bool
  | VCVarOp 'vb 
  | VCNotOp "'vb ValueCondition" 
  | VCAndOp "'vb ValueCondition" "'vb ValueCondition" 

notation (output) VCConstOp  ("_\<^sub>B\<^sub>O" 50)
notation (latex) VCConstOp ("_\<^raw:$_{\mathrm{BO}}$>" 51)
notation (output) VCVarOp ("\<lbrakk>_\<rbrakk>\<^sub>B\<^sub>O" 60)
notation (latex) VCVarOp ("\<lbrakk>_\<rbrakk>\<^raw:$_{\mathrm{BO}}$>" 61)
notation (output) VCNotOp ("'(\<not>\<^sub>B\<^sub>O _')" 80)
notation (latex) VCNotOp ("\<^raw:$\overline{>_\<^raw:}$>" 81)
notation (output) VCAndOp ("'(_\<and>\<^sub>B\<^sub>O_')" 75)
notation (latex) VCAndOp ("_\<and>\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VCOrOp :: "'vb ValueCondition \<Rightarrow> 'vb ValueCondition \<Rightarrow> 'vb ValueCondition"
where "VCOrOp b1 b2 \<equiv> VCNotOp (VCAndOp (VCNotOp b1) (VCNotOp b2))"

notation (output) VCOrOp ("_\<or>\<^sub>B\<^sub>O_" 70)
notation (latex) VCOrOp ("_+\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VCNandOp :: "'vb ValueCondition \<Rightarrow> 'vb ValueCondition \<Rightarrow> 'vb ValueCondition"
where "VCNandOp b1 b2 \<equiv> (VCNotOp (VCAndOp b1 b2))"

notation (output) VCNandOp ("_\<^sup>\<not>\<and>\<^sub>B\<^sub>O_" 70)
notation (latex) VCNandOp ("_\<^sup>\<not>\<and>\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VCXorOp :: "'vb ValueCondition \<Rightarrow> 'vb ValueCondition \<Rightarrow> 'vb ValueCondition"
where "VCXorOp b1 b2 \<equiv> (VCAndOp (VCNandOp b1 b2) (VCOrOp b1 b2))"

notation (output) VCXorOp ("_\<otimes>\<^sub>B\<^sub>O_" 70)
notation (latex) VCXorOp ("_\<otimes>\<^raw:$_{\mathrm{BO}}$>_" 70)

(*>*)

text {* Before introducing our fault modelling formalisation, we define new datatypes and slight 
modification in existing ones.
%
To be able to later compare Boolean variables to fault trees' basic events variables, we introduce 
Boolean expressions with variables.
%
Accordingly to the work reported in %~\cite{}
, all Boolean operators can be derived from @{term "Not A"} @{const "Not"} @{text "\<not>" }
and @{term "(op \<and>) A B"} @{text "\<and>" }operators.
%
For example, to express an @{term "(op \<or>) A B"}, we use the expression 
@{term "Not ((op \<and>) (Not A) (Not B))"}.
%
Following this idea, we introduce our datatype @{typ "'VarNames ValueCondition"}
  *}

primrec ValueCondition_eval :: "'vb ValueCondition \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ValueCondition_eval (VCConstOp c) _ = c" |
  "ValueCondition_eval (VCVarOp v) env = (env v)" |
  "ValueCondition_eval (VCNotOp b) env = (\<not> ValueCondition_eval b env)" |
  "ValueCondition_eval (VCAndOp b1 b2) env = 
    ((ValueCondition_eval b1 env) \<and> (ValueCondition_eval b2 env))"

primrec ValueCondition_to_bool_expr :: "'vb ValueCondition \<Rightarrow> 'vb bool_expr"
where
  "ValueCondition_to_bool_expr (VCConstOp c) = Const_bool_expr c" |
  "ValueCondition_to_bool_expr (VCVarOp v) = Atom_bool_expr v" |
  "ValueCondition_to_bool_expr (VCNotOp b) = Neg_bool_expr (ValueCondition_to_bool_expr b)" |
  "ValueCondition_to_bool_expr (VCAndOp b1 b2) = 
    And_bool_expr (ValueCondition_to_bool_expr b1) (ValueCondition_to_bool_expr b2)"

lemma value_preservation: "val_bool_expr (ValueCondition_to_bool_expr b) s = ValueCondition_eval b s"
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
