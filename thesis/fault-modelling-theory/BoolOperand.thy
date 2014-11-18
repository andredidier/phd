(*<*)
theory BoolOperand

imports Main FaultModellingTypes Boolean_Expression_Checkers

begin
(*>*)

(*<*)
datatype 'vb BoolOperand = 
  VBBConstOp bool
  | VBBVarOp 'vb 
  | VBBNotOp "'vb BoolOperand" 
  | VBBAndOp "'vb BoolOperand" "'vb BoolOperand" 

notation (output) VBBConstOp  ("_\<^sub>B\<^sub>O" 50)
notation (latex) VBBConstOp ("_\<^raw:$_{\mathrm{BO}}$>" 51)
notation (output) VBBVarOp ("\<lbrakk>_\<rbrakk>\<^sub>B\<^sub>O" 60)
notation (latex) VBBVarOp ("\<lbrakk>_\<rbrakk>\<^raw:$_{\mathrm{BO}}$>" 61)
notation (output) VBBNotOp ("'(\<not>\<^sub>B\<^sub>O _')" 80)
notation (latex) VBBNotOp ("\<^raw:$\overline{>_\<^raw:}$>" 81)
notation (output) VBBAndOp ("'(_\<and>\<^sub>B\<^sub>O_')" 75)
notation (latex) VBBAndOp ("_\<and>\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VBBOrOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBOrOp b1 b2 \<equiv> VBBNotOp (VBBAndOp (VBBNotOp b1) (VBBNotOp b2))"

notation (output) VBBOrOp ("_\<or>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBOrOp ("_+\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VBBNandOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBNandOp b1 b2 \<equiv> (VBBNotOp (VBBAndOp b1 b2))"

notation (output) VBBNandOp ("_\<^sup>\<not>\<and>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBNandOp ("_\<^sup>\<not>\<and>\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VBBXorOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBXorOp b1 b2 \<equiv> (VBBAndOp (VBBNandOp b1 b2) (VBBOrOp b1 b2))"

notation (output) VBBXorOp ("_\<otimes>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBXorOp ("_\<otimes>\<^raw:$_{\mathrm{BO}}$>_" 70)

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
Following this idea, we introduce our datatype @{typ "'VarNames BoolOperand"}
  *}

primrec BoolOperand_eval :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where
  "BoolOperand_eval (VBBConstOp c) _ = c" |
  "BoolOperand_eval (VBBVarOp v) env = (env v)" |
  "BoolOperand_eval (VBBNotOp b) env = (\<not> BoolOperand_eval b env)" |
  "BoolOperand_eval (VBBAndOp b1 b2) env = 
    ((BoolOperand_eval b1 env) \<and> (BoolOperand_eval b2 env))"

primrec BoolOperand_to_bool_expr :: "'vb BoolOperand \<Rightarrow> 'vb bool_expr"
where
  "BoolOperand_to_bool_expr (VBBConstOp c) = Const_bool_expr c" |
  "BoolOperand_to_bool_expr (VBBVarOp v) = Atom_bool_expr v" |
  "BoolOperand_to_bool_expr (VBBNotOp b) = Neg_bool_expr (BoolOperand_to_bool_expr b)" |
  "BoolOperand_to_bool_expr (VBBAndOp b1 b2) = 
    And_bool_expr (BoolOperand_to_bool_expr b1) (BoolOperand_to_bool_expr b2)"

lemma value_preservation: "val_bool_expr (BoolOperand_to_bool_expr b) s = BoolOperand_eval b s"
apply (induction b)
apply (auto)
done

definition BoolOperand_Tautology :: "'vb BoolOperand \<Rightarrow> bool"
where "BoolOperand_Tautology \<equiv> taut_test \<circ> BoolOperand_to_bool_expr"

corollary Tautology_eval: "BoolOperand_Tautology b = (\<forall> env. BoolOperand_eval b env)"
apply (simp add: BoolOperand_Tautology_def value_preservation taut_test)
done

definition BoolOperand_Sat :: "'vb BoolOperand \<Rightarrow> bool"
where "BoolOperand_Sat \<equiv> sat_test \<circ> BoolOperand_to_bool_expr"

corollary Sat_eval: "BoolOperand_Sat b = (\<exists> env. BoolOperand_eval b env)"
apply (simp add: BoolOperand_Sat_def value_preservation sat_test)
done

end
