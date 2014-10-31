theory ValuedTautology

imports FaultModellingTypes

begin

datatype 'variavel BoolOperand = 
  VBBConstOp bool
  | VBBVarOp 'variavel
  | VBBExpUnOp "bool \<Rightarrow> bool" "'variavel BoolOperand"
  | VBBExpBinOp "bool \<Rightarrow> bool \<Rightarrow> bool" "'variavel BoolOperand" "'variavel BoolOperand"

datatype 'variavel ValuesOperand =
  VBVConstOp Values
  | VBVVarOp 'variavel

type_synonym ('vb,'vv) ValuedBool = "('vb BoolOperand \<times> 'vv ValuesOperand)"

primrec "BoolOperand_eval" :: "'variavel BoolOperand \<Rightarrow> ('variavel \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) valuation = b" |
  "BoolOperand_eval (VBBVarOp a) valuation = valuation a" |
  "BoolOperand_eval (VBBExpUnOp exp_op op1) valuation = exp_op (BoolOperand_eval op1 valuation)" |
  "BoolOperand_eval (VBBExpBinOp exp_op op1 op2) valuation = 
    exp_op (BoolOperand_eval op1 valuation) (BoolOperand_eval op2 valuation)"

primrec "ValuesOperand_eval" :: "'variavel ValuesOperand \<Rightarrow> ('variavel \<Rightarrow> Values) \<Rightarrow> Values" where
  "ValuesOperand_eval (VBVConstOp v) valuation = v" |
  "ValuesOperand_eval (VBVVarOp a) valuation = valuation a"

definition ValuedBool_bool_eval :: "('vb,'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where 
  "ValuedBool_bool_eval VB valuation \<equiv> BoolOperand_eval (fst VB) valuation"

definition ValuedBool_value_eval :: "('vb, 'vv) ValuedBool \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> Values" where 
  "ValuedBool_value_eval VB valuation \<equiv> ValuesOperand_eval (snd VB) valuation"

type_synonym ('vb, 'vv) ValuedBoolExp = "(('vb,'vv) ValuedBool) list"

primrec ValuedBoolExp_bool_eval :: "('vb,'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "ValuedBoolExp_bool_eval [] val_b = False" |
  "ValuedBoolExp_bool_eval (s # ss) val_b = 
    ((ValuedBool_bool_eval s val_b) \<or> (ValuedBoolExp_bool_eval ss val_b))"


definition ValuedTautology :: "('vb, 'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> bool" where
  "ValuedTautology VBExp val_b val_v \<equiv> (
      (ValuedBoolExp_bool_eval VBExp val_b) \<and>
      (ValuedTautology_set (ValuedBoolExp_to_set VBExp) val_b val_v)
    )"

lemma not_valued_tautology1 : "\<not> ValuedTautology (SVBExp (VBBVarOp A, U)) val_b val_v"
apply (auto simp add: ValuedTautology_def ValuedTautology_set_def)
done

lemma not_valued_tautology2 : 
  "\<not> ValuedTautology (BVBExp (op \<or>) (SVBExp (VBBVarOp A, U)) (SVBExp (VBBVarOp B, V))) val_b val_v"
apply (auto simp add: ValuedTautology_def ValuedTautology_set_def)
done

lemma valued_tautology_or : 
  "(BoolOperand_eval A val_b) \<Longrightarrow> (BoolOperand_eval B val_b) \<Longrightarrow>
  (((BoolOperand_eval A val_b) \<and> (BoolOperand_eval B val_b)) \<longrightarrow> (U = V)) \<Longrightarrow> 
  ValuedTautology 
    (BVBExp (op \<or>)
      (BVBExp (op \<or>) 
        (SVBExp (A, U))
        (SVBExp (B, V)))
      (SVBExp ((VBBExpBinOp (op \<and>) 
                (VBBExpUnOp Not A) 
                (VBBExpUnOp Not B)), Q))) 
    val_b val_v"
apply (auto simp add: ValuedTautology_def ValuedTautology_set_def ValuedBool_bool_eval_def)
done

end
