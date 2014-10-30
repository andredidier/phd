theory ValuedTautology

imports FaultModellingTypes

begin

type_synonym 'a gate = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

datatype 'variavel ValuedBoolOperand = 
  ValuedBoolConstOperand bool
  | ValuedBoolVarOperand 'variavel
  | ValuedBoolExpOperand "bool \<Rightarrow> bool \<Rightarrow> bool" "'variavel ValuedBoolOperand" "'variavel ValuedBoolOperand"

type_synonym 'variavel ValuedBool = "('variavel ValuedBoolOperand \<times> Values)"

primrec "operand_eval" :: "'variavel ValuedBoolOperand \<Rightarrow> ('variavel \<Rightarrow> bool) \<Rightarrow> bool" where
  "operand_eval (ValuedBoolConstOperand b) valuation = b" |
  "operand_eval (ValuedBoolVarOperand a) valuation = valuation a" |
  "operand_eval (ValuedBoolExpOperand exp_op op1 op2) valuation = 
    exp_op (operand_eval op1 valuation) (operand_eval op2 valuation)"

definition bool_eval :: "'variavel ValuedBool \<Rightarrow> ('variavel \<Rightarrow> bool) \<Rightarrow> bool" where 
  "bool_eval VB valuation \<equiv> operand_eval (fst VB) valuation"

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a" 

datatype 'variavel ValuedBoolExp = 
  SingleValuedBoolExp "'variavel ValuedBool"
  | BinaryValuedBoolExp "('variavel ValuedBool) binop" "'variavel ValuedBoolExp" "'variavel ValuedBoolExp"

end
