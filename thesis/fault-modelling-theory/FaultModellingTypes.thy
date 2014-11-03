theory FaultModellingTypes
imports Complex_Main

begin

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a" 

datatype FMode = Omission | Commission

datatype Values = 
  FMNominal real 
  | FMFailure FMode 

datatype 'variavel BoolOperand = 
  VBBConstOp bool
  | VBBVarOp 'variavel
  | VBBExpUnOp "bool \<Rightarrow> bool" "'variavel BoolOperand"
  | VBBExpBinOp "bool binop" "'variavel BoolOperand" "'variavel BoolOperand"

datatype ('vb, 'vv) ValuesOperand =
  VBVConstOp Values
  | VBVVarOp 'vv
  | VBVExpOp "('vb, 'vv) ValuedBool list" and
  ('vb, 'vv) ValuedBool = VB "'vb BoolOperand" "('vb, 'vv) ValuesOperand"

end
