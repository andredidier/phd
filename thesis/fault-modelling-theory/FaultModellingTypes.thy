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
  | VBBExpBinOp "bool \<Rightarrow> bool \<Rightarrow> bool" "'variavel BoolOperand" "'variavel BoolOperand"

datatype 'variavel ValuesOperand =
  VBVConstOp Values
  | VBVVarOp 'variavel

type_synonym ('vb,'vv) ValuedBool = "('vb BoolOperand \<times> 'vv ValuesOperand)"

type_synonym ('vb, 'vv) ValuedBoolExp = "nat \<rightharpoonup> (('vb,'vv) ValuedBool)"


end
