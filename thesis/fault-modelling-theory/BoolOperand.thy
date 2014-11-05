theory BoolOperand

imports Main FaultModellingTypes

begin

primrec "BoolOperand_eval" :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) vb = b" |
  "BoolOperand_eval (VBBVarOp a) vb = vb a" |
  "BoolOperand_eval (VBBExpUnOp exp_op op1) vb = exp_op (BoolOperand_eval op1 vb)" |
  "BoolOperand_eval (VBBExpBinOp exp_op op1 op2) vb = 
    exp_op (BoolOperand_eval op1 vb) (BoolOperand_eval op2 vb)"

primrec 
  expand_BoolOperand_ValuesOperand :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuesOperand \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_list :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuedBool list \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_VB :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuedBool \<Rightarrow> ('vb, 'vv) ValuedBool"
where
  "expand_BoolOperand_ValuesOperand e (VBVConstOp c) = (VB e (VBVConstOp c)) # []" |
  "expand_BoolOperand_ValuesOperand e (VBVVarOp v) = (VB e (VBVVarOp v)) # []" |
  expand_BoolOperand_ValuesOperand_VBExpOp:
  "expand_BoolOperand_ValuesOperand e (VBVExpOp Es) = expand_BoolOperand_ValuesOperand_list e Es" |
  "expand_BoolOperand_ValuesOperand_list e [] = []" |
  "expand_BoolOperand_ValuesOperand_list e (E # Es) = 
    (expand_BoolOperand_ValuesOperand_VB e E) # (expand_BoolOperand_ValuesOperand_list e Es)" |
  "expand_BoolOperand_ValuesOperand_VB e1 (VB e2 v2) = VB (VBBExpBinOp (op \<and>) e1 e2) v2"

(* FAZER O NORMALISE DE BOOLEANO PARA SUPORTAR A EQUIVALENCIA DE ÁRVORE COM BOOLEANO *)

end
