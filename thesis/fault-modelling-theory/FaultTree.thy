theory FaultTree
imports Main FaultModellingTypes BoolOperand
begin

datatype 'vb FaultTree =
  BasicEvent "'vb"
  | IntermediaryEvent "'vb FTGate" "'vb FaultTree" "'vb FaultTree" and
  'vb FTGate = FTGAnd | FTGOr

fun FT_BO_equiv :: "'vb FaultTree \<Rightarrow> 'vb BoolOperand \<Rightarrow> bool"
where
  "FT_BO_equiv (BasicEvent v1) (VBBVarOp v2) = (v1 = v2)" |
  "FT_BO_equiv (IntermediaryEvent FTGAnd t1 t2) (VBBAndOp b1 b2) = 
    ((FT_BO_equiv t1 b1) \<and> (FT_BO_equiv t2 b2))" |
  "FT_BO_equiv (IntermediaryEvent FTGOr t1 t2) (VBBOrOp b1 b2) = 
    ((FT_BO_equiv t1 b1) \<and> (FT_BO_equiv t2 b2))" |
  "FT_BO_equiv T B = False"

primrec FT_to_BO :: "'vb FaultTree \<Rightarrow> 'vb BoolOperand" and
  FT_to_BO_gate :: "'vb FTGate \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "FT_to_BO (BasicEvent v) = VBBVarOp v" |
  "FT_to_BO (IntermediaryEvent g t1 t2) = FT_to_BO_gate g (FT_to_BO t1) (FT_to_BO t2)" |
  "FT_to_BO_gate FTGAnd b1 b2 = VBBAndOp b1 b2" |
  "FT_to_BO_gate FTGOr b1 b2 = VBBOrOp b1 b2"

definition FaultTree_eval :: "'vb FaultTree \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where "FaultTree_eval T vb = BoolOperand_eval (FT_to_BO T) vb"

(*
theorem "FaultTree_eval T vb \<longrightarrow> BoolOperand_eval (FT_to_BO T) vb"
apply (auto)
apply (auto simp add: FT_to_BO_def)
apply (auto simp add: FaultTree_eval_def)
apply (auto simp add: BoolOperand_eval_def)
done*)

(*
theorem "(BoolOperand_eval (FT_to_BO T) = (BoolOperand_eval B)) \<longrightarrow> (FaultTree_eval T vb = BoolOperand_eval B vb)"
apply (auto)
apply (auto simp add: FT_to_BO_def)
apply (auto simp add: FaultTree_eval_def)
apply (auto simp add: BoolOperand_eval_def)
done*)

end
