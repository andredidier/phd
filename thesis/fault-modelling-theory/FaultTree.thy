theory FaultTree
imports Main FaultModellingTypes ModeCondition Complex_Main
begin

datatype FaultTreeGate = FTGAnd | FTGOr

datatype 'vb FaultTree =
  BasicEvent "'vb"
  | IntermediaryEvent FaultTreeGate "'vb FaultTree" "'vb FaultTree" 

fun FT_BO_equiv :: "'vb FaultTree \<Rightarrow> 'vb ModeCondition \<Rightarrow> bool"
where
  "FT_BO_equiv (BasicEvent v1) (MCVar v2) = (v1 = v2)" |
  "FT_BO_equiv (IntermediaryEvent FTGAnd t1 t2) (MCAnd b1 b2) = 
    ((FT_BO_equiv t1 b1) \<and> (FT_BO_equiv t2 b2))" |
  "FT_BO_equiv (IntermediaryEvent FTGOr t1 t2) (MCOr b1 b2) = 
    ((FT_BO_equiv t1 b1) \<and> (FT_BO_equiv t2 b2))" |
  "FT_BO_equiv T B = False"

primrec GateToOp :: "FaultTreeGate \<Rightarrow> ('vb ModeCondition binop)"
where
  "GateToOp FTGAnd = (\<lambda> a b. MCAnd a b)" |
  "GateToOp FTGOr = (\<lambda> a b. MCOr a b)"

primrec FT_to_BO :: "'vb FaultTree \<Rightarrow> 'vb ModeCondition"
where
  "FT_to_BO (BasicEvent v) = MCVar v" |
  "FT_to_BO (IntermediaryEvent g t1 t2) = (GateToOp g) (FT_to_BO t1) (FT_to_BO t2)"

definition FaultTree_eval :: "'vb FaultTree \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where "FaultTree_eval T vb = ModeCondition_eval (FT_to_BO T) vb"

(*
theorem "FaultTree_eval T vb \<longrightarrow> ModeCondition_eval (FT_to_BO T) vb"
apply (auto)
apply (auto simp add: FT_to_BO_def)
apply (auto simp add: FaultTree_eval_def)
apply (auto simp add: ModeCondition_eval_def)
done*)

(*
theorem "(ModeCondition_eval (FT_to_BO T) = (ModeCondition_eval B)) \<longrightarrow> 
  (FaultTree_eval T vb = ModeCondition_eval B vb)"
apply (auto)
apply (auto simp add: FT_to_BO_def)
apply (auto simp add: FaultTree_eval_def)
apply (auto simp add: ModeCondition_eval_def)
done*)

(*Returns the minimum basic event level, related to the root event*)
primrec min_basicEventLevel :: "'vb FaultTree \<Rightarrow> nat" 
where
  "min_basicEventLevel (BasicEvent _) = 0" |
  "min_basicEventLevel (IntermediaryEvent _ l r) =  
    1 + min (min_basicEventLevel l) (min_basicEventLevel r)"

primrec Gate_probability :: "FaultTreeGate \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
where
  "Gate_probability FTGAnd a b = a * b" |
  "Gate_probability FTGOr a b = (a + b) - (a * b)" 

primrec FT_probability :: "'vb FaultTree \<Rightarrow> ('vb \<Rightarrow> real) \<Rightarrow> real"
where
  "FT_probability (BasicEvent v1) P = P v1" |
  "FT_probability (IntermediaryEvent g l r) P = 
    (Gate_probability g) (FT_probability l P) (FT_probability r P)"

end
