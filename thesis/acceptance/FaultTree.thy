theory FaultTree
imports Main FaultModellingTypes ModeCondition ConditionalModePredicate Complex_Main
begin

datatype_new FaultTreeGate = FTGAnd | FTGOr

datatype_new 'a FaultTree =
  BasicEvent "'a"
  | IntermediaryEvent FaultTreeGate "'a FaultTree" "'a FaultTree" 

primrec FTG2BE :: "FaultTreeGate \<Rightarrow> 'a bool_expr \<Rightarrow> 'a bool_expr \<Rightarrow> 'a bool_expr"
where
  "FTG2BE FTGAnd b1 b2 = And_bool_expr b1 b2" |
  "FTG2BE FTGOr b1 b2 = Or_bool_expr b1 b2"

primrec FT2BE :: "'a FaultTree \<Rightarrow> 'a bool_expr"
where
  "FT2BE (BasicEvent a) = Atom_bool_expr a" |
  "FT2BE (IntermediaryEvent g t1 t2) = FTG2BE g (FT2BE t1) (FT2BE t2)"

definition FT_equiv_CVP :: "'a FaultTree \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> bool"
where
  "FT_equiv_CVP t P v \<equiv> equiv_test (FT2BE t) (CVP2BE P v)"

definition FaultTree_eval :: "'a FaultTree \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where "FaultTree_eval t s = val_bool_expr (FT2BE t) s"

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

primrec FT_probability :: "'a FaultTree \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
where
  "FT_probability (BasicEvent v1) P = P v1" |
  "FT_probability (IntermediaryEvent g l r) P = 
    (Gate_probability g) (FT_probability l P) (FT_probability r P)"

end
