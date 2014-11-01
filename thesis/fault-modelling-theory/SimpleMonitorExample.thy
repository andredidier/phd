theory SimpleMonitorExample
imports SystemModel ValuedTautology
begin

datatype FailureVarName = FBattery nat | FMon
datatype ValueVarName = Mon nat

definition Battery :: "nat \<Rightarrow> (FailureVarName, 'vv) Component" where
  "Battery m \<equiv> (m, ({}, { (1, 
    map_of [ 
      (1,(VBBExpUnOp Not (VBBVarOp (FBattery m)), VBVConstOp (FMNominal 5))),
      (2,(VBBVarOp (FBattery m), VBVConstOp (FMFailure Omission))) 
    ] ) }))"

definition In :: "ValueVarName \<Rightarrow> ((FailureVarName, ValueVarName) ValuedBoolExp)" where
  "In x \<equiv> map_of [ (1, (VBBConstOp True, VBVVarOp x)) ]"
  

definition Monitor :: "nat \<Rightarrow> (((FailureVarName, ValueVarName) ValuedBoolExp) \<Rightarrow> bool) \<Rightarrow> 
    (FailureVarName, ValueVarName) Component" where
  "Monitor m P \<equiv> (m, ({
      (1, In (Mon 1)),
      (2, In (Mon 2))
    }, {
      (1, map_of [
        (1, (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBConstOp (P (In (Mon 1)))), 
            VBVVarOp (Mon 1))),
        (2, (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBExpUnOp Not (VBBConstOp (P (In (Mon 1))))), 
            VBVVarOp (Mon 2))),
        (3, (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBConstOp (P (In (Mon 1)))), 
            VBVVarOp (Mon 2))),
        (4, (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBExpUnOp Not (VBBConstOp (P (In (Mon 1))))), 
            VBVVarOp (Mon 1)))
      ])
    }))"

definition SMon :: "(FailureVarName \<Rightarrow> bool) \<Rightarrow> (ValueVarName \<Rightarrow> Values) \<Rightarrow> (FailureVarName, ValueVarName) System" where
  "SMon val_b val_v\<equiv> (
    {
      Battery 1, Battery 2, 
      Monitor 3 (\<lambda> Es. ((ValuedBoolExp_value_eval Es val_b val_v) = (FMNominal 2)))
    }, 
    {((1,1), (3,1)), ((2,1), (3,2))}
  )"

end
