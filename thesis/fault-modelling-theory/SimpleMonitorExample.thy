theory SimpleMonitorExample
imports SystemModel ValuedTautology
begin

datatype FailureVarName = FBattery nat | FMon
datatype ValueVarName = MonIn nat | BatOut nat | MonOut

definition Battery :: "nat \<Rightarrow> (FailureVarName, ValueVarName) Component" where
  "Battery m \<equiv> ({}, 
    [
      BatOut m \<mapsto> 
        VBVExpOp [ 
          VB (VBBVarOp (FBattery 1)) (VBVConstOp (FMFailure Omission)),
          VB (VBBExpUnOp Not (VBBVarOp (FBattery m))) (VBVConstOp (FMNominal 5))
        ]
    ])"


definition Monitor :: "((FailureVarName, ValueVarName) ValuesOperand \<Rightarrow> bool) \<Rightarrow> (FailureVarName, ValueVarName) Component" where
  "Monitor P \<equiv> ({MonIn 1, MonIn 2}, 
    [
      MonOut \<mapsto> 
        VBVExpOp [
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBConstOp (P (VBVVarOp (MonIn 1)))))
            (VBVVarOp (MonIn 1)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBExpUnOp Not (VBBConstOp (P (VBVVarOp (MonIn 1))))))
            (VBVVarOp (MonIn 2)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBConstOp (P (VBVVarOp (MonIn 1)))))
            (VBVVarOp (MonIn 2)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBExpUnOp Not (VBBConstOp (P (VBVVarOp (MonIn 1))))))
            (VBVVarOp (MonIn 1))
        ]
    ])"


definition SMon :: "(FailureVarName, ValueVarName) System" where
  "SMon \<equiv> (
    { Battery 1, Battery 2, Monitor (\<lambda> x. False) }, 
    [ MonIn 1 \<mapsto> BatOut 1, MonIn 2 \<mapsto> BatOut 2 ]
  )"

end
