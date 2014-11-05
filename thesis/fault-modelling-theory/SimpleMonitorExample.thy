theory SimpleMonitorExample
imports SystemModel ValuedTautology
begin

datatype FailureVarName = FBattery nat | FMon

definition Battery :: "nat \<Rightarrow> FailureVarName Component" where
  "Battery m \<equiv> (0, 
    [
        VBVExpOp [ 
          VB (VBBVarOp (FBattery m)) (VBVConstOp (FMFailure Omission)),
          VB (VBBExpUnOp Not (VBBVarOp (FBattery m))) (VBVConstOp (FMNominal 5))
        ]
    ])"


definition Monitor :: "nat \<Rightarrow> ((FailureVarName, ComponentPort) ValuesOperand \<Rightarrow> bool) \<Rightarrow> FailureVarName Component" where
  "Monitor m P \<equiv> (2, 
    [
        VBVExpOp [
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBConstOp (P (VBVVarOp (m, 1)))))
            (VBVVarOp (m, 1)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBExpUnOp Not (VBBConstOp (P (VBVVarOp (m, 1))))))
            (VBVVarOp (m, 2)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBConstOp (P (VBVVarOp (m, 1)))))
            (VBVVarOp (m, 2)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBExpUnOp Not (VBBConstOp (P (VBVVarOp (m, 1))))))
            (VBVVarOp (m, 1))
        ]
    ])"


definition SMon :: "FailureVarName System" where
  "SMon \<equiv> (
    [ Battery 0, Battery 1, Monitor 2 (\<lambda> x. False)], 
    [ (2,1) \<mapsto> (0,1), (2,2) \<mapsto> (1,1) ]
  )"

end
