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


definition Monitor :: "(nat \<Rightarrow> ComponentPort) \<Rightarrow> ((FailureVarName, ComponentPort) ValuesOperand \<Rightarrow> bool) \<Rightarrow> FailureVarName Component" where
  "Monitor Port P \<equiv> (2, 
    [
        VBVExpOp [
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBConstOp (P (VBVVarOp (Port 1)))))
            (VBVVarOp (Port 1)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBExpUnOp Not (VBBVarOp FMon))
              (VBBExpUnOp Not (VBBConstOp (P (VBVVarOp (Port 1))))))
            (VBVVarOp (Port 2)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBConstOp (P (VBVVarOp (Port 1)))))
            (VBVVarOp (Port 2)),
          VB 
            (VBBExpBinOp 
              (op \<and>) 
              (VBBVarOp FMon)
              (VBBExpUnOp Not (VBBConstOp (P (VBVVarOp (Port 1))))))
            (VBVVarOp (Port 1))
        ]
    ])"


definition SMon :: "FailureVarName System" where
  "SMon \<equiv> (
    [ Battery 1, Battery 2, Monitor (\<lambda> p_index. (2, p_index)) (\<lambda> x. False)], 
    [ (2,0) \<mapsto> (0,0), (2,1) \<mapsto> (1,0) ]
  )"

end
