theory SimpleMonitorExample

imports FaultModelling

begin

datatype FMode = Omission ("O\<^sub>M") | Commission ("C\<^sub>O\<^sub>m")

datatype FailureVarName = FBattery nat | FMon

notation FBattery ("F\<^sub>b\<^sub>_" 50)

definition Battery :: "nat \<Rightarrow> (FailureVarName, FMode) Component" where
  "Battery m \<equiv> (0, 
    [
        VBVExpOp [ 
          VB (VBBVarOp (FBattery m)) (VBVConstOp (FMFailure Omission)),
          VB (VBBNotOp (VBBVarOp (FBattery m))) (VBVConstOp (FMNominal 5))
        ]
    ])"


definition Monitor :: "(nat \<Rightarrow> ComponentPort) \<Rightarrow> 
  ((FailureVarName, ComponentPort, FMode) ValuesOperand \<Rightarrow> bool) \<Rightarrow> 
  (FailureVarName, FMode) Component" where
  "Monitor Port P \<equiv> (2, 
    [
        VBVExpOp [
          VB 
            (VBBAndOp 
              (VBBNotOp (VBBVarOp FMon))
              (VBBConstOp (P (VBVVarOp (Port 1)))))
            (VBVVarOp (Port 1)),
          VB 
            (VBBAndOp 
              (VBBNotOp (VBBVarOp FMon))
              (VBBNotOp (VBBConstOp (P (VBVVarOp (Port 1))))))
            (VBVVarOp (Port 2)),
          VB 
            (VBBAndOp 
              (VBBVarOp FMon)
              (VBBConstOp (P (VBVVarOp (Port 1)))))
            (VBVVarOp (Port 2)),
          VB 
            (VBBAndOp 
              (VBBVarOp FMon)
              (VBBNotOp (VBBConstOp (P (VBVVarOp (Port 1))))))
            (VBVVarOp (Port 1))
        ]
    ])"


definition SMon :: "(FailureVarName, FMode) System" where
  "SMon \<equiv> (
    [ Battery 1, Battery 2, Monitor (\<lambda> p_index. (2, p_index)) (\<lambda> x. False)], 
    [ (2,0) \<mapsto> (0,0), (2,1) \<mapsto> (1,0) ]
  )"

end
