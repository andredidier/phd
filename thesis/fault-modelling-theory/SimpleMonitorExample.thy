theory SimpleMonitorExample

imports FaultModelling

begin

datatype FMode = Omission ("O\<^sub>M") | Commission ("C\<^sub>O\<^sub>m")

datatype FailureVarName = FB1 | FB2 | FMon

notation FB1 ("F\<^sub>B\<^sub>1" 50)
notation FB2 ("F\<^sub>B\<^sub>2" 50)

definition Battery :: "FailureVarName \<Rightarrow> (FailureVarName, FMode) Component" where
  "Battery FB \<equiv> (0, 
    [
        VBVExpOp [ 
          VB (VBBVarOp (FB)) (VBVConstOp (FMFailure Omission)),
          VB (VBBNotOp (VBBVarOp (FB))) (VBVConstOp (FMNominal 5))
        ]
    ])"

fun lt_values_fmode :: "FMode Values option \<Rightarrow> FMode Values \<Rightarrow> bool"
where
  "lt_values_fmode None _ = False" |
  "lt_values_fmode (Some (FMNominal a)) (FMNominal b) = (a < b)" |
  "lt_values_fmode (Some (FMFailure _)) (FMNominal b) = (b > 0)" |
  "lt_values_fmode _ (FMFailure _) = False" 

definition Monitor :: "(nat \<Rightarrow> ComponentPort) \<Rightarrow> 
  ((FailureVarName, ComponentPort, FMode) ValuesOperand \<Rightarrow> bool) \<Rightarrow> 
  (FailureVarName, FMode) Component" where
  "Monitor Port P \<equiv> (2, 
    [
        VBVExpOp [
          VB 
            (VBBAndOp 
              (VBBNotOp (VBBVarOp FMon))
              (VBBConstOp (P (VBVVarOp (Port 0)))))
            (VBVVarOp (Port 0)),
          VB 
            (VBBAndOp 
              (VBBNotOp (VBBVarOp FMon))
              (VBBNotOp (VBBConstOp (P (VBVVarOp (Port 0))))))
            (VBVVarOp (Port 1)),
          VB 
            (VBBAndOp 
              (VBBVarOp FMon)
              (VBBConstOp (P (VBVVarOp (Port 0)))))
            (VBVVarOp (Port 1)),
          VB 
            (VBBAndOp 
              (VBBVarOp FMon)
              (VBBNotOp (VBBConstOp (P (VBVVarOp (Port 0))))))
            (VBVVarOp (Port 0))
        ]
    ])"


definition SMon :: "(FailureVarName \<Rightarrow> bool) \<Rightarrow> (ComponentPort  \<Rightarrow> FMode Values) \<Rightarrow>
    (FailureVarName, FMode) System" where
  "SMon vb vv \<equiv> (
    [ Battery FB1, Battery FB2, 
      Monitor 
        (\<lambda> p_index. (2, p_index)) 
        (\<lambda> x. lt_values_fmode (ValuesOperand_value_eval x vb vv) (FMNominal 2))], 
    [ (2,0) \<mapsto> (0,0), (2,1) \<mapsto> (1,0) ]
  )"

theorem valid_SMon : "ValidSystem (SMon vb vv)"
apply (auto simp add: ValidSystem_def)
apply (simp add: ValidConnection_def)
apply (auto)
apply (auto simp add: ValidComponents_def)
apply (auto simp add: SystemConnections_def)
apply (auto simp add: SystemComponentsInputs_def SystemComponentsOutputs_def)
done

end
