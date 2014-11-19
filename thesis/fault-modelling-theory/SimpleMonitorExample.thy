theory SimpleMonitorExample

imports FaultModelling

begin

datatype FMode = Omission ("O\<^sub>M") | Commission ("C\<^sub>O\<^sub>m")

datatype FailureVarName = 
  FB1 ("F\<^sub>B\<^sub>1" 50) 
  | FB2 ("F\<^sub>B\<^sub>2" 50)
  | FMon ("F\<^sub>M\<^sub>o\<^sub>n" 50)

datatype ComponentPortName = 
  OutB1 ("out\<^sub>B\<^sub>1") 
  | OutB2 ("out\<^sub>B\<^sub>2") 
  | In1Mon ("in\<^sub>M\<^sub>o\<^sub>n\<^sub>1")
  | In2Mon ("in\<^sub>M\<^sub>o\<^sub>n\<^sub>2")
  | OutMon ("out\<^sub>M\<^sub>o\<^sub>n")

definition Battery :: "ComponentPortName \<Rightarrow> FailureVarName \<Rightarrow> 
  (FailureVarName, FMode, ComponentPortName, ComponentPortName) Component" where
  "Battery OutP FB \<equiv> \<lambda> m.
  [
    OutP \<mapsto> 
      VBVExpOp [ 
        VB (VCVarOp (FB)) (VBVConstOp (FMFailure Omission)),
        VB (VCNotOp (VCVarOp (FB))) (VBVConstOp (FMNominal 5))
      ]
  ]"

definition Monitor :: " 
  ((FailureVarName, FMode, ComponentPortName) ValuesOperand \<Rightarrow> FailureVarName ValueCondition) \<Rightarrow> 
  (FailureVarName, FMode, ComponentPortName, ComponentPortName) Component" where
  "Monitor P \<equiv>  \<lambda> m.
  [ 
    OutMon \<mapsto>
      VBVExpOp [
        VB 
          (VCAndOp 
            (VCNotOp (VCVarOp FMon))
            (P (m In1Mon)))
          (m In1Mon),
        VB 
          (VCAndOp 
            (VCNotOp (VCVarOp FMon))
            (VCNotOp (P (m In1Mon))))
          (m In2Mon),
        VB 
          (VCAndOp 
            (VCVarOp FMon)
            (P (m In1Mon)))
          (m In2Mon),
        VB 
          (VCAndOp 
            (VCVarOp FMon)
            (VCNotOp (P (m In1Mon))))
          (m In1Mon)
      ]
  ]"

definition SMon_A :: "(ComponentPortName, ComponentPortName) Connections"
where
  "SMon_A \<equiv> [ In1Mon \<mapsto> OutB1, In2Mon \<mapsto> OutB2 ] "

definition SMon_Cs :: 
  "(FailureVarName, FMode, ComponentPortName, ComponentPortName) Component list"
where 
  "SMon_Cs \<equiv> 
  [ 
    Battery OutB1 FB1, 
    Battery OutB2 FB2, 
    Monitor 
      (ValuesOperandPredicate_ValueCondition (lte_Values (FMNominal 2)))
  ]"

definition SMon :: 
  "(FailureVarName, FMode, ComponentPortName, ComponentPortName) Component" 
where
  "SMon \<equiv> (
    System SMon_A SMon_Cs
  )"

definition SMon_OutMon :: "(FailureVarName, FMode, ComponentPortName) ValuesOperand"
where
  "SMon_OutMon \<equiv> the (SMon (\<lambda> x. VBVConstOp (FMVar x)) OutMon)"

value "SMon_OutMon"

value "normalise_ValueCondition 
  (ValuesOperandPredicate_ValueCondition (eq_Values (FMFailure Omission)) SMon_OutMon)"

lemma "
  ValueCondition_eval (
    ValuesOperandPredicate_ValueCondition (eq_Values (FMFailure Omission)) SMon_OutMon
  ) vb
  =
  ValueCondition_eval (
    VCOrOp 
    (
      VCAndOp (VCVarOp FB1) (VCVarOp FB2)
    )
    (
      VCAndOp 
        (VCVarOp FMon) 
        (VCOrOp (VCVarOp FB1) (VCVarOp FB2))
    )
  ) vb"
apply (auto)
apply (auto simp add: SMon_OutMon_def SMon_def SMon_Cs_def SMon_A_def Battery_def Monitor_def)
apply (auto simp add: System_def SystemPortValuation_def SystemComponents_def fun_upd_fun_def)
apply (auto simp add: normalise_expand_ValuesOperand_def)
done

end
