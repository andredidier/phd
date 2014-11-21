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
      CMExp [ 
        CM (MCVar (FB)) (CMConst (FailureMode Omission)),
        CM (MCNot (MCVar (FB))) (CMConst (NominalMode 5))
      ]
  ]"

lemma "ValuedTautology (the ((Battery outp fb) env outp))"
apply (auto simp add: Battery_def)
apply (auto simp add: ValuedTautology_def ValuedTautology_CVList_def CMP2MC_def)
apply (auto simp add: ModeCondition_Tautology_def taut_test_def)
done

definition Monitor :: " 
  ((FailureVarName, FMode, ComponentPortName) ConditionalMode \<Rightarrow> FailureVarName ModeCondition) \<Rightarrow> 
  (FailureVarName, FMode, ComponentPortName, ComponentPortName) Component" where
  "Monitor P \<equiv>  \<lambda> m.
  [ 
    OutMon \<mapsto>
      CMExp [
        CM 
          (MCAnd 
            (MCNot (MCVar FMon))
            (P (m In1Mon)))
          (m In1Mon),
        CM 
          (MCAnd 
            (MCNot (MCVar FMon))
            (MCNot (P (m In1Mon))))
          (m In2Mon),
        CM 
          (MCAnd 
            (MCVar FMon)
            (P (m In1Mon)))
          (m In2Mon),
        CM 
          (MCAnd 
            (MCVar FMon)
            (MCNot (P (m In1Mon))))
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
      (ConditionalModePredicate_ModeCondition (lte_Values (NominalMode 2)))
  ]"

definition SMon :: 
  "(FailureVarName, FMode, ComponentPortName, ComponentPortName) Component" 
where
  "SMon \<equiv> System SMon_A SMon_Cs"


definition SMon_OutMon :: "(FailureVarName, FMode, ComponentPortName) ConditionalMode"
where
  "SMon_OutMon \<equiv> the (SMon (\<lambda> x. CMConst (VarMode x)) OutMon)"


theorem "ValuedTautology SMon_OutMon"
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: SMon_OutMon_def SMon_def SMon_A_def SMon_Cs_def)
sorry

lemma "
  ModeCondition_Equiv
    (ConditionalModePredicate_ModeCondition (eq_Values (FailureMode Omission)) SMon_OutMon)
    (
      MCOr 
      (
        MCAnd (MCVar FB1) (MCVar FB2)
      )
      (
        MCAnd 
          (MCVar FMon) 
          (MCOr (MCVar FB1) (MCVar FB2))
      )
    )"
apply (auto simp add: SMon_OutMon_def SMon_def SMon_Cs_def SMon_A_def Battery_def Monitor_def)
apply (auto simp add: System_def SystemPortValuation_def SystemComponents_def fun_upd_fun_def)
apply (auto simp add: ConditionalModePredicate_ModeCondition_def CMPPredicate_def)
apply (auto simp add: lte_Values_def)
apply (auto simp add: CMP2MC_def fold_def)
apply (auto simp add: ModeCondition_Equiv_def equiv_test_def taut_test_def Let_def)
apply (auto simp add: normalise_ConditionalMode_def)
done

end
