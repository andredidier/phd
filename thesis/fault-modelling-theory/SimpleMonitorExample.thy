theory SimpleMonitorExample

imports FaultModelling FaultTree

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

type_synonym SMComponent =
"(FailureVarName, FMode, ComponentPortName, ComponentPortName) Component"

type_synonym SMValue = "(FMode, ComponentPortName) OperationalMode"

type_synonym SMConditionalMode = "(FailureVarName, FMode, ComponentPortName) ConditionalMode"

definition Battery :: "ComponentPortName \<Rightarrow> FailureVarName \<Rightarrow> SMComponent" where
  "Battery OutP FB \<equiv> \<lambda> m.
  [
    OutP \<mapsto> CVIF FB (CVC (FailureMode Omission)) (CVC (NominalMode 5))
  ]"

definition Monitor :: "(SMValue \<Rightarrow> bool) \<Rightarrow> SMComponent" where
  "Monitor P \<equiv> \<lambda> m . 
  [
    OutMon \<mapsto>
      CVIF FMon 
        (ConditionalValuePredicate P (m In1Mon) (m In1Mon) (m In2Mon)) 
        (ConditionalValuePredicate P (m In1Mon) (m In2Mon) (m In1Mon)) 
  ]"

definition SMon_A :: "(ComponentPortName, ComponentPortName) Connections"
where
  "SMon_A \<equiv> [ In1Mon \<mapsto> OutB1, In2Mon \<mapsto> OutB2 ] "

definition SMon_Cs :: "SMComponent list"
where 
  "SMon_Cs \<equiv> 
  [ 
    Battery OutB1 FB1, 
    Battery OutB2 FB2, 
    Monitor (\<lambda> b . (eq_Values (FailureMode Omission) b) \<or> (gt_Values (NominalMode 2) b))
  ]"

definition SMon :: "SMComponent" 
where
  "SMon \<equiv> System SMon_A SMon_Cs"


definition SMon_OutMon :: "SMConditionalMode"
where
  "SMon_OutMon \<equiv> the (SMon (\<lambda> x. CVC (VarMode x)) OutMon)"

lemma "equiv_test 
  (CVP2BE 
    (\<lambda> b . b = (FailureMode Omission)) 
    (the ((Battery OutB1 FB1) (\<lambda> x. CVC (VarMode x)) OutB1)))
  (Atom_bool_expr FB1)"
apply (auto simp add: Battery_def equiv_test)
done

lemma "equiv_test 
    (CVP2BE (\<lambda> b . b = (FailureMode Omission)) SMon_OutMon)
    (Or_bool_expr 
      (And_bool_expr (Atom_bool_expr FB1) (Atom_bool_expr FB2)) 
      (And_bool_expr 
        (Atom_bool_expr FMon) 
        (Or_bool_expr (Atom_bool_expr FB1) (Atom_bool_expr FB2))))"
apply (simp add: SMon_OutMon_def SMon_def SMon_Cs_def SMon_A_def Battery_def Monitor_def)
apply (simp add: System_def SystemComponents_def SystemPortValuation_def )
apply (simp add: fun_upd_fun_def)
apply (simp add: lt_Values_def)
apply (auto simp add: equiv_test)
done

end
