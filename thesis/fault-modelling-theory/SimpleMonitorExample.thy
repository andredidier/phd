theory SimpleMonitorExample

imports FaultModelling

begin

datatype FMode = Omission ("O\<^sub>M") | Commission ("C\<^sub>O\<^sub>m")

datatype FailureVarName = FB1 | FB2 | FMon

notation FB1 ("F\<^sub>B\<^sub>1" 50)
notation FB2 ("F\<^sub>B\<^sub>2" 50)

datatype ComponentPortName = 
  OutB1 ("out\<^sub>B\<^sub>1") 
  | OutB2 ("out\<^sub>B\<^sub>2") 
  | In1Mon ("in\<^sub>M\<^sub>o\<^sub>n\<^sub>1")
  | In2Mon ("in\<^sub>M\<^sub>o\<^sub>n\<^sub>2")
  | OutMon ("out\<^sub>M\<^sub>o\<^sub>n")

definition Battery :: "FailureVarName \<Rightarrow> (FailureVarName, ComponentPortName, FMode) Component" where
  "Battery FB \<equiv> [OutB1 \<mapsto> 
        VBVExpOp [ 
          VB (VBBVarOp (FB)) (VBVConstOp (FMFailure Omission)),
          VB (VBBNotOp (VBBVarOp (FB))) (VBVConstOp (FMNominal 5))
        ]
    ]"

fun lt_values_fmode :: "FMode Values option \<Rightarrow> FMode Values \<Rightarrow> bool"
where
  "lt_values_fmode None _ = False" |
  "lt_values_fmode (Some (FMNominal a)) (FMNominal b) = (a < b)" |
  "lt_values_fmode (Some (FMFailure _)) (FMNominal b) = (b > 0)" |
  "lt_values_fmode _ (FMFailure _) = False" 

definition Monitor :: " 
  ((FailureVarName, ComponentPortName, FMode) ValuesOperand \<Rightarrow> bool) \<Rightarrow> 
  (FailureVarName, ComponentPortName, FMode) Component" where
  "Monitor P \<equiv>  
    [ OutMon \<mapsto>
        VBVExpOp [
          VB 
            (VBBAndOp 
              (VBBNotOp (VBBVarOp FMon))
              (VBBConstOp (P (VBVVarOp In1Mon))))
            (VBVVarOp In1Mon),
          VB 
            (VBBAndOp 
              (VBBNotOp (VBBVarOp FMon))
              (VBBNotOp (VBBConstOp (P (VBVVarOp In1Mon)))))
            (VBVVarOp In2Mon),
          VB 
            (VBBAndOp 
              (VBBVarOp FMon)
              (VBBConstOp (P (VBVVarOp In1Mon))))
            (VBVVarOp In2Mon),
          VB 
            (VBBAndOp 
              (VBBVarOp FMon)
              (VBBNotOp (VBBConstOp (P (VBVVarOp In1Mon)))))
            (VBVVarOp In1Mon)
        ]
    ]"


definition SMon :: "(FailureVarName \<Rightarrow> bool) \<Rightarrow> (ComponentPortName \<Rightarrow> FMode Values) \<Rightarrow>
    (FailureVarName, ComponentPortName, FMode) Component" where
  "SMon vb vv \<equiv> (
    System 
    [ In1Mon \<mapsto> OutB1, In2Mon \<mapsto> OutB2 ] 
    [ Battery FB1, 
      Battery FB2, 
      Monitor 
        (\<lambda> x. lt_values_fmode (ValuesOperand_value_eval x vb vv) (FMNominal 2))]
  )"

value "the ((SMon vb vv) OutMon)"


(*TODO: predicates over output expressions *)

end
