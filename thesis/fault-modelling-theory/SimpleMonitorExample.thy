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

definition Battery :: "FailureVarName \<Rightarrow> 
  ((ComponentPortName CInput) \<Rightarrow> ((FailureVarName, ComponentPortName, FMode) ValuesOperand)) \<Rightarrow>
  (FailureVarName, ComponentPortName, FMode) Component" where
  "Battery FB inputs \<equiv> 
  [
    OutB1 \<mapsto> 
      VBVExpOp [ 
        VB (VBBVarOp (FB)) (VBVConstOp (FMFailure Omission)),
        VB (VBBNotOp (VBBVarOp (FB))) (VBVConstOp (FMNominal 5))
      ]
  ]"

definition Monitor :: " 
  ((FailureVarName, ComponentPortName, FMode) ValuesOperand \<Rightarrow> FailureVarName BoolOperand) \<Rightarrow> 
  ((ComponentPortName CInput) \<Rightarrow> ((FailureVarName, ComponentPortName, FMode) ValuesOperand)) \<Rightarrow>
  (FailureVarName, ComponentPortName, FMode) Component" where
  "Monitor P inputs \<equiv>  
  [ 
    OutMon \<mapsto>
      VBVExpOp [
        VB 
          (VBBAndOp 
            (VBBNotOp (VBBVarOp FMon))
            (P (inputs In1Mon)))
          (inputs In1Mon),
        VB 
          (VBBAndOp 
            (VBBNotOp (VBBVarOp FMon))
            (VBBNotOp (P (inputs In1Mon))))
          (inputs In2Mon),
        VB 
          (VBBAndOp 
            (VBBVarOp FMon)
            (P (inputs In1Mon)))
          (inputs In2Mon),
        VB 
          (VBBAndOp 
            (VBBVarOp FMon)
            (VBBNotOp (P (inputs In1Mon))))
          (inputs In1Mon)
      ]
  ]"


definition SMon :: "(ComponentPortName \<Rightarrow> FMode Values) \<Rightarrow>
    (FailureVarName, ComponentPortName, FMode) Component" where
  "SMon vv \<equiv> (
    System 
    [ In1Mon \<mapsto> OutB1, In2Mon \<mapsto> OutB2 ] 
    [ 
      Battery FB1, 
      Battery FB2, 
      Monitor 
        (ValuesOperandPredicate_BoolOperand (lte_Values (FMNominal 2)) vv)
    ]
  )"

value "the ((SMon vv) OutMon)"

definition Basic :: "(FailureVarName, ComponentPortName, FMode) Component" where
  "Basic \<equiv> 
  (
    System
    [ In1Mon \<mapsto> OutB1, In2Mon \<mapsto> OutB2 ]
    [ 
      (\<lambda> inputs. 
        [ 
          OutMon \<mapsto> 
            VBVExpOp [ 
              VB (VBBConstOp True) (inputs In1Mon),
              VB (VBBConstOp False) (inputs In2Mon)
            ]
        ] ),
      (\<lambda> inputs. [ OutB1 \<mapsto> VBVConstOp (FMNominal 1) ]),
      (\<lambda> inputs. [ OutB2 \<mapsto> VBVConstOp (FMNominal 2) ])
    ]
  )"

value "the (Basic OutMon)"



(*TODO: predicates over output expressions *)

end
