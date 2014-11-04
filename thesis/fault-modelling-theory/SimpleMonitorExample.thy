theory SimpleMonitorExample
imports SystemModel ValuedTautology
begin

datatype FailureVarName = FBattery nat | FMon
datatype ValueVarName = MonIn nat | BatOut nat

primrec valuation :: "ValueVarName \<Rightarrow> (FailureVarName, ValueVarName) ValuesOperand" 
where
  "valuation (BatOut m) = VBVExpOp [ 
      VB (VBBExpUnOp Not (VBBVarOp (FBattery m))) (VBVConstOp (FMNominal 5)),
      VB (VBBVarOp (FBattery m)) (VBVConstOp (FMFailure Omission))
    ]"

definition Battery :: "nat \<Rightarrow> (FailureVarName, 'vv) Component" where
  "Battery m \<equiv> (m, ({}, { (1, 
    VBVExpOp [ 
      VB (VBBExpUnOp Not (VBBVarOp (FBattery m))) (VBVConstOp (FMNominal 5)),
      VB (VBBVarOp (FBattery m)) (VBVConstOp (FMFailure Omission))
    ] ) }))"

definition Monitor :: "nat \<Rightarrow> (((FailureVarName, ValueVarName) ValuesOperand) \<Rightarrow> bool) \<Rightarrow> 
    (FailureVarName, ValueVarName) Component" where
  "Monitor m P \<equiv> (m, ({
      (1, VBVVarOp (MonIn 1)),
      (2, VBVVarOp (MonIn 2))
    }, {
      (1, VBVExpOp [
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
      ])
    }))"

fun option_op :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "option_op f None vo = False" |
  "option_op f vo None = False" |
  "option_op f (Some v1) (Some v2) = f v1 v2"

fun lt_values :: "Values \<Rightarrow> Values \<Rightarrow> bool" where
  "lt_values (FMFailure f) v = True" |
  "lt_values v (FMFailure f) = False" |
  "lt_values (FMNominal n1) (FMNominal n2) = (n1 \<le> n2)"

definition SMon :: "(FailureVarName \<Rightarrow> bool) \<Rightarrow> (ValueVarName \<Rightarrow> Values) \<Rightarrow> 
    (FailureVarName, ValueVarName) System" where
  "SMon vb vv \<equiv> (
    {
      Battery 1, Battery 2, 
      Monitor 3 (\<lambda> Es. option_op lt_values (Some (FMNominal 2)) (ValuesOperand_value_eval Es vb vv))
    }, 
    {((1,1), (3,1)), ((2,1), (3,2))}
  )"

end
