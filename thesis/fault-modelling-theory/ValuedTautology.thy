theory ValuedTautology

imports FaultModellingTypes Map

begin

datatype 'variavel BoolOperand = 
  VBBConstOp bool
  | VBBVarOp 'variavel
  | VBBExpUnOp "bool \<Rightarrow> bool" "'variavel BoolOperand"
  | VBBExpBinOp "bool \<Rightarrow> bool \<Rightarrow> bool" "'variavel BoolOperand" "'variavel BoolOperand"

datatype 'variavel ValuesOperand =
  VBVConstOp Values
  | VBVVarOp 'variavel

type_synonym ('vb,'vv) ValuedBool = "('vb BoolOperand \<times> 'vv ValuesOperand)"

primrec "BoolOperand_eval" :: "'variavel BoolOperand \<Rightarrow> ('variavel \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) valuation = b" |
  "BoolOperand_eval (VBBVarOp a) valuation = valuation a" |
  "BoolOperand_eval (VBBExpUnOp exp_op op1) valuation = exp_op (BoolOperand_eval op1 valuation)" |
  "BoolOperand_eval (VBBExpBinOp exp_op op1 op2) valuation = 
    exp_op (BoolOperand_eval op1 valuation) (BoolOperand_eval op2 valuation)"

primrec "ValuesOperand_eval" :: "'variavel ValuesOperand \<Rightarrow> ('variavel \<Rightarrow> Values) \<Rightarrow> Values" where
  "ValuesOperand_eval (VBVConstOp v) valuation = v" |
  "ValuesOperand_eval (VBVVarOp a) valuation = valuation a"

primrec ValuedBool_bool_eval :: "(('vb,'vv) ValuedBool) option \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where 
  "ValuedBool_bool_eval None valuation = False" |
  "ValuedBool_bool_eval (Some VB) valuation = BoolOperand_eval (fst VB) valuation"

primrec ValuedBool_value_eval :: "(('vb, 'vv) ValuedBool) option \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> Values" where 
  "ValuedBool_value_eval None valuation = FMUndefined" |
  "ValuedBool_value_eval (Some VB) valuation = ValuesOperand_eval (snd VB) valuation"

type_synonym ('vb, 'vv) ValuedBoolExp = "nat \<rightharpoonup> (('vb,'vv) ValuedBool)"

definition ValuedBoolExp_bool_eval :: "('vb,'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "ValuedBoolExp_bool_eval Es val_b \<equiv> (\<exists> i \<in> (dom Es). ValuedBool_bool_eval (Es i) val_b)"

lemma to_be_or_not_to_be1 : "(BoolOperand_eval E val_b) \<or> (BoolOperand_eval (VBBExpUnOp Not E) val_b)"
apply (auto)
done

lemma to_be_or_not_to_be2 : "ValuedBoolExp_bool_eval (map_of [ (1, (E,V)), (2,(VBBExpUnOp Not E, U)) ]) val_b"
apply (auto simp add: to_be_or_not_to_be1 ValuedBoolExp_bool_eval_def ValuedBool_bool_eval_def )
done

lemma to_be_or_not_to_be3 : 
  "(\<not> (ValuedBool_bool_eval (Some (VBBExpUnOp Not E,V)) val_b)) \<Longrightarrow> (ValuedBool_bool_eval (Some (E,U)) val_b)"
apply (auto simp add: ValuedBool_bool_eval_def)
done

definition ValuedTautology_values :: "nat \<Rightarrow> nat \<Rightarrow> ('vb, 'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> bool" where
 "ValuedTautology_values i j Es val_b val_v \<equiv> 
    (
      (ValuedBool_bool_eval (Es i) val_b) \<and> (ValuedBool_bool_eval (Es j) val_b)
    ) 
    \<longrightarrow> 
    (
      (ValuedBool_value_eval (Es i) val_v) = (ValuedBool_value_eval (Es j) val_v)
    )"

definition ValuedTautology :: "('vb, 'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> bool" where
  "ValuedTautology Es val_b val_v \<equiv> 
      (ValuedBoolExp_bool_eval Es val_b) \<and>
      ( \<forall> i \<in> dom Es . \<forall> j \<in> dom Es . ValuedTautology_values i j Es val_b val_v)"

lemma valued_tautology_basic_or : "(ValuedTautology (map_of [(1,(E,V)), (2,(VBBExpUnOp Not E,U))]) val_b val_v)"
apply (auto)
apply (simp add: ValuedTautology_def)
apply (simp add: ValuedBoolExp_bool_eval_def)
apply (simp add: ValuedTautology_values_def)
done

lemma not_valued_tautology1 : "\<not> (val_b A) \<Longrightarrow> \<not> ValuedTautology (map_of [(1,(VBBVarOp A, U))]) val_b val_v"
apply (auto)
apply (simp add: ValuedTautology_def)
apply (simp add: ValuedTautology_values_def)
apply (simp add: ValuedBoolExp_bool_eval_def)
done

lemma not_valued_tautology2 : 
  "\<not> (val_b A) \<and> \<not> (val_b B) \<Longrightarrow> \<not> ValuedTautology (map_of [(1,(VBBVarOp A, U)), (2,(VBBVarOp B, V))]) val_b val_v"
apply (auto simp add: ValuedTautology_def )
apply (simp add: ValuedTautology_values_def)
apply (simp add: ValuedBoolExp_bool_eval_def)
done



end
