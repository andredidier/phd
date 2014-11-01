theory ValuedTautology

imports FaultModellingTypes

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

definition ValuedBool_bool_eval :: "('vb,'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where 
  "ValuedBool_bool_eval VB valuation \<equiv> BoolOperand_eval (fst VB) valuation"

definition ValuedBool_value_eval :: "('vb, 'vv) ValuedBool \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> Values" where 
  "ValuedBool_value_eval VB valuation \<equiv> ValuesOperand_eval (snd VB) valuation"

type_synonym ('vb, 'vv) ValuedBoolExp = "(nat \<times> (('vb,'vv) ValuedBool)) set"

definition ValuedBoolExp_bool_eval :: "('vb,'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "ValuedBoolExp_bool_eval Es val_b \<equiv> (\<exists> E \<in> Es. ValuedBool_bool_eval (snd E) val_b)"

lemma to_be_or_not_to_be1 : "(BoolOperand_eval E val_b) \<or> (BoolOperand_eval (VBBExpUnOp Not E) val_b)"
apply (auto)
done

lemma to_be_or_not_to_be2 : "ValuedBoolExp_bool_eval { (1,(E,V)), (2,(VBBExpUnOp Not E, U))  } val_b"
apply (auto simp add: to_be_or_not_to_be1 ValuedBoolExp_bool_eval_def ValuedBool_bool_eval_def )
done

lemma to_be_or_not_to_be3 : 
  "(\<not> (ValuedBool_bool_eval (VBBExpUnOp Not E,V) val_b)) \<Longrightarrow> (ValuedBool_bool_eval (E,U) val_b)"
apply (auto simp add: ValuedBool_bool_eval_def)
done

definition IndexedValuedBoolExp :: "('vb, 'vv) ValuedBoolExp \<Rightarrow> bool" where
  "IndexedValuedBoolExp Es \<equiv> (\<forall> i j VBi VBj . ((i, VBi) \<in> Es \<and> (j, VBj) \<in> Es \<and> (i = j)) \<longrightarrow> (VBi = VBj))"

definition ValuedTautology :: "('vb, 'vv) ValuedBoolExp \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values) \<Rightarrow> bool" where
  "ValuedTautology Es val_b val_v \<equiv> (
      (IndexedValuedBoolExp Es) \<and>
      (ValuedBoolExp_bool_eval Es val_b) \<and>
      (\<forall> i j VBi VBj . (i \<noteq> j) \<and> ((i,VBi) \<in> Es) \<and> ((j,VBj) \<in> Es) \<and> 
        (((ValuedBool_bool_eval VBi val_b) \<and> (ValuedBool_bool_eval VBj val_b)) \<longrightarrow>  
          ((ValuedBool_value_eval VBi val_v) = (ValuedBool_value_eval VBj val_v))) )
    )"

lemma not_valued_tautology1 : "\<not> ValuedTautology {(1,(VBBVarOp A, U))} val_b val_v"
apply (auto simp add: ValuedTautology_def)
done

lemma not_valued_tautology2 : 
  "\<not> ValuedTautology {(1,(VBBVarOp A, U)), (2,(VBBVarOp B, V)) } val_b val_v"
apply (auto simp add: ValuedTautology_def)
done

lemma valued_tautology_basic_or : "(ValuedTautology { (1,(E,V)), (2,(VBBExpUnOp Not E,U)) } val_b val_v)"
apply (simp add: ValuedTautology_def IndexedValuedBoolExp_def ValuedBoolExp_bool_eval_def to_be_or_not_to_be3
  ValuedBool_bool_eval_def ValuedBool_value_eval_def BoolOperand_eval_def ValuesOperand_eval_def)

done


end
