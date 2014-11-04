theory ValuedTautology

imports FaultModellingTypes Map

begin

primrec "BoolOperand_eval" :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) vb = b" |
  "BoolOperand_eval (VBBVarOp a) vb = vb a" |
  "BoolOperand_eval (VBBExpUnOp exp_op op1) vb = exp_op (BoolOperand_eval op1 vb)" |
  "BoolOperand_eval (VBBExpBinOp exp_op op1 op2) vb = 
    exp_op (BoolOperand_eval op1 vb) (BoolOperand_eval op2 vb)"

primrec 
  expand_BoolOperand_ValuesOperand :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuesOperand \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_list :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuedBool list \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_VB :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuedBool \<Rightarrow> ('vb, 'vv) ValuedBool"
where
  "expand_BoolOperand_ValuesOperand e (VBVConstOp c) = (VB e (VBVConstOp c)) # []" |
  "expand_BoolOperand_ValuesOperand e (VBVVarOp v) = (VB e (VBVVarOp v)) # []" |
  expand_BoolOperand_ValuesOperand_VBExpOp:
  "expand_BoolOperand_ValuesOperand e (VBVExpOp Es) = expand_BoolOperand_ValuesOperand_list e Es" |
  "expand_BoolOperand_ValuesOperand_list e [] = []" |
  "expand_BoolOperand_ValuesOperand_list e (E # Es) = 
    (expand_BoolOperand_ValuesOperand_VB e E) # (expand_BoolOperand_ValuesOperand_list e Es)" |
  "expand_BoolOperand_ValuesOperand_VB e1 (VB e2 v2) = VB (VBBExpBinOp (op \<and>) e1 e2) v2"

primrec 
  normalise_ValuesOperand :: "('vb, 'vv) ValuesOperand \<Rightarrow> ('vb, 'vv) ValuesOperand" and
  normalise_ValuesOperand_list :: "('vb, 'vv) ValuedBool list \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  normalise_ValuesOperand_VB :: "('vb, 'vv) ValuedBool \<Rightarrow> ('vb, 'vv) ValuedBool list" 
where
  "normalise_ValuesOperand (VBVConstOp c) = VBVConstOp c" |
  "normalise_ValuesOperand (VBVVarOp v) = VBVVarOp v" |
  normalise_ValuesOperand_VBVExpOp:
  "normalise_ValuesOperand (VBVExpOp E) = VBVExpOp (normalise_ValuesOperand_list E)" |
  "normalise_ValuesOperand_list [] = []" |
  "normalise_ValuesOperand_list (e # E) = (normalise_ValuesOperand_VB e) @ (normalise_ValuesOperand_list E)" |
  "normalise_ValuesOperand_VB (VB e v) = expand_BoolOperand_ValuesOperand e v"

lemma normalise_sanity1: 
  "(normalise_ValuesOperand (VBVExpOp [ VB e1 (VBVExpOp [VB e2 v2]) ])) = (VBVExpOp [ VB (VBBExpBinOp (op \<and>) e1 e2) v2])"
apply (auto)
done


primrec 
  ValuesOperand_bool_eval :: "('vb, 'vv) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_list :: "('vb, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_VB :: "('vb, 'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "ValuesOperand_bool_eval (VBVConstOp c) vb = True" |
  "ValuesOperand_bool_eval (VBVVarOp v) vb = True" |
  ValuedTautology_VBVExpOp:
  "ValuesOperand_bool_eval (VBVExpOp Es) vb = (ValuesOperand_bool_eval_list Es vb)" |
  "ValuesOperand_bool_eval_list [] vb = False" |
  "ValuesOperand_bool_eval_list (E # Es) vb = 
    ((ValuesOperand_bool_eval_VB E vb) \<or> (ValuesOperand_bool_eval_list Es vb))" |
  "ValuesOperand_bool_eval_VB (VB e v) vb = (BoolOperand_eval e vb)"

primrec choose_value :: "Values option binop" where
  "choose_value None vo = vo" |
  "choose_value (Some v) vo = (if (Some v) = vo then vo else None)"

primrec
  ValuesOperand_value_eval :: "('vb, 'vv) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values option) \<Rightarrow> Values option" and
  ValuesOperand_value_eval_list :: "('vb, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values option) \<Rightarrow> Values option list" and
  ValuesOperand_value_eval_VB :: "('vb, 'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values option) \<Rightarrow> Values option" 
where
  "ValuesOperand_value_eval (VBVConstOp c) vb vv = Some c" |
  "ValuesOperand_value_eval (VBVVarOp v) vb vv = vv v" |
  "ValuesOperand_value_eval (VBVExpOp Es) vb vv = 
    (fold choose_value (ValuesOperand_value_eval_list Es vb vv) None)" |
  "ValuesOperand_value_eval_list [] vb vv = []" |
  "ValuesOperand_value_eval_list (E # Es) vb vv = 
    (ValuesOperand_value_eval_VB E vb vv) # (ValuesOperand_value_eval_list Es vb vv)" |
  "ValuesOperand_value_eval_VB (VB e v) vb vv = 
    (if (BoolOperand_eval e vb) then (ValuesOperand_value_eval v vb vv) else None)"

definition
  UniqueValue :: "('vb, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values option) \<Rightarrow> bool" 
where
  "UniqueValue Es vb vv \<equiv> 
  card (
    set (
      map 
        (\<lambda> E. ValuesOperand_value_eval_VB E vb vv) 
        (filter (\<lambda> E. ValuesOperand_bool_eval_VB E vb) Es)
    )
  ) = 1"

primrec 
  ValuedTautology :: "('vb, 'vv) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> Values option) \<Rightarrow> bool" and
  ValuedTautology_list :: "('vb, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuedTautology_VB :: "('vb, 'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "ValuedTautology (VBVConstOp c) vb vv = True" |
  "ValuedTautology (VBVVarOp v) vb vv = True" |
  "ValuedTautology (VBVExpOp Es) vb vv = 
    ((ValuedTautology_list Es vb) \<and> (UniqueValue Es vb vv))" |
  "ValuedTautology_list [] vb = False" |
  "ValuedTautology_list (E # Es) vb = 
    ((ValuedTautology_VB E vb) \<or> (ValuedTautology_list Es vb))" |
  "ValuedTautology_VB (VB e v) vb = (BoolOperand_eval e vb)"

lemma to_be_or_not_to_be[simp]: "(BoolOperand_eval A vb) \<or> (BoolOperand_eval (VBBExpUnOp Not A) vb)"
apply (auto)
done

lemma to_be_or_not_to_be_list[simp]: "ValuedTautology_list [VB A U, VB (VBBExpUnOp Not A) V] vb"
apply (auto)
done

lemma to_be_or_not_to_be_two_active_list[simp]: "UniqueValue [VB A U, VB (VBBExpUnOp Not A) V] vb vv"
apply (simp add: UniqueValue_def)
done

lemma valued_tautology_basic_or : 
  "ValuedTautology (VBVExpOp [VB A U, VB (VBBExpUnOp Not A) V]) vb vv"
apply (auto)
done

lemma valued_tautology_or : 
  "((BoolOperand_eval A vb \<and> BoolOperand_eval B vb) \<longrightarrow> U = V) \<Longrightarrow> ValuedTautology (VBVExpOp [VB A U, VB B V, 
    VB (VBBExpBinOp (op \<and>) (VBBExpUnOp Not A) (VBBExpUnOp Not B)) Q]) 
  vb vv"
apply (auto)
apply (auto simp add: UniqueValue_def)
done

lemma not_valued_tautology1 : "(\<not> (BoolOperand_eval A vb)) \<Longrightarrow> (\<not> ValuedTautology (VBVExpOp [VB A U]) vb vv)"
apply (auto)
done

lemma not_valued_tautology2 : 
  "(\<not> (BoolOperand_eval A vb) \<and> \<not> (BoolOperand_eval B vb)) \<Longrightarrow> \<not> ValuedTautology (VBVExpOp [VB A U, VB B V]) vb vv"
apply (auto)
done


end
