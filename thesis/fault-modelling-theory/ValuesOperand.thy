theory ValuesOperand

imports ValueCondition Complex_Main FaultModellingTypes

begin

datatype_new ('FMode, 'vv) Values = 
  FMNominal real 
  | FMFailure "'FMode"
  | FMVar (var: 'vv)

datatype_new ('vb, 'FMode, 'vv) ValuesOperand =
  VBVConst "('FMode, 'vv) Values"
  | VBVExp "('vb, 'FMode, 'vv) ValuedBool list" and
  ('vb, 'FMode, 'vv) ValuedBool = 
    VB (VBE:"'vb ValueCondition") (VBV:"('vb, 'FMode, 'vv) ValuesOperand")

notation (output) FMNominal ("N\<langle>_\<rangle>" 40)
notation (output) FMFailure ("F\<langle>_\<rangle>" 41)
notation (output) FMVar ("_" 41)
notation (output) VBVConst  ("_" 50)
notation (output) VBVExp ("VT _" 80)
notation (output) VB (infix "\<surd>" 80)

primrec 
  ValuesOperand_bool_eval :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "ValuesOperand_bool_eval (VBVConst c) vb = True" |
  "ValuesOperand_bool_eval (VBVExp Es) vb = (ValuesOperand_bool_eval_list Es vb)" |
  "ValuesOperand_bool_eval_list [] vb = False" |
  "ValuesOperand_bool_eval_list (E # Es) vb = 
    ((ValuesOperand_bool_eval_VB E vb) \<or> (ValuesOperand_bool_eval_list Es vb))" |
  "ValuesOperand_bool_eval_VB (VB e v) vb = (ValueCondition_eval e vb)"

primrec choose_value :: "('FMode, 'vv) Values option binop" where
  "choose_value None vo = vo" |
  "choose_value (Some v) vo = (if (Some v) = vo then vo else None)"

primrec single_value :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 
  ('vb, 'FMode, 'vv) ValuedBool \<Rightarrow>
  ('vb, 'FMode, 'vv) ValuedBool option"
where
  "single_value [] E = (Some E)" |
  "single_value (E1 # Es) E2 = 
    (if (VBV E1) = (VBV E2) then (single_value Es E2) else None)" 

primrec
  ValuesOperand_values_eval :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 
    ('vb \<Rightarrow> bool) \<Rightarrow> ('FMode, 'vv) Values list" and
  ValuesOperand_values_eval_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('FMode, 'vv) Values list" and
  ValuesOperand_values_eval_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('FMode, 'vv) Values list" 
where
  "ValuesOperand_values_eval (VBVConst c) vb = c # []" |
  "ValuesOperand_values_eval (VBVExp Es) vb = (ValuesOperand_values_eval_list Es vb)" |
  "ValuesOperand_values_eval_list [] vb = []" |
  "ValuesOperand_values_eval_list (E # Es) vb = 
    (ValuesOperand_values_eval_VB E vb) @ (ValuesOperand_values_eval_list Es vb)" |
  "ValuesOperand_values_eval_VB (VB e v) vb = 
    (if (ValueCondition_eval e vb) then (ValuesOperand_values_eval v vb) else [])"

notation (output) ValuesOperand_values_eval ("\<lbrakk>_\<rbrakk> \<langle>_\<rangle>")

primrec ValuedTautology_values_nonemptylist :: 
  "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values list \<Rightarrow> bool"
where
  "ValuedTautology_values_nonemptylist vref [] = True" |
  "ValuedTautology_values_nonemptylist vref (v # vs) = 
    ((vref = v) \<and> (ValuedTautology_values_nonemptylist vref vs))"

primrec ValuedTautology_values_list :: "('FMode, 'vv) Values list \<Rightarrow> bool"
where
  "ValuedTautology_values_list [] = False" |
  "ValuedTautology_values_list (v # vs) = ValuedTautology_values_nonemptylist v vs"

definition ValuedTautology :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ValuedTautology v vb \<equiv> ValuedTautology_values_list (ValuesOperand_values_eval v vb)"

notation (output) ValuedTautology ("_/ \<Gamma>/ \<langle>_\<rangle>")

lemma  [simp]: "
  \<lbrakk>
    ValuesOperand_values_eval U vb \<noteq> [];
    ValuesOperand_values_eval V vb \<noteq> []
  \<rbrakk> 
  \<Longrightarrow> 
  (ValuesOperand_values_eval (VBVExp [VB A U, VB (VCNot A) V]) vb) \<noteq> []"
apply (simp)
done

theorem [simp]: "
  \<lbrakk>
    ValuedTautology U vb;
    ValuedTautology V vb
  \<rbrakk> 
  \<Longrightarrow> 
  ValuedTautology (VBVExp [VB A U, VB (VCNot A) V]) vb"
apply (simp add: ValuedTautology_def)
done

lemma [simp]: "ValuedTautology V vb \<Longrightarrow> ValuesOperand_values_eval V vb \<noteq> []"
apply (auto simp add: ValuedTautology_def ValuesOperand_values_eval_def)
done

lemma [simp]: "ValuedTautology V vb \<Longrightarrow> ValuedTautology_values_list (
    ValuesOperand_values_eval V vb )"
apply (simp add: ValuedTautology_def ValuesOperand_values_eval_def)
done

lemma [simp]: "ValuedTautology_values_list xs \<longrightarrow> ValuedTautology_values_list (xs @ xs)"
apply (induct_tac xs)
apply (simp)
apply (simp add: ValuedTautology_values_list_def)
apply (simp add: ValuedTautology_values_nonemptylist_def)
sorry

lemma [simp]: "ValuedTautology V vb \<Longrightarrow> ValuedTautology_values_list (
    (ValuesOperand_values_eval V vb) @ (ValuesOperand_values_eval V vb))"
apply (auto simp add: ValuedTautology_def ValuesOperand_values_eval_def)
done

lemma valued_tautology_or : 
  "\<lbrakk>
    ValuedTautology U vb;
    ValuedTautology V vb;
    ValuedTautology Q vb;
    ((ValueCondition_eval A vb \<and> ValueCondition_eval B vb) \<longrightarrow> U = V)
   \<rbrakk>
   \<Longrightarrow> 
   ValuedTautology (VBVExp [VB A U, VB B V, VB (VCAnd (VCNot A) (VCNot B)) Q]) vb"
apply (simp add: ValuedTautology_def)
done

lemma not_valued_tautology1 : "
(\<not> (ValueCondition_eval A vb)) \<Longrightarrow> 
  (\<not> ValuedTautology (VBVExp [VB A U]) vb)"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

lemma not_valued_tautology2 : 
  "(\<not> (ValueCondition_eval A vb) \<and> \<not> (ValueCondition_eval B vb)) \<Longrightarrow> 
  \<not> ValuedTautology (VBVExp [VB A U, VB B V]) vb"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

primrec 
  ValuesOperandPredicate_ValueCondition :: "(('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 'vb ValueCondition" and
  ValuesOperandPredicate_ValueCondition_list :: "(('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 'vb ValueCondition" and
  ValuesOperandPredicate_ValueCondition_VB :: "(('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> 'vb ValueCondition"
where
  "ValuesOperandPredicate_ValueCondition P (VBVConst c) = (VCConst (P c))" |
  "ValuesOperandPredicate_ValueCondition P (VBVExp Es) = 
    (ValuesOperandPredicate_ValueCondition_list P Es)" |
  "ValuesOperandPredicate_ValueCondition_list _ [] = (VCConst False)" |
  "ValuesOperandPredicate_ValueCondition_list P (E # Es) = VCOr  
    (ValuesOperandPredicate_ValueCondition_VB P E) 
    (ValuesOperandPredicate_ValueCondition_list P Es)" |
  "ValuesOperandPredicate_ValueCondition_VB P (VB e v) = 
    VCAnd e (ValuesOperandPredicate_ValueCondition P v)"

fun lte_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool" (infix "\<le>\<^sub>V" 50)
where
  "lte_Values (FMNominal a) (FMNominal b) = (a \<le> b)" |
  "lte_Values (FMFailure _) (FMNominal b) = (b > 0)" |
  "lte_Values a b = (a = b)"

abbreviation gte_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool" (infix "\<ge>\<^sub>V" 50)
where
  "gte_Values a b \<equiv> lte_Values b a"

abbreviation gt_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool" (infix ">\<^sub>V" 50)
where
  "gt_Values a b \<equiv> \<not> (lte_Values a b)"

abbreviation lt_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool" (infix "<\<^sub>V" 50)
where
  "lt_Values a b \<equiv> gt_Values b a"

abbreviation eq_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool" (infix "=\<^sub>V" 50)
where
  "eq_Values a b \<equiv> (lte_Values a b \<and> gte_Values a b)"

value "ValuesOperandPredicate_ValueCondition 
  (lte_Values (FMNominal 2))   (VBVExp [
    VB (VCVar A) (VBVConst (FMFailure F1)),
    VB (VCNot (VCVar A)) (VBVConst (FMNominal 5))
  ]) 
  "

primrec 
  apply_ValueCondition :: 
    "'vb ValueCondition \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" and
  apply_ValueCondition_list :: 
    "'vb ValueCondition \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 
      ('vb, 'FMode, 'vv) ValuedBool list" and
  apply_ValueCondition_VB :: 
    "'vb ValueCondition \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool"
where
  "apply_ValueCondition e (VBVConst c) = (VB e (VBVConst c)) # []" |
  expand_ValueCondition_ValuesOperand_VBExpOp:
  "apply_ValueCondition e (VBVExp Es) = apply_ValueCondition_list e Es" |
  "apply_ValueCondition_list e [] = []" |
  "apply_ValueCondition_list e (E # Es) = 
    (apply_ValueCondition_VB e E) # (apply_ValueCondition_list e Es)" |
  "apply_ValueCondition_VB e1 (VB e2 v2) = VB (VCAnd e1 e2) v2"


primrec 
  expand_ValuesOperand :: 
    "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand" and
  expand_ValuesOperand_list :: 
    "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" and
  expand_ValuesOperand_VB :: 
    "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" 
where
  "expand_ValuesOperand (VBVConst c) = VBVConst c" |
  expand_ValuesOperand_VBVExp:
  "expand_ValuesOperand (VBVExp E) = VBVExp (expand_ValuesOperand_list E)" |
  "expand_ValuesOperand_list [] = []" |
  "expand_ValuesOperand_list (e # E) = 
    (expand_ValuesOperand_VB e) @ (expand_ValuesOperand_list E)" |
  "expand_ValuesOperand_VB (VB e v) = (
    case v of
      (VBVExp E2) \<Rightarrow> (apply_ValueCondition e (expand_ValuesOperand v)) |
      _ \<Rightarrow> [VB e (expand_ValuesOperand v)]
  )"

value "expand_ValuesOperand (
  VBVExp [VB (VCVar v1) (
      VBVExp [
        VB (VCVar v2) (VBVExp [
          VB (VCVar v3) (VBVVarOp v4)
        ])
      ]
    )]
  )"

lemma "expand_ValuesOperand (
  VBVExp [VB (VCVar v1) (
      VBVExp [
        VB (VCVar v2) (VBVExp [
          VB (VCVar v3) (VBVConst v4)
        ])
      ]
    )]
  ) = 
  (VBVExp [
    VB 
      (VCAnd (VCVar v1) (VCAnd (VCVar v2) (VCVar v3)))
      (VBVConst v4)
  ])"
apply (auto)
done

primrec 
  SingleOperand_list :: 
    "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 
      ('vb, 'FMode, 'vv) ValuesOperand option" and
  SingleOperand_VB :: 
    "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow>
      ('vb, 'FMode, 'vv) ValuesOperand option"
where
  "SingleOperand_list [] E = Some E" |
  "SingleOperand_list (E1 # Es) E = (
    let nE1 = (SingleOperand_VB E1 E)
    in let nEs = (SingleOperand_list Es E)
    in if nE1 = nEs then nE1 else None
  )" |
  "SingleOperand_VB (VB e v) E = (if v = E then (Some v) else None)"

primrec SingleOperand :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 
  ('vb, 'FMode, 'vv) ValuesOperand option"
where 
  "SingleOperand [] = None" |
  "SingleOperand (E # Es) = (SingleOperand_list Es (VBV E))"

primrec 
  normalise_ValuesOperand :: 
    "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand" and
  normalise_ValuesOperand_list :: 
    "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" and
  normalise_ValuesOperand_VB :: 
    "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool option" 
where
  "normalise_ValuesOperand (VBVConst c) = (VBVConst c)" |
  "normalise_ValuesOperand (VBVExp Es) =  (
    let 
      nEs = normalise_ValuesOperand_list Es;
      so = SingleOperand nEs
    in if so = None then VBVExp nEs else the so
  )" |
  "normalise_ValuesOperand_list [] = []" |
  "normalise_ValuesOperand_list (E # Es) = (
    let nE = normalise_ValuesOperand_VB E
    in if nE = None then (normalise_ValuesOperand_list Es)
    else (the nE) # (normalise_ValuesOperand_list Es)
  )" |
  "normalise_ValuesOperand_VB (VB e v) = 
  (
    if (\<not> ValueCondition_Sat e) then None
    else Some (VB e (normalise_ValuesOperand v))
  )"

definition normalise_expand_ValuesOperand ::
  "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand"
where
  "normalise_expand_ValuesOperand v \<equiv> normalise_ValuesOperand (expand_ValuesOperand v)"

primrec 
  isExpandedNormal_ValuesOperand :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> bool" and
  isExpandedNormal_ValuesOperand_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> bool" and
  isExpandedNormal_ValuesOperand_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> bool" 
where
  "isExpandedNormal_ValuesOperand (VBVConst c) = True" |
  "isExpandedNormal_ValuesOperand (VBVExp Es) = (isExpandedNormal_ValuesOperand_list Es)" |
  "isExpandedNormal_ValuesOperand_list [] = True" |
  "isExpandedNormal_ValuesOperand_list (E # Es) = 
    ((isExpandedNormal_ValuesOperand_VB E) \<and> (isExpandedNormal_ValuesOperand_list Es))" |
  "isExpandedNormal_ValuesOperand_VB (VB e v) = 
    ((ValueCondition_Sat e) \<and> (isExpandedNormal_ValuesOperand v))"

theorem "(v = normalise_expand_ValuesOperand v) \<longleftrightarrow> (isExpandedNormal_ValuesOperand v)"
sorry

primrec choose_values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values option 
  \<Rightarrow> ('FMode, 'vv) Values option"
where
  "choose_values _ None = None" |
  "choose_values v1 (Some v2) = (if (v1 = v2) then (Some v1) else None)"

definition ValuesOperand_value_eval :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 
  ('vb \<Rightarrow> bool) \<Rightarrow> ('FMode, 'vv) Values option"
where
  "ValuesOperand_value_eval Es vb \<equiv> 
    fold choose_values (ValuesOperand_values_eval Es vb) None"

value "ValuesOperand_value_eval (VBVExp [
  VB (VCVar A) (VBVConst U), 
  VB (VCVar B) (VBVConst U)] ) vb"

lemma [simp]: "(ValuedTautology (VBVExp Es) vb) \<Longrightarrow> 
  (length (ValuesOperand_values_eval (VBVExp Es) vb) > 0)"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

lemma "(ValuedTautology (VBVExp Es) vb) \<Longrightarrow> 
  (ValuesOperand_value_eval (VBVExp Es) vb = Some v)"
apply (induct Es)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuesOperand_value_eval_def)
apply (auto simp add: choose_values_def)
apply (auto simp add: ValuedTautology_values_list_def)
apply (auto simp add: ValuedTautology_values_nonemptylist_def)
apply (auto simp add: fold_def)
apply (auto simp add: ValuesOperand_values_eval_list_def)
apply (auto simp add: ValuesOperand_values_eval_VB_def)
sorry

lemma "(ValuesOperand_values_eval (VBVExp [VB (VCNot A) V, VB A V]) vb) = 
  ValuesOperand_values_eval V vb"
apply (auto)
done

end
