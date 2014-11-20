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

type_synonym ('vb, 'FMode, 'vv) ConditionValue = 
  "('vb ValueCondition \<times> ('FMode, 'vv) Values)"

notation (output) FMNominal ("N\<langle>_\<rangle>" 40)
notation (output) FMFailure ("F\<langle>_\<rangle>" 41)
notation (output) FMVar ("_" 41)
notation (output) VBVConst  ("_" 50)
notation (output) VBVExp ("VT _" 80)
notation (output) VB (infix "\<surd>" 80)

primrec expand_VO2CV :: "'vb ValueCondition \<Rightarrow> 
  ('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow>
  ('vb, 'FMode, 'vv) ConditionValue list"
where
  "expand_VO2CV e [] = []" |
  "expand_VO2CV e (v # vs) = (VCAnd e (fst v), snd v) # (expand_VO2CV e vs)"

primrec 
  VO2CV :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ConditionValue list" and
  VO2CV_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb, 'FMode, 'vv) ConditionValue list" and
  VO2CV_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ConditionValue list" 
where
  "VO2CV (VBVConst c) = [ (VCConst True, c) ]" |
  "VO2CV (VBVExp v) = VO2CV_list v" |
  "VO2CV_list [] = []" |
  "VO2CV_list (E # Es) = (VO2CV_VB E) @ (VO2CV_list Es)" |
  "VO2CV_VB (VB e v) = expand_VO2CV e (VO2CV v)"

fun mkVO :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 
  ('vb, 'FMode, 'vv) ValuesOperand"
where
  "mkVO (VBVConst c1) (VBVConst c2) = VBVConst c1" |
  "mkVO (VBVConst c1) (VBVExp Es) = (VBVExp ((VB (VCConst True) (VBVConst c1)) # Es))" |
  "mkVO (VBVExp Es1) (VBVExp Es2) = VBVExp (Es1 @ Es2)" |
  "mkVO (VBVExp Es) (VBVConst c1) = (VBVExp (Es @ [VB (VCConst True) (VBVConst c1)]))" 

fun CV2VO :: "('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand"
where
  "CV2VO [] = VBVExp []" |
  "CV2VO [ cv ] = 
  (
    if ValueCondition_Tautology (fst cv) 
      then VBVConst (snd cv) 
      else VBVExp [ VB (fst cv) (VBVConst (snd cv)) ]
  )" |
  "CV2VO (cv # cvs) = mkVO (CV2VO [cv]) (CV2VO cvs)"

definition CVList_condition :: "('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow> 'vb ValueCondition"
where
  "CVList_condition cvs \<equiv> fold (\<lambda> a b. VCOr (fst a) b) cvs (VCConst False)"

definition ValuedTautology_CVList :: "('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow> bool"
where
  "ValuedTautology_CVList cvs \<equiv> cvs \<noteq> [] \<and>
    ((ValueCondition_Tautology \<circ> CVList_condition) cvs) \<and>
    (\<forall> i j. 
      (i < length cvs) \<and> (j < length cvs) \<and>
      (
        let ei = fst (cvs!i); ej = fst (cvs!j); vi = snd (cvs!i); vj = snd (cvs!j)
        in ValueCondition_Sat (VCAnd ei ej) \<longrightarrow> vi = vj
      )
    )"

definition CVList_eval_values :: 
  "('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow> 
  'vb VCEnv \<Rightarrow> 
  ('FMode, 'vv) Values list"
where
  "CVList_eval_values cvs s \<equiv> 
  (
    let 
      filtercvs = filter (\<lambda> cv. ValueCondition_eval (fst cv) s);
      getvalue = map snd;
      filterValue = (\<lambda> vs. if vs = [] then [] else (filter (\<lambda> v. v = hd vs) vs))
    in (filterValue \<circ> getvalue \<circ> filtercvs) cvs
  )"

lemma [simp]: "ValuedTautology_CVList cvs \<Longrightarrow> length (CVList_eval_values cvs s) = 1"
apply (induct cvs)
apply (auto simp add: ValuedTautology_CVList_def)
done


(*
primrec
  ValuesOperand_values_eval :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 
    'vb VCEnv \<Rightarrow> ('FMode, 'vv) Values list" and
  ValuesOperand_values_eval_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 'vb VCEnv \<Rightarrow> 
    ('FMode, 'vv) Values list" and
  ValuesOperand_values_eval_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> 'vb VCEnv \<Rightarrow> 
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
*)

primrec  
  VO2VC :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 'vb ValueCondition" and
  VO2VC_list :: 
    "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 'vb ValueCondition" and
  VO2VC_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> 'vb ValueCondition"
where
  "VO2VC (VBVConst _) = (VCConst True)" |
  "VO2VC (VBVExp Es) = VO2VC_list Es" |
  "VO2VC_list [] = (VCConst False)" |
  "VO2VC_list (E # Es) = VCOr (VO2VC_VB E) (VO2VC_list Es)" |
  "VO2VC_VB (VB e _) = e"

definition ValuedTautology :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> bool"
where
  "ValuedTautology v \<equiv> (ValuedTautology_CVList \<circ> VO2CV) v"

notation (output) ValuedTautology ("\<TT> _")

lemma [simp]: "
  \<lbrakk>
    ValuedTautology U;
    ValuedTautology V
  \<rbrakk> 
  \<Longrightarrow> ValuedTautology (VBVExp [VB (VCConst True) U, VB (VCNot (VCConst True)) V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CVList_def)
done

lemma [simp]: "
  \<lbrakk>
    ValuedTautology U;
    ValuedTautology V
  \<rbrakk> 
  \<Longrightarrow> 
  ValuedTautology (VBVExp [VB A U, VB (VCNot A) V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CVList_def)
done

lemma valued_tautology_or : 
  "\<lbrakk>
    ValuedTautology U;
    ValuedTautology V;
    ValuedTautology Q;
    (ValueCondition_Sat (VCAnd A B) \<longrightarrow> U = V)
   \<rbrakk>
   \<Longrightarrow> 
   ValuedTautology (VBVExp [VB A U, VB B V, VB (VCAnd (VCNot A) (VCNot B)) Q])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CVList_def)
done

lemma not_valued_tautology1 : "
(\<not> (ValueCondition_Sat A)) \<Longrightarrow> 
  (\<not> ValuedTautology (VBVExp [VB A U]))"
apply (auto simp add: ValuedTautology_def ValuedTautology_CVList_def)
done

lemma not_valued_tautology2 : 
  "(\<not> (ValueCondition_Sat (VCOr A B))) \<Longrightarrow> 
  \<not> ValuedTautology (VBVExp [VB A U, VB B V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CVList_def)
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

fun nominal_op :: 
  "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> 
  (real \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow>
  (('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "nominal_op (FMNominal a) (FMNominal b) f _ = (f a b)" |
  "nominal_op (FMFailure _) (FMNominal _) _ _ = False" |
  "nominal_op (FMNominal _) (FMFailure _) _ _ = False" |
  "nominal_op a b _ g = (g a b)"

definition lte_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool"
where
  "lte_Values a b \<equiv> nominal_op a b (op \<le>) (op =)"

abbreviation gte_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool" 
where
  "gte_Values a b \<equiv> lte_Values b a"

definition lt_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool"
where
  "lt_Values a b \<equiv> nominal_op a b (op <) (\<lambda> _ _. False)"

abbreviation gt_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool"
where
  "gt_Values a b \<equiv> lt_Values b a"

abbreviation eq_Values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values \<Rightarrow> bool"
where
  "eq_Values a b \<equiv> (a = b)"

notation (output) lte_Values  (infix "\<le>" 50)
notation (output) gte_Values  (infix "\<ge>" 50)
notation (output) lt_Values  (infix "<" 50)
notation (output) gt_Values  (infix ">" 50)
notation (output) eq_Values  (infix "=" 50)

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

definition ValuesOperand_eval_values :: 
  "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 'vb VCEnv \<Rightarrow> ('FMode, 'vv) Values list"
where
  "ValuesOperand_eval_values v s \<equiv> CVList_eval_values (VO2CV v) s"

theorem [simp]: "ValuedTautology v \<Longrightarrow> length (ValuesOperand_eval_values v s) = 1"
apply (induct v)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuesOperand_eval_values_def)
done

definition normalise_ConditionValue_filter :: 
  "('vb, 'FMode, 'vv) ConditionValue \<Rightarrow> ('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow> bool"
where
  "normalise_ConditionValue_filter cv cvs \<equiv> 
    ValueCondition_Sat (fst cv) \<and> 
    (cvs \<noteq> [] \<longrightarrow> \<not> (\<exists> i. snd cv = snd (cvs!i) \<and> ValueCondition_Equiv (fst cv) (fst (cvs!i))))"

primrec normalise_ConditionValue :: "
  ('vb, 'FMode, 'vv) ConditionValue list \<Rightarrow> ('vb, 'FMode, 'vv) ConditionValue list"
where
  "normalise_ConditionValue [] = []" |
  "normalise_ConditionValue (cv # cvs) = (
    if (normalise_ConditionValue_filter cv cvs) 
      then cv # (normalise_ConditionValue cvs)
      else (normalise_ConditionValue cvs)
  )"

definition
  normalise_ValuesOperand :: 
    "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand" 
where
  "normalise_ValuesOperand \<equiv> CV2VO \<circ> normalise_ConditionValue \<circ> VO2CV" 

primrec 
  isNormal_ValuesOperand :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> bool" and
  isNormal_ValuesOperand_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> bool" and
  isNormal_ValuesOperand_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> bool" 
where
  "isNormal_ValuesOperand (VBVConst c) = True" |
  "isNormal_ValuesOperand (VBVExp Es) = (isNormal_ValuesOperand_list Es)" |
  "isNormal_ValuesOperand_list [] = True" |
  "isNormal_ValuesOperand_list (E # Es) = 
    ((isNormal_ValuesOperand_VB E) \<and> (isNormal_ValuesOperand_list Es))" |
  "isNormal_ValuesOperand_VB (VB e v) = 
    ((ValueCondition_Sat e) \<and> (isNormal_ValuesOperand v))"

lemma [simp]: "(isNormal_ValuesOperand \<circ> normalise_ValuesOperand) v"
apply (induct v)
apply (auto simp add: normalise_ValuesOperand_def isNormal_ValuesOperand_def)
apply (auto simp add: ValueCondition_Tautology_def)
apply (auto simp add: taut_test_def)
apply (auto simp add: normalise_ConditionValue_filter_def)
apply (auto simp add: ValueCondition_Sat_def)
apply (auto simp add: sat_test_def)
apply (auto simp add: ValueCondition_to_bool_expr_def)
sorry

theorem "\<lbrakk> v \<noteq> VBVExp [] \<rbrakk> \<Longrightarrow> (v = normalise_ValuesOperand v) \<longleftrightarrow> (isNormal_ValuesOperand v)"
apply (induct v)
apply (auto simp add: normalise_ValuesOperand_def normalise_ConditionValue_filter_def)
apply (auto simp add: ValueCondition_Tautology_def ValueCondition_Sat_def)
apply (auto simp add: taut_test_def sat_test_def)
sorry

primrec choose_values :: "('FMode, 'vv) Values \<Rightarrow> ('FMode, 'vv) Values option 
  \<Rightarrow> ('FMode, 'vv) Values option"
where
  "choose_values _ None = None" |
  "choose_values v1 (Some v2) = (if (v1 = v2) then (Some v1) else None)"

definition ValuesOperand_value_eval :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 
  'vb VCEnv \<Rightarrow> ('FMode, 'vv) Values option"
where
  "ValuesOperand_value_eval Es vb \<equiv> 
    fold choose_values (ValuesOperand_eval_values Es vb) None"


lemma [simp]: "(ValuedTautology (VBVExp Es)) \<Longrightarrow> 
  (length (ValuesOperand_eval_values (VBVExp Es) vb) = 1)"
apply (auto)
done

lemma "(ValuedTautology (VBVExp Es)) \<Longrightarrow> 
  (ValuesOperand_value_eval (VBVExp Es) vb = Some v)"
apply (induct Es)
apply (auto simp add: ValuesOperand_value_eval_def)
apply (auto simp add: ValuesOperand_eval_values_def)
apply (auto simp add: CVList_eval_values_def)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuedTautology_CVList_def)
done


end
