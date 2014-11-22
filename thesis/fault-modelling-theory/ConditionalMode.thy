theory ConditionalMode

imports ModeCondition Complex_Main FaultModellingTypes

begin

datatype_new ('FMode, 'vv) OperationalMode = 
  NominalMode real 
  | FailureMode "'FMode"
  | VarMode (var: 'vv)

datatype_new ('vb, 'FMode, 'vv) ConditionalMode =
  CMConst "('FMode, 'vv) OperationalMode"
  | CMExp "('vb, 'FMode, 'vv) CMPair list" and
  ('vb, 'FMode, 'vv) CMPair = 
    CM (CMC:"'vb ModeCondition") (CMM:"('vb, 'FMode, 'vv) ConditionalMode")

type_synonym ('vb, 'FMode, 'vv) ConditionalModePair = 
  "('vb ModeCondition \<times> ('FMode, 'vv) OperationalMode)"

notation (output) NominalMode ("N\<langle>_\<rangle>" 40)
notation (output) FailureMode ("F\<langle>_\<rangle>" 41)
notation (output) VarMode ("_" 41)
notation (output) CMConst  ("_" 50)
notation (output) CMExp ("VT _" 80)
notation (output) CM (infix "\<surd>" 80)

primrec expand_CM2CMP :: "'vb ModeCondition \<Rightarrow> 
  ('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow>
  ('vb, 'FMode, 'vv) ConditionalModePair list"
where
  "expand_CM2CMP e [] = []" |
  "expand_CM2CMP e (v # vs) = (MCAnd e (fst v), snd v) # (expand_CM2CMP e vs)"

primrec 
  CM2CMP :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalModePair list" and
  CM2CMP_list :: "('vb, 'FMode, 'vv) CMPair list \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalModePair list" and
  CM2CMP_CM :: "('vb, 'FMode, 'vv) CMPair \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalModePair list" 
where
  "CM2CMP (CMConst c) = [ (MCConst True, c) ]" |
  "CM2CMP (CMExp v) = CM2CMP_list v" |
  "CM2CMP_list [] = []" |
  "CM2CMP_list (E # Es) = (CM2CMP_CM E) @ (CM2CMP_list Es)" |
  "CM2CMP_CM (CM e v) = expand_CM2CMP e (CM2CMP v)"

fun mkVO :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
  ('vb, 'FMode, 'vv) ConditionalMode"
where
  "mkVO (CMConst c1) (CMConst c2) = CMConst c1" |
  "mkVO (CMConst c1) (CMExp Es) = (CMExp ((CM (MCConst True) (CMConst c1)) # Es))" |
  "mkVO (CMExp Es1) (CMExp Es2) = CMExp (Es1 @ Es2)" |
  "mkVO (CMExp Es) (CMConst c1) = (CMExp (Es @ [CM (MCConst True) (CMConst c1)]))" 

fun CMP2CM :: "('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalMode"
where
  "CMP2CM [] = CMExp []" |
  "CMP2CM [ cv ] = 
  (
    if ModeCondition_Tautology (fst cv) 
      then CMConst (snd cv) 
      else CMExp [ CM (fst cv) (CMConst (snd cv)) ]
  )" |
  "CMP2CM (cv # cvs) = mkVO (CMP2CM [cv]) (CMP2CM cvs)"

definition CMP2MC :: "('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 'vb ModeCondition"
where
  "CMP2MC cvs \<equiv> fold (\<lambda> a b. MCOr (fst a) b) cvs (MCConst False)"

definition ValuedTautology_CMPList :: "('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "ValuedTautology_CMPList cmpl \<equiv> cmpl \<noteq> [] \<and>
    ((ModeCondition_Tautology \<circ> CMP2MC) cmpl) \<and>
    (\<forall> i j. 
      (
        let ei = fst (cmpl!i); ej = fst (cmpl!j); vi = snd (cmpl!i); vj = snd (cmpl!j)
        in ModeCondition_Absorb ei ej \<longrightarrow> vi = vj
      )
    )"

definition CMPList_eval_values :: 
  "('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 
  'vb MCEnv \<Rightarrow> 
  ('FMode, 'vv) OperationalMode list"
where
  "CMPList_eval_values cvs s \<equiv> 
  (
    let 
      filtercvs = filter (\<lambda> cv. ModeCondition_eval (fst cv) s);
      getvalue = map snd;
      filterValue = (\<lambda> vs. if vs = [] then [] else hd vs # (filter (\<lambda> v. v \<noteq> hd vs) (tl vs)))
    in (filterValue \<circ> getvalue \<circ> filtercvs) cvs
  )"
lemma CMPList_eval_values_single: 
  "\<lbrakk> ModeCondition_eval a s \<rbrakk> \<Longrightarrow> (CMPList_eval_values [(a,x)] s = [x])"
apply (simp add: CMPList_eval_values_def)
done

corollary CMPList_eval_values_not_empty: "
  \<lbrakk> ModeCondition_eval a s \<rbrakk> \<Longrightarrow> 
  (CMPList_eval_values [(a,x)] s) \<noteq> []"
apply (simp add: CMPList_eval_values_single)
done


theorem UniqueValue_ValuedTautology: 
  "ValuedTautology_CMPList cmpl \<longrightarrow> (\<forall> s. length (CMPList_eval_values cmpl s) = 1)"
using [[simp_trace=true]]
apply (induct cmpl)
apply (simp add: ValuedTautology_CMPList_def)
apply (simp)
apply (auto)
apply (auto simp add: t1)
done


(*
primrec
  ConditionalMode_values_eval :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
    'vb MCEnv \<Rightarrow> ('FMode, 'vv) OperationalMode list" and
  ConditionalMode_values_eval_list :: "('vb, 'FMode, 'vv) CMPair list \<Rightarrow> 'vb MCEnv \<Rightarrow> 
    ('FMode, 'vv) OperationalMode list" and
  ConditionalMode_values_eval_VB :: "('vb, 'FMode, 'vv) CMPair \<Rightarrow> 'vb MCEnv \<Rightarrow> 
    ('FMode, 'vv) OperationalMode list" 
where
  "ConditionalMode_values_eval (CMConst c) vb = c # []" |
  "ConditionalMode_values_eval (CMExp Es) vb = (ConditionalMode_values_eval_list Es vb)" |
  "ConditionalMode_values_eval_list [] vb = []" |
  "ConditionalMode_values_eval_list (E # Es) vb = 
    (ConditionalMode_values_eval_VB E vb) @ (ConditionalMode_values_eval_list Es vb)" |
  "ConditionalMode_values_eval_VB (VB e v) vb = 
    (if (ModeCondition_eval e vb) then (ConditionalMode_values_eval v vb) else [])"

notation (output) ConditionalMode_values_eval ("\<lbrakk>_\<rbrakk> \<langle>_\<rangle>")
*)

primrec  
  CM2MC :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> 'vb ModeCondition" and
  CM2MC_list :: 
    "('vb, 'FMode, 'vv) CMPair list \<Rightarrow> 'vb ModeCondition" and
  CM2MC_VB :: "('vb, 'FMode, 'vv) CMPair \<Rightarrow> 'vb ModeCondition"
where
  "CM2MC (CMConst _) = (MCConst True)" |
  "CM2MC (CMExp Es) = CM2MC_list Es" |
  "CM2MC_list [] = (MCConst False)" |
  "CM2MC_list (E # Es) = MCOr (CM2MC_VB E) (CM2MC_list Es)" |
  "CM2MC_VB (CM e _) = e"

definition ValuedTautology :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> bool"
where
  "ValuedTautology v \<equiv> (ValuedTautology_CMPList \<circ> CM2CMP) v"

notation (output) ValuedTautology ("\<TT> _")

lemma [simp]: "
  \<lbrakk>
    ValuedTautology U;
    ValuedTautology V
  \<rbrakk> 
  \<Longrightarrow> ValuedTautology (CMExp [VB (MCConst True) U, VB (MCNot (MCConst True)) V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma [simp]: "
  \<lbrakk>
    ValuedTautology U;
    ValuedTautology V
  \<rbrakk> 
  \<Longrightarrow> 
  ValuedTautology (CMExp [VB A U, VB (MCNot A) V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma valued_tautology_or : 
  "\<lbrakk>
    ValuedTautology U;
    ValuedTautology V;
    ValuedTautology Q;
    (ModeCondition_Sat (MCAnd A B) \<longrightarrow> U = V)
   \<rbrakk>
   \<Longrightarrow> 
   ValuedTautology (CMExp [VB A U, VB B V, VB (MCAnd (MCNot A) (MCNot B)) Q])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma not_valued_tautology1 : "
(\<not> (ModeCondition_Sat A)) \<Longrightarrow> 
  (\<not> ValuedTautology (CMExp [VB A U]))"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma not_valued_tautology2 : 
  "(\<not> (ModeCondition_Sat (MCOr A B))) \<Longrightarrow> 
  \<not> ValuedTautology (CMExp [VB A U, VB B V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

definition CMPPredicate :: "(('FMode, 'vv) OperationalMode \<Rightarrow> bool) \<Rightarrow> 
  ('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 'vb ModeCondition"
where
  "CMPPredicate P cmps = 
  (
    let 
      select = filter (\<lambda> cmp. P (snd cmp));
      transform = CMP2MC
    in (transform \<circ> select) cmps
  )"

lemma "(CMPPredicate (\<lambda> _. True) cmpl) = (CMP2MC cmpl)"
apply (induct cmpl)
apply (auto simp add: CMPPredicate_def)
done

lemma "(CMPPredicate (\<lambda> _. False) cmpl) = MCConst False"
apply (induct cmpl)
apply (auto simp add: CMPPredicate_def CMP2MC_def)
done

definition 
  ConditionalModePredicate_ModeCondition :: "(('FMode, 'vv) OperationalMode \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> 'vb ModeCondition"
where
  "ConditionalModePredicate_ModeCondition P cm \<equiv> CMPPredicate P (CM2CMP cm)"

fun nominal_op :: 
  "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> 
  (real \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow>
  (('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "nominal_op (NominalMode a) (NominalMode b) f _ = (f a b)" |
  "nominal_op (FailureMode _) (NominalMode _) _ _ = False" |
  "nominal_op (NominalMode _) (FailureMode _) _ _ = False" |
  "nominal_op a b _ g = (g a b)"

definition lte_Values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> bool"
where
  "lte_Values a b \<equiv> nominal_op a b (op \<le>) (op =)"

abbreviation gte_Values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> bool" 
where
  "gte_Values a b \<equiv> lte_Values b a"

definition lt_Values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> bool"
where
  "lt_Values a b \<equiv> nominal_op a b (op <) (\<lambda> _ _. False)"

abbreviation gt_Values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> bool"
where
  "gt_Values a b \<equiv> lt_Values b a"

abbreviation eq_Values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode \<Rightarrow> bool"
where
  "eq_Values a b \<equiv> (a = b)"

notation (output) lte_Values  (infix "\<le>" 50)
notation (output) gte_Values  (infix "\<ge>" 50)
notation (output) lt_Values  (infix "<" 50)
notation (output) gt_Values  (infix ">" 50)
notation (output) eq_Values  (infix "=" 50)

value "ConditionalModePredicate_ModeCondition 
  (lte_Values (NominalMode 2))   (CMExp [
    VB (MCVar A) (CMConst (FailureMode F1)),
    VB (MCNot (MCVar A)) (CMConst (NominalMode 5))
  ]) 
  "

definition ConditionalMode_eval_values :: 
  "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> 'vb MCEnv \<Rightarrow> ('FMode, 'vv) OperationalMode list"
where
  "ConditionalMode_eval_values v s \<equiv> CMPList_eval_values (CM2CMP v) s"

theorem [simp]: "ValuedTautology v \<Longrightarrow> length (ConditionalMode_eval_values v s) = 1"
apply (induct v)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ConditionalMode_eval_values_def)
done

definition normalise_ConditionalModePair_filter :: 
  "('vb, 'FMode, 'vv) ConditionalModePair \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "normalise_ConditionalModePair_filter cv cvs \<equiv> 
    ModeCondition_Sat (fst cv) \<and> 
    (filter (\<lambda> cv2. snd cv = snd (cv2) \<and> ModeCondition_Equiv (fst cv) (fst (cv2))) cvs = [])"

primrec normalise_ConditionalModePair :: "
  ('vb, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalModePair list"
where
  "normalise_ConditionalModePair [] = []" |
  "normalise_ConditionalModePair (cv # cvs) = (
    if (normalise_ConditionalModePair_filter cv cvs) 
      then cv # (normalise_ConditionalModePair cvs)
      else (normalise_ConditionalModePair cvs)
  )"

definition
  normalise_ConditionalMode :: 
    "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('vb, 'FMode, 'vv) ConditionalMode" 
where
  "normalise_ConditionalMode \<equiv> CMP2CM \<circ> normalise_ConditionalModePair \<circ> CM2CMP" 

(*
primrec 
  isNormal_ConditionalMode :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> bool" and
  isNormal_ConditionalMode_list :: "('vb, 'FMode, 'vv) CMPair list \<Rightarrow> bool" and
  isNormal_ConditionalMode_CM :: "('vb, 'FMode, 'vv) CMPair \<Rightarrow> bool" 
where
  "isNormal_ConditionalMode (CMConst c) = True" |
  "isNormal_ConditionalMode (CMExp Es) = (isNormal_ConditionalMode_list Es)" |
  "isNormal_ConditionalMode_list [] = True" |
  "isNormal_ConditionalMode_list (E # Es) = 
    ((isNormal_ConditionalMode_CM E) \<and> (isNormal_ConditionalMode_list Es))" |
  "isNormal_ConditionalMode_CM (CM e v) = 
    ((ModeCondition_Sat e) \<and> (isNormal_ConditionalMode v))"

lemma [simp]: "(isNormal_ConditionalMode \<circ> normalise_ConditionalMode) v"
apply (induct v)
apply (auto simp add: normalise_ConditionalMode_def isNormal_ConditionalMode_def)
apply (auto simp add: ModeCondition_Tautology_def)
apply (auto simp add: taut_test_def)
apply (auto simp add: normalise_ConditionalModePair_filter_def)
apply (auto simp add: ModeCondition_Sat_def)
apply (auto simp add: sat_test_def)
apply (auto simp add: ModeCondition_to_bool_expr_def)
sorry

theorem "\<lbrakk> v \<noteq> CMExp [] \<rbrakk> \<Longrightarrow> (v = normalise_ConditionalMode v) \<longleftrightarrow> (isNormal_ConditionalMode v)"
apply (induct v)
apply (auto simp add: normalise_ConditionalMode_def normalise_ConditionalModePair_filter_def)
apply (auto simp add: ModeCondition_Tautology_def ModeCondition_Sat_def)
apply (auto simp add: taut_test_def sat_test_def)
sorry
*)
primrec choose_values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode option 
  \<Rightarrow> ('FMode, 'vv) OperationalMode option"
where
  "choose_values _ None = None" |
  "choose_values v1 (Some v2) = (if (v1 = v2) then (Some v1) else None)"

definition ConditionalMode_eval_value :: "('vb, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
  'vb MCEnv \<Rightarrow> ('FMode, 'vv) OperationalMode option"
where
  "ConditionalMode_eval_value Es vb \<equiv> 
    fold choose_values (ConditionalMode_eval_values Es vb) None"


lemma [simp]: "(ValuedTautology (CMExp Es)) \<Longrightarrow> 
  (length (ConditionalMode_eval_values (CMExp Es) vb) = 1)"
apply (auto)
done

lemma "(ValuedTautology (CMExp Es)) \<Longrightarrow> 
  (ConditionalMode_eval_value (CMExp Es) vb = Some v)"
apply (induct Es)
apply (auto simp add: ConditionalMode_eval_value_def)
apply (auto simp add: ConditionalMode_eval_values_def)
apply (auto simp add: CMPList_eval_values_def)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuedTautology_CMPList_def)
sorry

theorem "(ValuedTautology cm) \<Longrightarrow> 
  (ConditionalMode_eval_value cm vb = Some v)"
apply (induct cm)
apply (auto simp add: ConditionalMode_eval_value_def)
apply (auto simp add: ConditionalMode_eval_values_def)
apply (auto simp add: CMPList_eval_values_def)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuedTautology_CMPList_def)
done

end
