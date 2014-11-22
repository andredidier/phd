theory ConditionalMode

imports ModeCondition Complex_Main FaultModellingTypes

begin

datatype_new ('FMode, 'vv) OperationalMode = 
  NominalMode real 
  | FailureMode "'FMode"
  | VarMode (var: 'vv)

datatype_new ('a, 'FMode, 'vv) ConditionalMode =
  CMConst "('FMode, 'vv) OperationalMode"
  | CMExp "('a, 'FMode, 'vv) CMPair list" and
  ('a, 'FMode, 'vv) CMPair = 
    CM (CMC:"'a") (CMM:"('a, 'FMode, 'vv) ConditionalMode")

type_synonym ('a, 'FMode, 'vv) ConditionalModePair = 
  "('a \<times> ('FMode, 'vv) OperationalMode)"

notation (output) NominalMode ("N\<langle>_\<rangle>" 40)
notation (output) FailureMode ("F\<langle>_\<rangle>" 41)
notation (output) VarMode ("_" 41)
notation (output) CMConst  ("_" 50)
notation (output) CMExp ("VT _" 80)
notation (output) CM (infix "\<surd>" 80)

primrec expand_CM2CMP :: "('a, 'b, 'c) Condition \<Rightarrow> 'a \<Rightarrow>
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow>
  ('a, 'FMode, 'vv) ConditionalModePair list"
where
  "expand_CM2CMP c e [] = []" |
  "expand_CM2CMP c e (v # vs) = 
    (Both c e (fst v), snd v) # (expand_CM2CMP c e vs)"

primrec 
  CM2CMP :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list" and
  CM2CMP_list :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair list \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list" and
  CM2CMP_CM :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list" 
where
  "CM2CMP cond (CMConst c) = [ (Top cond, c) ]" |
  "CM2CMP cond (CMExp v) = CM2CMP_list cond v" |
  "CM2CMP_list cond [] = []" |
  "CM2CMP_list cond (E # Es) = (CM2CMP_CM cond E) @ (CM2CMP_list cond Es)" |
  "CM2CMP_CM cond (CM e v) = expand_CM2CMP cond e (CM2CMP cond v)"

fun mkVO :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode"
where
  "mkVO cond (CMConst c1) (CMConst c2) = CMConst c1" |
  "mkVO cond (CMConst c1) (CMExp Es) = (CMExp ((CM (Top cond) (CMConst c1)) # Es))" |
  "mkVO cond (CMExp Es1) (CMExp Es2) = CMExp (Es1 @ Es2)" |
  "mkVO cond (CMExp Es) (CMConst c1) = (CMExp (Es @ [CM (Top cond) (CMConst c1)]))" 

fun CMP2CM :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalMode"
where
  "CMP2CM _ [] = CMExp []" |
  "CMP2CM cond [ cv ] = 
  (
    if Tautology cond (fst cv) 
      then CMConst (snd cv) 
      else CMExp [ CM (fst cv) (CMConst (snd cv)) ]
  )" |
  "CMP2CM cond (cv # cvs) = mkVO cond (CMP2CM cond [cv]) (CMP2CM cond cvs)"

definition CMP2MC :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 'a"
where
  "CMP2MC cond cmpl \<equiv> fold (\<lambda> a b. Any cond (fst a) b) cmpl (Bot cond)"

definition ValuedTautology_CMPList :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "ValuedTautology_CMPList cond cmpl \<equiv> cmpl \<noteq> [] \<and>
    (((Tautology cond) \<circ> (CMP2MC cond)) cmpl) \<and>
    (\<forall> i j. 
      (
        let ei = fst (cmpl!i); ej = fst (cmpl!j); vi = snd (cmpl!i); vj = snd (cmpl!j)
        in Absorb cond ei ej \<longrightarrow> vi = vj
      )
    )"

definition CMPList_eval_values :: 
  "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 
  ('b \<Rightarrow> 'c) \<Rightarrow> 
  ('FMode, 'vv) OperationalMode set"
where
  "CMPList_eval_values cond cmpl s \<equiv> 
  (
    let 
      filtercvs = filter (\<lambda> cv. Eval cond (fst cv) s);
      getvalue = map snd
    in (set \<circ> getvalue \<circ> filtercvs) cmpl
  )"

lemma CMPList_eval_values_single: 
  "\<lbrakk> Eval cond a s \<rbrakk> \<Longrightarrow> (CMPList_eval_values cond [(a,x)] s = {x})"
apply (simp add: CMPList_eval_values_def)
done

corollary CMPList_eval_values_not_empty: "
  \<lbrakk> Eval cond a s \<rbrakk> \<Longrightarrow> 
  (CMPList_eval_values cond [(a,x)] s) \<noteq> {}"
apply (simp add: CMPList_eval_values_single)
done

lemma t1:
  "\<lbrakk> ValuePreservation cond; ValidOps cond; ValidLattice cond \<rbrakk> \<Longrightarrow>
  ValuedTautology_CMPList cond cmpl \<longrightarrow> (\<forall> s. card (CMPList_eval_values cond cmpl s) > 0)"
apply (induct cmpl)
apply (simp add: ValuedTautology_CMPList_def)
apply (simp)
apply (auto)
sorry

theorem UniqueValue_ValuedTautology: 
  "\<lbrakk> ValuePreservation cond; ValidOps cond \<rbrakk> \<Longrightarrow>
  ValuedTautology_CMPList cond cmpl \<longrightarrow> (\<forall> s. card (CMPList_eval_values cond cmpl s) = 1)"
(*using [[simp_trace=true]]*)
apply (induct cmpl)
apply (simp add: ValuedTautology_CMPList_def)
apply (simp)
apply (auto)
apply (auto simp add: t1)
(*
apply (auto simp add: CMPList_eval_values_def ValuedTautology_CMPList_def CMP2MC_def)
apply (auto simp add: ValuePreservation_def ValidBinops_def)
*)
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
  CM2MC :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 'a" and
  CM2MC_list :: 
    "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair list \<Rightarrow> 'a" and
  CM2MC_VB :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair \<Rightarrow> 'a"
where
  "CM2MC cond (CMConst _) = (Top cond)" |
  "CM2MC cond (CMExp Es) = CM2MC_list cond Es" |
  "CM2MC_list cond [] = (Bot cond)" |
  "CM2MC_list cond (E # Es) = Any cond (CM2MC_VB cond E) (CM2MC_list cond Es)" |
  "CM2MC_VB cond (CM e _) = e"

definition ValuedTautology :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> bool"
where
  "ValuedTautology cond v \<equiv> ((ValuedTautology_CMPList cond) \<circ> (CM2CMP cond)) v"

notation (output) ValuedTautology ("\<VV>\<TT> _")

lemma [simp]: "
  \<lbrakk>
    cond = BoolCondition;
    ValuedTautology cond U;
    ValuedTautology cond V
  \<rbrakk> 
  \<Longrightarrow> ValuedTautology cond (CMExp [VB (MCConst True) U, VB (MCNot (MCConst True)) V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma [simp]: "
  \<lbrakk>
    cond = BoolCondition;
    ValuedTautology cond U;
    ValuedTautology cond V
  \<rbrakk> 
  \<Longrightarrow> 
  ValuedTautology cond (CMExp [VB A U, VB (MCNot A) V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma valued_tautology_or : 
  "\<lbrakk>
    cond = BoolCondition;
    ValuedTautology cond U;
    ValuedTautology cond V;
    ValuedTautology cond Q;
    (Sat cond (MCAnd A B) \<longrightarrow> U = V)
   \<rbrakk>
   \<Longrightarrow> 
   ValuedTautology cond (CMExp [VB A U, VB B V, VB (MCAnd (MCNot A) (MCNot B)) Q])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma not_valued_tautology1 : "cond = BoolCondition \<Longrightarrow>
  (\<not> (Sat cond A)) \<Longrightarrow> 
  (\<not> ValuedTautology cond (CMExp [VB A U]))"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

lemma not_valued_tautology2 : 
  "cond = BoolCondition \<Longrightarrow> (\<not> (Sat cond (MCOr A B))) \<Longrightarrow> 
  \<not> ValuedTautology cond (CMExp [VB A U, VB B V])"
apply (auto simp add: ValuedTautology_def ValuedTautology_CMPList_def)
sorry

definition CMPPredicate :: "('a, 'b, 'c) Condition \<Rightarrow> (('FMode, 'vv) OperationalMode \<Rightarrow> bool) \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 'a"
where
  "CMPPredicate cond P cmps = 
  (
    let 
      select = filter (\<lambda> cmp. P (snd cmp));
      transform = CMP2MC cond
    in (transform \<circ> select) cmps
  )"

lemma "cond = BoolCondition \<Longrightarrow> (CMPPredicate cond (\<lambda> _. True) cmpl) = (CMP2MC cond cmpl)"
apply (induct cmpl)
apply (auto simp add: CMPPredicate_def)
done

lemma "cond = BoolCondition \<Longrightarrow> (CMPPredicate cond (\<lambda> _. True) cmpl) = (CMP2MC cond cmpl)"
apply (induct cmpl)
apply (auto simp add: CMPPredicate_def)
done

lemma "cond = BoolCondition \<Longrightarrow> (CMPPredicate cond (\<lambda> _. False) cmpl) = MCConst False"
apply (induct cmpl)
apply (auto simp add: CMPPredicate_def CMP2MC_def)
done

definition 
  ConditionalModePredicate_ModeCondition :: "('a, 'b, 'c) Condition \<Rightarrow> 
    (('FMode, 'vv) OperationalMode \<Rightarrow> bool) \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 'a"
where
  "ConditionalModePredicate_ModeCondition cond P cm \<equiv> CMPPredicate cond P (CM2CMP cond cm)"

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

definition ConditionalMode_eval_values :: 
  "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 
  ('FMode, 'vv) OperationalMode list"
where
  "ConditionalMode_eval_values cond v s \<equiv> CMPList_eval_values cond (CM2CMP cond v) s"

lemma "cond = BoolCondition \<Longrightarrow>
  ValuedTautology cond v \<Longrightarrow> length (ConditionalMode_eval_values cond v s) = 1"
apply (induct v)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ConditionalMode_eval_values_def)
sorry

theorem "ValuedTautology cond v \<Longrightarrow> length (ConditionalMode_eval_values cond v s) = 1"
apply (induct v)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ConditionalMode_eval_values_def)
sorry

definition normalise_ConditionalModePair_filter :: 
  "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalModePair \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "normalise_ConditionalModePair_filter cond cv cvs \<equiv> 
    Sat cond (fst cv) \<and> 
    (filter (\<lambda> cv2. snd cv = snd (cv2) \<and> Equiv cond (fst cv) (fst (cv2))) cvs = [])"

primrec normalise_ConditionalModePair :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> ('a, 'FMode, 'vv) ConditionalModePair list"
where
  "normalise_ConditionalModePair _ [] = []" |
  "normalise_ConditionalModePair cond (cv # cvs) = (
    if (normalise_ConditionalModePair_filter cond cv cvs) 
      then cv # (normalise_ConditionalModePair cond cvs)
      else (normalise_ConditionalModePair cond cvs)
  )"

definition
  normalise_ConditionalMode :: 
    "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalMode" 
where
  "normalise_ConditionalMode cond \<equiv> 
    (CMP2CM cond) \<circ> (normalise_ConditionalModePair cond) \<circ> (CM2CMP cond)" 

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

definition ConditionalMode_eval_value :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
  ('b \<Rightarrow> 'c) \<Rightarrow> ('FMode, 'vv) OperationalMode option"
where
  "ConditionalMode_eval_value cond Es vb \<equiv> 
    fold choose_values (ConditionalMode_eval_values cond Es vb) None"


lemma "cond = BoolCondition \<Longrightarrow> (ValuedTautology cond (CMExp Es)) \<Longrightarrow> 
  (length (ConditionalMode_eval_values cond (CMExp Es) vb) = 1)"
apply (auto)
sorry

lemma "cond = BoolCondition \<Longrightarrow> (ValuedTautology cond (CMExp Es)) \<Longrightarrow> 
  (ConditionalMode_eval_value cond (CMExp Es) vb = Some v)"
apply (induct Es)
apply (auto simp add: ConditionalMode_eval_value_def)
apply (auto simp add: ConditionalMode_eval_values_def)
apply (auto simp add: CMPList_eval_values_def)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuedTautology_CMPList_def)
sorry

theorem "cond = BoolCondition \<Longrightarrow> (ValuedTautology cond cm) \<Longrightarrow> 
  (ConditionalMode_eval_value cond cm vb = Some v)"
apply (induct cm)
apply (auto simp add: ConditionalMode_eval_value_def)
apply (auto simp add: ConditionalMode_eval_values_def)
apply (auto simp add: CMPList_eval_values_def)
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuedTautology_CMPList_def)
sorry

end
