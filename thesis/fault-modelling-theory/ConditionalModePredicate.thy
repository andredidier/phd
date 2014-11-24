theory ConditionalModePredicate
imports ConditionalMode
begin

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

end
