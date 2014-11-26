theory ConditionalModePredicate
imports ConditionalMode Boolean_Expression_Checkers
begin

primrec ConditionalValuePredicate :: "('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 
  ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue"
where
  "ConditionalValuePredicate P (CVC b) t1 t2 = (if P b then t1 else t2)" |
  "ConditionalValuePredicate P (CVIF a t1 t2) t3 t4 = 
    CVIF a (ConditionalValuePredicate P t1 t3 t4) (ConditionalValuePredicate P t2 t3 t4)"

primrec CVP2BE :: "('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 'a bool_expr"
where
  "CVP2BE P (CVC b) = Const_bool_expr (P b)" |
  "CVP2BE P (CVIF a t1 t2) = 
    Or_bool_expr 
      (And_bool_expr (Atom_bool_expr a) (CVP2BE P t1)) 
      (And_bool_expr (Neg_bool_expr (Atom_bool_expr a)) (CVP2BE P t2))"

notation (output) ConditionalValuePredicate ("_\<^sub>P \<surd> _ \<oslash> _" 80)

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
