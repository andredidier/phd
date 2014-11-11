theory ValuesOperand

imports BoolOperand Complex_Main FaultModellingTypes

begin

text {* We define a data type to represent  *}

datatype 'FMode Values = 
  FMNominal real 
  | FMFailure "'FMode"

datatype ('vb, 'vv, 'FMode) ValuesOperand =
  VBVConstOp "'FMode Values"
  | VBVVarOp 'vv
  | VBVExpOp "('vb, 'vv, 'FMode) ValuedBool list" and
  ('vb, 'vv, 'FMode) ValuedBool = VB "'vb BoolOperand" "('vb, 'vv, 'FMode) ValuesOperand"

notation (output) FMNominal ("_\<^sub>N" 40)
notation (output) FMFailure ("_\<^sub>F" 41)
notation (output) VBVConstOp  ("_\<^sub>V" 50)
notation (latex) VBVConstOp ("_\<^raw:$_{\mathrm{V}}$>" 51)
notation (output) VBVVarOp ("\<lbrakk>_\<rbrakk>\<^sub>V" 60)
notation (latex) VBVVarOp ("\<lbrakk>_\<rbrakk>\<^raw:$_{\mathrm{V}}$>" 61)
notation (output) VBVExpOp ("Vs _" 80)
notation (latex) VBVExpOp ("\<^raw:$\mathrm{V} >_\<^raw:$>" 81)
notation (output) VB ("_ <_>" 80)

primrec 
  ValuesOperand_bool_eval :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_list :: "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_VB :: "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "ValuesOperand_bool_eval (VBVConstOp c) vb = True" |
  "ValuesOperand_bool_eval (VBVVarOp v) vb = True" |
  ValuedTautology_VBVExpOp:
  "ValuesOperand_bool_eval (VBVExpOp Es) vb = (ValuesOperand_bool_eval_list Es vb)" |
  "ValuesOperand_bool_eval_list [] vb = False" |
  "ValuesOperand_bool_eval_list (E # Es) vb = 
    ((ValuesOperand_bool_eval_VB E vb) \<or> (ValuesOperand_bool_eval_list Es vb))" |
  "ValuesOperand_bool_eval_VB (VB e v) vb = (BoolOperand_eval e vb)"

value "op \<or>"

primrec choose_value :: "'FMode Values option binop" where
  "choose_value None vo = vo" |
  "choose_value (Some v) vo = (if (Some v) = vo then vo else None)"

primrec
  ValuesOperand_values_eval :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> 
    ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> 'FMode Values) \<Rightarrow> 'FMode Values list" and
  ValuesOperand_values_eval_list :: "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('vv \<Rightarrow> 'FMode Values) \<Rightarrow> 'FMode Values list" and
  ValuesOperand_values_eval_VB :: "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('vv \<Rightarrow> 'FMode Values) \<Rightarrow> 'FMode Values list" 
where
  "ValuesOperand_values_eval (VBVConstOp c) vb vv = c # []" |
  "ValuesOperand_values_eval (VBVVarOp v) vb vv = (vv v) # []" |
  "ValuesOperand_values_eval (VBVExpOp Es) vb vv = (ValuesOperand_values_eval_list Es vb vv)" |
  "ValuesOperand_values_eval_list [] vb vv = []" |
  "ValuesOperand_values_eval_list (E # Es) vb vv = 
    (ValuesOperand_values_eval_VB E vb vv) @ (ValuesOperand_values_eval_list Es vb vv)" |
  "ValuesOperand_values_eval_VB (VB e v) vb vv = 
    (if (BoolOperand_eval e vb) then (ValuesOperand_values_eval v vb vv) else [])"

(*
primrec
  ValuesOperand_value_eval :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> 
    ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> 'FMode Values option) \<Rightarrow> 'FMode Values option" and
  ValuesOperand_value_eval_list :: "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('vv \<Rightarrow> 'FMode Values option) \<Rightarrow> 'FMode Values option list" and
  ValuesOperand_value_eval_VB :: "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('vv \<Rightarrow> 'FMode Values option) \<Rightarrow> 'FMode Values option" 
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
*)

primrec ValuedTautology_values_nonemptylist :: "'FMode Values \<Rightarrow> 'FMode Values list \<Rightarrow> bool"
where
  "ValuedTautology_values_nonemptylist vref [] = True" |
  "ValuedTautology_values_nonemptylist vref (v # vs) = 
    ((vref = v) \<and> (ValuedTautology_values_nonemptylist vref vs))"

primrec ValuedTautology_values_list :: "'FMode Values list \<Rightarrow> bool"
where
  "ValuedTautology_values_list [] = False" |
  "ValuedTautology_values_list (v # vs) = ValuedTautology_values_nonemptylist v vs"

definition ValuedTautology :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    ('vv \<Rightarrow> 'FMode Values) \<Rightarrow> bool"
where
  "ValuedTautology Es vb vv \<equiv> ValuedTautology_values_list (ValuesOperand_values_eval Es vb vv)"

lemma [simp]: "(BoolOperand_eval A vb) \<or> (BoolOperand_eval (VBBNotOp A) vb)"
apply (simp)
done

lemma  [simp]: "
  \<lbrakk>
    ValuesOperand_values_eval U vb vv \<noteq> [];
    ValuesOperand_values_eval V vb vv \<noteq> []
  \<rbrakk> 
  \<Longrightarrow> 
  (ValuesOperand_values_eval (VBVExpOp [VB A U, VB (VBBNotOp A) V]) vb vv) \<noteq> []"
apply (simp)
done

theorem [simp]: "
  \<lbrakk>
    ValuedTautology U vb vv;
    ValuedTautology V vb vv
  \<rbrakk> 
  \<Longrightarrow> 
  ValuedTautology (VBVExpOp [VB A U, VB (VBBNotOp A) V]) vb vv"
apply (simp add: ValuedTautology_def)
done

lemma [simp]: "ValuedTautology V vb vv \<Longrightarrow> ValuesOperand_values_eval V vb vv \<noteq> []"
apply (auto simp add: ValuedTautology_def ValuesOperand_values_eval_def)
done

lemma [simp]: "ValuedTautology V vb vv \<Longrightarrow> ValuedTautology_values_list (
    ValuesOperand_values_eval V vb vv )"
apply (simp add: ValuedTautology_def ValuesOperand_values_eval_def)
done

lemma [simp]: "ValuedTautology_values_list xs \<longrightarrow> ValuedTautology_values_list (xs @ xs)"
apply (induct_tac xs)
apply (simp)
apply (simp add: ValuedTautology_values_list_def)
apply (simp add: ValuedTautology_values_nonemptylist_def)
sorry

lemma [simp]: "ValuedTautology V vb vv \<Longrightarrow> ValuedTautology_values_list (
    (ValuesOperand_values_eval V vb vv) @ (ValuesOperand_values_eval V vb vv))"
apply (auto simp add: ValuedTautology_def ValuesOperand_values_eval_def)
done

lemma valued_tautology_or : 
  "\<lbrakk>
    ValuedTautology U vb vv;
    ValuedTautology V vb vv;
    ValuedTautology Q vb vv;
    ((BoolOperand_eval A vb \<and> BoolOperand_eval B vb) \<longrightarrow> U = V)
   \<rbrakk>
   \<Longrightarrow> 
   ValuedTautology (VBVExpOp [VB A U, VB B V, VB (VBBAndOp (VBBNotOp A) (VBBNotOp B)) Q]) vb vv"
apply (simp add: ValuedTautology_def)
done

lemma not_valued_tautology1 : "(\<not> (BoolOperand_eval A vb)) \<Longrightarrow> (\<not> ValuedTautology (VBVExpOp [VB A U]) vb vv)"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

lemma not_valued_tautology2 : 
  "(\<not> (BoolOperand_eval A vb) \<and> \<not> (BoolOperand_eval B vb)) \<Longrightarrow> \<not> ValuedTautology (VBVExpOp [VB A U, VB B V]) vb vv"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

primrec 
  ValuesOperandPredicate_BoolOperand :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> 
    (('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> bool) \<Rightarrow> 'vb BoolOperand" and
  ValuesOperandPredicate_BoolOperand_list :: "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> 
    (('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> bool) \<Rightarrow> 'vb BoolOperand" and
  ValuesOperandPredicate_BoolOperand_VB :: "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> 
    (('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> bool) \<Rightarrow> 'vb BoolOperand"
where
  "ValuesOperandPredicate_BoolOperand (VBVConstOp c) P = (VBBConstOp (P (VBVConstOp c)))" |
  "ValuesOperandPredicate_BoolOperand (VBVVarOp v) P = (VBBConstOp (P (VBVVarOp v)))" |
  "ValuesOperandPredicate_BoolOperand (VBVExpOp Es) P = ValuesOperandPredicate_BoolOperand_list Es P" |
  "ValuesOperandPredicate_BoolOperand_list [] P = (VBBConstOp False)" |
  "ValuesOperandPredicate_BoolOperand_list (E # Es) P = VBBOrOp  
    (ValuesOperandPredicate_BoolOperand_VB E P) (ValuesOperandPredicate_BoolOperand_list Es P)" |
  "ValuesOperandPredicate_BoolOperand_VB (VB e v) P = (if (P v) then e else (VBBConstOp False))"

primrec 
  expand_BoolOperand_ValuesOperand :: 
    "'vb BoolOperand \<Rightarrow> ('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> ('vb, 'vv, 'FMode) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_list :: 
    "'vb BoolOperand \<Rightarrow> ('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> 
      ('vb, 'vv, 'FMode) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_VB :: 
    "'vb BoolOperand \<Rightarrow> ('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> ('vb, 'vv, 'FMode) ValuedBool"
where
  "expand_BoolOperand_ValuesOperand e (VBVConstOp c) = (VB e (VBVConstOp c)) # []" |
  "expand_BoolOperand_ValuesOperand e (VBVVarOp v) = (VB e (VBVVarOp v)) # []" |
  expand_BoolOperand_ValuesOperand_VBExpOp:
  "expand_BoolOperand_ValuesOperand e (VBVExpOp Es) = expand_BoolOperand_ValuesOperand_list e Es" |
  "expand_BoolOperand_ValuesOperand_list e [] = []" |
  "expand_BoolOperand_ValuesOperand_list e (E # Es) = 
    (expand_BoolOperand_ValuesOperand_VB e E) # (expand_BoolOperand_ValuesOperand_list e Es)" |
  "expand_BoolOperand_ValuesOperand_VB e1 (VB e2 v2) = VB (VBBAndOp e1 e2) v2"

primrec 
  normalise_ValuesOperand :: 
    "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> ('vb, 'vv, 'FMode) ValuesOperand" and
  normalise_ValuesOperand_list :: 
    "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> ('vb, 'vv, 'FMode) ValuedBool list" and
  normalise_ValuesOperand_VB :: 
    "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> ('vb, 'vv, 'FMode) ValuedBool list" 
where
  "normalise_ValuesOperand (VBVConstOp c) = VBVConstOp c" |
  "normalise_ValuesOperand (VBVVarOp v) = VBVVarOp v" |
  normalise_ValuesOperand_VBVExpOp:
  "normalise_ValuesOperand (VBVExpOp E) = VBVExpOp (normalise_ValuesOperand_list E)" |
  "normalise_ValuesOperand_list [] = []" |
  "normalise_ValuesOperand_list (e # E) = 
    (normalise_ValuesOperand_VB e) @ (normalise_ValuesOperand_list E)" |
  "normalise_ValuesOperand_VB (VB e v) = expand_BoolOperand_ValuesOperand e v"

lemma 
  "(normalise_ValuesOperand V) \<noteq> (normalise_ValuesOperand U) \<Longrightarrow>
  BoolOperand_eval ((ValuesOperandPredicate_BoolOperand (VBVExpOp [VB A U, VB (VBBExpUnOp Not A) V]) 
    (\<lambda> Es. ((normalise_ValuesOperand Es) = (normalise_ValuesOperand U))))) vb
  = (BoolOperand_eval A vb)"
apply (auto)
done

primrec choose_values :: "'FMode Values \<Rightarrow> 'FMode Values option \<Rightarrow> 'FMode Values option"
where
  "choose_values _ None = None" |
  "choose_values v1 (Some v2) = (if (v1 = v2) then (Some v1) else None)"

definition ValuesOperand_value_eval :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> 
  ('vb \<Rightarrow> bool) \<Rightarrow> ('vv \<Rightarrow> 'FMode Values) \<Rightarrow> 'FMode Values option"
where
  "ValuesOperand_value_eval Es vb vv \<equiv> 
    fold choose_values (ValuesOperand_values_eval Es vb vv) None"

lemma [simp]: "(ValuedTautology (VBVExpOp Es) vb vv) \<Longrightarrow> 
  (length (ValuesOperand_values_eval (VBVExpOp Es) vb vv) > 0)"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

lemma "(ValuedTautology (VBVExpOp Es) vb vv) \<Longrightarrow> 
  (ValuesOperand_value_eval (VBVExpOp Es) vb vv = Some v)"
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuesOperand_value_eval_def)
apply (auto simp add: choose_values_def)
apply (auto simp add: ValuedTautology_values_list_def)
apply (auto simp add: ValuedTautology_values_nonemptylist_def)
apply (auto simp add: fold_def)
apply (auto simp add: ValuesOperand_values_eval_list_def)
sorry

primrec 
  ValuesOperand_variables :: "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> 'vv set" and
  ValuesOperand_variables_list :: "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> 'vv set" and
  ValuesOperand_variables_VB :: "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> 'vv set" 
where
  "ValuesOperand_variables (VBVConstOp c) = {}" |
  "ValuesOperand_variables (VBVVarOp v) = {v}" |
  "ValuesOperand_variables (VBVExpOp E) = ValuesOperand_variables_list E" |
  "ValuesOperand_variables_list [] = {}" |
  "ValuesOperand_variables_list (e # E) = 
    (ValuesOperand_variables_VB e) \<union> (ValuesOperand_variables_list E)" |
  "ValuesOperand_variables_VB (VB e v) = ValuesOperand_variables v"

primrec 
  ValuesOperand_replace_var :: 
    "('vb, 'vv, 'FMode) ValuesOperand \<Rightarrow> ('vv \<rightharpoonup> ('vb, 'vv, 'FMode) ValuesOperand) \<Rightarrow> 
    ('vb, 'vv, 'FMode) ValuesOperand" and
  ValuesOperand_replace_var_list :: 
    "('vb, 'vv, 'FMode) ValuedBool list \<Rightarrow> ('vv \<rightharpoonup> ('vb, 'vv, 'FMode) ValuesOperand) \<Rightarrow>
    ('vb, 'vv, 'FMode) ValuedBool list" and
  ValuesOperand_replace_var_VB :: 
    "('vb, 'vv, 'FMode) ValuedBool \<Rightarrow> ('vv \<rightharpoonup> ('vb, 'vv, 'FMode) ValuesOperand) \<Rightarrow>
    ('vb, 'vv, 'FMode) ValuedBool" 
where
  "ValuesOperand_replace_var (VBVConstOp c) _ = VBVConstOp c" |
  "ValuesOperand_replace_var (VBVVarOp v) m = (if m v = None then (VBVVarOp v) else the (m v))" |
  "ValuesOperand_replace_var (VBVExpOp E) m = VBVExpOp (ValuesOperand_replace_var_list E m )" |
  "ValuesOperand_replace_var_list [] _ = []" |
  "ValuesOperand_replace_var_list (e # E) m  = 
    (ValuesOperand_replace_var_VB e m) # (ValuesOperand_replace_var_list E m)" |
  "ValuesOperand_replace_var_VB (VB e v) m = (VB e (ValuesOperand_replace_var v m))"

value "ValuesOperand_replace_var 
  (VBVExpOp [VB (VBBNotOp (VBBVarOp B)) (VBVVarOp A), VB (VBBVarOp B) (VBVVarOp A)]) 
  [A \<mapsto> (VBVConstOp (FMNominal 5))]"

lemma "(ValuesOperand_values_eval (VBVExpOp [VB (VBBNotOp A) V, VB A V]) vb vv) = 
  ValuesOperand_values_eval V vb vv"
apply (auto)
done

end
