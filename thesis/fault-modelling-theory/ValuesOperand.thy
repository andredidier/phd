theory ValuesOperand

imports BoolOperand Complex_Main FaultModellingTypes

begin

text {* We define a data type to represent  *}

datatype_new ('FMode, 'vv) Values = 
  FMNominal real 
  | FMFailure "'FMode"
  | FMVar (var: 'vv)

datatype_new ('vb, 'FMode, 'vv) ValuesOperand =
  VBVConstOp "('FMode, 'vv) Values"
  | VBVExpOp "('vb, 'FMode, 'vv) ValuedBool list" and
  ('vb, 'FMode, 'vv) ValuedBool = 
    VB (VBE:"'vb BoolOperand") (VBV:"('vb, 'FMode, 'vv) ValuesOperand")

notation (output) FMNominal ("_\<^sub>N" 40)
notation (output) FMFailure ("_\<^sub>F" 41)
notation (output) FMVar ("\<lbrakk>_\<rbrakk>\<^sub>F\<^sub>M" 41)
notation (output) VBVConstOp  ("_\<^sub>V" 50)
notation (latex) VBVConstOp ("_\<^raw:$_{\mathrm{V}}$>" 51)
notation (output) VBVExpOp ("Vs _" 80)
notation (latex) VBVExpOp ("\<^raw:$\mathrm{V} >_\<^raw:$>" 81)
notation (output) VB ("_ <_>" 80)

primrec 
  ValuesOperand_bool_eval :: "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_list :: "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" and
  ValuesOperand_bool_eval_VB :: "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "ValuesOperand_bool_eval (VBVConstOp c) vb = True" |
  ValuedTautology_VBVExpOp:
  "ValuesOperand_bool_eval (VBVExpOp Es) vb = (ValuesOperand_bool_eval_list Es vb)" |
  "ValuesOperand_bool_eval_list [] vb = False" |
  "ValuesOperand_bool_eval_list (E # Es) vb = 
    ((ValuesOperand_bool_eval_VB E vb) \<or> (ValuesOperand_bool_eval_list Es vb))" |
  "ValuesOperand_bool_eval_VB (VB e v) vb = (BoolOperand_eval e vb)"

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
  "ValuesOperand_values_eval (VBVConstOp c) vb = c # []" |
  "ValuesOperand_values_eval (VBVExpOp Es) vb = (ValuesOperand_values_eval_list Es vb)" |
  "ValuesOperand_values_eval_list [] vb = []" |
  "ValuesOperand_values_eval_list (E # Es) vb = 
    (ValuesOperand_values_eval_VB E vb) @ (ValuesOperand_values_eval_list Es vb)" |
  "ValuesOperand_values_eval_VB (VB e v) vb = 
    (if (BoolOperand_eval e vb) then (ValuesOperand_values_eval v vb) else [])"

(*
primrec
  ValuesOperand_value_eval :: "('vb, 'FMode) ValuesOperand \<Rightarrow> 
    ('vb \<Rightarrow> bool) \<Rightarrow> (('vv, 'FMode) VBVVarOpVal option) \<Rightarrow> 'FMode Values option" and
  ValuesOperand_value_eval_list :: "('vb, 'FMode) ValuedBool list \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    (('vv, 'FMode) VBVVarOpVal option) \<Rightarrow> 'FMode Values option list" and
  ValuesOperand_value_eval_VB :: "('vb, 'FMode) ValuedBool \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> 
    (('vv, 'FMode) VBVVarOpVal option) \<Rightarrow> 'FMode Values option" 
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
  "ValuedTautology Es vb \<equiv> ValuedTautology_values_list (ValuesOperand_values_eval Es vb)"

lemma [simp]: "(BoolOperand_eval A vb) \<or> (BoolOperand_eval (VBBNotOp A) vb)"
apply (simp)
done

lemma  [simp]: "
  \<lbrakk>
    ValuesOperand_values_eval U vb \<noteq> [];
    ValuesOperand_values_eval V vb \<noteq> []
  \<rbrakk> 
  \<Longrightarrow> 
  (ValuesOperand_values_eval (VBVExpOp [VB A U, VB (VBBNotOp A) V]) vb) \<noteq> []"
apply (simp)
done

theorem [simp]: "
  \<lbrakk>
    ValuedTautology U vb;
    ValuedTautology V vb
  \<rbrakk> 
  \<Longrightarrow> 
  ValuedTautology (VBVExpOp [VB A U, VB (VBBNotOp A) V]) vb"
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
    ((BoolOperand_eval A vb \<and> BoolOperand_eval B vb) \<longrightarrow> U = V)
   \<rbrakk>
   \<Longrightarrow> 
   ValuedTautology (VBVExpOp [VB A U, VB B V, VB (VBBAndOp (VBBNotOp A) (VBBNotOp B)) Q]) vb"
apply (simp add: ValuedTautology_def)
done

lemma not_valued_tautology1 : "
(\<not> (BoolOperand_eval A vb)) \<Longrightarrow> 
  (\<not> ValuedTautology (VBVExpOp [VB A U]) vb)"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

lemma not_valued_tautology2 : 
  "(\<not> (BoolOperand_eval A vb) \<and> \<not> (BoolOperand_eval B vb)) \<Longrightarrow> 
  \<not> ValuedTautology (VBVExpOp [VB A U, VB B V]) vb"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

primrec 
  ValuesOperandPredicate_BoolOperand :: "(('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> 'vb BoolOperand" and
  ValuesOperandPredicate_BoolOperand_list :: "(('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 'vb BoolOperand" and
  ValuesOperandPredicate_BoolOperand_VB :: "(('FMode, 'vv) Values \<Rightarrow> bool) \<Rightarrow> 
    ('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> 'vb BoolOperand"
where
  "ValuesOperandPredicate_BoolOperand P (VBVConstOp c) = (VBBConstOp (P c))" |
  "ValuesOperandPredicate_BoolOperand P (VBVExpOp Es) = 
    normalise_BoolOperand (ValuesOperandPredicate_BoolOperand_list P Es)" |
  "ValuesOperandPredicate_BoolOperand_list _ [] = (VBBConstOp False)" |
  "ValuesOperandPredicate_BoolOperand_list P (E # Es) = VBBOrOp  
    (ValuesOperandPredicate_BoolOperand_VB P E) 
    (ValuesOperandPredicate_BoolOperand_list P Es)" |
  "ValuesOperandPredicate_BoolOperand_VB P (VB e v) = 
    VBBAndOp e (ValuesOperandPredicate_BoolOperand P v)"

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

value "ValuesOperandPredicate_BoolOperand 
  (lte_Values (FMNominal 2))   (VBVExpOp [
    VB (VBBVarOp A) (VBVConstOp (FMFailure F1)),
    VB (VBBNotOp (VBBVarOp A)) (VBVConstOp (FMNominal 5))
  ]) 
  "

primrec 
  apply_BoolOperand :: 
    "'vb BoolOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" and
  apply_BoolOperand_list :: 
    "'vb BoolOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> 
      ('vb, 'FMode, 'vv) ValuedBool list" and
  apply_BoolOperand_VB :: 
    "'vb BoolOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool"
where
  "apply_BoolOperand e (VBVConstOp c) = (VB e (VBVConstOp c)) # []" |
  expand_BoolOperand_ValuesOperand_VBExpOp:
  "apply_BoolOperand e (VBVExpOp Es) = apply_BoolOperand_list e Es" |
  "apply_BoolOperand_list e [] = []" |
  "apply_BoolOperand_list e (E # Es) = 
    (apply_BoolOperand_VB e E) # (apply_BoolOperand_list e Es)" |
  "apply_BoolOperand_VB e1 (VB e2 v2) = VB (VBBAndOp e1 e2) v2"


primrec 
  expand_ValuesOperand :: 
    "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand" and
  expand_ValuesOperand_list :: 
    "('vb, 'FMode, 'vv) ValuedBool list \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" and
  expand_ValuesOperand_VB :: 
    "('vb, 'FMode, 'vv) ValuedBool \<Rightarrow> ('vb, 'FMode, 'vv) ValuedBool list" 
where
  "expand_ValuesOperand (VBVConstOp c) = VBVConstOp c" |
  expand_ValuesOperand_VBVExpOp:
  "expand_ValuesOperand (VBVExpOp E) = VBVExpOp (expand_ValuesOperand_list E)" |
  "expand_ValuesOperand_list [] = []" |
  "expand_ValuesOperand_list (e # E) = 
    (expand_ValuesOperand_VB e) @ (expand_ValuesOperand_list E)" |
  "expand_ValuesOperand_VB (VB e v) = (
    case v of
      (VBVExpOp E2) \<Rightarrow> (apply_BoolOperand e (expand_ValuesOperand v)) |
      _ \<Rightarrow> [VB e (expand_ValuesOperand v)]
  )"

value "expand_ValuesOperand (
  VBVExpOp [VB (VBBVarOp v1) (
      VBVExpOp [
        VB (VBBVarOp v2) (VBVExpOp [
          VB (VBBVarOp v3) (VBVVarOp v4)
        ])
      ]
    )]
  )"

lemma "expand_ValuesOperand (
  VBVExpOp [VB (VBBVarOp v1) (
      VBVExpOp [
        VB (VBBVarOp v2) (VBVExpOp [
          VB (VBBVarOp v3) (VBVConstOp v4)
        ])
      ]
    )]
  ) = 
  (VBVExpOp [
    VB 
      (VBBAndOp (VBBVarOp v1) (VBBAndOp (VBBVarOp v2) (VBBVarOp v3)))
      (VBVConstOp v4)
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
  "normalise_ValuesOperand (VBVConstOp c) = (VBVConstOp c)" |
  "normalise_ValuesOperand (VBVExpOp Es) =  (
    let nEs = normalise_ValuesOperand_list Es
    in let so = SingleOperand nEs
    in if so = None then VBVExpOp nEs else the so
  )" |
  "normalise_ValuesOperand_list [] = []" |
  "normalise_ValuesOperand_list (E # Es) = (
    let nE = normalise_ValuesOperand_VB E
    in if nE = None then (normalise_ValuesOperand_list Es)
    else (the nE) # (normalise_ValuesOperand_list Es)
  )" |
  "normalise_ValuesOperand_VB (VB e v) = (
    let ne = (normalise_BoolOperand e)
    in
      if (ne = VBBConstOp False) then None
      else Some (VB ne (normalise_ValuesOperand v))
    )"

definition normalise_expand_ValuesOperand ::
  "('vb, 'FMode, 'vv) ValuesOperand \<Rightarrow> ('vb, 'FMode, 'vv) ValuesOperand"
where
  "normalise_expand_ValuesOperand v \<equiv> normalise_ValuesOperand (expand_ValuesOperand v)"

(*
lemma 
  "(normalise_ValuesOperand V) \<noteq> (normalise_ValuesOperand U) \<Longrightarrow>
  BoolOperand_eval ((ValuesOperandPredicate_BoolOperand (VBVExpOp [VB A U, VB (VBBNotOp A) V]) 
    (\<lambda> Es. ((normalise_ValuesOperand Es) = (normalise_ValuesOperand U))))) vb
  = (BoolOperand_eval A vb)"
apply (auto)
done
*)

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

value "ValuesOperand_value_eval (VBVExpOp [
  VB (VBBVarOp A) (VBVConstOp U), 
  VB (VBBVarOp B) (VBVConstOp U)] ) vb"

lemma [simp]: "(ValuedTautology (VBVExpOp Es) vb) \<Longrightarrow> 
  (length (ValuesOperand_values_eval (VBVExpOp Es) vb) > 0)"
apply (auto)
apply (auto simp add: ValuedTautology_def)
done

lemma "(ValuedTautology (VBVExpOp Es) vb) \<Longrightarrow> 
  (ValuesOperand_value_eval (VBVExpOp Es) vb = Some v)"
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ValuesOperand_value_eval_def)
apply (auto simp add: choose_values_def)
apply (auto simp add: ValuedTautology_values_list_def)
apply (auto simp add: ValuedTautology_values_nonemptylist_def)
apply (auto simp add: fold_def)
apply (auto simp add: ValuesOperand_values_eval_list_def)
sorry

lemma "(ValuesOperand_values_eval (VBVExpOp [VB (VBBNotOp A) V, VB A V]) vb) = 
  ValuesOperand_values_eval V vb"
apply (auto)
done

end
