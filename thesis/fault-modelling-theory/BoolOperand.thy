(*<*)
theory BoolOperand

imports Main FaultModellingTypes

begin
(*>*)

(*<*)
datatype 'vb BoolOperand = 
  VBBConstOp bool
  | VBBVarOp 'vb 
  | VBBNotOp "'vb BoolOperand" 
  | VBBAndOp "'vb BoolOperand" "'vb BoolOperand" 

notation (output) VBBConstOp  ("_\<^sub>B\<^sub>O" 50)
notation (latex) VBBConstOp ("_\<^raw:$_{\mathrm{BO}}$>" 51)
notation (output) VBBVarOp ("\<lbrakk>_\<rbrakk>\<^sub>B\<^sub>O" 60)
notation (latex) VBBVarOp ("\<lbrakk>_\<rbrakk>\<^raw:$_{\mathrm{BO}}$>" 61)
notation (output) VBBNotOp ("'(\<not>\<^sub>B\<^sub>O _')" 80)
notation (latex) VBBNotOp ("\<^raw:$\overline{>_\<^raw:}$>" 81)
notation (output) VBBAndOp ("'(_\<and>\<^sub>B\<^sub>O_')" 75)
notation (latex) VBBAndOp ("_\<and>\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VBBOrOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBOrOp b1 b2 \<equiv> VBBNotOp (VBBAndOp (VBBNotOp b1) (VBBNotOp b2))"

notation (output) VBBOrOp ("_\<or>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBOrOp ("_+\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VBBNandOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBNandOp b1 b2 \<equiv> (VBBNotOp (VBBAndOp b1 b2))"

notation (output) VBBNandOp ("_\<^sup>\<not>\<and>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBNandOp ("_\<^sup>\<not>\<and>\<^raw:$_{\mathrm{BO}}$>_" 70)

abbreviation VBBXorOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBXorOp b1 b2 \<equiv> (VBBAndOp (VBBNandOp b1 b2) (VBBOrOp b1 b2))"

notation (output) VBBXorOp ("_\<otimes>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBXorOp ("_\<otimes>\<^raw:$_{\mathrm{BO}}$>_" 70)

(*>*)

text {* Before introducing our fault modelling formalisation, we define new datatypes and slight 
modification in existing ones.
%
To be able to later compare Boolean variables to fault trees' basic events variables, we introduce 
Boolean expressions with variables.
%
Accordingly to the work reported in %~\cite{}
, all Boolean operators can be derived from @{term "Not A"} @{const "Not"} @{text "\<not>" }
and @{term "(op \<and>) A B"} @{text "\<and>" }operators.
%
For example, to express an @{term "(op \<or>) A B"}, we use the expression 
@{term "Not ((op \<and>) (Not A) (Not B))"}.
%
Following this idea, we introduce our datatype @{typ "'VarNames BoolOperand"}
  *}

datatype 'vb ifex = 
  CIF bool ("_\<^sub>i\<^sub>f") 
  | VIF 'vb ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>f") 
  | IF "'vb ifex" "'vb ifex" "'vb ifex" ("'(_')\<^sub>C '& '(_')\<^sub>T '(_')\<^sub>F")

primrec bool2if :: "'vb BoolOperand \<Rightarrow> 'vb ifex"
where
  "bool2if (VBBConstOp c) = CIF c" |
  "bool2if (VBBVarOp v) = VIF v" |
  "bool2if (VBBNotOp b) = IF (bool2if b) (CIF False) (CIF True)" |
  "bool2if (VBBAndOp b1 b2) = IF (bool2if b1) (bool2if b2) (CIF False)"

primrec normif :: "'vb ifex \<Rightarrow> 'vb ifex \<Rightarrow> 'vb ifex \<Rightarrow> 'vb ifex"
where
  "normif (CIF c) t e = IF (CIF c) t e" |
  "normif (VIF v) t e = IF (VIF v) t e" |
  "normif (IF b t e) u f = normif b (normif t u f) (normif e u f)"

primrec normifex :: "'vb ifex \<Rightarrow> 'vb ifex"
where
  "normifex (CIF c) = CIF c" |
  "normifex (VIF v) = VIF v" |
  "normifex (IF b t e) = normif b (normifex t) (normifex e)"

primrec simpif_env :: "
  'vb ifex \<Rightarrow> ('vb \<rightharpoonup> bool) \<Rightarrow>
  'vb ifex \<Rightarrow> 'vb ifex \<Rightarrow> 
  'vb ifex"
where
  "simpif_env (CIF c) env t e = (if c then t else e)" |
  "simpif_env (VIF v) env t e = 
  (
    case (env v) of
      None \<Rightarrow> (IF (VIF v) t e) |
      Some c \<Rightarrow> (if c then t else e)
  )" |
  "simpif_env (IF b t e) env u f = (IF (IF b t e) u f)"

primrec buildifex_env :: "'vb ifex \<Rightarrow> ('vb \<rightharpoonup> bool) \<Rightarrow> ('vb \<rightharpoonup> bool)"
where
  "buildifex_env (CIF c) env = env" |
  "buildifex_env (VIF v) env = (env (v \<mapsto> True))" |
  "buildifex_env (IF b t e) env = env"

primrec simpifex_env :: "'vb ifex \<Rightarrow> ('vb \<rightharpoonup> bool) \<Rightarrow> 'vb ifex"
where
  "simpifex_env (CIF c) env = CIF c" |
  "simpifex_env (VIF v) env = 
  (
    case (env v) of
      None \<Rightarrow> VIF v |
      Some c \<Rightarrow> CIF c
  )" |
  "simpifex_env (IF b t e) env = 
  (
    let
      nenv = buildifex_env b env;
      b_simp_env = simpifex_env b;
      t_simp = simpifex_env t nenv;
      e_simp = simpifex_env e (apply_map nenv Not);
      r = simpif_env (b_simp_env env) env t_simp e_simp
    in 
      case t_simp of
        CIF tc \<Rightarrow> 
        (
          case e_simp of
            CIF ec \<Rightarrow> 
              if tc \<and> \<not> ec 
                then (b_simp_env env) 
                else if (\<not> tc \<and> ec)
                then (b_simp_env (apply_map env Not))
                else if tc = ec then (CIF tc)
                else r |
            _ \<Rightarrow> r
        ) |
        VIF tv \<Rightarrow>
        (
          case e_simp of
            VIF ev \<Rightarrow> if tv = ev then VIF tv else r |
            _ \<Rightarrow> r
        ) |
        _ \<Rightarrow> r
  )"

definition simpifex :: "'vb ifex \<Rightarrow> 'vb ifex"
where
  "simpifex b \<equiv> simpifex_env (normifex b) Map.empty"

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow>
  simpifex (IF (VIF A) (IF (VIF B) (CIF True) (CIF False)) (IF (VIF A) (CIF True) (CIF False))) 
  = IF (VIF A) (VIF B) (CIF False)"
apply (auto simp add: simpifex_def apply_map_def)
done

definition BoolOperand_simplify :: 
  "'vb BoolOperand \<Rightarrow> 'vb ifex"
where
  "BoolOperand_simplify b \<equiv> simpifex (bool2if b)"

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow>
  BoolOperand_simplify (VBBAndOp (VBBVarOp A) (VBBAndOp (VBBVarOp B) (VBBVarOp A))) = 
  IF (VIF A) (VIF B) (CIF False)"
apply (auto simp add: BoolOperand_simplify_def simpifex_def)
done

primrec BoolOperand_eval :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool"
where
  "BoolOperand_eval (VBBConstOp c) _ = c" |
  "BoolOperand_eval (VBBVarOp v) env = (env v)" |
  "BoolOperand_eval (VBBNotOp b) env = (\<not> BoolOperand_eval b env)" |
  "BoolOperand_eval (VBBAndOp b1 b2) env = 
    ((BoolOperand_eval b1 env) \<and> (BoolOperand_eval b2 env))"

definition BoolOperand_Tautology :: "'vb BoolOperand \<Rightarrow> bool"
where "BoolOperand_Tautology b \<equiv> (BoolOperand_simplify b = CIF True)"

value "simpifex (normifex (bool2if (VBBOrOp (VBBConstOp False) (VBBConstOp True))))"

lemma " 
  (BoolOperand_simplify
  (
        VBBOrOp (VBBConstOp False) (VBBConstOp True)
  )) = (CIF True)"
quickcheck
(*apply (auto simp add: BoolOperand_Tautology_def)*)
apply (auto simp add: BoolOperand_simplify_def)
apply (auto simp add: simpifex_def)
done

lemma " 
  (BoolOperand_simplify
  (
        VBBOrOp (VBBNotOp (VBBVarOp A)) (VBBVarOp A)
  )) = (CIF True)"
(*apply (auto simp add: BoolOperand_Tautology_def)*)
apply (auto simp add: BoolOperand_simplify_def)
apply (auto simp add: simpifex_def)
apply (auto simp add: apply_map_def)
done

lemma " 
  (BoolOperand_simplify
  (
        VBBOrOp (VBBVarOp A) (VBBNotOp (VBBVarOp A))
  )) = (CIF True)"
quickcheck
(*apply (auto simp add: BoolOperand_Tautology_def)*)
apply (auto simp add: BoolOperand_simplify_def)
apply (auto simp add: simpifex_def)
apply (auto simp add: apply_map_def)
done

lemma " 
  (BoolOperand_simplify
  (
      VBBAndOp 
        (VBBOrOp (VBBVarOp A) (VBBNotOp (VBBVarOp A)))
        (VBBOrOp (VBBNotOp (VBBVarOp A)) (VBBVarOp A))
  )) = (CIF True)"
quickcheck
(*apply (auto simp add: BoolOperand_Tautology_def)*)
apply (auto simp add: BoolOperand_simplify_def)
apply (auto simp add: simpifex_def)
apply (auto simp add: apply_map_def)
done

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> 
  (BoolOperand_simplify
  (
      VBBOrOp 
        (VBBOrOp (VBBVarOp A) (VBBVarOp B)) 
        (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBNotOp (VBBVarOp B)))
  )) = (CIF True)"
quickcheck
(*apply (auto simp add: BoolOperand_Tautology_def)*)
apply (auto simp add: BoolOperand_simplify_def)
apply (auto simp add: simpifex_def)
apply (auto simp add: apply_map_def)
done

end
