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

datatype_new 'vb ifex = 
  CIF bool 
  | VIF "'vb"
  | IF "'vb ifex" "'vb ifex" "'vb ifex"

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

primrec norm :: "'vb ifex \<Rightarrow> 'vb ifex"
where
  "norm (CIF c) = (CIF c)" |
  "norm (VIF v) = (VIF v)" |
  "norm (IF b t e) = normif b (norm t) (norm e)"

primrec simplifyif :: "'vb ifex \<Rightarrow> 'vb ifex \<Rightarrow> 'vb ifex \<Rightarrow> 'vb ifex"
where
  "simplifyif (CIF c) t e = (if c then t else e)" |
  "simplifyif (VIF v) t e = IF (VIF v) t e" |
  "simplifyif (IF b t e) u f = simplifyif b (simplifyif t u f) (simplifyif e u f)"

primrec simplifyifex :: "'vb ifex \<Rightarrow> 'vb ifex"
where
  "simplifyifex (CIF c) = (CIF c)" |
  "simplifyifex (VIF v) = (VIF v)" |
  "simplifyifex (IF b t e) = 
  (
    let 
      nt = simplifyifex t;
      ne = simplifyifex e;
      nif = simplifyif b nt ne
    in
      case nt of
        CIF ntc \<Rightarrow> 
        (
          case ne of
            CIF nec \<Rightarrow> 
            (
              if (ntc \<and> \<not> nec) then b else nif
            ) |
            _ \<Rightarrow> nif
        ) |
        _ \<Rightarrow> nif
  )"

value "simplifyifex (norm (bool2if (VBBAndOp (VBBVarOp A) (VBBOrOp (VBBVarOp B) (VBBVarOp A)))))"

value "simplifyifex (norm (bool2if (VBBAndOp (VBBNotOp (VBBVarOp A)) 
  (VBBOrOp (VBBVarOp B) (VBBVarOp A)))))"

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

definition normalise_BoolOperand :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperand b = b"

definition isNormal_BoolOperand :: "'vb BoolOperand \<Rightarrow> bool"
where
  "isNormal_BoolOperand BOp \<equiv> False" 

primrec "BoolOperand_eval" :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) vb = b" |
  "BoolOperand_eval (VBBVarOp a) vb = vb a" |
  "BoolOperand_eval (VBBNotOp op1) vb = (\<not> (BoolOperand_eval op1 vb))" |
  "BoolOperand_eval (VBBAndOp op1 op2) vb = 
    ((BoolOperand_eval op1 vb) \<and> (BoolOperand_eval op2 vb))"

(*<*) (* Lemas de sanidade *)
text {* True \<or> False = True *}

lemma "normalise_BoolOperand (VBBOrOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp True"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* False \<and> True = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp False) (VBBConstOp True)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* False \<or> True = False *}

lemma "normalise_BoolOperand (VBBOrOp (VBBConstOp False) (VBBConstOp True)) = VBBConstOp True"
apply (auto simp add: normalise_BoolOperand_def )
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* True \<and> False = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* \<not> False \<or> False = True *}

lemma "normalise_BoolOperand (VBBOrOp (VBBNotOp (VBBConstOp False)) (VBBConstOp False)) = VBBConstOp True"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* \<not> True \<and> True = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBNotOp (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* \<not> True \<or> True = False *}

lemma "normalise_BoolOperand (VBBOrOp (VBBNotOp (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp True"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

text {* True \<and> False = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

lemma "(normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBVarOp B))) = VBBVarOp B"
apply (auto simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

lemma "\<lbrakk> A \<noteq> B;b = VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBVarOp B) \<rbrakk> \<Longrightarrow>
  normalise_BoolOperand b = b"
apply (auto simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
apply (auto simp add: RemoveConsts_BoolOperands_def)
apply (auto simp add: Let_def)
done

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> normalise_BoolOperand 
  (
    VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))
  ) = 
  (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBVarOp B))"
apply (simp add: normalise_BoolOperand_def)
apply (simp add: RemoveSame_BoolOperands_def)
apply (simp add: RemoveSimmetric_BoolOperands_def)
apply (simp add: Let_def)
done


lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> normalise_BoolOperand 
  (
    VBBAndOp 
      (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))) 
      (VBBAndOp (VBBVarOp A) (VBBNotOp (VBBVarOp B)))
  ) = 
  (
    VBBConstOp True
  )"
apply (auto simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def)
apply (auto simp add: Let_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def)
done

(* Fim dos lemas de sanidade. *) (*>*)

theorem normalise_isNormal: "(BOp = normalise_BoolOperand BOp) \<longleftrightarrow> (isNormal_BoolOperand BOp)"
sorry

lemma eval_norm_l1: "
  BoolOperand_eval (normalise_BoolOperandNot (normalise_BoolOperand BOp)) vb = 
  (\<not> (BoolOperand_eval BOp vb))"
sorry

lemma eval_norm_l2: "BoolOperand_eval (normalise_BoolOperandAnd 
  (normalise_BoolOperand BOp1) (normalise_BoolOperand BOp2)) vb = 
  ((BoolOperand_eval BOp1 vb) \<and> (BoolOperand_eval BOp2 vb))"
apply (auto)
sorry

theorem eval_norm: "BoolOperand_eval BOp vb = BoolOperand_eval (normalise_BoolOperand BOp) vb"
apply (case_tac BOp)
apply (auto simp add: normalise_BoolOperand_def)
apply (auto simp add: RemoveSame_BoolOperands_def RemoveSame_BoolOperandsPair_def)
apply (auto simp add: RemoveSimmetric_BoolOperands_def RemoveSimmetric_BoolOperandsPair_def)
apply (auto simp add: RemoveConsts_BoolOperands_def)
apply (auto simp add: BoolOperand_eval_def)
(*apply (simp add: eval_norm_l1)
apply (simp add: eval_norm_l2)*)
sorry

definition BoolOperand_Tautology :: "'vb BoolOperand \<Rightarrow> bool"
where
  "BoolOperand_Tautology b \<equiv> (RemoveSimmetric_BoolOperands (BoolOperand_Ands b) = {})"

value "normalise_BoolOperand (
      VBBAndOp 
        (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))) 
        (VBBAndOp (VBBVarOp A) (VBBNotOp (VBBVarOp B)))
  )"
value "normalise_BoolOperand (
        (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))) 
  )"

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> 
  BoolOperand_Tautology
  (
      VBBAndOp 
        (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))) 
        (VBBAndOp (VBBVarOp A) (VBBNotOp (VBBVarOp B)))
  ) "
apply (auto simp add: BoolOperand_Tautology_def RemoveSimmetric_BoolOperands_def)
done

end
