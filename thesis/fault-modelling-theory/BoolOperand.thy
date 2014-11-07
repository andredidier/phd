(*<*)
theory BoolOperand

imports Main 

begin
(*>*)

(*<*)
datatype 'vb BoolOperand = 
  VBBConstOp bool ("BO")
  | VBBVarOp 'vb 
  | VBBNotOp "'vb BoolOperand" 
  | VBBAndOp "'vb BoolOperand" "'vb BoolOperand" 

notation (output) VBBConstOp  ("_\<^sub>B\<^sub>O" 50)
notation (latex) VBBConstOp ("_\<^raw:$_{\mathrm{BO}}$>" 51)
notation (output) VBBVarOp ("\<lbrakk>_\<rbrakk>\<^sub>B\<^sub>O" 60)
notation (latex) VBBVarOp ("\<lbrakk>_\<rbrakk>\<^raw:$_{\mathrm{BO}}$>" 61)
notation (output) VBBNotOp ("\<not>\<^sub>B\<^sub>O _" 80)
notation (latex) VBBNotOp ("\<^raw:$\overline{>_\<^raw:}$>" 81)
notation (latex output) VBBAndOp ("_\<cdot>_" 70)

abbreviation VBBOrOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBOrOp b1 b2 \<equiv> VBBNotOp (VBBAndOp (VBBNotOp b1) (VBBNotOp b2))"

notation (output) VBBOrOp ("_+\<^sub>B\<^sub>O_" 75)
notation (latex) VBBOrOp ("_+\<^raw:$_{\mathrm{BO}}$>_" 76)

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

primrec normalise_BoolOperandNot :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperandNot (VBBConstOp c) = VBBConstOp (\<not> c)" |
  "normalise_BoolOperandNot (VBBVarOp v) = VBBNotOp (VBBVarOp v)" |
  "normalise_BoolOperandNot (VBBNotOp b) = b" |
  "normalise_BoolOperandNot (VBBAndOp b1 b2) = VBBNotOp (VBBAndOp b1 b2)"

fun normalise_BoolOperandAnd :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperandAnd (VBBConstOp c1) b2 = (if c1 then b2 else (VBBConstOp c1))" |
  "normalise_BoolOperandAnd b1 (VBBConstOp c2) = (if c2 then b1 else (VBBConstOp c2))" |
  "normalise_BoolOperandAnd b1 b2 = (if b1 = b2 then b1 else VBBAndOp b1 b2)"

primrec normalise_BoolOperand :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperand (VBBConstOp c) = VBBConstOp c" |
  "normalise_BoolOperand (VBBVarOp v) = VBBVarOp v" |
  "normalise_BoolOperand (VBBNotOp b) = normalise_BoolOperandNot (normalise_BoolOperand b)" |
  "normalise_BoolOperand (VBBAndOp b1 b2) = 
    normalise_BoolOperandAnd (normalise_BoolOperand b1) (normalise_BoolOperand b2)"

primrec isNormal_BoolOperand :: "'vb BoolOperand \<Rightarrow> bool"
where
  "isNormal_BoolOperand (VBBConstOp _) = True" |
  "isNormal_BoolOperand (VBBVarOp _) = True" |
  "isNormal_BoolOperand (VBBNotOp b) = isNormal_BoolOperand b" |
  "isNormal_BoolOperand (VBBAndOp b1 b2) = ((isNormal_BoolOperand b1) \<and> (isNormal_BoolOperand b2))"

primrec "BoolOperand_eval" :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) vb = b" |
  "BoolOperand_eval (VBBVarOp a) vb = vb a" |
  "BoolOperand_eval (VBBNotOp op1) vb = (\<not> (BoolOperand_eval op1 vb))" |
  "BoolOperand_eval (VBBAndOp op1 op2) vb = 
    ((BoolOperand_eval op1 vb) \<and> (BoolOperand_eval op2 vb))"

(*<*) (* Lemas de sanidade *)
text {* True \<or> False = True *}

lemma "normalise_BoolOperand (VBBOrOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp True"
apply (auto)
done

text {* False \<and> True = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp False) (VBBConstOp True)) = VBBConstOp False"
apply (auto)
done

text {* False \<or> True = False *}

lemma "normalise_BoolOperand (VBBOrOp (VBBConstOp False) (VBBConstOp True)) = VBBConstOp True"
apply (auto)
done

text {* True \<and> False = True *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (auto)
done

text {* \<not> False \<or> False = True *}

lemma "normalise_BoolOperand (VBBOrOp (VBBNotOp (VBBConstOp False)) (VBBConstOp False)) = VBBConstOp True"
apply (auto)
done

text {* \<not> True \<and> True = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBNotOp (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp False"
apply (auto)
done

text {* \<not> True \<or> True = False *}

lemma "normalise_BoolOperand (VBBOrOp (VBBNotOp (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp True"
apply (auto)
done

text {* True \<and> False = True *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (auto)
done

(*
lemma "(BOp = (normalise_BoolOperand BOp)) \<Longrightarrow> 
  case BOp of VBBConstOp c \<Rightarrow> True | _ \<Rightarrow> no_VBBConstOp BOp"
apply (case_tac "BOp")
apply (auto simp add: no_VBBConstOp_def)
apply (auto simp add: normalise_BoolOperand_def)
done
*)
(* Fim dos lemas de sanidade. *) (*>*)

(*
theorem normalise_implies_eval : "(A \<noteq> B) \<Longrightarrow> 
  (normalise_BoolOperand A = normalise_BoolOperand B) \<Longrightarrow> 
  (BoolOperand_eval A vb = BoolOperand_eval B vb)"
apply (auto)
apply (auto simp add: BoolOperand_eval_def)
apply (auto simp add: normalise_BoolOperand_def)
done
*)

lemma eval_norm_l1_l1 [simp]: "
  BoolOperand_eval
    (normalise_BoolOperandNot (normalise_BoolOperandNot (normalise_BoolOperand BOp))) vb = 
  BoolOperand_eval BOp vb"
apply (case_tac BOp)
apply (auto)
sorry


lemma eval_norm_l1_l2 [simp]: "
  (BoolOperand_eval
    (normalise_BoolOperandNot (
      normalise_BoolOperandAnd (normalise_BoolOperand BOp1) (normalise_BoolOperand BOp2)
    )) vb) = 
  (\<not> (BoolOperand_eval BOp1 vb) \<or> (\<not> BoolOperand_eval BOp2 vb))"
apply (auto)
sorry


lemma eval_norm_l1 [simp]: "
  BoolOperand_eval (normalise_BoolOperandNot (normalise_BoolOperand BOp)) vb = 
  (\<not> (BoolOperand_eval BOp vb))"
apply (case_tac BOp)
apply (auto)
done

lemma eval_norm_l2 [simp]: "BoolOperand_eval (normalise_BoolOperandAnd 
  (normalise_BoolOperand BOp1) (normalise_BoolOperand BOp2)) vb = 
  ((BoolOperand_eval BOp1 vb) \<and> (BoolOperand_eval BOp2 vb))"
apply (auto)
sorry

theorem eval_norm: "BoolOperand_eval BOp vb = BoolOperand_eval (normalise_BoolOperand BOp) vb"
apply (case_tac BOp)
apply (auto)
done

end
