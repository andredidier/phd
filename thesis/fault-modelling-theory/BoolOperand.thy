(*<*)
theory BoolOperand

imports Main FaultModellingTypes

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
notation (output) VBBAndOp ("_\<cdot>_" 75)
notation (latex) VBBAndOp ("_\<cdot>_" 75)

type_synonym 'vb VBBVarOpVal = "'vb \<Rightarrow> bool"

abbreviation VBBOrOp :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where "VBBOrOp b1 b2 \<equiv> VBBNotOp (VBBAndOp (VBBNotOp b1) (VBBNotOp b2))"

notation (output) VBBOrOp ("_\<or>\<^sub>B\<^sub>O_" 70)
notation (latex) VBBOrOp ("_+\<^raw:$_{\mathrm{BO}}$>_" 70)

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
  "normalise_BoolOperandAnd (VBBAndOp b1 b2) (VBBAndOp b3 b4) = (
    if 
      b1 = VBBNotOp b3 \<or> VBBNotOp b1 = b3 \<or> 
      b1 = VBBNotOp b4 \<or> VBBNotOp b1 = b4 \<or> 
      b2 = VBBNotOp b3 \<or> VBBNotOp b2 = b3 \<or> 
      b2 = VBBNotOp b4 \<or> VBBNotOp b2 = b4
    then (VBBConstOp False)
    else VBBAndOp (VBBAndOp b1 b2) b3
  )" |
  "normalise_BoolOperandAnd (VBBAndOp b1 b2) b3 = (
    if 
      b1 = VBBNotOp b3 \<or> VBBNotOp b1 = b3 \<or> 
      b2 = VBBNotOp b3 \<or> VBBNotOp b2 = b3
    then (VBBConstOp False)
    else if b1 = b3 \<or> b2 = b3 then VBBAndOp b1 b2
    else VBBAndOp (VBBAndOp b1 b2) b3
  )" |
  "normalise_BoolOperandAnd b1 (VBBAndOp b2 b3) = (
    if 
      b1 = VBBNotOp b2 \<or> VBBNotOp b1 = b2 \<or> 
      b2 = VBBNotOp b3 \<or> VBBNotOp b2 = b3
    then (VBBConstOp False)
    else if b1 = b2 \<or> b1 = b3 then VBBAndOp b2 b3
    else VBBAndOp (VBBAndOp b1 b2) b3
  )" |
  "normalise_BoolOperandAnd b1 b2 = (if b1 = b2 then b1 else VBBAndOp b1 b2)"

primrec BoolOperand_Ands :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand list"
where
  "BoolOperand_Ands (VBBConstOp c) = [ (VBBConstOp c) ]" |
  "BoolOperand_Ands (VBBVarOp v) = [ (VBBVarOp v) ]" |
  "BoolOperand_Ands (VBBNotOp b) = 
    apply_f_list 
      (BoolOperand_Ands b) 
      (\<lambda> nb. case nb of VBBNotOp nnb \<Rightarrow> nnb | _ \<Rightarrow> VBBNotOp nb)" |
  "BoolOperand_Ands (VBBAndOp b1 b2) = (BoolOperand_Ands b1) @ (BoolOperand_Ands b2)"


(* Ajeitar aqui: se for (not VBBConstOp False)? *)
primrec RemoveConsts_BoolOperands :: "'vb BoolOperand list \<Rightarrow> 'vb BoolOperand list"
where
  "RemoveConsts_BoolOperands [] = []" |
  "RemoveConsts_BoolOperands (b # bs) = 
    (
      case b of
        VBBConstOp c \<Rightarrow> if c then (RemoveConsts_BoolOperands bs) else [VBBConstOp False] |
        _ \<Rightarrow> (b # (RemoveConsts_BoolOperands bs))
    )"


primrec RemoveSame_BoolOperands :: "'vb BoolOperand list \<Rightarrow> 'vb BoolOperand list"
where
  "RemoveSame_BoolOperands [] = []" |
  "RemoveSame_BoolOperands (b # bs) = 
    (
      b # (filter (\<lambda> b2. b \<noteq> b2) (RemoveSame_BoolOperands bs))
    )"

primrec RemoveSimmetric_BoolOperands :: 
  "'vb BoolOperand set \<Rightarrow> 'vb BoolOperand list \<Rightarrow> 'vb BoolOperand list"
where
  "RemoveSimmetric_BoolOperands R [] = []" |
  "RemoveSimmetric_BoolOperands R (b # bs) = 
    (
      if (b \<notin> R) \<and> (List.find (\<lambda> x. b = VBBNotOp x \<or> VBBNotOp b = x) bs) = None 
      then (b # (RemoveSimmetric_BoolOperands R bs))
      else (RemoveSimmetric_BoolOperands (R \<union> {b}) bs)
    )"

primrec BoolOperands_Ands_to_And :: "'vb BoolOperand list \<Rightarrow> 'vb BoolOperand"
where
  "BoolOperands_Ands_to_And [] = (VBBConstOp True)" |
  "BoolOperands_Ands_to_And (b # bs) = 
  (
    if bs = [] 
    then b 
    else (VBBAndOp b (BoolOperands_Ands_to_And bs))
  )"

definition normalise_BoolOperand :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperand b = 
    (
    BoolOperands_Ands_to_And \<circ> 
    (RemoveSimmetric_BoolOperands {}) \<circ> 
    RemoveSame_BoolOperands \<circ>
    RemoveConsts_BoolOperands \<circ> 
    BoolOperand_Ands
    ) b"

primrec isNormal_not_VBBConstOp :: "'vb BoolOperand \<Rightarrow> bool"
where
  "isNormal_not_VBBConstOp (VBBConstOp _) = False" |
  "isNormal_not_VBBConstOp (VBBVarOp _) = True" |
  "isNormal_not_VBBConstOp (VBBNotOp BOp) = (
    case BOp of
      (VBBNotOp _) \<Rightarrow> False |
      _ \<Rightarrow> isNormal_not_VBBConstOp BOp
  )" |
  "isNormal_not_VBBConstOp (VBBAndOp BOp1 BOp2) = 
    ((BOp1 \<noteq> BOp2) \<and> (isNormal_not_VBBConstOp BOp1) \<and> (isNormal_not_VBBConstOp BOp2))"

definition isNormal_BoolOperand :: "'vb BoolOperand \<Rightarrow> bool"
where
  "isNormal_BoolOperand BOp \<equiv> 
  (
    case BOp of
      VBBConstOp _ \<Rightarrow> True |
      _ \<Rightarrow> isNormal_not_VBBConstOp BOp
  )" 

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
done

text {* False \<and> True = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp False) (VBBConstOp True)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
done

text {* False \<or> True = False *}

lemma "normalise_BoolOperand (VBBOrOp (VBBConstOp False) (VBBConstOp True)) = VBBConstOp True"
apply (simp add: normalise_BoolOperand_def)
done

text {* True \<and> False = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
done

text {* \<not> False \<or> False = True *}

lemma "normalise_BoolOperand (VBBOrOp (VBBNotOp (VBBConstOp False)) (VBBConstOp False)) = VBBConstOp True"
apply (simp add: normalise_BoolOperand_def)
done

text {* \<not> True \<and> True = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBNotOp (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
done

text {* \<not> True \<or> True = False *}

lemma "normalise_BoolOperand (VBBOrOp (VBBNotOp (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp True"
apply (simp add: normalise_BoolOperand_def)
done

text {* True \<and> False = False *}

lemma "normalise_BoolOperand (VBBAndOp (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (simp add: normalise_BoolOperand_def)
done

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> normalise_BoolOperand 
  (
    VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))
  ) = 
  (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBVarOp B))"
apply (simp add: normalise_BoolOperand_def)
done

lemma "normalise_BoolOperand 
  (
    VBBAndOp 
      (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))) 
      (VBBAndOp (VBBVarOp A) (VBBNotOp (VBBVarOp B)))
  ) = 
  (
    VBBConstOp True
  )"
apply (simp add: normalise_BoolOperand_def)
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
apply (simp)
apply (simp)
apply (simp add: eval_norm_l1)
apply (simp add: eval_norm_l2)
done

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
