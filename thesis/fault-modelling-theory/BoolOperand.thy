theory BoolOperand

imports Main FaultModellingTypes

begin
(*
primrec 
  expand_BoolOperand_ValuesOperand :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuesOperand \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_list :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuedBool list \<Rightarrow> ('vb, 'vv) ValuedBool list" and
  expand_BoolOperand_ValuesOperand_VB :: "'vb BoolOperand \<Rightarrow> ('vb, 'vv) ValuedBool \<Rightarrow> ('vb, 'vv) ValuedBool"
where
  "expand_BoolOperand_ValuesOperand e (VBVConstOp c) = (VB e (VBVConstOp c)) # []" |
  "expand_BoolOperand_ValuesOperand e (VBVVarOp v) = (VB e (VBVVarOp v)) # []" |
  expand_BoolOperand_ValuesOperand_VBExpOp:
  "expand_BoolOperand_ValuesOperand e (VBVExpOp Es) = expand_BoolOperand_ValuesOperand_list e Es" |
  "expand_BoolOperand_ValuesOperand_list e [] = []" |
  "expand_BoolOperand_ValuesOperand_list e (E # Es) = 
    (expand_BoolOperand_ValuesOperand_VB e E) # (expand_BoolOperand_ValuesOperand_list e Es)" |
  "expand_BoolOperand_ValuesOperand_VB e1 (VB e2 v2) = VB (VBBExpBinOp (op \<and>) e1 e2) v2"
*)

primrec normalise_BoolOperand :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperand (VBBConstOp c) = VBBConstOp c" |
  "normalise_BoolOperand (VBBVarOp v) = VBBVarOp v" |
  "normalise_BoolOperand (VBBExpUnOp unop b) = (
    let nb = normalise_BoolOperand b
    in
    case nb of
      VBBConstOp c \<Rightarrow> VBBConstOp (unop c) |
      VBBVarOp v \<Rightarrow> VBBExpUnOp unop nb |
      VBBExpUnOp unop2 b2 \<Rightarrow> (
        if (\<forall> b. unop (unop2 b) = b)
        then b2
        else VBBExpUnOp unop nb
      )|
      _ \<Rightarrow> VBBExpUnOp unop nb
  )" |
  "normalise_BoolOperand (VBBExpBinOp binop b1 b2) = (
    let nb1 = normalise_BoolOperand b1
    in let nb2 = normalise_BoolOperand b2
    in
      case nb1 of
        VBBConstOp c1 \<Rightarrow> (
          if (\<forall> b. (binop c1 b) = b)
          then nb2
          else nb1
        ) |
        VBBVarOp v1 \<Rightarrow> (
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then nb2
              else nb1 |
            _ \<Rightarrow> VBBExpBinOp binop nb1 nb2
        ) |
        VBBExpUnOp unop1 nb1b \<Rightarrow> (
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then nb2
              else nb1 |
            _ \<Rightarrow> VBBExpBinOp binop nb1 nb2
        ) |
        VBBExpBinOp binop1 nb1b1 nb1b2 \<Rightarrow> (
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then nb2
              else nb1 |
            _ \<Rightarrow> VBBExpBinOp binop nb1 nb2
        )
  )"

primrec "BoolOperand_eval" :: "'vb BoolOperand \<Rightarrow> ('vb \<Rightarrow> bool) \<Rightarrow> bool" where
  "BoolOperand_eval (VBBConstOp b) vb = b" |
  "BoolOperand_eval (VBBVarOp a) vb = vb a" |
  "BoolOperand_eval (VBBExpUnOp exp_op op1) vb = exp_op (BoolOperand_eval op1 vb)" |
  "BoolOperand_eval (VBBExpBinOp exp_op op1 op2) vb = 
    exp_op (BoolOperand_eval op1 vb) (BoolOperand_eval op2 vb)"

text {* True \<or> False = True *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<or>) (VBBConstOp True) (VBBConstOp False)) = VBBConstOp True"
apply (auto)
done

text {* False \<and> True = False *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<and>) (VBBConstOp False) (VBBConstOp True)) = VBBConstOp False"
apply (auto)
done

text {* False \<or> True = False *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<or>) (VBBConstOp False) (VBBConstOp True)) = VBBConstOp True"
apply (auto)
done

text {* True \<and> False = True *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<and>) (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (auto)
done

text {* \<not> False \<or> False = True *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<or>) (VBBExpUnOp Not (VBBConstOp False)) (VBBConstOp False)) = VBBConstOp True"
apply (auto)
done

text {* \<not> True \<and> True = False *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<and>) (VBBExpUnOp Not (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp False"
apply (auto)
done

text {* \<not> True \<or> True = False *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<or>) (VBBExpUnOp Not (VBBConstOp True)) (VBBConstOp True)) = VBBConstOp True"
apply (auto)
done

text {* True \<and> False = True *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<and>) (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (auto)
done

primrec no_VBBConstOp :: "'vb BoolOperand \<Rightarrow> bool"
where
  "no_VBBConstOp (VBBConstOp c) = False" |
  "no_VBBConstOp (VBBVarOp v) = True" |
  "no_VBBConstOp (VBBExpUnOp unop b) = no_VBBConstOp b" |
  "no_VBBConstOp (VBBExpBinOp binop b1 b2) = (no_VBBConstOp b1 \<and> no_VBBConstOp b2)"

lemma "case (normalise_BoolOperand BO) of VBBConstOp c \<Rightarrow> True | _ \<Rightarrow> no_VBBConstOp BO"
apply (case_tac BO)
apply (auto simp add: normalise_BoolOperand_def)
sorry

theorem "(normalise_BoolOperand A = normalise_BoolOperand B) \<Longrightarrow> (BoolOperand_eval A vb = BoolOperand_eval B vb)"
apply (auto)
apply (auto simp add: BoolOperand_eval_def)
apply (auto simp add: normalise_BoolOperand_def)
sorry


end
