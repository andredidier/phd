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
      VBBVarOp v \<Rightarrow> VBBExpUnOp unop (VBBVarOp v) |
      VBBExpUnOp unop2 b2 \<Rightarrow> VBBExpUnOp (\<lambda> a. unop (unop2 a)) b2 |
      VBBExpBinOp binop b1 b2 \<Rightarrow> VBBExpBinOp (\<lambda> a b. unop (binop a b)) b1 b2
  )" |
  "normalise_BoolOperand (VBBExpBinOp binop b1 b2) = (
    let nb1 = normalise_BoolOperand b1
    in let nb2 = normalise_BoolOperand b2
    in
      case nb1 of
        VBBConstOp c1 \<Rightarrow> (
          if (\<forall> b. (binop c1 b) = c1) then VBBConstOp c1
          else
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then VBBConstOp c2
              else VBBConstOp (binop c1 c2) |
            VBBExpUnOp unop2 nb2b \<Rightarrow> VBBExpUnOp (\<lambda> a. binop c1 (unop2 a)) nb2b |
            VBBExpBinOp binop2 nb2b1 nb2b2 \<Rightarrow> VBBExpBinOp (\<lambda> a b. binop c1 (binop2 a b)) nb2b1 nb2b2 |
            _ \<Rightarrow> VBBExpBinOp binop nb1 nb2
        ) |
        VBBVarOp v1 \<Rightarrow> (
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then VBBConstOp c2
              else VBBExpUnOp (\<lambda> a. binop a c2) (VBBVarOp v1) |
            _ \<Rightarrow> VBBExpBinOp binop nb1 nb2
        ) |
        VBBExpUnOp unop1 nb1b \<Rightarrow> (
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then VBBConstOp c2
              else VBBExpUnOp (\<lambda> a. binop (unop1 a) c2) nb1b |
            VBBExpUnOp unop2 nb2b \<Rightarrow> VBBExpBinOp (\<lambda> a b. binop (unop1 a) (unop2 b)) nb1b nb2b |
            _ \<Rightarrow> VBBExpBinOp (\<lambda> a b. binop (unop1 a) b) nb1b nb2
        ) |
        VBBExpBinOp binop1 nb1b1 nb1b2 \<Rightarrow> (
          case nb2 of
            VBBConstOp c2 \<Rightarrow> 
              if (\<forall> b. (binop b c2) = c2)
              then VBBConstOp c2
              else VBBExpBinOp (\<lambda> a b. binop (binop1 a b) c2) nb1b1 nb1b2 |
            VBBExpUnOp unop2 nb2b \<Rightarrow> VBBExpBinOp (\<lambda> a b. binop a (unop2 b) ) (VBBExpBinOp binop1 nb1b1 nb1b2) nb2b |
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
apply (auto simp add: Let_def)
done

text {* True \<and> False = True *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<and>) (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (auto)
apply (auto simp add: Let_def)
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
apply (auto simp add: Let_def)
done

text {* True \<and> False = True *}

lemma "normalise_BoolOperand (VBBExpBinOp (op \<and>) (VBBConstOp True) (VBBConstOp False)) = VBBConstOp False"
apply (auto)
apply (auto simp add: Let_def)
done

lemma "normalise_BoolOperand (VBBExpBinOp (\<lambda> a b. \<not> a \<or> \<not> b) (VBBConstOp False) (VBBConstOp True)) = VBBConstOp True"
apply (auto)
done

lemma "(normalise_BoolOperand A = normalise_BoolOperand B) \<Longrightarrow> (BoolOperand_eval A vb = BoolOperand_eval B vb)"
apply (auto)
apply (auto simp add: BoolOperand_eval_def)
apply (auto simp add: normalise_BoolOperand_def)
done

end
