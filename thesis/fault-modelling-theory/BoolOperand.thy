theory BoolOperand

imports Main 

begin

datatype 'variavel BoolOperand = 
  VBBConstOp bool ("BO")
  | VBBVarOp 'variavel 
  | VBBNotOp "'variavel BoolOperand" 
  | VBBAndOp "'variavel BoolOperand" "'variavel BoolOperand" 

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

primrec normalise_BoolOperand :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperand (VBBConstOp c) = VBBConstOp c" |
  "normalise_BoolOperand (VBBVarOp v) = VBBVarOp v" |
  "normalise_BoolOperand (VBBNotOp b) = (
    let nb = normalise_BoolOperand b
    in
    case nb of
      VBBConstOp c \<Rightarrow> VBBConstOp (\<not> c) |
      VBBNotOp b2 \<Rightarrow> b2 |
      _ \<Rightarrow> VBBNotOp nb
  )" |
  "normalise_BoolOperand (VBBAndOp b1 b2) = (
    let nb1 = normalise_BoolOperand b1
    in let nb2 = normalise_BoolOperand b2
    in
      if nb1 = nb2 then nb1
      else if VBBNotOp nb1 = nb2 then VBBConstOp False
      else if nb1 = VBBNotOp nb2 then VBBConstOp False
      else
        case nb1 of
          VBBConstOp c1 \<Rightarrow> if c1 then nb2 else nb1 |
          _ \<Rightarrow> (
            case nb2 of
              VBBConstOp c2 \<Rightarrow> if c2 then nb1 else nb2 |
              _ \<Rightarrow> VBBAndOp nb1 nb2
          )
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

primrec no_VBBConstOp :: "'vb BoolOperand \<Rightarrow> bool"
where
  "no_VBBConstOp (VBBConstOp c) = False" |
  "no_VBBConstOp (VBBVarOp v) = True" |
  "no_VBBConstOp (VBBNotOp b) = no_VBBConstOp b" |
  "no_VBBConstOp (VBBAndOp b1 b2) = (no_VBBConstOp b1 \<and> no_VBBConstOp b2)"

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

end
