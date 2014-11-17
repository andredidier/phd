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
notation (output) VBBAndOp ("_\<and>\<^sub>B\<^sub>O_" 75)
notation (latex) VBBAndOp ("_.\<^raw:$_{\mathrm{BO}}$>_" 70)

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

primrec RemoveConsts_BoolOperands :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "RemoveConsts_BoolOperands (VBBConstOp c) = (VBBConstOp c)" |
  "RemoveConsts_BoolOperands (VBBVarOp v) = (VBBVarOp v)" |
  "RemoveConsts_BoolOperands (VBBNotOp b) = 
    (
      let nb = RemoveConsts_BoolOperands b
      in
        case nb of
          VBBConstOp nbc \<Rightarrow> VBBConstOp (\<not> nbc)|
          VBBNotOp nbb \<Rightarrow> nbb |
          _ \<Rightarrow> VBBNotOp nb
    )" |
  "RemoveConsts_BoolOperands (VBBAndOp b1 b2) = 
    (
      let 
        nb1 = RemoveConsts_BoolOperands b1;
        nb2 = RemoveConsts_BoolOperands b2
      in 
        case nb1 of
          VBBConstOp c1 \<Rightarrow> if c1 then nb2 else (VBBConstOp False) |
          _ \<Rightarrow> 
          (
            case nb2 of
              VBBConstOp c2 \<Rightarrow> if c2 then nb1 else (VBBConstOp False) |
              _ \<Rightarrow> VBBAndOp nb1 nb2
          )
    )"

abbreviation is_negation :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand \<Rightarrow> bool" 
where
  "is_negation b1 b2 \<equiv> b1 = VBBNotOp b2 \<or> VBBNotOp b1 = b2"

primrec RemoveSame_BoolOperandsPair :: 
  "'vb BoolOperand set \<Rightarrow> 'vb BoolOperand \<Rightarrow> ('vb BoolOperand \<times> 'vb BoolOperand set)"
where
  "RemoveSame_BoolOperandsPair _ (VBBConstOp c) = (VBBConstOp c, {})" |
  "RemoveSame_BoolOperandsPair R (VBBVarOp v) = (VBBVarOp v, { VBBVarOp v })" |
  "RemoveSame_BoolOperandsPair R (VBBNotOp b) = (
    let 
      negation = \<lambda> X. { x. \<exists> nx \<in> X. is_negation x nx };
      nR = negation R;
      nb = RemoveSame_BoolOperandsPair nR b;
      nbb = fst nb
    in
      case nbb of
        VBBNotOp nbbb \<Rightarrow> (nbbb, negation (snd nb)) |
        _ \<Rightarrow> (VBBNotOp nbb, negation (snd nb))
  )" |
  "RemoveSame_BoolOperandsPair R (VBBAndOp b1 b2) = (
    let
      nb1 = RemoveSame_BoolOperandsPair R b1;
      nb1b = fst nb1; nb1R = snd nb1;
      nb2 = RemoveSame_BoolOperandsPair (R \<union> nb1R)  b2;
      nb2b = fst nb2; nb2R = snd nb2;
      nbS = nb1R \<union> nb2R
    in
      if (nb1b \<in> R) 
        then 
          if (nb2b \<in> R) 
          then ((VBBConstOp True), nbS)
          else (nb2b, nbS)
        else
          if (nb2b \<in> R) 
          then (nb1b, nbS)
          else (VBBAndOp nb1b nb2b, nbS)
  )"

definition RemoveSame_BoolOperands :: " 'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "RemoveSame_BoolOperands b = fst (RemoveSame_BoolOperandsPair {} b)"
  
lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> (RemoveSame_BoolOperands  
  (VBBAndOp (VBBVarOp A) (VBBOrOp (VBBVarOp A) (VBBVarOp B)))) = 
  (VBBAndOp (VBBVarOp A) (VBBVarOp B))"
apply (auto simp add: RemoveSame_BoolOperands_def Let_def)
done

lemma "
  \<lbrakk> 
    (A \<noteq> B);
    (b = VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B)));
    r = b
  \<rbrakk> \<Longrightarrow>
  (RemoveSame_BoolOperands b) = r"
apply (auto simp add: RemoveSame_BoolOperands_def Let_def)
done

lemma "
  \<lbrakk> 
    (A \<noteq> B);
    (b = 
      VBBAndOp 
        (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBAndOp (VBBConstOp True) (VBBVarOp B))) 
        (VBBAndOp (VBBVarOp A) (VBBNotOp (VBBVarOp B)))
    );
    r = b
  \<rbrakk> \<Longrightarrow>
  (RemoveSame_BoolOperands b) = r"
apply (auto simp add: RemoveSame_BoolOperands_def Let_def)
done

datatype 'a FindVar = NormalVar 'a | NegatedVar 'a

primrec FindVars_BoolOperands :: 
  "'vb BoolOperand \<Rightarrow> ('vb FindVar \<rightharpoonup> bool) \<Rightarrow> ('vb FindVar \<rightharpoonup> bool)"
where
  "FindVars_BoolOperands (VBBConstOp _) m = m" |
  "FindVars_BoolOperands (VBBVarOp v) m = 
  (
    m ++ [ NormalVar v \<mapsto> True, NegatedVar v \<mapsto> False ]
  )" |
  "FindVars_BoolOperands (VBBNotOp b) m = 
  (
    FindVars_BoolOperands b (apply_map m Not)
  )" |
  "FindVars_BoolOperands (VBBAndOp b1 b2) m = 
  (
    let 
      nm1 = FindVars_BoolOperands b1 m;
      nm2 = FindVars_BoolOperands b2 m
    in
      merge_map nm1 nm2 (op \<or>)
  )
  "

primrec RemoveSimmetric_BoolOperandsFind :: "'vb BoolOperand \<Rightarrow> 'vb set \<Rightarrow> 'vb BoolOperand"
where
  "RemoveSimmetric_BoolOperandsFind (VBBConstOp c) _ = VBBConstOp c" |
  "RemoveSimmetric_BoolOperandsFind (VBBVarOp v) S = 
    (if v \<in> S then VBBConstOp True else VBBVarOp v)" |
  "RemoveSimmetric_BoolOperandsFind (VBBNotOp b) S = 
  (
  VBBNotOp (RemoveSimmetric_BoolOperandsFind b S)
  )" |
  "RemoveSimmetric_BoolOperandsFind (VBBAndOp b1 b2) S =
    VBBAndOp (RemoveSimmetric_BoolOperandsFind b1 S) (RemoveSimmetric_BoolOperandsFind b2 S)"

definition RemoveSimmetric_BoolOperands :: 
  "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "RemoveSimmetric_BoolOperands b \<equiv> 
  (
    let
      fv = FindVars_BoolOperands b Map.empty;
      contains = \<lambda> fvv. (case (fv fvv) of None \<Rightarrow> False | Some bv \<Rightarrow> bv);
      contains_var = \<lambda> v. (contains (NormalVar v)) \<and> (contains (NegatedVar v))
    in RemoveSimmetric_BoolOperandsFind b (Collect contains_var)
  )"

lemma "(RemoveSimmetric_BoolOperands 
  (VBBAndOp (VBBVarOp A) (VBBOrOp (VBBVarOp A) (VBBVarOp B)))) = 
  (VBBAndOp (VBBVarOp A) (VBBOrOp (VBBVarOp A) (VBBVarOp B)))"
apply (simp add: RemoveSimmetric_BoolOperands_def)
apply (simp add: merge_map_def)
apply (simp add: apply_map_def)
done

lemma "
  \<lbrakk> 
    A \<noteq> B;
    b = VBBAndOp 
      (VBBAndOp (VBBNotOp (VBBVarOp A)) (VBBVarOp B)) 
      (VBBAndOp (VBBVarOp A) (VBBNotOp (VBBVarOp B)));
    r = VBBAndOp
      (VBBAndOp (VBBConstOp True) (VBBConstOp True))
      (VBBAndOp (VBBConstOp True) (VBBConstOp True))
  \<rbrakk> \<Longrightarrow> 
  RemoveSimmetric_BoolOperands b = r"
apply (auto simp add: RemoveSimmetric_BoolOperands_def )
apply (simp add: merge_map_def)
done

definition normalise_BoolOperand :: "'vb BoolOperand \<Rightarrow> 'vb BoolOperand"
where
  "normalise_BoolOperand b = 
    (
    RemoveConsts_BoolOperands \<circ>
    RemoveSimmetric_BoolOperands \<circ> 
    RemoveSame_BoolOperands \<circ>
    RemoveConsts_BoolOperands
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
