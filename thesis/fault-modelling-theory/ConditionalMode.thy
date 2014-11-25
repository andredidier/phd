theory ConditionalMode

imports ModeCondition Complex_Main FaultModellingTypes

begin

datatype_new ('FMode, 'vv) OperationalMode = 
  NominalMode real 
  | FailureMode "'FMode"
  | VarMode (var: 'vv)

datatype_new ('a, 'FMode, 'vv) ConditionalMode =
  CMConst "('FMode, 'vv) OperationalMode"
  | CMExp "('a, 'FMode, 'vv) CMPair list" and
  ('a, 'FMode, 'vv) CMPair = 
    CM (CMC:"'a") (CMM:"('a, 'FMode, 'vv) ConditionalMode")

type_synonym ('a, 'FMode, 'vv) ConditionalModePair = 
  "('a \<times> ('FMode, 'vv) OperationalMode)"

notation (output) NominalMode ("N\<langle>_\<rangle>" 40)
notation (output) FailureMode ("F\<langle>_\<rangle>" 41)
notation (output) VarMode ("_" 41)
notation (output) CMConst  ("_" 50)
notation (output) CMExp ("VT _" 80)
notation (output) CM (infix "\<surd>" 80)

primrec expand_CM2CMP :: "('a, 'b, 'c) Condition \<Rightarrow> 'a \<Rightarrow>
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow>
  ('a, 'FMode, 'vv) ConditionalModePair list"
where
  "expand_CM2CMP c e [] = []" |
  "expand_CM2CMP c e (v # vs) = 
    (Both c e (fst v), snd v) # (expand_CM2CMP c e vs)"

primrec 
  CM2CMP :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list" and
  CM2CMP_list :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair list \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list" and
  CM2CMP_CM :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair \<Rightarrow> 
    ('a, 'FMode, 'vv) ConditionalModePair list" 
where
  "CM2CMP cond (CMConst c) = [ (Top cond, c) ]" |
  "CM2CMP cond (CMExp v) = CM2CMP_list cond v" |
  "CM2CMP_list cond [] = []" |
  "CM2CMP_list cond (E # Es) = (CM2CMP_CM cond E) @ (CM2CMP_list cond Es)" |
  "CM2CMP_CM cond (CM e v) = expand_CM2CMP cond e (CM2CMP cond v)"

fun mkVO :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode"
where
  "mkVO cond (CMConst c1) (CMConst c2) = 
    CMExp (CM (Top cond) (CMConst c1) # CM (Top cond) (CMConst c2) # [])" |
  "mkVO cond (CMConst c1) (CMExp Es) = (CMExp ((CM (Top cond) (CMConst c1)) # Es))" |
  "mkVO cond (CMExp Es1) (CMExp Es2) = CMExp (Es1 @ Es2)" |
  "mkVO cond (CMExp Es) (CMConst c1) = (CMExp (Es @ [CM (Top cond) (CMConst c1)]))" 

fun CMP2CM :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalMode"
where
  "CMP2CM _ [] = CMExp []" |
  "CMP2CM cond [ cv ] = 
  (
    if Tautology cond (fst cv) 
      then CMConst (snd cv) 
      else CMExp [ CM (fst cv) (CMConst (snd cv)) ]
  )" |
  "CMP2CM cond (cv # cvs) = mkVO cond (CMP2CM cond [cv]) (CMP2CM cond cvs)"

definition CMP2MC :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 'a"
where
  "CMP2MC cond cmpl \<equiv> fold (\<lambda> a b. Any cond (fst a) b) cmpl (Bot cond)"

definition ValuedTautology_CMPList1 :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "ValuedTautology_CMPList1 C ls \<equiv> ls \<noteq> [] \<and> (((Tautology C) \<circ> (CMP2MC C)) ls)"

definition ValuedTautology_CMPList2 :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "ValuedTautology_CMPList2 C ls \<equiv> 
  (ls \<noteq> [] \<and>
    (\<forall> i j s. 
      (
        let ei = fst (ls!i); ej = fst (ls!j); vi = snd (ls!i); vj = snd (ls!j)
        in ((Eval C s ei) \<and> (Eval C s ej)) \<longrightarrow> vi = vj
      )
    )
  )"

definition ValuedTautology_CMPList :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> bool"
where
  "ValuedTautology_CMPList C ls \<equiv> (ValuedTautology_CMPList1 C ls \<and> ValuedTautology_CMPList2 C ls)"

definition CMPList_eval_values :: 
  "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalModePair list \<Rightarrow> 
  ('b \<Rightarrow> 'c) \<Rightarrow> 
  ('FMode, 'vv) OperationalMode list"
where
  "CMPList_eval_values cond cmpl s \<equiv> 
  (
    let 
      filtercvs = filter ((Eval cond s) \<circ> fst);
      getvalue = map snd
    in (remdups \<circ> getvalue \<circ> filtercvs) cmpl
  )"

lemma VTL1: "\<lbrakk> ValuedTautology_CMPList1 C as \<rbrakk> \<Longrightarrow> CMPList_eval_values C as s \<noteq> []"
apply (induct as)
apply (auto simp add: ValuedTautology_CMPList1_def CMPList_eval_values_def )
sorry

lemma VTL2: "\<lbrakk> ValuedTautology_CMPList1 C ls \<rbrakk> \<Longrightarrow> \<forall> s. length (CMPList_eval_values C ls s) > 0"
apply (induct ls)
apply (simp)
apply (auto simp add: ValuedTautology_CMPList1_def CMPList_eval_values_def)
sorry

lemma VTL3: "ValuedTautology_CMPList2 C ls \<Longrightarrow> \<forall> s. length (CMPList_eval_values C ls s) \<le> (Suc 0)"
apply (induct ls)
apply (simp add: CMPList_eval_values_def )
apply (auto simp add: ValuedTautology_CMPList2_def )

sorry

theorem VTL: "
  \<lbrakk> 
    ValuedTautology_CMPList C ls; 
    f = (\<lambda> s. length (CMPList_eval_values C ls s))
  \<rbrakk> \<Longrightarrow> f s = (Suc 0)"
apply (subgoal_tac "(f s > 0 \<and> f s \<le> (Suc 0))")
apply (arith)
apply (simp add: ValuedTautology_CMPList_def VTL1 VTL2 VTL3)
done

primrec  
  CM2MC :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 'a" and
  CM2MC_list :: 
    "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair list \<Rightarrow> 'a" and
  CM2MC_VB :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) CMPair \<Rightarrow> 'a"
where
  "CM2MC cond (CMConst _) = (Top cond)" |
  "CM2MC cond (CMExp Es) = CM2MC_list cond Es" |
  "CM2MC_list cond [] = (Bot cond)" |
  "CM2MC_list cond (E # Es) = Any cond (CM2MC_VB cond E) (CM2MC_list cond Es)" |
  "CM2MC_VB cond (CM e v) = Both cond e (CM2MC cond v)"

definition ValuedTautology :: "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> bool"
where
  "ValuedTautology cond v \<equiv> ((ValuedTautology_CMPList cond) \<circ> (CM2CMP cond)) v"

notation (output) ValuedTautology ("\<VV>\<TT> _")

definition ConditionalMode_eval_values :: 
  "('a, 'b, 'c) Condition \<Rightarrow> ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 
  ('FMode, 'vv) OperationalMode list"
where
  "ConditionalMode_eval_values cond v s \<equiv> CMPList_eval_values cond (CM2CMP cond v) s"

lemma ValuedTautologyUniqueness1: "
  \<lbrakk> 
    ValuedTautology C v;
    f = (\<lambda> s . length (ConditionalMode_eval_values C v s))
  \<rbrakk> \<Longrightarrow> f s = 1"
apply (insert VTL [of C "CM2CMP C v" f s])
apply (auto simp add: ValuedTautology_def)
apply (auto simp add: ConditionalMode_eval_values_def)
done

theorem ValuedTautologyUniqueness: 
  "ValuedTautology C v \<Longrightarrow> length (ConditionalMode_eval_values C v s) = 1"
apply (insert ValuedTautologyUniqueness1)
apply (auto)
done

primrec choose_values :: "('FMode, 'vv) OperationalMode \<Rightarrow> ('FMode, 'vv) OperationalMode option 
  \<Rightarrow> ('FMode, 'vv) OperationalMode option"
where
  "choose_values v1 None = Some v1" |
  "choose_values v1 (Some v2) = (if (v1 = v2) then (Some v1) else None)"

definition ConditionalMode_eval_value :: "('a, 'b, 'c) Condition \<Rightarrow> 
  ('a, 'FMode, 'vv) ConditionalMode \<Rightarrow> 
  ('b \<Rightarrow> 'c) \<Rightarrow> ('FMode, 'vv) OperationalMode option"
where
  "ConditionalMode_eval_value cond Es vb \<equiv> 
    fold choose_values (ConditionalMode_eval_values cond Es vb) None"

lemma length_choose_values: "\<lbrakk> length ls = 1 \<rbrakk> \<Longrightarrow> \<exists> x . fold choose_values ls None = Some x"
apply (insert length_Suc_conv [of ls 0])
apply (auto)
done

theorem ValuedTautologyUniqueValue: "ValuedTautology C v \<Longrightarrow> 
  \<exists> x . (ConditionalMode_eval_value C v s = Some x)"
apply (insert ValuedTautologyUniqueness [of C v s])
apply (auto simp add: ConditionalMode_eval_value_def)
apply (insert length_choose_values [of "ConditionalMode_eval_values C v s"])
apply (auto simp add: ConditionalMode_eval_values_def)
done

end
