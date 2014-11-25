(*<*)
theory ModeCondition

imports Main FaultModellingTypes Boolean_Expression_Checkers

begin
(*>*)

(*<*)

datatype_new ('a, 'b, 'c) Condition = 
  Operations 
    (Tautology:"'a \<Rightarrow> bool") 
    (Sat: "'a \<Rightarrow> bool") 
    (Equiv: "'a \<Rightarrow> 'a \<Rightarrow> bool")
    (Absorb: "'a \<Rightarrow> 'a \<Rightarrow> bool")
    (Eval: "('b \<Rightarrow> 'c) \<Rightarrow>'a \<Rightarrow>  bool")
    (Top: "'a")
    (Bot: "'a")
    (Both: "'a binop")
    (Any: "'a binop")
    (Not: "'a \<Rightarrow> 'a")

notation (output) Tautology ("\<TT>\<index> _" 70) 
notation (output) Sat ("\<SS>\<index> _" 70)
notation (output) Equiv (infixr "\<EE>\<index>" 70)
notation (output) Absorb (infixr "\<AA>\<index>" 70)
notation (output) Eval ("_\<Colon>\<lbrakk>_\<rbrakk>\<index>" 70)
notation (output) Top ("\<top>\<index>")
notation (output) Bot ("\<bottom>\<index>")
notation (output) Both (infixr "\<and>\<index>" 50)
notation (output) Any (infixr "\<or>\<index>" 50)
notation (output) Not ("\<not>\<index>_" 50)

datatype 'vb BoolEx = 
  MCConst bool
  | MCVar 'vb 
  | MCNot "'vb BoolEx" 
  | MCAnd "'vb BoolEx" "'vb BoolEx" 

type_synonym 'a SeqEx = "'a list set"

notation (output) MCConst  ("_\<^sub>B" 60)
notation (output) MCVar ("_\<^sub>B" 60)
notation (output) MCNot ("\<not>_" 64)
notation (output) MCAnd (infix "\<and>" 65)

abbreviation MCOr :: "'vb BoolEx \<Rightarrow> 'vb BoolEx \<Rightarrow> 'vb BoolEx"
where "MCOr b1 b2 \<equiv> MCNot (MCAnd (MCNot b1) (MCNot b2))"

notation (output) MCOr (infix "\<or>" 70)

abbreviation MCNand :: "'vb BoolEx \<Rightarrow> 'vb BoolEx \<Rightarrow> 'vb BoolEx"
where "MCNand b1 b2 \<equiv> (MCNot (MCAnd b1 b2))"

notation (output) MCNand (infix "\<^sup>\<not>\<and>" 73)

abbreviation MCXor :: "'vb BoolEx \<Rightarrow> 'vb BoolEx \<Rightarrow> 'vb BoolEx"
where "MCXor b1 b2 \<equiv> (MCAnd (MCNand b1 b2) (MCOr b1 b2))"

notation (output) MCXor (infix "\<otimes>" 70)

type_synonym 'vb MCEnv = "'vb \<Rightarrow> bool"

primrec BoolEx_to_bool_expr :: "'vb BoolEx \<Rightarrow> 'vb bool_expr"
where
  "BoolEx_to_bool_expr (MCConst c) = Const_bool_expr c" |
  "BoolEx_to_bool_expr (MCVar v) = Atom_bool_expr v" |
  "BoolEx_to_bool_expr (MCNot b) = Neg_bool_expr (BoolEx_to_bool_expr b)" |
  "BoolEx_to_bool_expr (MCAnd b1 b2) = 
    And_bool_expr (BoolEx_to_bool_expr b1) (BoolEx_to_bool_expr b2)"

(*>*)

primrec BoolEx_eval :: "'vb MCEnv \<Rightarrow> 'vb BoolEx \<Rightarrow> bool"
where
  "BoolEx_eval _ (MCConst c) = c" |
  "BoolEx_eval s (MCVar v) = (s v)" |
  "BoolEx_eval s (MCNot b) = (\<not> BoolEx_eval s b)" |
  "BoolEx_eval s (MCAnd b1 b2) = 
    ((BoolEx_eval s b1) \<and> (BoolEx_eval s b2))"


definition absorb_rule :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "absorb_rule a b \<equiv> (a \<longrightarrow> b) \<or> (b \<longrightarrow> a)"

definition absorb_test :: "'a bool_expr \<Rightarrow> 'a bool_expr \<Rightarrow> bool"
where
  "absorb_test a b \<equiv> taut_test (Or_bool_expr (Imp_bool_expr a b) (Imp_bool_expr b a))"

definition BoolEx_Absorb :: "'vb BoolEx \<Rightarrow> 'vb BoolEx \<Rightarrow> bool"
where
  "BoolEx_Absorb c1 c2 \<equiv> 
    (
        absorb_test (BoolEx_to_bool_expr c1) (BoolEx_to_bool_expr c2)
    )"

definition BoolCondition :: "('vb BoolEx, 'vb, bool) Condition" ("\<^sub>B")
where
  "BoolCondition \<equiv> 
  Operations 
    (taut_test \<circ> BoolEx_to_bool_expr) 
    (sat_test \<circ> BoolEx_to_bool_expr) 
    (\<lambda> c1 c2. equiv_test (BoolEx_to_bool_expr c1) (BoolEx_to_bool_expr c2)) 
    (BoolEx_Absorb)
    (BoolEx_eval)
    (MCConst True)
    (MCConst False)
    (MCAnd)
    (MCOr)
    (MCNot)"

declare BoolCondition_def [simp]

definition Tautology_Eval_s :: "('a, 'b, 'c) Condition \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> bool"
where "Tautology_Eval_s C s a \<equiv> (Tautology C a = Eval C s a)"

definition ValuePreservation :: "('a, 'b, 'c) Condition \<Rightarrow> bool"
where
  "ValuePreservation C \<equiv> (\<forall> a b.
    (Tautology C a = (\<forall> s. Eval C s a)) \<and>
    (Sat C a = (\<exists> s. Eval C s a)) \<and>
    (Absorb C a b = (\<forall> s. absorb_rule (Eval C s a) (Eval C s b))) \<and>
    (Equiv C a b = (\<forall> s. Eval C s a = Eval C s b))
  )"

definition ValidLattice :: "('a, 'b, 'c) Condition \<Rightarrow> bool"
where
  "ValidLattice C \<equiv> 
    (Tautology C (Top C)) \<and>
    (\<not> (Sat C (Bot C))
  )"

definition ValidOps :: "('a, 'b, 'c) Condition \<Rightarrow> bool"
where
  "ValidOps cond \<equiv> (\<forall> a b.
    (Equiv cond (Any cond a (Bot cond)) a) \<and>
    (Equiv cond (Any cond a (Top cond)) (Top cond)) \<and>
    (Equiv cond (Both cond a (Bot cond)) (Bot cond)) \<and>
    (Equiv cond (Both cond a (Top cond)) a) \<and>
    (Equiv cond (Any cond a b) (Any cond b a)) \<and>
    (Equiv cond (Both cond a b) (Both cond b a)) \<and>
    (Equiv cond (Bot cond) (Not cond (Top cond))) \<and>
    (Equiv cond (Top cond) (Not cond (Bot cond)))
  )"

definition ValidCondition :: "('a, 'b, 'c) Condition \<Rightarrow> bool"
where
  "ValidCondition C \<equiv> ValuePreservation C \<and> ValidLattice C \<and> ValidOps C"

lemma "\<lbrakk> ValuePreservation C \<rbrakk> \<Longrightarrow> 
  Tautology C a \<Longrightarrow> ((\<forall> s. \<not> Eval C s a)) \<Longrightarrow> False"
apply (simp add: ValuePreservation_def)
done

(*
definition TautologyProperty :: "('a, 'b, 'c) Condition \<Rightarrow> bool"
where
  "TautologyProperty cond \<equiv> \<forall> a. Tautology cond a \<longrightarrow> 
    (\<exists> b c. Equiv cond b (Not cond c) \<and> (Equiv cond a (Any cond b c)))"

lemma "\<lbrakk> C = BoolCondition; ValidOps C; ValidLattice C; ValuePreservation C \<rbrakk> \<Longrightarrow> 
  TautologyProperty C"
apply (auto)
apply (auto simp add: ValidOps_def TautologyProperty_def ValidLattice_def ValuePreservation_def)
apply (auto simp add: BoolEx_eval_def BoolEx_Absorb_def)
apply (auto simp add: taut_test equiv_test sat_test BoolEx_to_bool_expr_def)
done
*)

lemma ValuePreservation_BoolEx: 
  "val_bool_expr (BoolEx_to_bool_expr b) s = BoolEx_eval s b"
apply (induction b)
apply (auto)
done

lemma ValuePreservation_BoolCondition: "ValuePreservation BoolCondition"
apply (auto simp add: ValuePreservation_def)
apply (auto simp add: taut_test ValuePreservation_BoolEx )
apply (auto simp add: sat_test ValuePreservation_BoolEx)
apply (auto simp add: absorb_rule_def BoolEx_Absorb_def absorb_test_def taut_test 
  ValuePreservation_BoolEx)
apply (auto simp add: equiv_test ValuePreservation_BoolEx)
done

lemma ValidOps_BoolCondition: "ValidOps BoolCondition"
apply (auto simp add: ValidOps_def equiv_test)
done

lemma ValidLattice_BoolCondition: "ValidLattice BoolCondition"
apply (auto simp add: ValidLattice_def taut_test sat_test)
done

theorem ValidCondition_BoolCondition: "ValidCondition BoolCondition"
apply (auto simp add: ValidCondition_def)
(*apply (auto simp add: ValuePreservation_BoolCondition)*)
apply (auto simp add: ValuePreservation_def)
apply (auto simp add: taut_test ValuePreservation_BoolEx)
apply (auto simp add: sat_test ValuePreservation_BoolEx)
apply (auto simp add: absorb_rule_def absorb_test_def BoolEx_Absorb_def taut_test 
  ValuePreservation_BoolEx)
apply (auto simp add: equiv_test ValuePreservation_BoolEx)
apply (auto simp add: ValidOps_def equiv_test)
apply (auto simp add: ValidLattice_def taut_test sat_test)
done

end
