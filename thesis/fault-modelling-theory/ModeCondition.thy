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
    (Eval:"'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool")

  (*fixes tautology :: "'a \<Rightarrow> bool" ("\<TT> _" 70) 
  fixes sat :: "'a \<Rightarrow> bool" ("\<SS> _" 70)
  fixes equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<EE>" 70)
  fixes absorb :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<AA>" 70)*)

datatype 'vb BoolEx = 
  MCConst bool
  | MCVar 'vb 
  | MCNot "'vb BoolEx" 
  | MCAnd "'vb BoolEx" "'vb BoolEx" 

notation (output) MCConst  ("_" 60)
notation (output) MCVar ("_" 60)
notation (output) MCNot ("\<not>_" 80)
notation (output) MCAnd (infix "\<and>" 75)

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

primrec BoolEx_eval :: "'vb BoolEx \<Rightarrow> 'vb MCEnv \<Rightarrow> bool"
where
  "BoolEx_eval (MCConst c) _ = c" |
  "BoolEx_eval (MCVar v) env = (env v)" |
  "BoolEx_eval (MCNot b) env = (\<not> BoolEx_eval b env)" |
  "BoolEx_eval (MCAnd b1 b2) env = 
    ((BoolEx_eval b1 env) \<and> (BoolEx_eval b2 env))"

definition absorb_rule :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "absorb_rule a b \<equiv> (a \<longrightarrow> b) \<or> (b \<longrightarrow> a)"

definition BoolEx_Absorb :: "'vb BoolEx \<Rightarrow> 'vb BoolEx \<Rightarrow> bool"
where
  "BoolEx_Absorb c1 c2 \<equiv> 
    (
      let                           
        absorb_test = 
          \<lambda> a b. taut_test (Or_bool_expr (Imp_bool_expr a b) (Imp_bool_expr b a))
      in
        absorb_test (BoolEx_to_bool_expr c1) (BoolEx_to_bool_expr c2)
    )"

definition BoolCondition :: "('vb BoolEx, 'vb, bool) Condition"
where
  "BoolCondition \<equiv> 
  Operations 
    (taut_test \<circ> BoolEx_to_bool_expr) 
    (sat_test \<circ> BoolEx_to_bool_expr) 
    (\<lambda> c1 c2. equiv_test (BoolEx_to_bool_expr c1) (BoolEx_to_bool_expr c2)) 
    (BoolEx_Absorb)
    (BoolEx_eval)"

declare BoolCondition_def [simp]

definition ValuePreservation :: "('a, 'b, 'c) Condition \<Rightarrow> bool"
where
  "ValuePreservation condition \<equiv> (\<forall> a b.
    (Tautology condition a = (\<forall> s. Eval condition a s)) \<and>
    (Sat condition a = (\<exists> s. Eval condition a s)) \<and>
    (Absorb condition a b = (\<forall> s. absorb_rule (Eval condition a s) (Eval condition b s))) \<and>
    (Equiv condition a b = (\<forall> s. Eval condition a s = Eval condition b s))
  )"

lemma ValuePreservation_BoolEx: 
  "val_bool_expr (BoolEx_to_bool_expr b) s = BoolEx_eval b s"
apply (induction b)
apply (auto)
done

corollary ValuePreservation_BoolCondition: "ValuePreservation BoolCondition"
apply (auto simp add: ValuePreservation_def)
apply (auto simp add: taut_test ValuePreservation_BoolEx)
apply (auto simp add: sat_test ValuePreservation_BoolEx)
apply (auto simp add: absorb_rule_def BoolEx_Absorb_def taut_test ValuePreservation_BoolEx)
apply (auto simp add: equiv_test ValuePreservation_BoolEx)
done

end
