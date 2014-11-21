(*<*)
theory ModeCondition

imports Main FaultModellingTypes Boolean_Expression_Checkers

begin
(*>*)

(*<*)
datatype 'vb ModeCondition = 
  MCConst bool
  | MCVar 'vb 
  | MCNot "'vb ModeCondition" 
  | MCAnd "'vb ModeCondition" "'vb ModeCondition" 

notation (output) MCConst  ("_" 60)
notation (output) MCVar ("_" 60)
notation (output) MCNot ("\<not>_" 80)
notation (output) MCAnd (infix "\<and>" 75)

abbreviation MCOr :: "'vb ModeCondition \<Rightarrow> 'vb ModeCondition \<Rightarrow> 'vb ModeCondition"
where "MCOr b1 b2 \<equiv> MCNot (MCAnd (MCNot b1) (MCNot b2))"

notation (output) MCOr (infix "\<or>" 70)

abbreviation MCNand :: "'vb ModeCondition \<Rightarrow> 'vb ModeCondition \<Rightarrow> 'vb ModeCondition"
where "MCNand b1 b2 \<equiv> (MCNot (MCAnd b1 b2))"

notation (output) MCNand (infix "\<^sup>\<not>\<and>" 73)

abbreviation MCXor :: "'vb ModeCondition \<Rightarrow> 'vb ModeCondition \<Rightarrow> 'vb ModeCondition"
where "MCXor b1 b2 \<equiv> (MCAnd (MCNand b1 b2) (MCOr b1 b2))"

notation (output) MCXor (infix "\<otimes>" 70)

type_synonym 'vb MCEnv = "'vb \<Rightarrow> bool"

(*>*)

primrec ModeCondition_eval :: "'vb ModeCondition \<Rightarrow> 'vb MCEnv \<Rightarrow> bool"
where
  "ModeCondition_eval (MCConst c) _ = c" |
  "ModeCondition_eval (MCVar v) env = (env v)" |
  "ModeCondition_eval (MCNot b) env = (\<not> ModeCondition_eval b env)" |
  "ModeCondition_eval (MCAnd b1 b2) env = 
    ((ModeCondition_eval b1 env) \<and> (ModeCondition_eval b2 env))"

primrec ModeCondition_to_bool_expr :: "'vb ModeCondition \<Rightarrow> 'vb bool_expr"
where
  "ModeCondition_to_bool_expr (MCConst c) = Const_bool_expr c" |
  "ModeCondition_to_bool_expr (MCVar v) = Atom_bool_expr v" |
  "ModeCondition_to_bool_expr (MCNot b) = Neg_bool_expr (ModeCondition_to_bool_expr b)" |
  "ModeCondition_to_bool_expr (MCAnd b1 b2) = 
    And_bool_expr (ModeCondition_to_bool_expr b1) (ModeCondition_to_bool_expr b2)"

lemma value_preservation [simp]: 
  "val_bool_expr (ModeCondition_to_bool_expr b) s = ModeCondition_eval b s"
apply (induction b)
apply (auto)
done

definition ModeCondition_Tautology :: "'vb ModeCondition \<Rightarrow> bool"
where "ModeCondition_Tautology \<equiv> taut_test \<circ> ModeCondition_to_bool_expr"

corollary Tautology_eval: "ModeCondition_Tautology b = (\<forall> env. ModeCondition_eval b env)"
apply (simp add: ModeCondition_Tautology_def taut_test)
done

definition ModeCondition_Sat :: "'vb ModeCondition \<Rightarrow> bool"
where "ModeCondition_Sat \<equiv> sat_test \<circ> ModeCondition_to_bool_expr"

corollary Sat_eval: "ModeCondition_Sat b = (\<exists> env. ModeCondition_eval b env)"
apply (simp add: ModeCondition_Sat_def sat_test)
done

definition ModeCondition_Equiv :: "'vb ModeCondition \<Rightarrow> 'vb ModeCondition \<Rightarrow> bool"
where
  "ModeCondition_Equiv c1 c2 \<equiv> 
    equiv_test (ModeCondition_to_bool_expr c1) (ModeCondition_to_bool_expr c2)"

corollary Equiv_eval: 
  "ModeCondition_Equiv c1 c2 = (\<forall> env. ModeCondition_eval c1 env = ModeCondition_eval c2 env)"
apply (auto simp add: ModeCondition_Equiv_def equiv_test_def taut_test)
done

definition ModeCondition_Absorb :: "'vb ModeCondition \<Rightarrow> 'vb ModeCondition \<Rightarrow> bool"
where
  "ModeCondition_Absorb c1 c2 \<equiv> 
    (
      let                           
        absorb_test = 
          \<lambda> a b. taut_test (Or_bool_expr (Imp_bool_expr a b) (Imp_bool_expr b a))
      in
        absorb_test (ModeCondition_to_bool_expr c1) (ModeCondition_to_bool_expr c2)
    )"

corollary Absorb_eval: 
  "ModeCondition_Absorb c1 c2 = 
    (\<forall> env. (ModeCondition_eval c1 env \<longrightarrow> ModeCondition_eval c2 env) \<or>
      (ModeCondition_eval c2 env \<longrightarrow> ModeCondition_eval c1 env)
    )"
apply (auto simp add: ModeCondition_Absorb_def equiv_test_def taut_test)
done

lemma "\<lbrakk> A \<noteq> B \<rbrakk> \<Longrightarrow> ModeCondition_Absorb (MCVar A) (MCAnd (MCVar A) (MCVar B))"
apply (auto simp add: ModeCondition_Absorb_def taut_test)
done

end
