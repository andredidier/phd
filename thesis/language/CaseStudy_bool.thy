theory CaseStudy_bool
imports ActivationLanguage_bool
begin

datatype CSOperationalModes = LP
datatype CSVars = B nat | F

definition PowerSource :: 
  "nat \<Rightarrow> (CSVars bexp, CSOperationalModes) activationLogic" where
"PowerSource i = Cons 
  (Atom (B i)) (Failure LP) 
  (Term (Neg (Atom (B i))) (Nominal (Some 12)))"

definition Monitor_pred :: 
  "(CSVars bexp, CSOperationalModes) activationLogic \<Rightarrow> 
  (CSVars bexp \<Rightarrow> CSVars bexp) \<Rightarrow> (CSVars bexp \<Rightarrow> CSVars bexp) \<Rightarrow> 
  CSVars bexp" where
"Monitor_pred in_x m_1 m_2 = 
  inf (m_1 ((al_pred in_x (Nominal (Some 12)))))
    (m_2 (Atom F))"

definition Monitor :: 
  "(CSVars bexp, CSOperationalModes) activationLogic \<Rightarrow>
  (CSVars bexp, CSOperationalModes) activationLogic \<Rightarrow>
  (CSVars bexp, CSOperationalModes) activationLogic" where
"Monitor in_1 in_2 = 
  al_concat (al_concat (al_concat () ()) ()) ()
  al_modes in_1 (Monitor_pred in_1 id Neg)"

end