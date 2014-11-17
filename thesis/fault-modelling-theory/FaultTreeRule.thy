theory FaultTreeRule

imports FaultTree

begin

datatype FaultTreeRule =
  BasicEventMinLevel nat
  | RootProbability real

primrec evaluateRule :: "'vb FaultTree \<Rightarrow> FaultTreeRule \<Rightarrow> ('vb \<Rightarrow> real) \<Rightarrow> bool"
where
  "evaluateRule ft (BasicEventMinLevel n) P = (min_basicEventLevel ft \<ge> n)" |
  "evaluateRule ft (RootProbability p) P = ((FT_probability ft P) \<le> p)"

definition unsatisfiedRules :: "'vb FaultTree \<Rightarrow> FaultTreeRule set \<Rightarrow> ('vb \<Rightarrow> real) 
  \<Rightarrow> FaultTreeRule set"
where
  "unsatisfiedRules ft rules P \<equiv> { r. r \<in> rules \<and> \<not> evaluateRule ft r P }"

definition evaluateRules :: "'vb FaultTree \<Rightarrow> FaultTreeRule set \<Rightarrow> ('vb \<Rightarrow> real) \<Rightarrow> bool"
where
  "evaluateRules ft rules P \<equiv> unsatisfiedRules ft rules P = {}"

definition verifyFaultTree :: "'vb FaultTree \<Rightarrow> FaultTreeRule set \<Rightarrow> ('vb \<Rightarrow> real) 
  \<Rightarrow> (bool \<times> FaultTreeRule set)"
where
  "verifyFaultTree ft rules P \<equiv> let unsats = unsatisfiedRules ft rules P in (unsats = {}, unsats)"

value "verifyFaultTree 
  (IntermediaryEvent FTGAnd 
    (IntermediaryEvent FTGAnd (BasicEvent A) (BasicEvent B)) 
    (IntermediaryEvent FTGAnd (BasicEvent C) (BasicEvent D))
  ) 
  ({ BasicEventMinLevel 2  }) 
  (\<lambda> v. if v = A then 0.1 else if v = B then 0.01 else 0)"

value "verifyFaultTree 
  (IntermediaryEvent FTGAnd (BasicEvent A) (BasicEvent B)) 
  ({ BasicEventMinLevel 2, RootProbability 0.11  }) 
  (\<lambda> v. if v = A then 0.1 else if v = B then 0.01 else 0)"

value "evaluateRules 
  (IntermediaryEvent FTGAnd (BasicEvent A) (BasicEvent B)) 
  ({ BasicEventMinLevel 2, RootProbability 0.11  }) 
  (\<lambda> v. if v = A then 0.1 else if v = B then 0.01 else 0)"

end
