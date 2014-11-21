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


lemma [simp]: "\<lbrakk> FT_probability ft P \<le> p  \<rbrakk> \<Longrightarrow> 
  (verifyFaultTree ft {RootProbability p} P) = (True, {})"
apply (induct ft)
apply (auto simp add: min_basicEventLevel_def verifyFaultTree_def)
apply (auto simp add: unsatisfiedRules_def)
done

lemma [simp]: "\<lbrakk> min_basicEventLevel ft > n  \<rbrakk> \<Longrightarrow> 
  (verifyFaultTree ft {BasicEventMinLevel n} P) = (True, {})"
apply (induct ft)
apply (auto simp add: min_basicEventLevel_def verifyFaultTree_def)
apply (auto simp add: unsatisfiedRules_def)
apply (auto simp add: min_basicEventLevel_def)
done

lemma [simp]: "\<lbrakk> FT_probability ft P \<le> p; min_basicEventLevel ft > n  \<rbrakk> \<Longrightarrow> 
  (verifyFaultTree ft {BasicEventMinLevel n, RootProbability p} P) = (True, {})"
apply (induct ft)
apply (auto simp add: min_basicEventLevel_def verifyFaultTree_def)
apply (auto simp add: unsatisfiedRules_def)
apply (auto simp add: min_basicEventLevel_def)
done

end
