theory FaultTreeRule

imports FaultTree

begin

text {*
  {@term BasicEventMinLevel n}: no basic event should appear before level n from the root. 
  {@term RootProbability p}: the root probability should be smaller than p.
  {@term NoHigherCombinations n}: no higher combinations of ANDs should appear. For example: if an 
intermediate event is caused by a fault F1, ..., Fn-1, than faults F1, ..., Fn-1 should not appear
in a combination with Fn.
  {@term OrProbability perc}: if an OR gate has events probability such that the lowest is perc 
  lower than the second lowest one.
*}

datatype FaultTreeRule =
  BasicEventMinLevel nat
  | RootProbability real
  | NoHigherCombinations nat
  | OrProbability real

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
