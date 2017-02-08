theory SyntaxSemanticsOfAlgebra

imports 
  Main
  "~~/src/HOL/Library/Dlist"
  "Temporal_Faults_Algebra_dlist"

begin

inductive minterm :: "'a set \<Rightarrow> ('a dlist \<times> 'a set) \<Rightarrow> bool"
for G :: "'a set"
where
"Dlist.set xs \<inter> nands = {} \<Longrightarrow> Dlist.set xs \<union> nands = G \<Longrightarrow> 
  minterm G (xs, nands)"

definition filter_all_formulas :: 
  "'a set \<Rightarrow> ('a dlist \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a dlist \<times> 'a set) set" where
"filter_all_formulas G P = 
  { (xs,nands). minterm G (xs,nands) \<and> P xs nands }"

definition all_formulas_of :: "'a set \<Rightarrow> ('a dlist \<times> 'a set) set" where
"all_formulas_of G = filter_all_formulas G (\<lambda>xs nands. True)"

datatype 'a expression = 
  eFalse |
  eTrue |
  eNeutral |
  eVar 'a |
  eNot "'a expression" |
  eAnd "'a expression" "'a expression" |
  eOr "'a expression" "'a expression" |
  eXB "'a expression" "'a expression"

definition dlist_take :: "nat \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
"dlist_take i ds = Dlist (take i (list_of_dlist ds))"

definition dlist_drop :: "nat \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
"dlist_drop i ds = Dlist (drop i (list_of_dlist ds))"

definition minterm_xbefore :: 
  "'a set \<Rightarrow> ('a dlist \<times> 'a set) set \<Rightarrow> 
  ('a dlist \<times> 'a set) set \<Rightarrow> ('a dlist \<times> 'a set) set" where
"minterm_xbefore G F1 F2 = filter_all_formulas G 
  (\<lambda>xs _ . \<exists>i.
    (dlist_take i xs, G - Dlist.set xs) \<in> F1 \<and>
    (dlist_take i xs, G - Dlist.set xs) \<in> F2
  )"

(*
primrec semantics_of :: 
  "'a set \<Rightarrow> 'a expression \<Rightarrow> ('a dlist \<times> 'a set) set" where
"semantics_of _ eFalse = {}" |
"semantics_of G eTrue = all_formulas_of G" |
"semantics_of G eNeutral = { (Dlist.empty, G) }" |
"semantics_of G (eVar x) = 
  filter_all_formulas G (\<lambda>xs _ . Dlist.member xs x)" |
"semantics_of G (eNot f) = all_formulas_of G - semantics_of G f" |
"semantics_of G (eAnd f1 f2) = semantics_of G f1 \<inter> semantics_of G f2" |
"semantics_of G (eOr f1 f2) = semantics_of G f1 \<union> semantics_of G f2" |
"semantics_of G (eXB f1 f2) = 
  minterm_xbefore G (semantics_of G f1) (semantics_of G f2)"
*)

primrec semantics_of :: "'a expression \<Rightarrow> 'a formula" where
"semantics_of eFalse = bot" |
"semantics_of eTrue = top" |
"semantics_of eNeutral = neutral" |
"semantics_of (eVar a) = (Abs_formula {ds. Dlist.member ds a})" |
"semantics_of (eAnd f1 f2) = inf (semantics_of f1) (semantics_of f2)" |
"semantics_of (eOr f1 f2) = sup (semantics_of f1) (semantics_of f2)" |
"semantics_of (eXB f1 f2) = xbefore (semantics_of f1) (semantics_of f2)" |
"semantics_of (eNot f) = - semantics_of f"

definition mk_eXB :: "'a \<Rightarrow> 'a expression \<Rightarrow> 'a expression" where
"mk_eXB x f = eXB (eVar x) f"

definition list_formula_of :: "'a list \<Rightarrow> 'a expression" where
"list_formula_of xs = foldr mk_eXB xs eNeutral"

definition mk_eNand :: "'a \<Rightarrow> 'a expression \<Rightarrow> 'a expression" where
"mk_eNand g f = eAnd (eNot (eVar g)) f"

definition mk_eNands :: "'a set \<Rightarrow> 'a expression" where
"mk_eNands nands = 
  Finite_Set.fold mk_eNand eTrue nands"

definition mk_eMinterm :: 
  "('a dlist \<times> 'a set) \<Rightarrow> 'a expression \<Rightarrow> 'a expression" where
"mk_eMinterm p f = 
  eOr (
    eAnd 
      (list_formula_of (list_of_dlist (fst p))) 
      (mk_eNands (snd p))) 
    f"

definition formula_of :: "('a dlist \<times> 'a set) set \<Rightarrow> 'a expression" where
"formula_of minterms = Finite_Set.fold mk_eMinterm eFalse minterms "

inductive reduce:: "'a expression \<Rightarrow> 'a expression \<Rightarrow> bool" where
reduce_idem: "reduce f f" |
eOr_true: "reduce (eOr eTrue f) eTrue" |
eOr_false: "reduce (eOr eFalse f) f" |
eOr_commute: "reduce (eOr f1 f2) f \<Longrightarrow> reduce (eOr f2 f1) f" |
Or_implies_eOr: "reduce f1 f \<or> reduce f2 f \<Longrightarrow> reduce (eOr f1 f2) f" |
"reduce (eOr f1 f2) f \<Longrightarrow> reduce (eOr (eAnd f1 f) (eAnd f2 f)) f" |
eNot_false: "reduce (eNot eFalse) eTrue" |
eNot_true: "reduce (eNot eTrue) eFalse" |
eNot_eNot: "reduce (eNot (eNot f)) f" |
eAnd_true: "reduce (eAnd eTrue f) f" |
eAnd_false: "reduce (eAnd eFalse f) eFalse" |
eAnd_commute: "reduce (eAnd f1 f2) f \<Longrightarrow> reduce (eAnd f2 f1) f" |
eAnd_implies1: "reduce (eAnd f1 f2) f \<Longrightarrow> reduce f1 f" |
eAnd_implies2: "reduce (eAnd f1 f2) f \<Longrightarrow> reduce f2 f" |
eAnd_eNot: "reduce (eAnd f (eNot f)) eFalse" |
eOr_eNot: "reduce (eOr f (eNot f)) eTrue" |
eXB_neutral_1: "reduce (eXB (eVar a) eNeutral) f" |
eXB_neutral_2: "reduce (eXB eNeutral (eVar a)) f" |
eXB_eOr_eAnd: 
  "reduce (eOr (eXB (eVar a) (eVar b)) (eXB (eVar b) (eVar a))) f \<Longrightarrow> 
  reduce (eAnd (eVar a) (eVar b)) f" |
eXB_eAnd_eOr: 
  "reduce (eAnd (eVar a) (eVar b)) f \<Longrightarrow> reduce (eOr (eXB (eVar a) (eVar b)) (eXB (eVar b) (eVar a))) f" 

inductive r2 :: "'a expression \<Rightarrow> 'a expression \<Rightarrow> bool" where
"r2 f f" |
"r2 (eAnd f1 f2) f \<Longrightarrow> r2 f1 f" |
"r2 (eAnd f1 f2) f \<Longrightarrow> r2 f2 f" 

lemma "r2 eFalse eTrue \<Longrightarrow> False"


theorem soundness: "reduce f1 f2 \<Longrightarrow> semantics_of f1 = semantics_of f2"
sorry

theorem completeness: 
  "semantics_of f = top \<Longrightarrow> reduce f eTrue"
sorry

lemma "a \<noteq> b \<Longrightarrow> reduce
  (eOr 
    (eOr (eXB (eVar a) (eVar b)) (eXB (eVar b) (eVar a))) 
    (eNot (eAnd (eVar a) (eVar b)))) eTrue"
proof-
  assume "\<not> reduce
  (eOr 
    (eOr (eXB (eVar a) (eVar b)) (eXB (eVar b) (eVar a))) 
    (eNot (eAnd (eVar a) (eVar b)))) eTrue"
  hence ""
    
qed
 



(*
"dlist_xbefore a b xs \<equiv> \<exists>i. a (xs\<dagger>..i) \<and> b (xs\<dagger>i..)"
*)

end