theory ActivationLanguageSyntax

imports 
  Main
begin

class activation_language_algebra =
  fixes bot :: "'a"
  fixes compl :: "'a \<Rightarrow> 'a"
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes tautology :: "'a \<Rightarrow> bool"
  fixes contradiction :: "'a \<Rightarrow> bool"

abbreviation sup where
  "sup x y \<equiv> compl (inf (compl x) (compl y))"

abbreviation implies where
  "implies x y \<equiv> sup (compl x) y"

abbreviation top where
  "top \<equiv> compl (bot)"

(* TODO : parametrizar os números *)
datatype 'a OperationalMode =
  Nominal "int option" | Failure 'a

datatype ('a::activation_language_algebra, 'o) activationLogic = 
  Term 'a "'o OperationalMode"
  | Cons 'a "'o OperationalMode" "('a, 'o)activationLogic" 

primrec al_belongs :: 
  "('a::activation_language_algebra \<times> 'o OperationalMode) \<Rightarrow> 
  ('a, 'o) activationLogic \<Rightarrow> bool" where
  "al_belongs t (Term pred operMode) = 
    (fst t = pred \<and> snd t = operMode)" |
  "al_belongs t (Cons pred operMode exp) = 
    ((fst t = pred \<and> snd t = operMode) \<or> al_belongs t exp)"

primrec activationLogicSemantics :: 
  "('a::activation_language_algebra, 'o) activationLogic \<Rightarrow> 
    ('a \<times> 'o OperationalMode) set" where
  "activationLogicSemantics (Term pred operMode) = 
    { (pred, operMode) }" |
  "activationLogicSemantics (Cons pred operMode exp) =
    { (pred, operMode) } \<union> (activationLogicSemantics exp)"

primrec al_filter :: 
  "(('a::activation_language_algebra \<times> 'o OperationalMode) \<Rightarrow> bool) \<Rightarrow>
  ('a, 'o) activationLogic \<Rightarrow> ('a, 'o) activationLogic" where
"al_filter f (Term pred operMode) = 
  (if f (pred, operMode) 
    then Term pred operMode 
    else Term bot (Nominal None))" |
"al_filter f (Cons pred operMode exp) =
  (if f (pred, operMode) 
    then Cons pred operMode (al_filter f exp)
    else al_filter f exp)"

definition al_h_1 :: 
  "('a::activation_language_algebra, 'o) activationLogic \<Rightarrow> 
  ('a, 'o) activationLogic" where
"al_h_1 exp = al_filter (\<lambda>t. \<not> contradiction (fst t)) exp"

primrec tau_al_h_2 :: 
  "('a::activation_language_algebra, 'o) activationLogic \<Rightarrow> 'a" where
"tau_al_h_2 (Term pred _) = compl pred" |
"tau_al_h_2 (Cons pred _ exp) = inf (compl pred) (tau_al_h_2 exp)"

definition al_h_2 :: 
  "('a::activation_language_algebra, 'o) activationLogic \<Rightarrow> 
  ('a, 'o) activationLogic" where
"al_h_2 exp = (let tau = (tau_al_h_2 exp) in
  if contradiction tau then exp 
  else Cons tau (Nominal None) exp)"

primrec al_concat :: 
  "('a::activation_language_algebra, 'o) activationLogic \<Rightarrow>
  ('a, 'o) activationLogic \<Rightarrow>
  ('a, 'o) activationLogic" where
"al_concat (Term pred operMode) exp = Cons pred operMode exp" |
"al_concat (Cons pred operMode exp1) exp2 = 
  Cons pred operMode (al_concat exp1 exp2)"

primrec al_pred :: "
  ('a::activation_language_algebra, 'o) activationLogic \<Rightarrow>
  'o OperationalMode \<Rightarrow> 'a" where
"al_pred (Term pred operMode) operMode_x = 
  (if operMode = operMode_x then pred else bot)" |
"al_pred (Cons pred operMode exp) operMode_x = 
  (if operMode = operMode_x 
    then sup pred (al_pred exp operMode_x)
    else al_pred exp operMode_x)"

primrec al_modes :: "
  ('a::activation_language_algebra, 'o) activationLogic \<Rightarrow>
  'a \<Rightarrow> ('a, 'o) activationLogic" where
"al_modes (Term pred operMode) pred_x = 
  (Term (inf pred pred_x) operMode)" |
"al_modes (Cons pred operMode exp) pred_x = 
  Cons (inf pred pred_x) operMode (al_modes exp pred_x)"

primrec al_activation :: "
  ('a::activation_language_algebra, 'o) activationLogic \<Rightarrow>
  'a \<Rightarrow> 'o OperationalMode set" where
"al_activation (Term pred operMode) pred_x = 
  (if tautology (implies pred_x pred) then { operMode } else {})" |
"al_activation (Cons pred operMode exp) pred_x = 
  (if tautology (implies pred_x pred) 
    then { operMode } \<union> (al_activation exp pred_x)
    else al_activation exp pred_x)"


end