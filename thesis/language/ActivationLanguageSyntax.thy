theory ActivationLanguageSyntax

imports 
  Main
  "~~/src/HOL/Library/Dlist"
begin

class activation_language_algebra =
  fixes al_bot :: "'a"
  fixes al_top :: "'a"
  fixes al_not :: "'a \<Rightarrow> 'a"
  fixes al_or :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes al_and :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes tautology :: "'a \<Rightarrow> bool"
  fixes contradiction :: "'a \<Rightarrow> bool"
  fixes eval :: "'a \<Rightarrow> bool"

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
    else Term al_bot (Nominal None))" |
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
"tau_al_h_2 (Term pred _) = al_not pred" |
"tau_al_h_2 (Cons pred _ exp) = al_and (al_not pred) (tau_al_h_2 exp)"

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

primrec operMode_absorb :: "('a \<times> 'o OperationalMode) \<Rightarrow> 
  ('a::activation_language_algebra, 'o) activationLogic \<Rightarrow>
  ('a, 'o) activationLogic" where
"operMode_absorb t (Term pred operMode) = 
  (if snd t = operMode 
    then Term (al_or pred (fst t)) operMode
    else Term pred operMode)" |
"operMode_absorb t (Cons pred operMode exp) = 
  (if snd t = operMode 
    then Cons (al_or pred (fst t)) operMode 
      (operMode_absorb t exp)
    else Cons pred operMode (operMode_absorb t exp)) "

primrec al_h_3_aux :: "
  ('a::activation_language_algebra, 'o) activationLogic \<Rightarrow> 
  ('a, 'o) activationLogic \<Rightarrow>
  ('a, 'o) activationLogic" where
"al_h_3_aux (Term pred operMode) exp2 = "

definition al_h_3 :: 
  "('a::activation_language_algebra, 'o) activationLogic \<Rightarrow> 
  ('a, 'o) activationLogic" where
"al_h_3 exp = al_concat (al_filter () exp) ()"
(*
Semantics
typedef ('a, 'o) activationLogic = 
  "UNIV::('a:: activation_language_algebra \<times> 'o) dlist set"
*)

end