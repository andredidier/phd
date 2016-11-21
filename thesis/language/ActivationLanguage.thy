theory ActivationLanguage

imports Complex_Main
begin

section {* A term in the language  *}

class term_predicate = boolean_algebra +
  fixes implies_bool :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

instantiation bool :: term_predicate
begin
  definition
    "implies_bool a b = (a \<longrightarrow> b)"
instance proof  
qed
end

datatype ('n, 'f) Mode = 
  Nominal "'n option" |
  Failure 'f

typedef ('e::term_predicate, 'n, 'f) Expression = 
  "UNIV::(('e \<times> (('n, 'f) Mode)) list set)" by simp

abbreviation Expression_to_predicate_list :: 
  "('e::term_predicate, 'n, 'f) Expression \<Rightarrow> 'e list" where
  "Expression_to_predicate_list E \<equiv> map fst (Rep_Expression E)"

subsection {* Healthiness 1 *}

primrec h1_aux1 :: 
  "('e::term_predicate \<times> ('n, 'f) Mode) \<Rightarrow> ('e \<times> ('n, 'f) Mode) list \<Rightarrow> 
    ('e \<times> ('n, 'f) Mode) list" where
"h1_aux1 _ [] = []" |
"h1_aux1 t1 (t2 # E) = 
  (if implies_bool (fst t2) (fst t1) then 
    (if snd t1 = snd t2 
      then h1_aux1 t1 E 
      else (inf (fst t1) (- (fst t2)), snd t2) # h1_aux1 t1 E) 
    else t2 # h1_aux1 t1 E
  )"

definition Expression_healthiness_1 :: 
  "('e::term_predicate, 'n, 'f) Expression \<Rightarrow> bool" ("H\<^sub>1") where
  "Expression_healthiness_1 E = 
    (\<forall> (p1,m1) \<in> set (Rep_Expression E). 
    (\<forall> (p2,m2) \<in> set (Rep_Expression E). 
      implies p1 p2 \<longrightarrow> m1 = m2 ))"

subsection {* Healthiness 2 *}

definition Expression_healthiness_2 :: 
  "('e::term_predicate, 'n, 'f) Expression \<Rightarrow> 
    ('e::term_predicate, 'n, 'f) Expression" ("H\<^sub>2") where
  "Expression_healthiness_2 E = 
    (let missing = 
      (not (fold or (Expression_to_predicate_list E) term_false), Nominal None)
      in Abs_Expression (missing # (Rep_Expression E)))"


subsection {* Healthiness condition *}

definition Expression_healthiness ("H") where 
  "Expression_healthiness = H\<^sub>1 \<circ> H\<^sub>2"

(* ======= ANTIGO*)

text {* It's the main datatype for the theories.  *}
datatype ('a, 'b) IfValue =
  Value 'b
  | If 'a "('a, 'b) IfValue" "('a, 'b) IfValue"

text {* An IfValue as a @{term "boolean_algebra"}*}

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

primrec IfValue2boolean_algebra :: 
  "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c::boolean_algebra) \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> 'c"
where
  "IfValue2boolean_algebra f _ (Value b) = (if f b then \<top> else \<bottom>)" |
  "IfValue2boolean_algebra f g (If a t e) =
    (g a \<sqinter> (IfValue2boolean_algebra f g t)) \<squnion> (- g a \<sqinter> IfValue2boolean_algebra f g e)"


no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

type_synonym 'a IfValueEnv = "('a * bool) list"

definition agree :: "('a \<Rightarrow> bool) \<Rightarrow> 'a IfValueEnv \<Rightarrow> bool" where
"agree s env = (\<forall>x b. map_of env x = Some b \<longrightarrow> s x = b)"

lemma agree_Nil: "agree s []"
by(simp add: agree_def)

lemma agree_Cons: "distinct(map fst env) \<Longrightarrow> x \<notin> set(map fst env)
  \<Longrightarrow> agree s ((x,b) # env) = ((if b then s x else \<not> s x) \<and> agree s env)"
by(auto simp: agree_def image_iff)

lemma agreeDT:
  "\<lbrakk> agree s env; distinct (map fst env) \<rbrakk> \<Longrightarrow> (x,True) \<in> set env \<Longrightarrow> s x"
by(simp add: agree_def)

lemma agreeDF:
  "\<lbrakk> agree s env; distinct (map fst env) \<rbrakk> \<Longrightarrow> (x,False) \<in> set env \<Longrightarrow> \<not> s x"
by(simp add: agree_def)

definition mkIF :: "'a \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> 
  ('a, 'b) IfValue" where
"mkIF x t1 t2 = (if t1 = t2 then t1 else If x t1 t2)"

fun reduce :: "'a IfValueEnv \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> 
  ('a, 'b) IfValue" where
"reduce env (If x t1 t2) = (case map_of env x of
     None \<Rightarrow> mkIF x (reduce ((x,True)#env) t1) (reduce ((x,False)#env) t2) |
     Some b \<Rightarrow> reduce env (if b then t1 else t2))" |
"reduce _ t = t"

primrec normif :: "'a IfValueEnv \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> 
  ('a, 'b) IfValue \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> ('a, 'b) IfValue" where
"normif env (Value b) t1 t2 = Value b" |
"normif env (If x t1 t2) t3 t4 =
  (case map_of env x of
     None \<Rightarrow> mkIF x (normif ((x,True) # env) t1 t3 t4) (normif ((x,False) # env) t2 t3 t4) |
     Some b \<Rightarrow> if b then normif env t1 t3 t4 else normif env t2 t3 t4)"

fun reduced :: "('a, 'b) IfValue \<Rightarrow> 'a set \<Rightarrow> bool" where
"reduced (If x t1 t2) X =
  (x \<notin> X \<and> t1 \<noteq> t2 \<and> reduced t1 (insert x X) \<and> reduced t2 (insert x X))" |
"reduced _ _ = True"

lemma reduced_antimono: "X \<subseteq> Y \<Longrightarrow> reduced t Y \<Longrightarrow> reduced t X"
apply(induction t arbitrary: X Y)
by auto (metis insert_mono)+

lemma reduced_mkIF: "x \<notin> X \<Longrightarrow>
  reduced t1 (insert x X) \<Longrightarrow> reduced t2 (insert x X) \<Longrightarrow> reduced (mkIF x t1 t2) X"
by(auto simp: mkIF_def intro:reduced_antimono)

lemma reduced_reduce:
  "distinct(map fst env) \<Longrightarrow> reduced (reduce env t) (fst ` set env)"
proof(induction t arbitrary: env)
  case (If x t1 t2)
  thus ?case using If.IH(1)[of "(x, True) # env"] If.IH(2)[of "(x, False) # env"]
    by(auto simp: map_of_eq_None_iff image_iff reduced_mkIF split: option.split)
qed auto

lemma reduced_normif:
  "distinct(map fst env) \<Longrightarrow> reduced (normif env t t1 t2) (fst ` set env)"
proof(induction t arbitrary: t1 t2 env)
  case (If x s1 s2)
  thus ?case using If.IH(1)[of "(x, True) # env"] If.IH(2)[of "(x, False) # env"]
    by(auto simp: reduced_mkIF map_of_eq_None_iff split: option.split)
qed (auto simp: reduced_reduce)

subsection {* Introducing operation modes and activation expression. *}

datatype ('f, 'a) OperationalMode =
  Nominal real
  | Failure 'f
  | Var 'a

type_synonym ('a, 'f, 'b) ActivationExpression =
  "('a, ('f, 'b) OperationalMode) IfValue"

subsection {* Value and Reduction comparison *}

primrec val_IfValue :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> 'b"
where
  "val_IfValue _ (Value v) = v" |
  "val_IfValue active (If a t e) = 
    (if active a then val_IfValue active t else val_IfValue active e)"

lemma val_mkIF: "val_IfValue s (mkIF x t1 t2) = val_IfValue s (If x t1 t2)"
apply (auto simp: mkIF_def Let_def)
done

theorem val_reduce: "agree s env \<Longrightarrow> distinct(map fst env) \<Longrightarrow>
  val_IfValue s (reduce env t) = val_IfValue s t"
apply(induct t arbitrary: s env)
apply(auto simp: map_of_eq_None_iff val_mkIF agree_Cons Let_def
  dest: agreeDT agreeDF split: option.splits)
done

lemma same_val_if_reduced:
  "reduced t X \<Longrightarrow> \<forall>x. x \<notin> X \<longrightarrow> s1 x = s2 x \<Longrightarrow> 
  val_IfValue s1 t = val_IfValue s2 t"
by(induction t arbitrary: X) auto


subsection {* Introducing if-value-predicates. *}

primrec IfValuePredicate :: "('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> 
  ('a, 'b) IfValue \<Rightarrow> ('a, 'b) IfValue \<Rightarrow> ('a, 'b) IfValue"
where
  "IfValuePredicate P (Value b) t1 t2 = (if P b then t1 else t2)" |
  "IfValuePredicate P (If a t1 t2) t3 t4 = 
    If a (IfValuePredicate P t1 t3 t4) (IfValuePredicate P t2 t3 t4)"

notation (output) IfValuePredicate ("_\<^sub>P \<surd> _ \<oslash> _" 80)

fun nominal_op :: 
  "('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> 
  (real \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow>
  (('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> bool) \<Rightarrow> bool" 
where
  "nominal_op (Nominal a) (Nominal b) f _ = (f a b)" |
  "nominal_op (Failure _) (Nominal _) _ _ = False" |
  "nominal_op (Nominal _) (Failure _) _ _ = False" |
  "nominal_op a b _ g = (g a b)"

definition lte_Values :: "('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> bool"
where
  "lte_Values a b \<equiv> nominal_op a b (op \<le>) (op =)"

abbreviation gte_Values :: "('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> bool" 
where
  "gte_Values a b \<equiv> lte_Values b a"

definition lt_Values :: "('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> bool"
where
  "lt_Values a b \<equiv> nominal_op a b (op <) (\<lambda> _ _. False)"

abbreviation gt_Values :: "('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> bool"
where
  "gt_Values a b \<equiv> lt_Values b a"

abbreviation eq_Values :: "('f, 'b) OperationalMode \<Rightarrow> ('f, 'b) OperationalMode \<Rightarrow> bool"
where
  "eq_Values a b \<equiv> (a = b)"

notation (output) lte_Values  (infix "\<le>" 50)
notation (output) gte_Values  (infix "\<ge>" 50)
notation (output) lt_Values  (infix "<" 50)
notation (output) gt_Values  (infix ">" 50)
notation (output) eq_Values  (infix "=" 50)

end
