theory ConditionalMode

imports ModeCondition Complex_Main FaultModellingTypes

begin

datatype_new ('a, 'b) ConditionalValue = 
  CVC (V: 'b)
  | CVIF 'a "('a, 'b) ConditionalValue" "('a, 'b) ConditionalValue" 

datatype_new ('a, 'b) CVPredicate = 
  CVPVar 'a
  | CVPEQ "('a, 'b) ConditionalValue" "'b"

datatype_new ('FMode, 'vv) OperationalMode = 
  NominalMode real 
  | FailureMode "'FMode"
  | VarMode (var: 'vv)

type_synonym ('a, 'FMode, 'vv) ConditionalMode = 
  "('a, ('FMode, 'vv) OperationalMode) ConditionalValue"

notation (output) NominalMode ("N\<langle>_\<rangle>" 40)
notation (output) FailureMode ("F\<langle>_\<rangle>" 41)
notation (output) VarMode ("_" 41)
notation (output) CVC  ("_" 50)
notation (output) CVIF ("_ \<surd> _ \<oslash> _" 80)

primrec val_ConditionalValue :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 'b" where
"val_ConditionalValue _ (CVC b) = b" |
"val_ConditionalValue s (CVIF a t1 t2) = 
  (if s a then val_ConditionalValue s t1 else val_ConditionalValue s t2)"

type_synonym 'a ConditionalValueEnv = "('a * bool) list"

definition agree :: "('a \<Rightarrow> bool) \<Rightarrow> 'a ConditionalValueEnv \<Rightarrow> bool" where
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

definition mkIF :: "'a \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 
  ('a, 'b) ConditionalValue" where
"mkIF x t1 t2 = (if t1 = t2 then t1 else CVIF x t1 t2)"

fun reduce :: "'a ConditionalValueEnv \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 
  ('a, 'b) ConditionalValue" where
"reduce env (CVIF x t1 t2) = (case map_of env x of
     None \<Rightarrow> mkIF x (reduce ((x,True)#env) t1) (reduce ((x,False)#env) t2) |
     Some b \<Rightarrow> reduce env (if b then t1 else t2))" |
"reduce _ t = t"

primrec normif :: "'a ConditionalValueEnv \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 
  ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue" where
"normif env (CVC b) t1 t2 = CVC b" |
"normif env (CVIF x t1 t2) t3 t4 =
  (case map_of env x of
     None \<Rightarrow> mkIF x (normif ((x,True) # env) t1 t3 t4) (normif ((x,False) # env) t2 t3 t4) |
     Some b \<Rightarrow> if b then normif env t1 t3 t4 else normif env t2 t3 t4)"

lemma val_mkIF: "val_ConditionalValue s (mkIF x t1 t2) = val_ConditionalValue s (CVIF x t1 t2)"
apply (auto simp: mkIF_def Let_def)
done

theorem val_reduce: "agree s env \<Longrightarrow> distinct(map fst env) \<Longrightarrow>
  val_ConditionalValue s (reduce env t) = val_ConditionalValue s t"
apply(induct t arbitrary: s env)
apply(auto simp: map_of_eq_None_iff val_mkIF agree_Cons Let_def
  dest: agreeDT agreeDF split: option.splits)
done

fun reduced :: "('a, 'b) ConditionalValue \<Rightarrow> 'a set \<Rightarrow> bool" where
"reduced (CVIF x t1 t2) X =
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
  case (CVIF x t1 t2)
  thus ?case using CVIF.IH(1)[of "(x, True) # env"] CVIF.IH(2)[of "(x, False) # env"]
    by(auto simp: map_of_eq_None_iff image_iff reduced_mkIF split: option.split)
qed auto

lemma reduced_normif:
  "distinct(map fst env) \<Longrightarrow> reduced (normif env t t1 t2) (fst ` set env)"
proof(induction t arbitrary: t1 t2 env)
  case (CVIF x s1 s2)
  thus ?case using CVIF.IH(1)[of "(x, True) # env"] CVIF.IH(2)[of "(x, False) # env"]
    by(auto simp: reduced_mkIF map_of_eq_None_iff split: option.split)
qed (auto simp: reduced_reduce)

lemma same_val_if_reduced:
  "reduced t X \<Longrightarrow> \<forall>x. x \<notin> X \<longrightarrow> s1 x = s2 x \<Longrightarrow> 
  val_ConditionalValue s1 t = val_ConditionalValue s2 t"
by(induction t arbitrary: X) auto
(*
primrec ConditionalValuePredicate :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> 'b \<Rightarrow>
  ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue \<Rightarrow> ('a, 'b) ConditionalValue"
where
  "ConditionalValuePredicate P\<^sub>b (CVC b1) b2 t1 t2 = (if P\<^sub>b b1 b2 then t1 else t2)" |
  "ConditionalValuePredicate P\<^sub>b (CVIF a t1 t2) b t3 t4 = "
*)
end
