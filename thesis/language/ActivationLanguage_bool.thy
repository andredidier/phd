theory ActivationLanguage_bool
imports Lattices ActivationLanguageSyntax
  "../Boolean_Expression_Checkers/Boolean_Expression_Checkers"
begin

section \<open>Boolean expression\<close>

text \<open>Copied from Boolean_Expression_Example\<close>

datatype 'a bexp =
  Const bool |
  Atom 'a |
  Neg "'a bexp" |
  And "'a bexp" "'a bexp"

fun bval where
"bval (Const b) s = b" |
"bval (Atom a) s = s a" |
"bval (Neg b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"

subsection \<open>Indirect Translation using the Boolean Expression Interface\<close> 

text \<open>Now we translate into @{datatype bool_expr} provided by the checkers interface and show that the 
  semantics remains the same:\<close>

fun bool_expr_of_bexp :: "'a bexp \<Rightarrow> 'a bool_expr" 
where
  "bool_expr_of_bexp (Const b) = Const_bool_expr b" 
| "bool_expr_of_bexp (Atom a) = Atom_bool_expr a" 
| "bool_expr_of_bexp (Neg b) = Neg_bool_expr(bool_expr_of_bexp b)" 
| "bool_expr_of_bexp (And b1 b2) = And_bool_expr (bool_expr_of_bexp b1) (bool_expr_of_bexp b2)"

lemma val_preservation: 
  "val_bool_expr (bool_expr_of_bexp b) s = bval b s"
  by (induction b) auto 

definition "my_taut_test_bool = bool_taut_test o bool_expr_of_bexp"
definition "my_sat_test_bool = bool_sat_test o bool_expr_of_bexp"

corollary my_taut_test: 
  "my_taut_test_bool b = (\<forall>s. bval b s)"
  by (simp add: my_taut_test_bool_def val_preservation bool_tests)

subsection \<open>Direct Translation into Reduced Binary Decision Trees\<close> 

text \<open>Now we translate into a reduced binary decision tree, show that the semantics remains the same and 
  the tree is reduced:\<close>

fun ifex_of :: "'a bexp \<Rightarrow> 'a ifex" 
where
  "ifex_of (Const b) = (if b then Trueif else Falseif)" 
| "ifex_of (Atom a) = IF a Trueif Falseif" 
| "ifex_of (Neg b)   = normif Mapping.empty (ifex_of b) Falseif Trueif" 
| "ifex_of (And b1 b2) = normif Mapping.empty (ifex_of b1) (ifex_of b2) Falseif"

lemma val_ifex: 
  "val_ifex (ifex_of b) s = bval b s"
  by (induction b) (simp_all add: agree_Nil val_normif)

theorem reduced_ifex: 
  "reduced (ifex_of b) {}"
  by (induction b) (simp; metis keys_empty reduced_normif)+

definition "my_taut_test_ifex = taut_test ifex_of"

corollary my_taut_test_ifex: 
  "my_taut_test_ifex b = (\<forall>s. bval b s)"
proof -
  interpret reduced_bdt_checkers ifex_of bval
    by (unfold_locales; insert val_ifex reduced_ifex; blast)
  show ?thesis
    by (simp add: my_taut_test_ifex_def taut_test)
qed

instantiation bexp :: (type) activation_language_algebra
begin

definition
  "bot_bexp = Const False"

definition
  "compl_bexp x = (Neg x)"

definition
  "inf_bexp x y = (And x y)"

definition
  "tautology_bexp x = my_taut_test_bool x"

definition
  "contradiction_bexp x = (\<not> my_sat_test_bool x)"
 
instance proof
qed 
end

end