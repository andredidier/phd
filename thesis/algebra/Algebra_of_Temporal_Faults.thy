section {* \Acl*{algebra}  *}
text {* \label{sec:theory-algebra} *}

(*<*)
theory Algebra_of_Temporal_Faults
imports Main 
begin
(*>*)

text {* 
In the following we present the algebraic laws for the \ac{algebra}. 
*}
(*
notation 
  inf (infixl "\<and>" 40) and
  sup (infixl "\<or>" 35) and
  bot ("\<bottom>") and
  top ("\<top>") and
  uminus ("\<not>") and
  xbefore (infixr "\<rightarrow>" 5) and
  tempo1 ("tempo\<^sub>1 _" 10) and
  tempo2 ("tempo\<^sub>2 _" 10) and
  tempo3 ("tempo\<^sub>3 _" 10) and
  tempo4 ("tempo\<^sub>4 _" 10) and
  neutral ("\<one>") and
  independent_events (infixl "\<triangleleft>\<triangleright>" 9)
*)

subsection {* Basic \ac{algebra} operators and $\tempo[1]{}$ *}

class algebra_of_temporal_faults_basic = boolean_algebra  +
  fixes neutral :: "'a" 
  fixes xbefore :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  
  fixes tempo1 :: "'a \<Rightarrow> bool"  
  assumes xbefore_bot_1: "xbefore bot a = bot"
  assumes xbefore_bot_2: "xbefore a bot = bot"
  assumes xbefore_neutral_1: "tempo1 a \<Longrightarrow> xbefore neutral a = a"
  assumes xbefore_neutral_2: "tempo1 a \<Longrightarrow> xbefore a neutral = a"
  assumes xbefore_not_idempotent: "tempo1 a \<Longrightarrow> xbefore a a = bot"
  assumes inf_tempo1: "\<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> tempo1 (inf a b)"
  assumes xbefore_not_sym: 
    "\<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> (xbefore a b) \<le> -(xbefore b a)"

subsection {* Definition of associativity of \ac{XBefore} *}
    
class algebra_of_temporal_faults_assoc = algebra_of_temporal_faults_basic +
  assumes xbefore_assoc: "\<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> 
    xbefore (xbefore a b) c = xbefore a (xbefore b c)"

subsection {* Equivalences in the \ac{algebra} and properties *}
    
class algebra_of_temporal_faults_equivs = algebra_of_temporal_faults_assoc +
  fixes independent_events :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  fixes tempo2 :: "'a \<Rightarrow> bool" 
  fixes tempo3 :: "'a \<Rightarrow> bool" 
  fixes tempo4 :: "'a \<Rightarrow> bool" 
  assumes xbefore_inf_equiv_bot: 
    "\<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> inf (xbefore a b) (xbefore b a) = bot"
  assumes xbefore_sup_equiv_inf: 
    "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow> 
    sup (xbefore a b) (xbefore b a) = inf a b"
  assumes sup_tempo2: "\<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> tempo2 (sup a b)"
  assumes inf_tempo3: "\<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> tempo3 (inf a b)"
  assumes sup_tempo4: "\<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow> tempo4 (sup a b)"

abbreviation tempo :: "'a::algebra_of_temporal_faults_equivs  \<Rightarrow> bool" where
"tempo a \<equiv> tempo1 a \<and> tempo2 a \<and> tempo3 a \<and> tempo4 a"

subsection {* \Ac{XBefore} transitivity *}

class algebra_of_temporal_faults_trans = algebra_of_temporal_faults_equivs +
  assumes xbefore_trans: 
    "\<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo2 a; tempo2 b; tempo2 c\<rbrakk> \<Longrightarrow>
    less_eq (inf (xbefore a b) (xbefore b c)) (xbefore a c)"
  assumes inf_xbefore_trans: "\<lbrakk> tempo1 b; tempo3 b \<rbrakk> \<Longrightarrow>
    inf (xbefore a b) (xbefore b c) = xbefore (xbefore a b) c"

subsection {* Mixed operators in \ac{algebra} *}

class algebra_of_temporal_faults_mixed_ops = algebra_of_temporal_faults_trans +
  assumes xbefore_sup_1: 
    "xbefore (sup a b) c = sup (xbefore a c) (xbefore b c)"
  assumes xbefore_sup_2: 
    "xbefore a (sup b c) = sup (xbefore a b) (xbefore a c)"
  assumes not_xbefore: "
    independent_events a b \<Longrightarrow>
    \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow>
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow>
    \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow>
    \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    - (xbefore a b) = sup (sup (- a) (- b)) (xbefore b a)"
  assumes inf_xbefore_equiv_sups_xbefore: "tempo2 a \<Longrightarrow> 
    inf a (xbefore b c) = sup (xbefore (inf a b) c) (xbefore b (inf a c))"
  assumes not_1_xbefore_equiv: "\<lbrakk>tempo1 a; tempo2 b \<rbrakk> \<Longrightarrow> xbefore (- a) b = b"
  assumes not_2_xbefore_equiv: "\<lbrakk>tempo1 b; tempo2 a \<rbrakk> \<Longrightarrow> xbefore a (- b) = a"

class algebra_of_temporal_faults = algebra_of_temporal_faults_mixed_ops

subsection {* Theorems in the context of \ac{algebra} *}

text {* 
The following theorems are valid for \ac{algebra}.
They are valid for any instantiation of the \ac{algebra} class as, for example, for the sets of distinct lists type.
*}

context algebra_of_temporal_faults
begin

text {* The following theorem proves \cref{thm:xbefore-inf-1}. *}
theorem xbefore_inf_1: 
  "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
  \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow> 
  xbefore (inf a b) c = 
    sup (xbefore (xbefore a b) c) (xbefore (xbefore b a) c)"
proof-
  assume "independent_events a b" "tempo1 a" "tempo1 b" 
  "tempo2 a" "tempo2 b" "tempo3 a" "tempo3 b" "tempo4 a" "tempo4 b"
  hence "xbefore (inf a b) c = xbefore (sup (xbefore a b) (xbefore b a)) c"
    by (simp add: xbefore_sup_equiv_inf)
  thus ?thesis by (simp add: xbefore_sup_1)
qed

text {* The following theorem proves \cref{thm:xbefore-inf-2}. *}
theorem xbefore_inf_2: 
  "independent_events b c \<Longrightarrow> \<lbrakk>tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> 
  \<lbrakk>tempo2 b; tempo2 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 b; tempo3 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 b; tempo4 c\<rbrakk> \<Longrightarrow> 
  xbefore a (inf b c) = 
    sup (xbefore a (xbefore b c)) (xbefore a (xbefore c b))"
proof-
  assume "independent_events b c" "tempo1 b" "tempo1 c" "tempo2 b" "tempo2 c" 
  "tempo3 b" "tempo3 c" "tempo4 b" "tempo4 c"
  hence "xbefore a (inf b c) = xbefore a (sup (xbefore b c) (xbefore c b))"
    by (simp add: xbefore_sup_equiv_inf)
  thus ?thesis by (simp add: xbefore_sup_2)
qed

text {* The following lemma proves \cref{thm:xbefore-sup-absorb-2}. *}
lemma xbefore_sup_absorb_1b: 
  "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    sup (xbefore b a) a = a"
by (metis inf_le1 order_trans sup.absorb2 sup.cobounded2 
  xbefore_sup_equiv_inf)

lemma xbefore_sup_absorb_2: 
  "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    sup a (xbefore a b) = a"
by (metis dual_order.trans inf.cobounded1 sup.absorb1 sup.cobounded1 
  xbefore_sup_equiv_inf)

text {* The following corollary proves \cref{thm:xbefore-sup-absorb-1}. *}
corollary xbefore_sup_absorb_1: 
  "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    sup (xbefore a b) a = a"
proof-
  assume 0: "independent_events a b" "tempo1 a" "tempo1 b" "tempo2 a" 
  "tempo2 b" "tempo3 a" "tempo3 b" "tempo4 a" "tempo4 b"
  hence "sup a (xbefore a b) = sup (xbefore a b) a" 
    by (simp add: sup.commute)
  thus ?thesis using 0 by (simp add: xbefore_sup_absorb_2)
qed

corollary xbefore_sup_absorb_2b: 
  "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    sup a (xbefore b a) = a"
proof-
  assume 0: "independent_events a b" "tempo1 a" "tempo1 b" "tempo2 a" 
  "tempo2 b" "tempo3 a" "tempo3 b" "tempo4 a" "tempo4 b"
  hence "sup a (xbefore b a) = sup (xbefore b a) a" 
    by (simp add: sup.commute)
  thus ?thesis using 0 by (simp add: xbefore_sup_absorb_1b)
qed

text {* The following corollary proves \cref{thm:xbefore_inf_absorb_1}. *}
theorem xbefore_inf_absorb_1: "independent_events a b \<Longrightarrow> 
  \<lbrakk> tempo1 a; tempo1 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo2 a; tempo2 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo3 a; tempo3 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo4 a; tempo4 b \<rbrakk> \<Longrightarrow>
  inf a (xbefore a b) = xbefore a b"
by (simp add: local.inf_absorb2 local.le_iff_sup xbefore_sup_absorb_1)

text {* The following corollary proves \cref{thm:xbefore_inf_absorb_2}. *}
theorem xbefore_inf_absorb_2: "independent_events a b \<Longrightarrow> 
  \<lbrakk> tempo1 a; tempo1 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo2 a; tempo2 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo3 a; tempo3 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo4 a; tempo4 b \<rbrakk> \<Longrightarrow>
  inf a (xbefore b a) = xbefore b a"
by (simp add: local.inf.absorb2 local.sup.absorb_iff1 xbefore_sup_absorb_2b)

text {* The following lemma proves \cref{thm:and_xbefore_equiv_or_xbefore_expanded}. *}
lemma inf_xbefore_equiv_sups_xbefore_expanded: 
  "independent_events a b \<Longrightarrow> independent_events a c \<Longrightarrow> 
  \<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo2 a; tempo2 b; tempo2 c\<rbrakk> \<Longrightarrow> 
  \<lbrakk>tempo3 a; tempo3 b; tempo3 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b; tempo4 c\<rbrakk> \<Longrightarrow> 
    inf a (xbefore b c) = 
    sup (sup (xbefore (xbefore a b) c) 
      (xbefore (xbefore b a) c)) 
      (xbefore (xbefore b c) a)"
proof-
  assume "independent_events a b" "independent_events a c" 
    "tempo1 a" "tempo1 b" "tempo1 c" 
    "tempo2 a" "tempo2 b" "tempo2 c" 
    "tempo3 a" "tempo3 b" "tempo3 c"
    "tempo4 a" "tempo4 b" "tempo4 c"
  hence "inf a (xbefore b c) = 
    sup (xbefore (inf a b) c) (xbefore b (inf a c))"
    "xbefore (inf a b) c = 
    sup (xbefore (xbefore a b) c) (xbefore (xbefore b a) c)"
    "xbefore b (inf a c) = 
    sup (xbefore (xbefore b a) c) (xbefore (xbefore b c) a)"
    by (auto simp add: inf_xbefore_equiv_sups_xbefore xbefore_inf_1 
      xbefore_inf_2 xbefore_assoc)
  thus ?thesis by (simp add: sup.assoc)
qed
text {* The following lemma proves \cref{thm:xbefore_sup_compl_inf_absorb1}. *}
lemma xbefore_sup_compl_inf_absorb1: 
  "independent_events a b \<Longrightarrow> \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> 
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    sup (inf a (-b)) (xbefore a b) = inf a (- (xbefore b a))"
proof -
  assume a1: "independent_events a b"
  assume a2: "tempo1 a"
  assume a3: "tempo1 b"
  assume a4: "tempo2 a"
  assume a5: "tempo2 b"
  assume a6: "tempo3 a"
  assume a7: "tempo3 b"
  assume a8: "tempo4 a"
  assume a9: "tempo4 b"
  then have f10: "- xbefore a b = sup (sup (- a) (- b)) (xbefore b a)"
    using a8 a7 a6 a5 a4 a3 a2 a1 by (meson local.not_xbefore)
  have f11: "\<forall>a aa ab. inf (a::'a) (sup aa ab) = sup (inf a aa) (inf a ab)"
    using local.distrib_imp2 local.sup_inf_distrib1 by force
  then have f12: "sup bot (xbefore b a) = inf b (sup (- b) (xbefore b a))"
    using a7 a3 by (metis local.inf_compl_bot local.inf_xbefore_trans local.xbefore_neutral_1)
  have f13: "inf (sup (- a) (- (- b))) (sup (- a) (- b)) = sup (- a) (inf b (- b))"
    using local.double_compl local.sup_inf_distrib1 by presburger
  have f14: "inf a (xbefore b a) = xbefore b a"
    using a9 a8 a7 a6 a5 a4 a3 a2 a1 by (meson xbefore_inf_absorb_2)
  have f15: "sup (sup (inf (sup (- a) (- b)) (- a)) (inf (xbefore b a) (- a))) bot = sup (- a) (inf b (- b))"
    using f10 a9 a8 a7 a6 a5 a4 a3 a2 a1 by (metis (no_types) local.compl_sup local.inf_compl_bot local.inf_sup_distrib2 xbefore_sup_absorb_1)
  have "inf a (- a) = sup (inf (xbefore b a) (- a)) bot"
    using f14 f11 by (metis (no_types) local.compl_inf local.inf_compl_bot)
  then have "sup (- sup (- a) (- (- b))) (- sup (- a) (- b)) = - inf (sup (sup (- a) (- b)) a) (- a)"
    using f15 f13 by (metis (full_types) local.compl_inf local.inf_sup_distrib2 local.sup_assoc)
  then have "sup (- sup (- a) (- (- b))) (- sup (- a) (- b)) = a"
    by (simp add: local.sup_assoc)
  then show ?thesis
    using f13 f12 f10 by (metis (no_types) local.compl_inf local.compl_sup local.double_compl local.inf_compl_bot local.sup_assoc local.sup_inf_distrib1)
qed

corollary xbefore_sup_equiv_inf_inf_nand: 
  "tempo a \<Longrightarrow> tempo b \<Longrightarrow> independent_events a b \<Longrightarrow> 
  sup (sup (xbefore a b) (xbefore b a)) (uminus (inf a b)) = top"
by (metis (mono_tags, lifting) boolean_algebra_class.sup_compl_top algebra_of_temporal_faults_equivs_class.xbefore_sup_equiv_inf)



end


end
(*>*)