section {* \Acl*{algebra}  *}
text {* \label{sec:theory-algebra} *}

(*<*)
theory Temporal_Faults_Algebra
imports Main 
begin
(*>*)

text {* 
In the following we present the algebraic laws for the \ac{algebra}. 
*}

subsection {* Basic \ac{algebra} operators and tempo1 *}

class temporal_faults_algebra_neutral = boolean_algebra +
  fixes neutral :: "'a"

class temporal_faults_algebra_basic = temporal_faults_algebra_neutral +
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
    
class temporal_faults_algebra_assoc = temporal_faults_algebra_basic +
  assumes xbefore_assoc: "\<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> 
    xbefore (xbefore a b) c = xbefore a (xbefore b c)"

subsection {* Equivalences in the \ac{algebra} and properties *}
    
class temporal_faults_algebra_equivs = temporal_faults_algebra_assoc +
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

subsection {* \Ac{XBefore} transitivity *}

class temporal_faults_algebra_trans = temporal_faults_algebra_equivs +
  assumes xbefore_trans: 
    "\<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo2 a; tempo2 b; tempo2 c\<rbrakk> \<Longrightarrow>
    less_eq (inf (xbefore a b) (xbefore b c)) (xbefore a c)"

subsection {* Mixed operators in \ac{algebra} *}

class temporal_faults_algebra_mixed_ops = temporal_faults_algebra_trans +
  assumes xbefore_sup_1: 
    "xbefore (sup a b) c = sup (xbefore a c) (xbefore b c)"
  assumes xbefore_sup_2: 
    "xbefore a (sup b c) = sup (xbefore a b) (xbefore a c)"
  assumes xbefore_not: "
    independent_events a b \<Longrightarrow>
    \<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow>
    \<lbrakk>tempo2 a; tempo2 b\<rbrakk> \<Longrightarrow>
    \<lbrakk>tempo3 a; tempo3 b\<rbrakk> \<Longrightarrow>
    \<lbrakk>tempo4 a; tempo4 b\<rbrakk> \<Longrightarrow>
    - (xbefore a b) = sup (sup (- a) (- b)) (xbefore b a)"
  assumes inf_xbefore_equiv_sups_xbefore: "tempo2 a \<Longrightarrow> inf a (xbefore b c) = 
    sup (xbefore (inf a b) c) (xbefore b (inf a c))"


class temporal_faults_algebra = temporal_faults_algebra_mixed_ops

subsection {* Theorems in the context of \ac{algebra} *}

text {* 
The following theorems are valid for \ac{algebra}.
They are valid for any instantiation of the \ac{algebra} class as, for example, for the sets of distinct lists type.
*}

context temporal_faults_algebra
begin

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

theorem xbefore_inf_absorb_1: "independent_events a b \<Longrightarrow> 
  \<lbrakk> tempo1 a; tempo1 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo2 a; tempo2 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo3 a; tempo3 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo4 a; tempo4 b \<rbrakk> \<Longrightarrow>
  inf a (xbefore a b) = xbefore a b"
by (simp add: local.inf_absorb2 local.le_iff_sup xbefore_sup_absorb_1)

theorem xbefore_inf_absorb_2: "independent_events a b \<Longrightarrow> 
  \<lbrakk> tempo1 a; tempo1 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo2 a; tempo2 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo3 a; tempo3 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo4 a; tempo4 b \<rbrakk> \<Longrightarrow>
  inf a (xbefore b a) = xbefore b a"
by (simp add: local.inf.absorb2 local.sup.absorb_iff1 xbefore_sup_absorb_2b)

(*
lemma inf_xbefore_equiv_sups_xbefore_1:
  "independent_events a b \<Longrightarrow> independent_events a c \<Longrightarrow> independente_events b c \<Longrightarrow> 
  \<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo2 a; tempo2 b; tempo2 c\<rbrakk> \<Longrightarrow> 
  \<lbrakk>tempo3 a; tempo3 b; tempo3 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo4 a; tempo4 b; tempo4 c\<rbrakk> \<Longrightarrow>
  inf a (xbefore b c) = 
  sup (sup (xbefore (xbefore a b) c) (xbefore (xbefore b a) c)) (xbefore (xbefore b c) a)"
*)
corollary inf_xbefore_equiv_sups_xbefore_expanded: 
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
  then have f10: "- sup (inf a (- b)) (xbefore a b) = inf (sup (- a) (- (- b))) (sup (sup (- a) (- b)) (xbefore b a))"
    using a8 a7 a6 a5 a4 a3 a2 a1 local.compl_inf local.compl_sup local.xbefore_not by presburger
  have f11: "sup (- a) (- a) = - a"
    by auto
  have f12: "\<forall>f a aa. \<not> abel_semigroup f \<or> f (a::'a) aa = f aa a"
    by (simp add: abel_semigroup.commute)
  then have f13: "inf (sup (- a) (- a)) (xbefore b a) = inf (xbefore b a) (- a)"
    using f11 local.inf.abel_semigroup_axioms by presburger
  have f14: "inf b (xbefore b a) = inf (xbefore b a) b"
    using f12 local.inf.abel_semigroup_axioms by blast
  have f15: "inf a (xbefore b a) = xbefore b a"
    using a9 a8 a7 a6 a5 a4 a3 a2 a1 by (meson xbefore_inf_absorb_2)
  then have f16: "inf (xbefore b a) a = xbefore b a"
    using f12 local.inf.abel_semigroup_axioms by presburger
  then have "inf b (xbefore b a) = inf (xbefore b a) (sup (xbefore a b) (xbefore b a))"
    using f14 a9 a8 a7 a6 a5 a4 a3 a2 a1 by (metis (full_types) local.inf.assoc local.xbefore_sup_equiv_inf)
  then have f17: "inf b (xbefore b a) = inf (sup (xbefore a b) a) (xbefore b a)"
    using f15 a3 a2 by (simp add: local.inf_sup_distrib1 local.inf_sup_distrib2 local.xbefore_inf_equiv_bot)
  have f18: "sup (xbefore a b) a = a"
    using a9 a8 a7 a6 a5 a4 a3 a2 a1 by (metis (no_types) xbefore_sup_absorb_1)
  have "inf (xbefore b a) (- a) = bot"
    by (metis f11 f13 f16 local.compl_inf_bot local.inf.left_commute local.inf_bot_right)
  then have f19: "inf (sup (- a) (- (- b))) (xbefore b a) = inf (sup (xbefore a b) a) (xbefore b a)"
    using f17 f13 by (simp add: local.inf_sup_distrib2)
  have "inf (sup (- a) (- (- b))) (sup (- a) (- b)) = sup (sup (- a) (- a)) (inf b (- b))"
    using local.distrib_imp1 local.inf_sup_distrib1 by force
  then have "- sup (inf a (- b)) (xbefore a b) = - inf (- xbefore b a) a"
    using f10 f15 f18 f19 local.inf_compl_bot local.inf_sup_distrib1 local.sup_commute by auto
  then show ?thesis
    using f12 by (metis (no_types) local.compl_eq_compl_iff local.inf.abel_semigroup_axioms)
qed

end

(*<*)
end
(*>*)