section {* \Acl*{algebra}  *}
text {* \label{sec:theory-algebra} *}

(*<*)
theory Temporal_Faults_Algebra
imports Main 
begin
(*>*)


class temporal_faults_algebra_basic = boolean_algebra +
  fixes xbefore :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes tempo1 :: "'a \<Rightarrow> bool"
  assumes xbefore_bot_1: "xbefore bot a = bot"
  assumes xbefore_bot_2: "xbefore a bot = bot"
  assumes xbefore_not_idempotent: "tempo1 a \<Longrightarrow> xbefore a a = bot"
  assumes inf_tempo1: "\<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> tempo1 (inf a b)"
  assumes xbefore_not_sym: 
    "\<lbrakk>tempo1 a; tempo1 b\<rbrakk> \<Longrightarrow> (xbefore a b) \<le> -(xbefore b a)"

class temporal_faults_algebra_assoc = temporal_faults_algebra_basic +
  assumes xbefore_assoc: "\<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> 
    xbefore (xbefore a b) c = xbefore a (xbefore b c)"

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
  
class temporal_faults_algebra_trans = temporal_faults_algebra_equivs +
  assumes xbefore_trans: 
    "\<lbrakk>tempo1 a; tempo1 b; tempo1 c\<rbrakk> \<Longrightarrow> \<lbrakk>tempo2 a; tempo2 b; tempo2 c\<rbrakk> \<Longrightarrow>
    less_eq (inf (xbefore a b) (xbefore b c)) (xbefore a c)"

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

(*TODO: verify where these theorem need to be used*)
(*<*)
theorem xbefore_inf_absorb_1: "independent_events a b \<Longrightarrow> 
  \<lbrakk> tempo1 a; tempo1 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo2 a; tempo2 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo3 a; tempo3 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo4 a; tempo4 b \<rbrakk> \<Longrightarrow>
  inf a (xbefore a b) = xbefore a b"
sorry

theorem xbefore_inf_absorb_2: "independent_events a b \<Longrightarrow> 
  \<lbrakk> tempo1 a; tempo1 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo2 a; tempo2 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo3 a; tempo3 b \<rbrakk> \<Longrightarrow>
  \<lbrakk> tempo4 a; tempo4 b \<rbrakk> \<Longrightarrow>
  inf a (xbefore b a) = xbefore b a"
sorry
(*>*)

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
  hence f10: "- xbefore a b = sup (sup (- a) (- b)) (xbefore b a)"
    using a8 a7 a6 a5 a4 a3 a2 a1 by (metis (no_types) local.xbefore_not)
  have f11: "\<forall>a aa ab. inf (a\<Colon>'a) (sup aa ab) = sup (inf a aa) (inf a ab)"
    using local.distrib_imp2 local.sup_inf_distrib1 by blast
  hence "sup (inf a (- b)) (inf a b) = a"
    by (metis (no_types) local.compl_sup_top local.inf_top_right)
  hence "sup (inf a (- b)) (xbefore a b) = 
    inf a (sup (inf a (- b)) (- xbefore b a))"
    using f10 by (metis (no_types) local.compl_sup local.double_compl 
      local.sup_inf_distrib1)
  hence f12: "sup (inf a (- b)) (xbefore a b) = 
    sup (inf a (- xbefore b a)) (inf a (- b))"
    using f11 by (simp add: local.sup.commute)
  have f13: "sup (xbefore a b) (xbefore b a) = inf a b"
    using a9 a8 a7 a6 a5 a4 a3 a2 a1 by (metis (no_types) 
      local.xbefore_sup_equiv_inf)
  have "sup a (xbefore b a) = a"
    using a9 a8 a7 a6 a5 a4 a3 a2 a1 by (meson xbefore_sup_absorb_2b)
  hence f14: "sup (inf a (- xbefore b a)) (xbefore b a) = a"
    using local.sup_inf_distrib2 by auto
  have "sup (xbefore a b) a = a"
    using a9 a8 a7 a6 a5 a4 a3 a2 a1 by (meson xbefore_sup_absorb_1)
  hence "sup (inf a (- xbefore b a)) (inf a b) = a"
    using f14 f13 by (metis (no_types) local.sup_left_commute)
  hence "sup (inf a (- xbefore b a)) (inf a b) = 
    sup (inf a (- xbefore b a)) a"
    using local.sup.commute by auto
  hence "sup (inf a (- b)) (xbefore a b) = 
    sup (inf a (- xbefore b a)) (inf (- b) (inf a b))"
    using f12 local.inf_commute local.sup_inf_distrib1 by auto
  thus ?thesis
    using local.inf_left_commute by auto
qed


end

(*<*)
end
(*>*)