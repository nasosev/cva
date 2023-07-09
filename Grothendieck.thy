section \<open> Grothendieck.thy \<close>

theory Grothendieck
imports Main Poset Prealgebra
begin

abbreviation d :: "('A set \<times> 'a)  \<Rightarrow> 'A set" where
"d Aa \<equiv> fst Aa"

abbreviation e :: "('A set \<times> 'a)  \<Rightarrow> 'a" where
"e Aa \<equiv> snd Aa"

definition gc :: "('A, 'a) Prealgebra \<Rightarrow> ('A set \<times> 'a) Poset" where
  "gc F \<equiv>
    \<lparr> Poset.el = { (A, a) . A \<in> Space.opens (space F) \<and> a \<in> Poset.el (ob F \<cdot> A)},
      Poset.le_rel = { ((A, a), (B, b)) . 
                     A \<in> Space.opens (space F) \<and> B \<in> Space.opens (space F) 
                     \<and> a \<in> Poset.el (ob F \<cdot> A) \<and> b \<in> Poset.el (ob F \<cdot> B)
                     \<and> B \<subseteq> A \<and> Poset.le (ob F \<cdot> B) (ar F \<cdot> (Space.make_inc B A) \<star> a) b } \<rparr>"

lemma gc_leI_raw : "A \<in> Space.opens (space F) \<Longrightarrow> B \<in> Space.opens (space F) \<Longrightarrow> B \<subseteq> A
\<Longrightarrow> a \<in> Poset.el (ob F \<cdot> A) \<Longrightarrow> b \<in> Poset.el (ob F \<cdot> B)
\<Longrightarrow> Poset.le (ob F \<cdot> B) ((ar F \<cdot> (Space.make_inc B A)) \<star> a) b \<Longrightarrow> Poset.le (gc F) (A,a) (B,b)"
  unfolding gc_def
  by simp

lemma gc_leI : "a \<in> el (gc F) \<Longrightarrow> b \<in> el (gc F) \<Longrightarrow> d
 b \<subseteq> d a \<Longrightarrow> Poset.le (ob F \<cdot> d b) ((ar F \<cdot> (Space.make_inc (d b) (d a))) \<star> e a) (e b) \<Longrightarrow> Poset.le (gc F) a b" 
  unfolding gc_def
  apply clarsimp
  by force

lemma gc_el : "el (gc F) = { (A, a) . A \<in> Space.opens (space F) \<and> a \<in> Poset.el (ob F \<cdot> A)}"
  unfolding gc_def 
  by simp

lemma gc_le_rel : "le_rel (gc F) = { ((A, a), (B, b)) .
 A \<in> Space.opens (space F) \<and> B \<in> Space.opens (space F) 
 \<and> a \<in> Poset.el (ob F \<cdot> A) \<and> b \<in> Poset.el (ob F \<cdot> B)
 \<and> B \<subseteq> A \<and> Poset.le (ob F \<cdot> B) (ar F \<cdot> (Space.make_inc B A) \<star> a) b }" 
  unfolding gc_def 
  by simp

lemma local_dom : "valid F \<Longrightarrow> Aa \<in> Poset.el (gc F)
\<Longrightarrow> d Aa \<in> opens (space F)"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD gc_def)

lemma gc_elem_local : "valid F \<Longrightarrow> Aa \<in> Poset.el (gc F) \<Longrightarrow> A = d Aa
\<Longrightarrow> e Aa \<in> Poset.el (ob F \<cdot> (d Aa))"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD gc_def)

lemma local_elem_gc : "valid F \<Longrightarrow> A \<in> opens (space F)
\<Longrightarrow> a \<in> Poset.el (ob F \<cdot> A) \<Longrightarrow> (A, a) \<in> Poset.el (gc F)"
  unfolding gc_def
  by simp

lemma d_antitone : "valid F \<Longrightarrow> Aa \<in> Poset.el (gc F) \<Longrightarrow> Bb \<in> Poset.el (gc F) \<Longrightarrow>
Poset.le (gc F) Aa Bb \<Longrightarrow> d Bb \<subseteq> d Aa"
  unfolding gc_def
  by (smt (verit) Poset.Poset.select_convs(2) case_prod_conv case_prod_unfold mem_Collect_eq)

lemma local_le : "valid F \<Longrightarrow> Aa \<in> Poset.el (gc F) \<Longrightarrow> Aa' \<in> Poset.el (gc F) \<Longrightarrow>
d Aa = d Aa' \<Longrightarrow> Poset.le (gc F) Aa Aa' \<Longrightarrow> Poset.le (ob F \<cdot> (d Aa)) (e Aa) (e Aa')"
  unfolding gc_def
  by (smt (z3) Poset.Poset.select_convs(2) Poset.ident_app valid_welldefined Product_Type.Collect_case_prodD Space.ident_def eq_fst_iff eq_snd_iff old.prod.case valid_identity)

lemma valid_gc_transitive :
  fixes F :: "('A,'a) Prealgebra" and A B C :: "'A Open" and a b c :: "'a"
  defines "T \<equiv> space F"
  defines "i_BA \<equiv> Space.make_inc B A"
  defines "i_CB \<equiv> Space.make_inc C B"
  defines "i_CA \<equiv> Space.make_inc C A"
  defines "prj_AB \<equiv> ar F \<cdot> i_BA"
  defines "prj_BC \<equiv> ar F \<cdot> i_CB"
  defines "prj_AC \<equiv> ar F \<cdot> i_CA"
  assumes F_valid : "valid F" and C_le_B : "C \<subseteq> B" and B_le_A : "B \<subseteq> A"
  and A_open : "A \<in> Space.opens T" and B_open : "B \<in> Space.opens T" and C_open "C \<in> Space.opens T"
  and A_el : "a \<in> el (ob F \<cdot> A)" and b_el : "b \<in> el (ob F \<cdot> B)" and c_el : "c \<in> el (ob F \<cdot> C)"
  and le_prj_a_b : "le (ob F \<cdot> B) (prj_AB \<star> a) b"
  and le_prj_b_c : "le (ob F \<cdot> C) (prj_BC \<star> b) c"
shows "le (ob F \<cdot> C) (prj_AC \<star> a) c"
proof - 
  have "Poset.valid_map prj_AB" using assms
  using valid_ar by fastforce 
  moreover have "Poset.valid_map prj_BC" using assms calculation
    using valid_ar by fastforce 
  moreover have "Poset.valid_map prj_AC" using assms calculation
    using valid_ar by fastforce 
  moreover have "le (ob F \<cdot> C) (prj_BC \<star> (prj_AB \<star>  a)) (prj_BC \<star>  b)"
    by (metis (no_types, lifting) A_el A_open B_le_A B_open C_le_B F_valid Inclusion.select_convs(1) Inclusion.select_convs(2) Poset.fun_app2 valid_welldefined T_def assms(14) b_el i_BA_def i_CB_def le_prj_a_b mem_Collect_eq prj_AB_def prj_BC_def valid_map_monotone)
  moreover have "le (ob F \<cdot> C) (prj_BC \<star> (prj_AB \<star> a)) c"
    by (smt (z3) A_el A_open B_le_A B_open C_le_B F_valid Inclusion.select_convs(1) Inclusion.select_convs(2) Poset.fun_app2 valid_welldefined T_def assms(14) b_el c_el calculation(4) i_BA_def i_CB_def le_prj_b_c mem_Collect_eq prj_AB_def prj_BC_def valid_transitivity)
  moreover have "prj_BC \<diamondop> prj_AB = prj_AC" using assms calculation
    by (metis (no_types, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) compose_inc_def mem_Collect_eq valid_composition) 
  moreover have "prj_BC \<star> (prj_AB \<star> a) = prj_AC \<star> a" using assms calculation
    by (smt (verit) Inclusion.select_convs(1) Inclusion.select_convs(2) Poset.compose_app Poset.fun_app Poset.fun_app2 valid_welldefined mem_Collect_eq) 
  ultimately show ?thesis
    by metis
qed

(* Main result *) 

proposition valid_gc:  
  fixes F :: "('A, 'a) Prealgebra"
  assumes valid_F : "valid F"
  shows "Poset.valid (gc F)"
proof (intro Poset.validI)
  fix x y
  assume a1: "(x, y) \<in> le_rel (gc F)" 
   show "x \<in> el (gc F) \<and> y \<in> el (gc F)" using assms a1 gc_def [where ?F=F]
     by (smt (verit) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD case_prod_unfold fst_conv local_elem_gc prod.collapse snd_conv)
next 
  fix x
  assume "x \<in> el (gc F)"
  define "T" where "T = space F" 
  define "i" where "i = Space.ident (d x)"
  have "e x = ((ar F) \<cdot> i) \<star> (e x)"
    by (metis Poset.ident_app T_def \<open>x \<in> el (gc F)\<close> gc_elem_local i_def local_dom valid_F valid_identity valid_ob) 
  moreover have "d x \<in> opens (space F)"
    using \<open>x \<in> el (gc F)\<close> local_dom valid_F by blast 

  moreover have "e x \<in> Poset.el (ob F \<cdot> (d x))"
    by (meson \<open>x \<in> el (gc F)\<close> gc_elem_local valid_F) 
  moreover have "Poset.le (ob F \<cdot> (d x)) (((ar F) \<cdot> i) \<star> (e x)) (e x)"
    by (metis calculation(1) calculation(2) calculation(3) valid_F valid_ob valid_reflexivity) 

  moreover have "(x,x) \<in> le_rel (gc F)"  using  calculation i_def T_def gc_def [where ?F = F]
    by (smt (verit) Poset.Poset.select_convs(2) Space.ident_def case_prod_conv mem_Collect_eq prod.collapse subsetI) 
  show "le (gc F) x x"
    by (simp add: \<open>(x, x) \<in> le_rel (gc F)\<close> \<open>x \<in> el (gc F)\<close>)
next
  fix x y
  assume a1: "x \<in> el (gc F)"
  assume a2: "y \<in> el (gc F)"
  assume a3: "le (gc F) x y"
  assume a4: "le (gc F) y x "
  show "x = y" using gc_def  [where ?F = F] assms  a1 a2 a3 a4
    by (smt (verit, del_insts) d_antitone gc_elem_local inf.absorb_iff2 le_boolE local_dom local_le prod.split_sel subset_antisym valid_antisymmetry valid_ob) 
next
  fix x y z
  assume a1: "x \<in> el (gc F)"
  assume a2: "y \<in> el (gc F)"
  assume a3: "z \<in> el (gc F)"
  assume a4: "le (gc F) x y"
  assume a5: "le (gc F) y z "
  show "le (gc F) x z" using gc_def [where ?F = F] assms a1 a2 a3 a4 a5 
valid_gc_transitive [where ?F = F and ?a="e x" and ?b="e y" and ?c="e z" and ?A="d x" and ?B="d y"
  and ?C="d z"]
    by (smt (verit, del_insts) Poset.Poset.select_convs(2) case_prod_conv  mem_Collect_eq prod.collapse subset_trans) 
qed

(* Local to global ordering *)

lemma valid_gc_le_wrap :
  fixes F :: "('A, 'a) Prealgebra" and Aa Bb :: "('A set \<times> 'a)"

  defines "i \<equiv> Space.make_inc (d Bb) (d Aa)"
  defines "pr \<equiv>  (ar F) \<cdot> i"
  defines "FA \<equiv>  ob F \<cdot> (d Aa)"
  defines "FB \<equiv>  ob F \<cdot> (d Bb)"

  assumes  "valid F"
  assumes "d Aa \<in> Space.opens (space F)"
  assumes "d Bb \<in> Space.opens (space F)"
  assumes "e Aa \<in> Poset.el FA"
  assumes "e Bb \<in> Poset.el FB"
  assumes "d Bb \<subseteq> d Aa"
  assumes "Poset.le FB (pr \<star> (e Aa)) (e Bb) "

  shows "le (gc F) Aa (Bb)"
  unfolding gc_def
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) FA_def FB_def assms(10) assms(11) assms(6) assms(7) assms(8) assms(9) case_prod_conv i_def mem_Collect_eq pr_def prod.collapse)

lemma valid_gc_le_unwrap :
  fixes F :: "('A, 'a) Prealgebra" and Aa Bb :: "('A set \<times> 'a)"
  defines "i \<equiv> Space.make_inc (d Bb) (d Aa)"
  defines "pr \<equiv> ar F \<cdot> i"
  defines "FA \<equiv> ob F \<cdot> (d Aa)"
  defines "FB \<equiv> ob F \<cdot> (d Bb)"
  
  assumes  F_valid : "valid F"
  and Aa_el : "Aa \<in> Poset.el (gc F) " and Bb_el : "Bb \<in> Poset.el (gc F)"
  and le_gc: "le (gc F) Aa Bb"
  
  shows "Poset.le FB (pr \<star> (e Aa)) (e Bb) \<and> d Bb \<subseteq> d Aa \<and> e Bb \<in> Poset.el FB \<and> e Aa \<in> Poset.el FA"
  proof -
    have "e Bb \<in> Poset.el FB \<and> e Aa \<in> Poset.el FA"
      by (simp add: Aa_el Bb_el FA_def FB_def gc_elem_local F_valid) 
    moreover have "Space.valid_inc i"
      by (metis Aa_el Inclusion.select_convs(1) Inclusion.select_convs(2) assms(7) d_antitone i_def le_gc F_valid) 
  moreover have "Poset.valid_map pr" using assms calculation
    by (metis (no_types, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) valid_welldefined local_dom mem_Collect_eq) 
    define "a_B" where "a_B = (pr \<star> (e Aa))"
    moreover have "Poset.dom pr = FA \<and> Poset.cod pr = FB"
      by (metis (no_types, lifting) Aa_el Bb_el FA_def FB_def Inclusion.simps(1) Inclusion.simps(2) valid_welldefined assms(1) assms(2) calculation(2) local_dom mem_Collect_eq F_valid)
    moreover have "a_B \<in> Poset.el FB"
      by (metis Poset.fun_app2 \<open>Poset.valid_map pr\<close> a_B_def calculation(1) calculation(4)) 
    moreover have " Poset.valid (gc F)"
      by (simp add: F_valid valid_gc) 
    moreover have "Poset.valid FB"
      using Poset.valid_map_welldefined_cod \<open>Poset.valid_map pr\<close> calculation(4) by blast 
    moreover have " d Bb \<subseteq> d Aa \<and> e Bb \<in> Poset.el FB \<and> e Aa \<in> Poset.el FA"
      using Aa_el Bb_el F_valid calculation(1) d_antitone le_gc by blast 
    moreover have "Poset.le FB a_B (e Bb)" using assms calculation gc_def [where ?F=F]
      by (smt (z3) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD eq_fst_iff old.prod.case snd_def)
    ultimately show ?thesis                                                                      
      by blast
  qed

end
