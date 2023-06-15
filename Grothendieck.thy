theory Grothendieck
imports Main Presheaf Poset
begin

(* covariant Grothendieck construction *)

definition gc :: "('A, 'a) Presheaf \<Rightarrow> ('A set \<times> 'a) Poset" where
  "gc \<Phi> \<equiv>
    let
        \<Phi>0 = Presheaf.ob \<Phi>;
        \<Phi>1 = Presheaf.ar \<Phi>;
        T = Presheaf.space \<Phi>;
        opens = Space.opens T;
        el = { (A, a) .  A \<in> opens \<and> a \<in> Poset.el (\<Phi>0 $ A) };
        inc = Space.make_inclusion T;
        le_rel  = { ((A, a), (B, b)) . A \<in> opens \<and> B \<in> opens \<and> a \<in> Poset.el ((\<Phi>0 $ A)) \<and> b \<in> Poset.el ((\<Phi>0 $ B))
                     \<and> B \<subseteq> A \<and> Poset.le (\<Phi>0 $ B) ((\<Phi>1 $ (inc B A)) $$ a) b }
    in
    \<lparr> Poset.el = el, Poset.le_rel = le_rel \<rparr>"

definition d :: "('A set \<times> 'a)  \<Rightarrow> 'A set" where
"d Aa = fst Aa"

definition e :: "('A set \<times> 'a)  \<Rightarrow> 'a" where
"e Aa = snd Aa"

(* LEMMAS *)

lemma local_dom : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> A = d Aa
\<Longrightarrow> T = Presheaf.space \<Phi>  \<Longrightarrow>  A \<in> opens T"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD d_def gc_def)

lemma gc_elem_local : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> A = d Aa
\<Longrightarrow> P_A = Presheaf.ob \<Phi> $ A \<Longrightarrow> a = snd Aa \<Longrightarrow> a \<in> Poset.el P_A"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD d_def gc_def)

lemma local_elem_gc : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> A \<in> opens (Presheaf.space \<Phi>)
\<Longrightarrow> P_A = Presheaf.ob \<Phi> $ A \<Longrightarrow> a \<in> Poset.el P_A \<Longrightarrow> (A,a) \<in> Poset.el P"
  unfolding gc_def
  by (simp add: Let_def)

lemma d_antitone : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> Bb \<in> Poset.el P \<Longrightarrow>
Poset.le P Aa Bb \<Longrightarrow> d Bb \<subseteq> d Aa"
  unfolding gc_def
  by (smt (verit) Poset.Poset.select_convs(2) case_prod_conv case_prod_unfold d_def mem_Collect_eq) 

lemma local_le : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> Aa' \<in> Poset.el P \<Longrightarrow>
d Aa = d Aa' \<Longrightarrow> Poset.le P Aa Aa' \<Longrightarrow> A = d Aa \<Longrightarrow> P_A = Presheaf.ob \<Phi> $ A \<Longrightarrow> a = snd Aa \<Longrightarrow> a' = snd Aa' \<Longrightarrow>
 Poset.le P_A a a' "
  unfolding gc_def
  by (smt (verit, del_insts) Poset.Poset.select_convs(2) Poset.ident_app Product_Type.Collect_case_prodD Space.ident_def case_prod_conv d_def make_inclusion_def posets_valid prod.collapse valid_identity)

lemma valid_gc_1 :
  fixes \<Phi> :: "('A,'a) Presheaf" and A :: "'A Open"
  assumes "valid \<Phi>" and "A \<in> opens (space \<Phi>)"
  shows "(ar \<Phi> $ (Space.ident (space \<Phi>) A)) = (Poset.ident (ob \<Phi> $ A))"
  by (simp add: assms(1) assms(2) valid_identity)

lemma valid_gc_transitive :
  fixes \<Phi> :: "('A,'a) Presheaf" and A B C :: "'A Open" and a b c :: "'a"
  defines "\<Phi>0 \<equiv> (ob \<Phi>)"
  defines "\<Phi>1 \<equiv> (ar \<Phi>)"
  defines "T \<equiv> Presheaf.space \<Phi>"
  defines "\<Phi>_A \<equiv> \<Phi>0 $ A"
  defines "\<Phi>_B \<equiv> \<Phi>0 $ B"
  defines "\<Phi>_C \<equiv> \<Phi>0 $ C"
  defines "i_BA \<equiv> \<lparr>Inclusion.space = T, dom = B, cod = A\<rparr>"
  defines "i_CB \<equiv> \<lparr>Inclusion.space = T, dom = C, cod = B\<rparr>"
  defines "i_CA \<equiv> \<lparr>Inclusion.space = T, dom = C, cod = A\<rparr>"
  defines "prj_AB \<equiv> (\<Phi>1 $ i_BA)"
  defines "prj_BC \<equiv> (\<Phi>1 $ i_CB)"
  defines "prj_AC \<equiv> (\<Phi>1 $ i_CA)"
  assumes "valid \<Phi>" and "C \<subseteq> B" and "B \<subseteq> A"
  and "A \<in> Space.opens T" and "B \<in> Space.opens T" and "C \<in> Space.opens T"
  and "a \<in> el \<Phi>_A" and "b \<in> el \<Phi>_B" and "c \<in> el \<Phi>_C"
  and "le \<Phi>_B (prj_AB $$ a) b"
  and "le \<Phi>_C (prj_BC $$ b) c"
shows "le \<Phi>_C (prj_AC $$ a) c"
proof -
  have "valid \<Phi> "
    by (simp add: assms(13))
 moreover have "le \<Phi>_B (prj_AB $$ a) b"
   by (simp add: assms(22))
   moreover have "a \<in> el \<Phi>_A"
     by (simp add: assms(19))
  moreover have "b \<in> el \<Phi>_B"
    using assms(20) by blast
  moreover have "Space.valid T"
    by (simp add: T_def calculation(1) space_valid)
  moreover have "Space.valid_inclusion i_BA"
    by (simp add: assms(15) assms(16) assms(17) calculation(5) i_BA_def valid_inclusion_def)
  moreover have "Poset.valid_map prj_AB"
    using T_def \<Phi>1_def calculation(1) calculation(6) i_BA_def inclusions_def poset_maps_valid prj_AB_def by fastforce
  moreover have "Poset.cod prj_AB = \<Phi>_B"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) T_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def calculation(1) calculation(6) cod_proj i_BA_def inclusions_def mem_Collect_eq prj_AB_def)
    moreover have "(prj_AB $$ a) \<in> el \<Phi>_B"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.simps(3) T_def \<Phi>0_def \<Phi>1_def \<Phi>_A_def \<Phi>_B_def calculation(1) calculation(3) calculation(6) i_BA_def image inclusions_def mem_Collect_eq prj_AB_def)
  moreover have "Space.valid_inclusion i_CB"
    by (simp add: assms(14) assms(17) assms(18) calculation(5) i_CB_def valid_inclusion_def)
moreover have "Poset.valid_map prj_BC"
  using T_def \<Phi>1_def assms(11) assms(8) calculation(1) calculation(10) inclusions_def poset_maps_valid by fastforce
  moreover have "le \<Phi>_C (prj_BC $$ (prj_AB $$  a)) (prj_BC $$  b)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) T_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def \<Phi>_C_def calculation(1) calculation(10) calculation(11) calculation(2) calculation(4) calculation(9) cod_proj dom_proj i_CB_def inclusions_def mem_Collect_eq prj_BC_def valid_monotonicity)
   moreover have "le \<Phi>_C (prj_BC $$ b) c"
     by (simp add: assms(23))
    moreover have "le \<Phi>_C (prj_BC $$ (prj_AB $$ a)) c"
      by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) T_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def \<Phi>_C_def assms(21) calculation(1) calculation(10) calculation(11) calculation(12) calculation(13) calculation(4) calculation(9) cod_proj i_CB_def image inclusions_def mem_Collect_eq prj_BC_def valid_cod valid_transitivity)
    ultimately show ?thesis
      by (smt (verit, del_insts) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) Space.compose_def T_def \<Phi>0_def \<Phi>1_def \<Phi>_A_def \<Phi>_B_def compose_app dom_proj i_BA_def i_CA_def i_CB_def inclusions_def mem_Collect_eq prj_AB_def prj_AC_def prj_BC_def valid_composition)
  qed

lemma valid_gc_welldefined : "Presheaf.valid \<Phi> \<Longrightarrow> le (gc \<Phi>) Aa Bb \<Longrightarrow> Aa \<in> el (gc \<Phi>) \<and> Bb \<in> el (gc \<Phi>)"
  unfolding gc_def
  apply (simp_all add: Let_def)
  by clarsimp

(* THEOREM *)

theorem valid_gc:  "Presheaf.valid \<Phi> \<Longrightarrow> Poset.valid (gc \<Phi>)"
  unfolding gc_def
apply (intro Poset.validI)
     apply clarsimp
     apply auto
        apply (simp_all add: Let_def)
  apply (metis Poset.ident_app Space.ident_def make_inclusion_def posets_valid valid_identity valid_reflexivity)
  apply blast
    apply auto[1]
  apply (metis Poset.ident_app Presheaf.ident_app Space.ident_def make_inclusion_def posets_valid subset_antisym valid_antisymmetry)
  by (smt (verit, best) make_inclusion_def order_trans valid_gc_transitive)

lemma valid_gc_le_wrap :
  fixes \<Phi> :: "('A, 'a) Presheaf" and Aa Bb :: "('A set \<times> 'a)"

  defines "i \<equiv> Space.make_inclusion (Presheaf.space \<Phi>) (d Bb) (d Aa)"
  defines "pr \<equiv>  (Presheaf.ar \<Phi>) $ i"
  defines "\<Phi>A \<equiv>  (Presheaf.ob \<Phi>) $ (d Aa)"
  defines "\<Phi>B \<equiv>  (Presheaf.ob \<Phi>) $ (d Bb)"

  assumes  "Presheaf.valid \<Phi>" 
  assumes "d Aa \<in> Space.opens (Presheaf.space \<Phi>)"
  assumes "d Bb \<in> Space.opens (Presheaf.space \<Phi>)"
  assumes "e Aa \<in> Poset.el \<Phi>A"
  assumes "e Bb \<in> Poset.el \<Phi>B"
  assumes "d Bb \<subseteq> d Aa"

  assumes "Poset.le \<Phi>B (pr $$ (e Aa)) (e Bb) "
  shows "le (gc \<Phi>) Aa (Bb)"
  unfolding gc_def
  apply (simp add:Let_def)
  apply safe
  apply (metis assms(6) d_def fst_conv)
      apply (metis assms(7) d_def fst_conv)
     apply (metis \<Phi>A_def assms(8) d_def e_def fst_conv snd_conv)
    apply (metis \<Phi>B_def assms(9) d_def e_def fst_conv snd_conv)
   apply (metis assms(10) d_def fst_conv subsetD)
  by (metis \<Phi>B_def assms(11) d_def e_def fst_conv i_def pr_def snd_conv)

lemma valid_gc_le_unwrap :
  fixes \<Phi> :: "('A, 'a) Presheaf" and Aa Bb :: "('A set \<times> 'a)"

  defines "i \<equiv> Space.make_inclusion (Presheaf.space \<Phi>) (d Bb) (d Aa)"
  defines "pr \<equiv>  (Presheaf.ar \<Phi>) $ i"
  defines "\<Phi>A \<equiv>  (Presheaf.ob \<Phi>) $ (d Aa)"
  defines "\<Phi>B \<equiv>  (Presheaf.ob \<Phi>) $ (d Bb)"
  defines "gc\<Phi> \<equiv> gc \<Phi>"

assumes  valid: "Presheaf.valid \<Phi>" 
and "Aa \<in> Poset.el gc\<Phi> " and "Bb \<in> Poset.el (gc \<Phi>)"
and le_gc: "le gc\<Phi> Aa Bb"

shows "Poset.le \<Phi>B (pr $$ (e Aa)) (e Bb) \<and> d Bb \<subseteq> d Aa \<and> e Bb \<in> Poset.el \<Phi>B \<and> e Aa \<in> Poset.el \<Phi>A"
proof -
  have a1: "le gc\<Phi> Aa Bb"
    by (simp add: le_gc)  
  moreover have "d Bb \<subseteq> d Aa"
    using assms(7) assms(8) d_antitone gc\<Phi>_def le_gc valid by blast 
  moreover have "e Bb \<in> Poset.el \<Phi>B \<and> e Aa \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def \<Phi>B_def assms(7) assms(8) e_def gc\<Phi>_def gc_elem_local valid) 
  moreover have "Space.valid_inclusion i"
    by (metis assms(7) assms(8) calculation(2) gc\<Phi>_def i_def local_dom space_valid valid valid_make_inclusion) 
  moreover have "Presheaf.valid \<Phi>"
    by (simp add: valid) 
  moreover have "i \<in> Space.inclusions (space \<Phi>)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) calculation(4) i_def inclusions_def make_inclusion_def mem_Collect_eq) 
  moreover have "Poset.valid_map pr" using Presheaf.poset_maps_valid
    using calculation(6) pr_def valid by blast
  define "a_B" where "a_B = (pr $$ (e Aa))"
  moreover have "Poset.dom pr = \<Phi>A \<and> Poset.cod pr = \<Phi>B"
    by (metis Inclusion.simps(2) Inclusion.simps(3) \<Phi>A_def \<Phi>B_def calculation(6) cod_proj dom_proj i_def make_inclusion_def pr_def valid)  
  moreover have "a_B \<in> Poset.el \<Phi>B" 
    using Poset.fun_app2 \<open>Poset.valid_map pr\<close> a_B_def calculation(3) calculation(8) by fastforce 
  moreover have " Poset.valid gc\<Phi>"
    by (simp add: gc\<Phi>_def valid valid_gc)  
  moreover have "Poset.valid \<Phi>B"
    using \<open>Poset.valid_map pr\<close> calculation(8) valid_cod by blast 
  moreover have "Poset.le \<Phi>B a_B (e Bb)" using gc_def a1
    apply (simp_all add: Let_def)
    unfolding gc\<Phi>_def gc_def
    apply auto
    apply (simp_all add: Let_def)
    apply clarsimp
    by (simp add: \<Phi>B_def a_B_def d_def e_def i_def pr_def)
  ultimately show ?thesis
    by blast
qed

end