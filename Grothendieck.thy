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

(* LEMMAS *)

lemma local_dom : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> A = d Aa
\<Longrightarrow> T = Presheaf.space \<Phi>  \<Longrightarrow>  A \<in> opens T"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD d_def gc_def)

lemma local_elem : "Presheaf.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> A = d Aa
\<Longrightarrow> P_A = Presheaf.ob \<Phi> $ A \<Longrightarrow> a = snd Aa \<Longrightarrow> a \<in> Poset.el P_A"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD d_def gc_def)

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

end