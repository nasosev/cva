theory Grothendieck
imports Main Presheaf Poset
begin

(* covariant Grothendieck construction *)

definition gc :: "('A, 'a) Presheaf \<Rightarrow> ('A set \<times> 'a) Poset" where
  "gc \<Phi> \<equiv>
    let
        \<Phi>0 = Presheaf.ob \<Phi>;
        \<Phi>1 = Presheaf.ar \<Phi>;
        space  = Presheaf.space \<Phi>;
        opens = Space.opens space;
        el = { (A, a) .  A \<in> opens \<and> a \<in> Poset.el (\<Phi>0 $ A) };
        le  =  \<lambda>(A,a) (B,b) .
            let
              i = \<lparr> Space.Inclusion.space = space, dom = B, cod = A \<rparr>;
              a_B = (\<Phi>1 $ i) $$ a;
              le_B = Poset.le (\<Phi>0 $ B)
            in  B \<subseteq> A \<and> le_B a_B b
    in
    \<lparr> Poset.el = el, Poset.le = le \<rparr>"

(* LEMMAS *)

lemma isValidGcPoset_1 :
  fixes \<Phi> :: "('A,'a) Presheaf" and A :: "'A Open"
  assumes "valid \<Phi>" and "A \<in> opens (space \<Phi>)"
  shows "(ar \<Phi> $ (Space.ident (space \<Phi>) A)) = (Poset.ident (ob \<Phi> $ A))"
  using assms(1) assms(2) valid_identity by blast


lemma isValidGcPoset_2 :
  fixes \<Phi> :: "('A,'a) Presheaf" and j i :: "'A Inclusion" and a b c :: "'a"
  defines "\<Phi>0 \<equiv> (ob \<Phi>)" 
  defines "\<Phi>1 \<equiv> (ar \<Phi>)"
  defines "A \<equiv> Space.cod j"
  defines "B \<equiv> Space.dom j"
  defines "C \<equiv> Space.dom i"
  defines "proj_BC \<equiv> (\<lambda> b . (\<Phi>1 $ i) $$ b)"
  defines "proj_AB \<equiv> (\<lambda> a. (\<Phi>1 $ j) $$ a)"
  defines "\<Phi>_A \<equiv> \<Phi>0 $ A"
  defines "\<Phi>_B \<equiv> \<Phi>0 $ B"
  defines "\<Phi>_C \<equiv> \<Phi>0 $ C"
  assumes "valid \<Phi>" and "j \<in> inclusions (space \<Phi>)" and "i \<in> inclusions (space \<Phi>)"
  and ABC : "Space.dom j = Space.cod i"
  and abc : "a \<in> el \<Phi>_A \<and> b \<in> el \<Phi>_B \<and> c \<in> el \<Phi>_C"
  and b_Cc  : "le \<Phi>_C (proj_BC b) c"
  and a_Bb : "le \<Phi>_B (proj_AB a) b"
shows "le \<Phi>_C ((proj_BC o proj_AB) a) c"
proof -
  have "valid \<Phi> "
    by (simp add: assms(11)) 
 moreover have "le \<Phi>_B (proj_AB a) b"
   by (simp add: a_Bb) 
   moreover have "a \<in> el \<Phi>_A"
     using abc by auto
  moreover have "b \<in> el \<Phi>_B"
    by (simp add: abc)
  moreover have "(proj_AB a) \<in> el \<Phi>_B"
    using A_def B_def \<Phi>0_def \<Phi>1_def \<Phi>_A_def \<Phi>_B_def assms(12) calculation(1) calculation(3) proj_AB_def by auto 
    moreover have "Space.cod i = B"
      by (simp add: ABC B_def) 
   moreover have "le \<Phi>_C (proj_BC  ( proj_AB  a)) (proj_BC  b)"
     by (metis C_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def \<Phi>_C_def a_Bb abc assms(13) calculation(1) calculation(5) calculation(6) cod_proj dom_proj poset_maps_valid proj_BC_def valid_monotonicity) 
   moreover have "le \<Phi>_C (proj_BC b) c"
     by (simp add: b_Cc) 
    moreover have "le \<Phi>_C (proj_BC  ( proj_AB  a)) c"
      by (metis C_def Poset.fun_app2 \<Phi>0_def \<Phi>1_def \<Phi>_B_def \<Phi>_C_def abc assms(13) b_Cc calculation(1) calculation(5) calculation(6) calculation(7) cod_proj dom_proj poset_maps_valid proj_BC_def valid_cod valid_transitivity) 
    ultimately show ?thesis
      by fastforce 
qed


lemma isValidGcPoset:  "Presheaf.valid \<Phi> \<Longrightarrow> Poset.valid (gc \<Phi>)"
  unfolding gc_def
  apply (intro Poset.validI)
    apply clarsimp
    apply safe
      apply auto
      apply (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Space.ident_def case_prod_conv dual_order.refl ident_app isValidGcPoset_1 mem_Collect_eq posets_valid valid_reflexivity)
     apply (metis (no_types, lifting) Poset.Poset.select_convs(2) case_prod_conv subset_antisym)
    apply (metis (no_types, lifting) Poset.Poset.select_convs(2) case_prod_conv subsetD)
  apply (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Poset.valid_def Space.ident_def case_prod_conv ident_app isValidGcPoset_1 mem_Collect_eq posets_valid subset_antisym)
   using isValidGcPoset_2  Presheaf.valid_composition  Presheaf.valid_welldefined sledgehammer

    
  
  
  












end
