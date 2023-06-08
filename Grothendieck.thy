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
  by (metis Presheaf.valid_def assms(1) assms(2))

lemma isValidGcPoset_2 :
  fixes \<Phi> :: "('A,'a) Presheaf" and j i :: "'A Inclusion" and a b c :: "'a"
  assumes "valid \<Phi>" and "j \<in> inclusions (space \<Phi>)" and "i \<in> inclusions (space \<Phi>)"
  and "\<Phi>0 = (ob \<Phi>)" and "\<Phi>1 = (ar \<Phi>)"
  and ABC : "Space.dom j = Space.cod i \<and> A = Space.cod j \<and> B = Space.dom j \<and> C = Space.dom i"
  and abc : "a \<in> el (\<Phi>0 $ A) \<and> b \<in> el (\<Phi>0 $ B) \<and> c \<in> el (\<Phi>0 $ C)"
  and b_Cc  : "le (\<Phi>0 $ C) ((\<Phi>1 $ i) $$ b) c"
  and a_Bb : "le (\<Phi>0 $ B) ((\<Phi>1 $ j) $$ a) b"
shows "le (\<Phi>0 $ A) ((\<Phi>1 $ (\<lparr>Inclusion.space = Presheaf.space \<Phi>, dom = C, cod = A\<rparr>)) $$ a) c"
proof -
  define proj_BC where  "proj_BC = (\<Phi>1 $ i)"
  define proj_AB where  "proj_AB = (\<Phi>1 $ j)"
  have "valid \<Phi> " by fact
  moreover have "le (\<Phi>0 $ B) ((\<Phi>1 $ j) $$ a) b" by fact
  moreover have "a \<in> el (\<Phi>0 $ A)"   by (simp add: abc)
  moreover have "b \<in> el (\<Phi>0 $ B)" by (simp add: abc)
  moreover have "(proj_AB $$ a) \<in> el (\<Phi>0 $ B)" by (metis ABC assms(2) assms(4) assms(5) calculation(1) calculation(3) image proj_AB_def)
  moreover have "Space.cod i = B" using ABC by auto
  moreover have "Poset.valid_map proj_BC"  by (simp add: assms(3) assms(5) calculation(1) proj_BC_def) 
  moreover have "Poset.cod proj_BC = ob \<Phi> $ C" using ABC assms(3) assms(5) calculation(1) cod_proj proj_BC_def by blast
  moreover have "Space.compose j i = \<lparr>Inclusion.space = Presheaf.space \<Phi>, dom = C, cod = A\<rparr>"
    by (smt (verit, del_insts) ABC Space.compose_def assms(2) assms(3) inclusions_def mem_Collect_eq)
  moreover have "le (\<Phi>0 $ B) (proj_BC $$ (proj_AB $$ a)) (proj_BC $$ b)"
  oops
qed





lemma isValidGcPoset:  "Presheaf.valid \<Phi> \<Longrightarrow> Poset.valid (gc \<Phi>)"
  unfolding gc_def
  apply (simp_all add: Let_def)
  











end
