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
              a_B = (\<Phi>1 $ i) ! a;
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
  and "\<Phi>0 = (ob \<Phi>)"
  and "\<Phi>1 = (ar \<Phi>)"
  and "Space.dom j = Space.cod i" 
  and "A = Space.cod j" and "B = Space.dom j" and "C = Space.dom i"
  and "a \<in> el (\<Phi>0 $ A)"
  and "b \<in> el (\<Phi>0 $ B)" 
  and "c \<in> el (\<Phi>0 $ C)"
  and "le (\<Phi>0 $ C) ((\<Phi>1 $ i) ! b) c" 
  and "le (\<Phi>0 $ B) ((\<Phi>1 $ j) ! a) b" 
shows "le (\<Phi>0 $ A) ((\<Phi>1 $ (\<lparr>Inclusion.space = Presheaf.space \<Phi>, dom = C, cod = A\<rparr>)) ! a) c" 
  unfolding validInclusion_def
  sorry



lemma isValidGcPoset:  "Presheaf.valid \<Phi> \<longrightarrow> Poset.valid (gc \<Phi>)"
  unfolding gc_def
  apply safe
  apply (simp_all add: Poset.valid_def Let_def)
  apply safe
     apply auto
    apply (simp_all add: Presheaf.valid_def[symmetric] Space.ident_def[symmetric])
    apply (subst isValidGcPoset_1)
      apply safe
    apply (subst Poset.ident_app)
     apply safe
    apply (subst Poset.reflexivity)
      apply (subst Presheaf.posetsValid)
        apply safe
   apply (smt (verit, best) Poset.valid_def ident_app isValidGcPoset_1 posetsValid)
apply (subst isValidGcPoset_2)
  
   
  


end
