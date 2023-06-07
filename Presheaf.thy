theory Presheaf
imports Main Poset Space Function
begin


record ('A, 'a) Presheaf =
  space :: "'A Space"
  ob :: "('A Open, 'a Poset) Function "
  ar :: "('A Inclusion, ('a, 'a) PosetMap) Function"

definition valid :: "('A, 'a) Presheaf \<Rightarrow> bool" where
  "valid \<Phi> \<equiv> 
    let 
      space = (space \<Phi>);
      \<Phi>0 = ob \<Phi>;
      \<Phi>1 = ar \<Phi>;
      welldefined = Space.valid space 
                    \<and> (\<forall>A. A \<in> opens space \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions space \<longrightarrow> Poset.validMap (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) );
      identity = (\<forall>A. A \<in> opens space \<longrightarrow> (\<Phi>1 $ (Space.ident space A)) = Poset.ident (\<Phi>0 $ A));
      composition = (\<forall>j i. j \<in> inclusions space \<longrightarrow> i \<in> inclusions space \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow>  (\<Phi>1 $ (Space.compose j i )) = (\<Phi>1 $ i) \<circ> (\<Phi>1 $ j))     
    in
    (welldefined \<and> identity \<and> composition)" 


(* EXAMPLES *)


definition exConstantDiscrete :: "'A set \<Rightarrow> ('A, 'a) Presheaf" where
  "exConstantDiscrete X \<equiv>
    let 
      space = Space.exDiscrete X;
      discretePoset = Poset.exDiscrete; 
      ob = Function.const (opens space) UNIV discretePoset;
      ar = Function.const (inclusions space) UNIV (Poset.ident discretePoset) 
    in
    (| space = space, ob = ob, ar = ar |)" 



(* lemma exConstantDiscrete_valid : "valid (exConstantDiscrete X)"
  unfolding valid_def exConstantDiscrete_def
  apply (auto simp add: Let_def)
      apply (simp add: Space.exDiscrete_valid)
  unfolding Function.const_def exDiscrete_def  Function.app_def
     apply (simp add: Poset.exDiscrete_valid Function.app_def Function.const_def Function.dom_def)
  unfolding Poset.validMap_def Poset.ident_def *)


(*lemma exConstantDiscrete_valid : "valid (exConstantDiscrete X)"
  unfolding valid_def exConstantDiscrete_def Space.exDiscrete_def Poset.exDiscrete_def Poset.validMap_def
  apply ( simp add: Let_def) 
  apply safe
  unfolding Space.valid_def
            apply safe
                apply simp_all
  unfolding Poset.valid_def
           apply simp_all
  unfolding Function.app_def Function.const_def
              apply simp_all
  apply (simp add: subset_iff)
              apply blast
             apply blast
  apply (simp add: Function.dom_def Space.inclusions_def)
  unfolding Space.inclusions_def Space.validInclusion_def
          apply simp_all
          apply (smt (verit) CollectI Function.dom_def Function.select_convs(2) Poset.Poset.select_convs(1) Poset.ident_def PosetMap.select_convs(2) UNIV_I)
         apply (smt (z3) Function.dom_def Function.select_convs(2) Poset.Poset.select_convs(1) Poset.ident_def PosetMap.select_convs(3) UNIV_I mem_Collect_eq)
*)

lemma space_discrete: "(Presheaf.space (exConstantDiscrete X)) = Space.exDiscrete X"
  by (clarsimp simp: exConstantDiscrete_def Let_unfold)


lemma exConstantDiscrete_valid : "valid (exConstantDiscrete X)"
unfolding valid_def 
  apply ( simp_all add: Let_def)
  apply safe
      apply (clarsimp simp: exConstantDiscrete_def Let_unfold)
  apply ( simp_all add: Space.valid_def)
      apply safe
          apply (simp_all add: Space.exDiscrete_def space_discrete Function.app_def Poset.valid_def)
        apply blast
       apply blast
      apply blast
     apply (simp_all add: Function.dom_def)
     apply safe
                    apply (clarsimp simp: exConstantDiscrete_def Space.exDiscrete_def Poset.exDiscrete_def Function.const_def)
                    apply (smt (verit, best) Function.select_convs(2) Poset.Poset.select_convs(2) Presheaf.select_convs(2) mem_Collect_eq old.prod.inject theI)
  apply (simp add: Poset.valid_def)
   
  

      


(*  unfolding valid_def 
  apply (auto simp add: Let_def)
  apply (clarsimp simp: exConstantDiscrete_def Let_unfold)
      apply (rule exConstantDiscrete_space)
     apply (clarsimp simp: space_discrete)
     apply (subst app_iff_dom)
      apply (clarsimp simp: const_def)
     apply (simp)
     apply (rule exDiscrete_valid)
     apply (subst app_iff_dom)
     apply (clarsimp)
     apply (clarsimp simp: space_discrete)
    apply (clarsimp)
    apply (rule validMapI; clarsimp simp: space_discrete)
   apply (clarsimp simp: space_discrete app_iff_dom)
   apply (subst app_iff_dom; clarsimp)
  apply (erule cod_in_valid_inclusions)
  apply (clarsimp simp: space_discrete app_iff_dom)
  apply (subst app_iff_dom; clarsimp)
    apply (erule dom_in_valid_inclusions)
   apply (clarsimp simp: space_discrete)
   apply (subst app_iff_dom)
    apply (clarsimp)
    apply (clarsimp simp: inclusions_def)
  apply (clarsimp simp: ident_def)
    apply (clarsimp simp: validInclusion_def)
   apply (clarsimp)
   apply (clarsimp simp: app_iff_dom)
  apply (subst app_iff_dom)
   apply (clarsimp simp: space_discrete)
   apply (clarsimp simp: Space.compose_def, safe)
  apply (clarsimp simp: in_inclusions_when)
    apply (clarsimp simp: inclusions_def)
    apply (metis Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) validInclusion_def order_trans)
  apply (clarsimp simp: in_inclusions_when)
  apply (clarsimp simp: app_iff_dom space_discrete)
  by (clarsimp simp: Poset.compose_def)

*)

          
  
              
           
           

  

end