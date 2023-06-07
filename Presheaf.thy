theory Presheaf
imports Main Poset Space Function
begin


record ('A, 'a) Presheaf =
  space :: "'A Space"
  ob :: "('A Open, 'a Poset) Function "
  ar :: "('A Inclusion, ('a, 'a) PosetMap) Function"

definition isValid :: "('A, 'a) Presheaf \<Rightarrow> bool" where
  "isValid \<Phi> \<equiv> 
    let 
      space = (space \<Phi>);
      \<Phi>0 = ob \<Phi>;
      \<Phi>1 = ar \<Phi>;
      welldefined = Space.isValid space 
                    \<and> (\<forall>A. A \<in> opens space \<longrightarrow> Poset.isValid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions space \<longrightarrow> Poset.isValidMap (\<Phi>1 $ i)
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



(* lemma exConstantDiscrete_isValid : "isValid (exConstantDiscrete X)"
  unfolding isValid_def exConstantDiscrete_def
  apply (auto simp add: Let_def)
      apply (simp add: Space.exDiscrete_isValid)
  unfolding Function.const_def exDiscrete_def  Function.app_def
     apply (simp add: Poset.exDiscrete_isValid Function.app_def Function.const_def Function.dom_def)
  unfolding Poset.isValidMap_def Poset.ident_def *)


lemma exConstantDiscrete_isValid : "isValid (exConstantDiscrete X)"
  unfolding isValid_def exConstantDiscrete_def Space.exDiscrete_def Poset.exDiscrete_def Poset.isValidMap_def
  apply ( simp add: Let_def) 
  apply safe
  unfolding Space.isValid_def
            apply safe
                apply simp_all
  unfolding Poset.isValid_def
           apply simp_all
  unfolding Function.app_def Function.const_def
              apply simp_all
  apply (simp add: subset_iff)
              apply blast
             apply blast
  
              
           
           

  

end