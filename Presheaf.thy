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


definition exConstantDiscrete :: "('A, 'a) Presheaf" where
  "exConstantDiscrete  \<equiv>
    let 
      space = Space.exDiscrete;
      discretePoset = Poset.exDiscrete; 
      ob = Function.const (opens space) UNIV discretePoset;
      ar = Function.const (inclusions space) UNIV (Poset.ident discretePoset) 
    in
    (| space = space, ob = ob, ar = ar |)" 



lemma exConstantDiscrete_valid : "valid exConstantDiscrete"
  unfolding valid_def
  apply (simp_all add: Let_def)
  apply safe
  apply (simp_all add: exConstantDiscrete_def)
        apply (intro Space.exDiscrete_valid Poset.exDiscrete_valid)
  apply (intro Space.exDiscrete_valid Poset.exDiscrete_valid)
      apply (intro Poset.ident_valid)
     apply (simp_all add: Poset.ident_def Space.exDiscrete_def Space.ident_def)
   apply (intro Function.const_app)
    apply (simp_all add: Space.exDiscrete_def Space.ident_def Space.inclusions_def Space.validInclusion_def Space.compose_def Id_on_def)
  apply safe
  apply (simp_all add: Poset.exDiscrete_def relcomp_def Poset.compose_def)
  apply auto
  done

  

end
