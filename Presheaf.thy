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

(*

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
                    \<and> (\<forall>x. x \<in> opens space \<longrightarrow> Poset.isValid (\<Phi>0 $ x))
                    \<and> (\<forall>i. i \<in> inclusions space \<longrightarrow> Poset.isValidMap (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) );
      identity = (\<forall>a. a \<in> opens space \<longrightarrow> (\<Phi>1 $ (Space.ident space a)) = Poset.ident (\<Phi>0 $ a));
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

lemma exConstantDiscrete_space : "Space.isValid (Space.exDiscrete X)"
  unfolding Space.isValid_def Space.exDiscrete_def
  apply (auto simp add: Let_def)
  done

lemma exDiscrete_isValid : "Poset.isValid (Poset.exDiscrete )"
  unfolding Poset.isValid_def Poset.exDiscrete_def
  apply (auto simp add: Let_def)
  done

lemma pos_le_refl: "Poset.isValid P \<Longrightarrow> x \<in> elements P \<Longrightarrow> le P x x"
  by (clarsimp simp: Poset.isValid_def)

lemma space_discrete: "(Presheaf.space (exConstantDiscrete X)) = Space.exDiscrete X"
  by (clarsimp simp: exConstantDiscrete_def Let_unfold)


lemma ob_exConstantDiscrete[simp]: 
  "ob (exConstantDiscrete X) = Function.const (opens (Space.exDiscrete X)) UNIV Poset.exDiscrete"
  by (clarsimp simp: exConstantDiscrete_def Let_unfold)


lemma ar_exConstantDiscrete[simp]: 
  "ar (exConstantDiscrete X) = Function.const (inclusions (Space.exDiscrete X)) UNIV (Poset.ident Poset.exDiscrete)"
  by (clarsimp simp: exConstantDiscrete_def Let_unfold)


lemma app_iff_dom: "x \<in> dom f \<Longrightarrow> (f $ x) = func f x"
  by (clarsimp simp: app_def)

lemma func_const[simp]: "Function.func (const d d' x ) y = x"
  by (clarsimp simp: const_def)

lemma dom_const[simp]: "Function.dom (const d d' x) = d"
  by (clarsimp simp: const_def)


lemma isValidMapI:
      "(\<And>x. x \<in> elements (PosetMap.dom F) \<Longrightarrow> PosetMap.func F x \<in> elements (PosetMap.cod F)) \<Longrightarrow> 
       (\<And>x y. x \<in> elements (PosetMap.dom F) \<Longrightarrow> y \<in> elements (PosetMap.dom F) \<Longrightarrow> le (PosetMap.dom F) x y \<Longrightarrow> le (PosetMap.cod F) (PosetMap.func F x) (PosetMap.func F y)) \<Longrightarrow>
       Poset.isValidMap F"
  by (clarsimp simp: Poset.isValidMap_def)

lemma dom_ident[simp]: "PosetMap.dom (Poset.ident f) = f"
  by (clarsimp simp: Poset.ident_def)


lemma cod_ident[simp]: "PosetMap.cod (Poset.ident f) = f"
  by (clarsimp simp: Poset.ident_def)

lemma ident_func[simp]: "PosetMap.func (Poset.ident x) = id"
   by (clarsimp simp: Poset.ident_def)

lemma cod_in_valid_inclusions: "i \<in> inclusions S \<Longrightarrow> Inclusion.cod i \<in> opens (S)"
  using inclusions_def isValidInclusion_def apply force
  done

lemma dom_in_valid_inclusions: "i \<in> inclusions S \<Longrightarrow> Inclusion.dom i \<in> opens (S)"
  using inclusions_def isValidInclusion_def apply force
  done


lemma space_of_ident[simp]: " Inclusion.space (Space.ident S a) = S"
  by (clarsimp simp: Space.ident_def)

lemma in_inclusions_when: "i \<in> inclusions S \<Longrightarrow> Inclusion.space i = S"
  by (clarsimp simp: inclusions_def)

lemma exConstantDiscrete_isValid : "isValid (exConstantDiscrete X)"
  unfolding isValid_def 
  apply (auto simp add: Let_def)
  apply (clarsimp simp: exConstantDiscrete_def Let_unfold)
      apply (rule exConstantDiscrete_space)
     apply (clarsimp simp: space_discrete)
     apply (subst app_iff_dom)
      apply (clarsimp simp: const_def)
     apply (simp)
     apply (rule exDiscrete_isValid)
     apply (subst app_iff_dom)
     apply (clarsimp)
     apply (clarsimp simp: space_discrete)
    apply (clarsimp)
    apply (rule isValidMapI; clarsimp simp: space_discrete)
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
    apply (clarsimp simp: isValidInclusion_def)
   apply (clarsimp)
   apply (clarsimp simp: app_iff_dom)
  apply (subst app_iff_dom)
   apply (clarsimp simp: space_discrete)
   apply (clarsimp simp: Space.compose_def, safe)
  apply (clarsimp simp: in_inclusions_when)
    apply (clarsimp simp: inclusions_def)
    apply (metis Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) isValidInclusion_def order_trans)
  apply (clarsimp simp: in_inclusions_when)
  apply (clarsimp simp: app_iff_dom space_discrete)
  by (clarsimp simp: Poset.compose_def)

         
  

end *)