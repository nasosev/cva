theory Presheaf
imports Main Poset Space Function
begin
declare [[show_types]]

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

      welldefined = (Space.valid space)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> opens space \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions space \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) );
      identity = (\<forall>A. A \<in> opens space \<longrightarrow> (\<Phi>1 $ (Space.ident space A)) = Poset.ident (\<Phi>0 $ A));
      composition = (\<forall>j i. j \<in> inclusions space \<longrightarrow> i \<in> inclusions space \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow>  (\<Phi>1 $ (Space.compose j i )) = (\<Phi>1 $ i) \<cdot> (\<Phi>1 $ j))
    in
    (welldefined \<and> identity \<and> composition)"


(* LEMMAS *)

lemma valid_welldefined [simp] : "valid \<Phi> \<Longrightarrow> Space.valid (space \<Phi>) \<and> Function.valid_map (ob \<Phi>) \<and> Function.valid_map (ar \<Phi>)"
  unfolding valid_def by (simp add: Let_def)

lemma valid_identity [simp] : "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> ar \<Phi> $ (Space.ident (space \<Phi>) A) = Poset.ident obA"
  unfolding valid_def by (simp add: Let_def)

lemma valid_composition [simp]: "valid \<Phi> \<Longrightarrow> j \<in> inclusions (space \<Phi>) \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar \<Phi> $ (Space.compose j i) = (ar \<Phi> $ i) \<cdot> (ar \<Phi> $ j)"
  by (metis Presheaf.valid_def)

lemma space_valid [simp]: "valid \<Phi> \<Longrightarrow> Space.valid (space \<Phi>)"
  by (metis Presheaf.valid_def)

lemma posets_valid [simp]: "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> Poset.valid ((ob \<Phi>) $ A)"
  by (metis Presheaf.valid_def)

lemma poset_maps_valid [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> Poset.valid_map ((ar \<Phi>) $ i)"
  by (metis Presheaf.valid_def)

lemma dom_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> B = Space.cod i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obB = ((ob \<Phi>) $ B) \<Longrightarrow> Poset.dom f = obB"
  by (metis Presheaf.valid_def)

lemma cod_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.dom i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obA = ((ob \<Phi>) $ A) \<Longrightarrow> Poset.cod f = obA"
  by (metis Presheaf.valid_def)

lemma image [simp]: "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> a \<in> Poset.el ((ob \<Phi>) $ (Space.cod i)) \<Longrightarrow>
    (((ar \<Phi>) $ i) $$ a) \<in> Poset.el ((ob \<Phi>) $ (Space.dom i)) "
  unfolding Presheaf.valid_def
  apply simp
  apply (simp add: Let_def)
  apply safe
  by (metis Poset.fun_app Poset.valid_map_def)





(* EXAMPLES *)


definition ex_constant_discrete :: "('A, 'a) Presheaf" where
  "ex_constant_discrete  \<equiv>
    let
      space = Space.ex_discrete;
      discretePoset = Poset.ex_discrete;
      ob = Function.const (opens space) UNIV discretePoset;
      ar = Function.const (inclusions space) UNIV (Poset.ident discretePoset)
    in
    (| space = space, ob = ob, ar = ar |)"



lemma ex_constant_discrete_valid : "valid ex_constant_discrete"
  unfolding valid_def

  


(*        apply (simp_all add: Function.valid_map_def)
apply (simp_all add: Poset.ident_def Space.ex_discrete_def Space.ident_def)
      apply safe
            apply (simp_all add :  Function.dom_def)
          apply auto
        apply (simp add:Function.const_def)
       apply (simp add:Function.const_def)
      apply (simp add:Function.const_def)
     apply (simp add:Function.const_def)
    apply (intro  Poset.ex_discrete_valid )
   apply (intro Function.const_app)
    apply (simp_all add: Space.ex_discrete_def Space.ident_def Space.inclusions_def Space.valid_inclusion_def Space.compose_def Id_on_def)
  apply safe
  apply (simp_all add: Poset.ex_discrete_def relcomp_def Poset.compose_def)
  apply auto
  done*)
end
