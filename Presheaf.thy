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

record ('A, 'a, 'b) PresheafMap =
  map_space :: "'A Space"
  nat :: "('A Open, ('a, 'b) PosetMap) Function"
  dom :: "('A, 'a) Presheaf"
  cod :: "('A, 'b) Presheaf"

definition valid_map :: "('A, 'a, 'b) PresheafMap \<Rightarrow> bool" where
 "valid_map \<phi> \<equiv>
    let
      space = (map_space \<phi>);
      f = nat \<phi>;

      welldefined = Space.valid space
                    \<and> valid (dom \<phi>) \<and> valid (cod \<phi>)
                    \<and> (Function.valid_map f)
                    \<and> (\<forall>A. A \<in> opens space \<longrightarrow> Poset.valid_map (f $ A))
                    \<and> (\<forall>A. A \<in> opens space \<longrightarrow> Poset.dom (f $ A) = (ob (dom \<phi>) $ A))
                    \<and> (\<forall>A. A \<in> opens space \<longrightarrow> Poset.cod (f $ A) = (ob (cod \<phi>) $ A));
      naturality = (\<forall>i. i \<in> inclusions space \<longrightarrow>
          (f $ Space.dom i) \<cdot> (ar (dom \<phi>) $ i) = (ar (cod \<phi>) $ i) \<cdot> (f $ Space.cod i))
    in
    (welldefined \<and> naturality)"

definition terminal :: "'A Space \<Rightarrow> ('A, unit) Presheaf" where
  "terminal T \<equiv>
    let
      space = T;
      ob = Function.const (Space.opens T) UNIV (Poset.discrete);
      ar = Function.const (Space.inclusions T) UNIV (Poset.ident Poset.discrete)
    in
    \<lparr> space = space, ob = ob, ar = ar \<rparr>
"

(* LEMMAS *)

lemma valid_welldefined  : "valid \<Phi> \<Longrightarrow> Space.valid (space \<Phi>) \<and> Function.valid_map (ob \<Phi>) \<and> Function.valid_map (ar \<Phi>)"
  unfolding valid_def by (simp add: Let_def)

lemma valid_identity  : "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> ar \<Phi> $ (Space.ident (space \<Phi>) A) = Poset.ident obA"
  unfolding valid_def by (simp add: Let_def)

lemma valid_composition :
  "valid \<Phi> \<Longrightarrow> j \<in> inclusions (space \<Phi>) \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar \<Phi> $ (Space.compose j i) = (ar \<Phi> $ i) \<cdot> (ar \<Phi> $ j)"
  by (metis Presheaf.valid_def)

lemma ident_app [simp] :  "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> a \<in> el obA \<Longrightarrow> 
  ar \<Phi> $ (Space.ident (space \<Phi>) A) $$ a = Poset.ident obA $$ a"
  by (simp add: valid_identity)

lemma space_valid : "valid \<Phi> \<Longrightarrow> Space.valid (space \<Phi>)"
  by (simp add: Presheaf.valid_welldefined)

lemma posets_valid : "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> Poset.valid ((ob \<Phi>) $ A)"
  by (metis Presheaf.valid_def)

lemma poset_maps_valid  : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> Poset.valid_map ((ar \<Phi>) $ i)"
  by (metis Presheaf.valid_def)

lemma dom_proj : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> B = Space.cod i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obB = ((ob \<Phi>) $ B) \<Longrightarrow> Poset.dom f = obB"
  by (metis Presheaf.valid_def)

lemma cod_proj : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.dom i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obA = ((ob \<Phi>) $ A) \<Longrightarrow> Poset.cod f = obA"
  by (metis Presheaf.valid_def)

lemma image : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i \<Longrightarrow> a \<in> Poset.el ((ob \<Phi>) $ A) \<Longrightarrow>
    (((ar \<Phi>) $ i) $$ a) \<in> Poset.el ((ob \<Phi>) $ B) "
  by (metis Poset.fun_app2 cod_proj dom_proj poset_maps_valid)

lemma terminal_valid : "Space.valid T \<Longrightarrow> valid (terminal T)"
  unfolding valid_def terminal_def
  apply (simp add: Let_def)
  apply safe
       apply (simp_all add:   discrete_valid ident_valid)
     apply (simp_all add: Poset.ident_def  valid_inclusion_cod valid_inclusion_dom const_valid)
  apply (smt (verit) Inclusion.select_convs(1) Space.ident_def UNIV_I const_app inclusions_def mem_Collect_eq valid_ident)
  by (smt (verit, best) Inclusion.select_convs(1) Poset.ident_def PosetMap.select_convs(3) Space.compose_def Space.compose_valid UNIV_I const_app discrete_valid ident_left_neutral ident_valid inclusions_def mem_Collect_eq)

(* EXAMPLES *)

definition ex_constant_discrete :: "('A, 'a) Presheaf" where
  "ex_constant_discrete  \<equiv>
    let
      space = Space.ex_discrete;
      discretePoset = Poset.discrete;
      ob = Function.const (opens space) UNIV discretePoset;
      ar = Function.const (inclusions space) UNIV (Poset.ident discretePoset)
    in
    (| space = space, ob = ob, ar = ar |)"

lemma ex_constant_discrete_valid : "valid ex_constant_discrete"
  unfolding valid_def
  apply (simp_all add: Let_def)
  apply safe
          apply (simp add: Space.ex_discrete_valid ex_constant_discrete_def)
         apply (simp add: ex_constant_discrete_def)
  apply (simp add: const_valid)
        apply (simp add: const_valid ex_constant_discrete_def)
  apply (simp add: discrete_valid ex_constant_discrete_def)
  apply (simp add: discrete_valid ex_constant_discrete_def ident_valid)
  apply (simp add: Poset.ident_def ex_constant_discrete_def ex_discrete_valid valid_inclusion_cod)
  apply (simp add: Poset.ident_def ex_constant_discrete_def ex_discrete_valid valid_inclusion_dom)
  apply (smt (verit) Inclusion.select_convs(1) Presheaf.Presheaf.select_convs(1) Presheaf.Presheaf.select_convs(2) Presheaf.Presheaf.select_convs(3) Space.ident_def UNIV_def const_app ex_constant_discrete_def ex_discrete_valid inclusions_def mem_Collect_eq valid_ident)
  by (smt (verit, del_insts) Inclusion.select_convs(1) Poset.ident_def PosetMap.select_convs(3) Presheaf.Presheaf.select_convs(1) Presheaf.Presheaf.select_convs(3) Space.compose_def Space.compose_valid UNIV_I const_app discrete_valid ex_constant_discrete_def ident_left_neutral ident_valid inclusions_def mem_Collect_eq)

end