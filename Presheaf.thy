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
      T = space \<Phi>;
      \<Phi>0 = ob \<Phi>;
      \<Phi>1 = ar \<Phi>;

      welldefined = (Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = \<Phi>0 $ (Space.cod i)
                           \<and>  Poset.cod (\<Phi>1 $ i) = \<Phi>0 $ (Space.dom i) );
      identity = (\<forall>A. A \<in> opens T \<longrightarrow> (\<Phi>1 $ (Space.ident T A)) = Poset.ident (\<Phi>0 $ A));
      composition = (\<forall>j i. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  \<Phi>1 $ (Space.compose j i ) = (\<Phi>1 $ i) \<cdot> (\<Phi>1 $ j))
    in
    welldefined \<and> identity \<and> composition"

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

(* To-do: can we prove this with meta implications?*)
lemma validI :
  fixes \<Phi> :: "('A,'a) Presheaf"
  defines "T \<equiv> space \<Phi>"
  defines "\<Phi>0 \<equiv> ob \<Phi>"
  defines "\<Phi>1 \<equiv> ar \<Phi>"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) )"
  assumes identity : "(\<forall>A. A \<in> opens T \<longrightarrow> (\<Phi>1 $ (Space.ident T A)) = Poset.ident (\<Phi>0 $ A))"
  assumes composition :" (\<forall> i j. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow> (\<Phi>1 $ (Space.compose j i )) = (\<Phi>1 $ i) \<cdot> (\<Phi>1 $ j))"
  shows "valid \<Phi>"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using \<Phi>0_def welldefined apply blast
  using \<Phi>1_def welldefined apply fastforce
  using T_def \<Phi>0_def welldefined apply presburger
  using T_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def identity apply blast
  using T_def \<Phi>1_def composition by blast

lemma valid_welldefined  : "valid \<Phi> \<Longrightarrow> let T = space \<Phi>; \<Phi>0 = ob \<Phi>; \<Phi>1 = ar \<Phi> in (Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) )"
  unfolding valid_def by (simp add: Let_def)

lemma valid_space  : "valid \<Phi> \<Longrightarrow> T = space \<Phi> \<Longrightarrow> (Space.valid T)"
  by (meson Presheaf.valid_welldefined)

lemma valid_ob  : "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> Poset.valid obA"
  unfolding valid_def by (simp add: Let_def)

(* To-do: why wont this prove?
lemma valid_ar  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> $ i =  Poset.valid_map ari"
 *)

lemma valid_ar  : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> Poset.valid_map ((ar \<Phi>) $ i)"
  by (metis Presheaf.valid_def)

lemma valid_dom  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> $ i \<Longrightarrow> Poset.dom ari = ob \<Phi> $ (Space.cod i)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_cod  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> $ i \<Longrightarrow> Poset.cod ari = ob \<Phi> $ (Space.dom i)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_identity  : "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> ar \<Phi> $ (Space.ident (space \<Phi>) A) = Poset.ident obA"
  unfolding valid_def by (simp add: Let_def)

lemma valid_composition :
  "valid \<Phi> \<Longrightarrow> j \<in> inclusions (space \<Phi>) \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar \<Phi> $ (Space.compose j i) = (ar \<Phi> $ i) \<cdot> (ar \<Phi> $ j)"
  by (metis Presheaf.valid_def)

lemma valid_mapI :
  fixes \<phi> :: "('A,'a,'b) PresheafMap"
  defines "T \<equiv> map_space \<phi>"
  defines "f \<equiv> nat \<phi>"
  defines "\<Phi> \<equiv> dom \<phi>"
  defines "\<Phi>' \<equiv> cod \<phi>"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map f)
                    \<and> valid \<Phi> \<and> valid \<Phi>'
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.valid_map (f $ A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.dom (f $ A) = (ob \<Phi> $ A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.cod (f $ A) = (ob \<Phi>' $ A))"
  assumes naturality : "(\<forall>i. i \<in> inclusions T \<longrightarrow>
          (f $ Space.dom i) \<cdot> (ar \<Phi> $ i) = (ar \<Phi>' $ i) \<cdot> (f $ Space.cod i))"
  shows "valid_map \<phi>"
  unfolding valid_map_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using \<Phi>_def welldefined apply blast
  using \<Phi>'_def welldefined apply blast
  using f_def welldefined apply blast
  using T_def f_def welldefined apply blast
  using T_def \<Phi>_def f_def welldefined apply presburger
  using T_def \<Phi>'_def f_def welldefined apply presburger
  using T_def \<Phi>'_def \<Phi>_def f_def naturality by presburger

lemma valid_map_welldefined :
  "valid_map \<phi> \<Longrightarrow> let f = nat \<phi>; \<Phi> = dom \<phi>; \<Phi>' = cod \<phi>; T = map_space \<phi> in (Space.valid T)
                    \<and> (Function.valid_map f)
                    \<and> valid \<Phi> \<and> valid \<Phi>'
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.valid_map (f $ A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.dom (f $ A) = (ob \<Phi> $ A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.cod (f $ A) = (ob \<Phi>' $ A))"
  by (metis Presheaf.valid_map_def)

lemma valid_map_space : "valid_map \<phi> \<Longrightarrow> Space.valid (map_space \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_dom : "valid_map \<phi> \<Longrightarrow> valid (dom \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_cod : "valid_map \<phi> \<Longrightarrow> valid (cod \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat : "valid_map \<phi> \<Longrightarrow> Function.valid_map (nat \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_welldefined :
  "valid_map \<phi> \<Longrightarrow> A \<in> opens (map_space \<phi>) \<Longrightarrow> Poset.valid_map (nat \<phi> $ A)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_dom : "valid_map \<phi> \<Longrightarrow> A \<in> opens (map_space \<phi>) \<Longrightarrow> Poset.dom ((nat \<phi>) $ A) = ob (dom \<phi>) $ A"
  by (meson Presheaf.valid_map_welldefined)

lemma valid_map_nat_cod : "valid_map \<phi> \<Longrightarrow> A \<in> opens (map_space \<phi>) \<Longrightarrow> Poset.cod ((nat \<phi>) $ A) = ob (cod \<phi>) $ A"
  by (meson Presheaf.valid_map_welldefined)

lemma valid_map_naturality :
  "valid_map \<phi> \<Longrightarrow> i \<in> inclusions (map_space \<phi>) \<Longrightarrow>
     (ar (cod \<phi>) $ i) \<cdot> (nat \<phi> $ Space.cod i) = (nat \<phi> $ Space.dom i) \<cdot> (ar (dom \<phi>) $ i)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_image :
  fixes \<phi> :: "('A, 'a, 'b) PresheafMap" and A :: "'A Open" and a :: "'a"
  defines "\<Phi>A \<equiv> Presheaf.ob (dom \<phi>) $ A"
  defines "\<Phi>'A \<equiv> Presheaf.ob (cod \<phi>) $ A"
  defines "f \<equiv> (nat \<phi>) $ A"
  assumes \<phi>_valid :"valid_map \<phi>"
  and A_open : "A \<in> Space.opens (map_space \<phi>)"
  and a_dom : "a \<in> Poset.el \<Phi>A"
shows " f $$ a \<in> Poset.el \<Phi>'A"
proof -
  have "valid_map \<phi>"
    using \<phi>_valid by force
  moreover have "A \<in> Space.opens (map_space \<phi>)"
    using A_open by blast
  moreover have "a \<in> Poset.el \<Phi>A"
    using a_dom by blast
  moreover have "Poset.dom f = \<Phi>A"
    by (metis A_open Presheaf.valid_map_welldefined \<Phi>A_def \<phi>_valid f_def)
  moreover have "Poset.valid_map f"
    by (metis A_open Presheaf.valid_map_welldefined \<phi>_valid f_def)
  moreover have "Poset.cod f = \<Phi>'A"
    by (metis A_open Presheaf.valid_map_welldefined \<Phi>'A_def \<phi>_valid f_def)
  ultimately show ?thesis
    by (meson Poset.fun_app2)
qed

lemma ident_app [simp] :
 "valid \<Phi> \<Longrightarrow> A \<in> opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> a \<in> el obA \<Longrightarrow>
  ar \<Phi> $ (Space.ident (space \<Phi>) A) $$ a = Poset.ident obA $$ a"
  by (simp add: valid_identity)

lemma dom_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> B = Space.cod i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obB = ((ob \<Phi>) $ B) \<Longrightarrow> Poset.dom f = obB"
  by (metis Presheaf.valid_def)

lemma cod_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.dom i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obA = ((ob \<Phi>) $ A) \<Longrightarrow> Poset.cod f = obA"
  by (metis Presheaf.valid_def)

lemma image : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i \<Longrightarrow> a \<in> Poset.el ((ob \<Phi>) $ A) \<Longrightarrow>
    (((ar \<Phi>) $ i) $$ a) \<in> Poset.el ((ob \<Phi>) $ B) "
  by (metis Poset.fun_app2 cod_proj dom_proj valid_ar)

lemma prj_monotone : "Presheaf.valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i
\<Longrightarrow> \<Phi>A = Presheaf.ob \<Phi> $ A \<Longrightarrow>  \<Phi>B = Presheaf.ob \<Phi> $ B \<Longrightarrow> a \<in> Poset.el \<Phi>A \<Longrightarrow> a' \<in> Poset.el \<Phi>'A \<Longrightarrow> Poset.le \<Phi>A a a'
 \<Longrightarrow> \<Phi>i = Presheaf.ar \<Phi> $ i \<Longrightarrow> Poset.le \<Phi>B (\<Phi>i $$ a) (\<Phi>i $$ a')"
  by (metis Poset.valid_welldefined Presheaf.valid_cod Presheaf.valid_dom valid_ar valid_inclusion_cod valid_monotonicity valid_ob valid_space)

lemma terminal_valid : "Space.valid T \<Longrightarrow> valid (terminal T)"
  unfolding valid_def terminal_def
  apply (simp add: Let_def)
  apply safe
       apply (simp_all add:   discrete_valid ident_valid)
     apply (simp_all add: Poset.ident_def  valid_inclusion_cod valid_inclusion_dom const_valid)
  apply (smt (verit) Inclusion.select_convs(1) Space.ident_def UNIV_I const_app inclusions_def mem_Collect_eq valid_ident)
  by (smt (verit, best) Inclusion.select_convs(1) Poset.ident_def PosetMap.select_convs(3) Space.compose_def Space.compose_valid UNIV_I const_app discrete_valid ident_left_neutral ident_valid inclusions_def mem_Collect_eq)

lemma terminal_value : "Space.valid T \<Longrightarrow> A \<in> Space.opens T \<Longrightarrow> one = terminal T \<Longrightarrow> Poset.el (ob one $ A) = {()}"
  by (simp add: UNIV_unit discrete_def terminal_def)

lemma terminal_value_proj : "Space.valid T \<Longrightarrow> i \<in> Space.inclusions T \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i
\<Longrightarrow> a \<in> Poset.el (ob one $ A) \<Longrightarrow> prj = (ar one) $ i \<Longrightarrow> prj $$ a = ()"
  by simp

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
  apply (intro validI)
    apply safe
          apply (simp_all add: ex_constant_discrete_def ex_discrete_valid)
         apply (simp_all add: const_valid)
       apply (simp_all add: discrete_valid)
      apply (simp_all add: discrete_valid ident_valid)
     apply (simp_all add: Poset.ident_def ex_discrete_valid valid_inclusion_cod)
    apply (simp_all add: ex_discrete_valid valid_inclusion_dom)
  apply (smt (verit, del_insts) Inclusion.select_convs(1) Space.ident_def UNIV_I const_app ex_discrete_valid inclusions_def mem_Collect_eq valid_ident)
  by (smt (verit, ccfv_threshold) Inclusion.select_convs(1) Poset.ident_def PosetMap.select_convs(3) Space.compose_def Space.compose_valid UNIV_I const_app discrete_valid ident_left_neutral ident_valid inclusions_def mem_Collect_eq)

end