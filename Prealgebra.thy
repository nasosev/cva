section \<open> Prealgebra.thy \<close>

theory Prealgebra
imports Main Function Space Poset Presheaf
begin

(* Prealgebra type (poset-valued presheaf) *)

record ('A, 'a) Prealgebra =
  space :: "'A Space"
  ob :: "('A Open, 'a Poset) Function"
  ar :: "('A Inclusion, ('a, 'a) PosetMap) Function"

definition valid :: "('A, 'a) Prealgebra \<Rightarrow> bool" where
  "valid F \<equiv>
    let
      welldefined = Space.valid (space F)
                    \<and> (Function.valid_map (ob F)) \<and> (Function.valid_map (ar F))
                    \<and> (\<forall>A. A \<in> opens (space F) \<longrightarrow> Poset.valid (ob F \<cdot> A))
                    \<and> (\<forall>i. i \<in> inclusions (space F) \<longrightarrow> Poset.valid_map (ar F \<cdot> i)
                           \<and>  Poset.dom (ar F \<cdot> i) = ob F \<cdot> Space.cod i
                           \<and>  Poset.cod (ar F \<cdot> i) = ob F \<cdot> Space.dom i );
      identity = (\<forall>A. A \<in> opens (space F) \<longrightarrow> (ar F \<cdot> (Space.ident A)) = Poset.ident (ob F \<cdot> A));
      composition = (\<forall>j i. j \<in> inclusions (space F) \<longrightarrow> i \<in> inclusions (space F) \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  ar F \<cdot> (j \<propto> i) = (ar F \<cdot> i) \<diamondop> (ar F \<cdot> j))
    in
    welldefined \<and> identity \<and> composition"

(* PrealgebraMap type (natural transformation *)

record ('A, 'a, 'b) PrealgebraMap =
  dom :: "('A, 'a) Prealgebra"
  cod :: "('A, 'b) Prealgebra"
  nat :: "('A Open, ('a, 'b) PosetMap) Function"

abbreviation map_space :: "('A, 'a, 'b) PrealgebraMap \<Rightarrow> 'A Space" where
"map_space f \<equiv> space (dom f)"

definition valid_map :: "('A, 'a, 'b) PrealgebraMap \<Rightarrow> bool" where
 "valid_map f \<equiv>
    let
      welldefined = Space.valid (map_space f)
                    \<and> map_space f = space (cod f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> (Function.valid_map (nat f))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Poset.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Poset.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Poset.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A));
      naturality = (\<forall>i. i \<in> inclusions (map_space f) \<longrightarrow>
          (nat f \<cdot> Space.dom i) \<diamondop> (ar (dom f) \<cdot> i) = (ar (cod f) \<cdot> i) \<diamondop> (nat f \<cdot> Space.cod i))
    in
    (welldefined \<and> naturality)"

(* Presheaf validity *)

lemma validI [intro] :
  fixes F :: "('A,'a) Prealgebra"
  assumes welldefined_space : "Space.valid (space F)"
  and welldefined_valid_ob : "Function.valid_map (ob F)"
  and welldefined_valid_ar : "Function.valid_map (ar F)"
  and welldefined_ob : "\<And>A. A \<in> opens (space F) \<Longrightarrow> Poset.valid (ob F \<cdot> A)"
  and welldefined_ar : "\<And>i. i \<in> inclusions (space F) \<Longrightarrow> Poset.valid_map (ar F \<cdot> i)"
  and welldefined_ar_dom : "\<And>i. i \<in> inclusions (space F) \<Longrightarrow> Poset.dom (ar F \<cdot> i) = (ob F \<cdot> Space.cod i)"
  and welldefined_ar_cod : "\<And>i. i \<in> inclusions (space F) \<Longrightarrow> Poset.cod (ar F \<cdot> i) = (ob F \<cdot> Space.dom i)"
  and identity : "(\<And>A. A \<in> opens (space F) \<Longrightarrow> (ar F \<cdot> (Space.ident A)) = Poset.ident (ob F \<cdot> A))"
  and composition :" (\<And>i j. j \<in> inclusions (space F) \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow>
        Space.dom j = Space.cod i \<Longrightarrow> (ar F \<cdot> (j \<propto> i )) = (ar F \<cdot> i) \<diamondop> (ar F \<cdot> j))"
  shows "valid F"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  apply (simp add: welldefined_space)
  apply (simp add: welldefined_valid_ob)
  apply (simp add: welldefined_valid_ar)
  apply (simp add: welldefined_ob)
  apply (simp add: welldefined_ar)
  apply (simp add: welldefined_ar_dom)
  apply (simp add: welldefined_ar_cod)
  using identity apply presburger
  by (simp add: composition)

lemma valid_welldefined  : "valid F \<Longrightarrow> let T = space F; F0 = ob F; F1 = ar F in (Space.valid T)
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Poset.valid (F0 \<cdot> A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (F1 \<cdot> i)
                           \<and>  Poset.dom (F1 \<cdot> i) = (F0 \<cdot> Space.cod i)
                           \<and>  Poset.cod (F1 \<cdot> i) = (F0 \<cdot> Space.dom i) )"
  unfolding valid_def by (simp add: Let_def)

lemma valid_space : "valid F \<Longrightarrow> Space.valid (space F)"
  by (meson Prealgebra.valid_welldefined)

lemma valid_ob : "valid F \<Longrightarrow> A \<in> opens (space F) \<Longrightarrow> Poset.valid (ob F \<cdot> A)"
  unfolding valid_def by (simp add: Let_def)

lemma valid_ar :
  fixes F :: "('A, 'a) Prealgebra" and i :: "'A Inclusion"
  assumes "valid F"
  and "i \<in> inclusions (space F)"
  shows "Poset.valid_map (ar F \<cdot> i)"
proof -
  define "F1" where "F1 = Prealgebra.ar F" 
  define "T" where "T = Prealgebra.space F" 
  have "(\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (F1 \<cdot> i))"  using valid_welldefined 
    by (metis (mono_tags, lifting) F1_def T_def assms(1)) 
    moreover have "i \<in> inclusions T"
      using T_def assms(2) by fastforce 
    moreover have "Poset.valid_map (F1 \<cdot> i)"
      using calculation(1) calculation(2) by auto
    ultimately show ?thesis
      using F1_def by force 
  qed

lemma valid_dom : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Poset.dom (ar F \<cdot> i) = ob F \<cdot> Space.cod i"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_cod : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Poset.cod (ar F \<cdot> i) = ob F \<cdot> Space.dom i"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_identity  : "valid F \<Longrightarrow> A \<in> opens (space F) \<Longrightarrow> ar F \<cdot> (Space.ident A) = Poset.ident (ob F \<cdot> A)"
  unfolding valid_def by (simp add: Let_def)

lemma valid_composition :
  "valid F \<Longrightarrow> j \<in> inclusions (space F) \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar F \<cdot> (j \<propto> i) = (ar F \<cdot> i) \<diamondop> (ar F \<cdot> j)" 
  unfolding valid_def
  by meson 

(* PresheafMap validity *)

lemma valid_mapI [intro] :
  fixes f :: "('A,'a,'b) PrealgebraMap"
  assumes welldefined : "Space.valid (map_space f)"
  and welldefined_spaces : "map_space f = space (cod f)"
  and welldefined_map : "Function.valid_map (nat f)"
  and welldefined_dom : "valid (dom f)"
  and welldefined_cod : "valid (cod f)"
  and welldefined_nat_val : "\<And>A. A \<in> opens (map_space f) \<Longrightarrow> Poset.valid_map (nat f \<cdot> A)"
  and welldefined_nat_dom : "\<And>A. A \<in> opens (map_space f) \<Longrightarrow> Poset.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A)"
  and welldefined_nat_cod : "\<And>A. A \<in> opens (map_space f) \<Longrightarrow> Poset.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A)"
  and naturality : "(\<And>i. i \<in> inclusions (map_space f) \<Longrightarrow>
          (nat f \<cdot> Space.dom i) \<diamondop> (ar (dom f) \<cdot> i) = (ar (cod f) \<cdot> i) \<diamondop> (nat f \<cdot> Space.cod i))"
  shows "valid_map f"
  unfolding valid_map_def
  apply (simp add: Let_def)
  apply safe
  apply (simp add: welldefined)
  apply (simp add: welldefined_spaces)
  apply (simp add: welldefined_dom)
  apply (simp add: welldefined_cod)
  apply (simp add: welldefined_map)
  using welldefined_nat_val apply blast
  using welldefined_nat_dom apply blast
  using welldefined_nat_cod apply blast
  by (simp add: naturality)

lemma valid_map_welldefined :
  "valid_map f \<Longrightarrow> Function.valid_map (nat f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Poset.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Poset.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Poset.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A))"
  by (meson Prealgebra.valid_map_def)

lemma valid_map_space : "valid_map f \<Longrightarrow> Space.valid (map_space f)"
  by (simp add: Prealgebra.valid_map_welldefined Prealgebra.valid_space)
 
lemma valid_map_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat : "valid_map f \<Longrightarrow> Function.valid_map (nat f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_welldefined :
  "valid_map f \<Longrightarrow> A \<in> opens (map_space f) \<Longrightarrow> Poset.valid_map (nat f \<cdot> A)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_dom : "valid_map f \<Longrightarrow> A \<in> opens (map_space f) \<Longrightarrow> Poset.dom ((nat f) \<cdot> A) = ob (dom f) \<cdot> A"
  by (meson Prealgebra.valid_map_welldefined)

lemma valid_map_nat_cod : "valid_map f \<Longrightarrow> A \<in> opens (map_space f) \<Longrightarrow> Poset.cod ((nat f) \<cdot> A) = ob (cod f) \<cdot> A"
  by (meson Prealgebra.valid_map_welldefined)

lemma valid_map_naturality :
  "valid_map f \<Longrightarrow> i \<in> inclusions (map_space f) \<Longrightarrow>
     (ar (cod f) \<cdot> i) \<diamondop> (nat f \<cdot> Space.cod i) = (nat f \<cdot> Space.dom i) \<diamondop> (ar (dom f) \<cdot> i)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_image :
  fixes f :: "('A, 'a, 'b) PrealgebraMap" and A :: "'A Open" and a :: "'a"
  defines "FA \<equiv> Prealgebra.ob (dom f) \<cdot> A"
  defines "F'A \<equiv> Prealgebra.ob (cod f) \<cdot> A"
  defines "fA \<equiv> (nat f) \<cdot> A"
  assumes f_valid :"valid_map f"
  and A_open : "A \<in> opens (map_space f)"
  and a_dom : "a \<in> Poset.el FA"
shows "fA \<star> a \<in> Poset.el F'A"
  by (metis A_open F'A_def FA_def Poset.fun_app2 Prealgebra.valid_map_welldefined a_dom fA_def f_valid)

(* Application *)

lemma ident_app [simp] :
 "valid F \<Longrightarrow> A \<in> opens (space F) \<Longrightarrow> 
  ar F \<cdot> (Space.ident A) \<star> a = Poset.ident (ob F \<cdot> A) \<star> a"
  by (simp add: valid_identity)

lemma image : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> a \<in> Poset.el (ob F \<cdot> (Space.cod i)) \<Longrightarrow>
    ((ar F \<cdot> i) \<star> a) \<in> Poset.el (ob F \<cdot> (Space.dom i)) "
  using Poset.fun_app2 valid_ar
  using valid_cod valid_dom by fastforce 

(* Restriction *)

lemma restricted_element :
  fixes F :: "('A, 'a) Prealgebra" and A B :: "'A Open" and a :: "'a"
  assumes F_valid :"valid F"
  and A_open : "A \<in> opens (space F)" and B_open : "B \<in> opens (space F)" 
  and B_le_A : "B \<subseteq> A"
  and x_el : "a \<in> el (ob F \<cdot> A)"
defines "i \<equiv> make_inc B A"
shows "(ar F \<cdot> i) \<star> a \<in> el (ob F \<cdot> B)"
  by (metis (no_types, lifting) A_open B_le_A B_open F_valid Inclusion.select_convs(1) Inclusion.select_convs(2) Prealgebra.image i_def inclusions_def mem_Collect_eq x_el) 

lemma res_dom [simp] : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Poset.dom (ar F \<cdot> i) = ob F \<cdot> (Space.cod i)"
  using valid_dom by blast

lemma res_cod [simp] : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Poset.cod (ar F \<cdot> i) = ob F \<cdot> (Space.dom i)"
  using valid_cod by blast

lemma res_monotone : 
  fixes F :: "('A,'a) Prealgebra" and i :: "'A Inclusion" and  a a' :: "'a"
  defines "FA \<equiv> Prealgebra.ob F \<cdot> (Space.cod i)"
  defines "FB \<equiv> Prealgebra.ob F \<cdot> (Space.dom i)"
  defines "Fi \<equiv> Prealgebra.ar F \<cdot> i"
  assumes F_valid : "valid F"
  and i_inc : "i \<in> inclusions (space F)" 
  and a_elem : "a \<in> Poset.el FA" and a'_elem : "a' \<in> Poset.el FA" 
  and a_le_a' : "Poset.le FA a a'"
shows "Poset.le FB (Fi \<star> a) (Fi \<star> a')"
  by (metis FA_def FB_def F_valid Fi_def Prealgebra.valid_ar Prealgebra.valid_cod Prealgebra.valid_dom a'_elem a_elem a_le_a' assms(5) valid_map_monotone)

lemma diamond_rule :
  fixes F :: "('A, 'a) Prealgebra" and A B C D :: "'A Open" and a :: "'a"
  assumes F_valid :"valid F"
  and A_open : "A \<in> opens (space F)" and B_open : "B \<in> opens (space F)" 
  and C_open : "C \<in> opens (space F)" and D_open : "D \<in> opens (space F)" 
  and B_le_A : "B \<subseteq> A" and C_le_A : "C \<subseteq> A" 
  and D_le_B : "D \<subseteq> B" and D_le_C : "D \<subseteq> C" 
  and a_el : "a \<in> el (ob F \<cdot> A)"
  defines "i_BA \<equiv> make_inc B A"
  and "i_CA \<equiv> make_inc C A"
  and "i_DB \<equiv> make_inc D B"
  and "i_DC \<equiv> make_inc D C"
shows "(ar F \<cdot> i_DB) \<star> ((ar F \<cdot> i_BA) \<star> a) = (ar F \<cdot> i_DC) \<star> ((ar F \<cdot> i_CA) \<star> a)"
  by (smt (verit) A_open B_le_A B_open C_le_A C_open D_le_B D_le_C D_open F_valid Inclusion.equality Inclusion.select_convs(1) Inclusion.select_convs(2) Poset.compose_app_assoc Prealgebra.valid_ar Prealgebra.valid_cod Prealgebra.valid_composition Prealgebra.valid_dom a_el cod_compose_inc dom_compose_inc i_BA_def i_CA_def i_DB_def i_DC_def inclusions_def mem_Collect_eq old.unit.exhaust)

(* Forgetful functor from [T, Pos] to [T, Set] *)

definition forget ::  "('A, 'a) Prealgebra \<Rightarrow> ('A, 'a) Presheaf" where
  "forget F \<equiv>
    \<lparr> Presheaf.space = space F, 

      ob = \<lparr> Function.cod = { el P | P . P \<in> Function.cod (ob F) }, 
             func = { (A, el (ob F \<cdot> A)) | A . A \<in> opens (space F) } \<rparr>, 

      ar =  \<lparr> Function.cod = { Poset.forget_map f | f . f \<in> Function.cod (ar F) }, 
             func = { (i, Poset.forget_map (ar F \<cdot> i)) | i . i \<in> inclusions (space F) } \<rparr> \<rparr>"

lemma forget_valid : "valid F \<Longrightarrow> Presheaf.valid (forget F)"
  oops
 
(* Examples *)

definition const ::  "'A Space \<Rightarrow> ('A, 'a) Prealgebra" where
  "const T \<equiv>
    let
      ob = Function.const (opens T) UNIV Poset.discrete;
      ar = Function.const (inclusions T) UNIV (Poset.ident Poset.discrete)
    in
    \<lparr> space = T, ob = ob, ar = ar \<rparr>"

lemma const_ob [simp] : "Space.valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> ob (const T) \<cdot> A = Poset.discrete"
  by (smt (verit) Function.const_app Prealgebra.Prealgebra.select_convs(2) Prealgebra.const_def UNIV_I) 

lemma const_ar [simp] : "Space.valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> ar (const T) \<cdot> i = Poset.ident Poset.discrete"
  by (metis Function.const_app Prealgebra.Prealgebra.select_convs(3) Prealgebra.const_def UNIV_I)

lemma const_value_res [simp] : "Space.valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> a \<in> el (ob (const T) \<cdot> (Space.cod i)) 
\<Longrightarrow> (ar (const T) \<cdot> i) \<star> a = a"
  by (simp add: discrete_valid valid_inc_cod)

lemma const_valid : "Space.valid T \<Longrightarrow> valid (const T)"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (simp add: Prealgebra.const_def)  
next
  case 2
  then show ?case
    by (metis Function.const_valid Prealgebra.Prealgebra.select_convs(2) Prealgebra.const_def UNIV_I valid_universe)
next
  case 3
  then show ?case
    by (metis Function.const_valid Prealgebra.Prealgebra.select_convs(3) Prealgebra.const_def UNIV_I valid_empty valid_ident_inc)
next
  case (4 A)
  then show ?case
    by (metis Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ob discrete_valid)
next
  case (5 i)
  then show ?case
    by (metis Poset.ident_valid Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar discrete_valid)
next
  case (6 i)
  then show ?case
    by (metis Poset.ident_dom Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar const_ob valid_inc_cod)                            
next
  case (7 i)
  then show ?case
    by (metis Poset.ident_cod Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar const_ob valid_inc_dom)
next
  case (8 A)
  then show ?case
    by (metis Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar const_ob valid_ident_inc)
next
  case (9 i j)
  then show ?case
    by (smt (verit, ccfv_threshold) CollectD CollectI Poset.compose_ident_left Poset.ident_cod Poset.ident_valid Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def cod_compose_inc compose_inc_valid const_ar discrete_valid dom_compose_inc inclusions_def)
qed 

abbreviation terminal :: "'A Space \<Rightarrow> ('A, unit) Prealgebra" where
"terminal \<equiv> const"

lemma terminal_ob [simp] : "Space.valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> ob (terminal T) \<cdot> A = Poset.discrete"
  by simp 

lemma terminal_ar [simp] : "Space.valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> ar (terminal T) \<cdot> i = Poset.ident Poset.discrete"
  by simp 

lemma terminal_value [simp] : "Space.valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> Poset.el (ob (terminal T) \<cdot> A) = {()}"
  by (simp add: Poset.discrete_def UNIV_unit) 

lemma terminal_value_res [simp] : "Space.valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> (ar (terminal T) \<cdot> i) \<star> a = ()"
  by simp

lemma terminal_valid : "Space.valid T \<Longrightarrow> valid (terminal T)"
  by (simp add: Prealgebra.const_valid) 

end
