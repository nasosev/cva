section \<open> Prealgebra.thy \<close>

theory Prealgebra
imports Main Poset Space Function
begin

(* Prealgebra type (poset-valued presheaf) *)

record ('A, 'a) Prealgebra =
  space :: "'A Space"
  ob :: "('A Open, 'a Poset) Function "
  ar :: "('A Inclusion, ('a, 'a) PosetMap) Function"

definition valid :: "('A, 'a) Prealgebra \<Rightarrow> bool" where
  "valid F \<equiv>
    let
      T = space F;
      F0 = ob F;
      F1 = ar F;

      welldefined = Space.valid T
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (F0 \<cdot> A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (F1 \<cdot> i)
                           \<and>  Poset.dom (F1 \<cdot> i) = F0 \<cdot> Space.cod i
                           \<and>  Poset.cod (F1 \<cdot> i) = F0 \<cdot> Space.dom i );
      identity = (\<forall>A. A \<in> Space.opens T \<longrightarrow> (F1 \<cdot> (Space.ident A)) = Poset.ident (F0 \<cdot> A));
      composition = (\<forall>j i. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  F1 \<cdot> (j \<propto> i) = (F1 \<cdot> i) \<diamondop> (F1 \<cdot> j))
    in
    welldefined \<and> identity \<and> composition"

(* PrealgebraMap type (natural transformation *)

record ('A, 'a, 'b) PrealgebraMap =
  nat :: "('A Open, ('a, 'b) PosetMap) Function"
  dom :: "('A, 'a) Prealgebra"
  cod :: "('A, 'b) Prealgebra"

abbreviation map_space :: "('A, 'a, 'b) PrealgebraMap \<Rightarrow> 'A Space" where
"map_space f \<equiv> space (dom f)"

definition valid_map :: "('A, 'a, 'b) PrealgebraMap \<Rightarrow> bool" where
 "valid_map f \<equiv>
    let
      T = (map_space f);

      welldefined = Space.valid T
                    \<and> T = space (cod f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> (Function.valid_map (nat f))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A));
      naturality = (\<forall>i. i \<in> inclusions T \<longrightarrow>
          (nat f \<cdot> Space.dom i) \<diamondop> (ar (dom f) \<cdot> i) = (ar (cod f) \<cdot> i) \<diamondop> (nat f \<cdot> Space.cod i))
    in
    (welldefined \<and> naturality)"

(* Validity *)

lemma validI :
  fixes F :: "('A,'a) Prealgebra"
  defines "T \<equiv> space F"
  defines "F0 \<equiv> ob F"
  defines "F1 \<equiv> ar F"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (F0 \<cdot> A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (F1 \<cdot> i)
                           \<and>  Poset.dom (F1 \<cdot> i) = (F0 \<cdot> Space.cod i)
                           \<and>  Poset.cod (F1 \<cdot> i) = (F0 \<cdot> Space.dom i) )"
  assumes identity : "(\<forall>A. A \<in> Space.opens T \<longrightarrow> (F1 \<cdot> (Space.ident A)) = Poset.ident (F0 \<cdot> A))"
  assumes composition :" (\<forall> i j. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow> (F1 \<cdot> (j \<propto> i )) = (F1 \<cdot> i) \<diamondop> (F1 \<cdot> j))"
  shows "valid F"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using F0_def welldefined apply blast
  using F1_def welldefined apply fastforce
  using T_def F0_def welldefined apply presburger
  using T_def F1_def welldefined apply blast
  using T_def F0_def F1_def welldefined apply blast
  using T_def F0_def F1_def welldefined apply blast
  using T_def F0_def F1_def identity apply blast
  using T_def F1_def composition by blast

lemma valid_welldefined  : "valid F \<Longrightarrow> let T = space F; F0 = ob F; F1 = ar F in (Space.valid T)
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (F0 \<cdot> A))
                    \<and> (\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Poset.valid_map (F1 \<cdot> i)
                           \<and>  Poset.dom (F1 \<cdot> i) = (F0 \<cdot> Space.cod i)
                           \<and>  Poset.cod (F1 \<cdot> i) = (F0 \<cdot> Space.dom i) )"
  unfolding valid_def by (simp add: Let_def)

lemma valid_space  : "valid F \<Longrightarrow> T = space F \<Longrightarrow> (Space.valid T)"
  by (meson Prealgebra.valid_welldefined)

lemma valid_ob  : "valid F \<Longrightarrow> A \<in> Space.opens (space F) \<Longrightarrow> obA = ob F \<cdot> A \<Longrightarrow> Poset.valid obA"
  unfolding valid_def by (simp add: Let_def)

lemma valid_ar  :
  fixes F :: "('A, 'a) Prealgebra" and i :: "'A Inclusion" and f ::  "('a,'a) PosetMap"
  assumes "valid F"
  and "i \<in> Space.inclusions (space F)"
  and "f  \<equiv> ar F \<cdot> i" 
  shows "Poset.valid_map f"
proof -
  define "F1" where "F1 = Prealgebra.ar F" 
  define "T" where "T = Prealgebra.space F" 
  have "(\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Poset.valid_map (F1 \<cdot> i))"  using valid_welldefined
    by (metis (mono_tags, lifting) CollectD CollectI F1_def T_def assms(1)) 
    moreover have "i \<in> Space.inclusions T"
      using T_def assms(2) by fastforce 
    moreover have "Poset.valid_map (F1 \<cdot> i)"
      using calculation(1) calculation(2) by auto
    ultimately show ?thesis
      using F1_def assms(3) by blast 
  qed

lemma valid_dom  : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Poset.dom (ar F \<cdot> i) = ob F \<cdot> Space.cod i"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_cod  : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Poset.cod (ar F \<cdot> i) = ob F \<cdot> Space.dom i"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_identity  : "valid F \<Longrightarrow> A \<in> Space.opens (space F) \<Longrightarrow> ar F \<cdot> (Space.ident A) = Poset.ident (ob F \<cdot> A)"
  unfolding valid_def by (simp add: Let_def)

lemma valid_composition :
  "valid F \<Longrightarrow> j \<in> inclusions (space F) \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar F \<cdot> (j \<propto> i) = (ar F \<cdot> i) \<diamondop> (ar F \<cdot> j)" 
  unfolding valid_def
  by meson 

lemma valid_mapI :
  fixes f :: "('A,'a,'b) PrealgebraMap"
  defines "T \<equiv> map_space f"
  defines "F \<equiv> dom f"
  defines "F' \<equiv> cod f"
  assumes welldefined : "Space.valid T
                    \<and> T = space (cod f)
                    \<and> (Function.valid_map (nat f))
                    \<and> valid F \<and> valid F'
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.dom (nat f \<cdot> A) = (ob F \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.cod (nat f \<cdot> A) = (ob F' \<cdot> A))"
  assumes naturality : "(\<forall>i. i \<in> inclusions T \<longrightarrow>
          (nat f \<cdot> Space.dom i) \<diamondop> (ar F \<cdot> i) = (ar F' \<cdot> i) \<diamondop> (nat f \<cdot> Space.cod i))"
  shows "valid_map f"
  unfolding valid_map_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using T_def welldefined apply blast
  using F_def welldefined apply blast
  using F'_def welldefined apply blast
  using welldefined apply blast
  using T_def welldefined apply blast
  apply (simp add: F_def T_def welldefined)
  apply (simp add: F'_def T_def welldefined)
  using F'_def F_def T_def naturality by blast

lemma valid_map_welldefined :
  "valid_map f \<Longrightarrow> let F = dom f; F' = cod f; T = map_space f in (Space.valid T)
                    \<and> (Function.valid_map (nat f))
                    \<and> valid F \<and> valid F'
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.dom (nat f \<cdot> A) = (ob F \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.cod (nat f \<cdot> A) = (ob F' \<cdot> A))"
  by (meson Prealgebra.valid_map_def)

lemma valid_map_space : "valid_map f \<Longrightarrow> Space.valid (map_space f)"
  by (meson Prealgebra.valid_map_welldefined)
 
lemma valid_map_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat : "valid_map f \<Longrightarrow> Function.valid_map (nat f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_welldefined :
  "valid_map f \<Longrightarrow> A \<in> Space.opens (map_space f) \<Longrightarrow> Poset.valid_map (nat f \<cdot> A)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_dom : "valid_map f \<Longrightarrow> A \<in> Space.opens (map_space f) \<Longrightarrow> Poset.dom ((nat f) \<cdot> A) = ob (dom f) \<cdot> A"
  by (meson Prealgebra.valid_map_welldefined)

lemma valid_map_nat_cod : "valid_map f \<Longrightarrow> A \<in> Space.opens (map_space f) \<Longrightarrow> Poset.cod ((nat f) \<cdot> A) = ob (cod f) \<cdot> A"
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
  and A_open : "A \<in> Space.opens (map_space f)"
  and a_dom : "a \<in> Poset.el FA"
shows "fA \<star> a \<in> Poset.el F'A"
proof -
  have "valid_map f"
    using f_valid by force
  moreover have "A \<in> Space.opens (map_space f)"
    using A_open by blast
  moreover have "a \<in> Poset.el FA"
    using a_dom by blast
  moreover have "Poset.dom fA = FA"
    by (metis A_open Prealgebra.valid_map_welldefined FA_def f_valid fA_def)
  moreover have "Poset.valid_map fA"
    by (metis A_open Prealgebra.valid_map_welldefined f_valid fA_def)
  moreover have "Poset.cod fA = F'A"
    by (metis A_open Prealgebra.valid_map_welldefined F'A_def f_valid fA_def)
  ultimately show ?thesis
    by (meson Poset.fun_app2)
qed

(* Application *)

lemma ident_app [simp] :
 "valid F \<Longrightarrow> A \<in> Space.opens (space F) \<Longrightarrow> a \<in> el obA \<Longrightarrow>
  ar F \<cdot> (Space.ident A) \<star> a = Poset.ident (ob F \<cdot> A) \<star> a"
  by (simp add: valid_identity)

lemma image : "valid F \<Longrightarrow> i \<in> Space.inclusions (space F) \<Longrightarrow> a \<in> Poset.el (ob F \<cdot> (Space.cod i)) \<Longrightarrow>
    ((ar F \<cdot> i) \<star> a) \<in> Poset.el (ob F \<cdot> (Space.dom i)) "
  using Poset.fun_app2 valid_ar
  using valid_cod valid_dom by fastforce 

(* Restriction *)

lemma res_dom [simp] : "valid F \<Longrightarrow> i \<in> Space.inclusions (space F) \<Longrightarrow> B = Space.cod i \<Longrightarrow> Poset.dom (ar F \<cdot> i) = ob F \<cdot> B"
  using valid_dom by blast

lemma res_cod [simp] : "valid F \<Longrightarrow> i \<in> Space.inclusions (space F) \<Longrightarrow> A = Space.dom i \<Longrightarrow> Poset.cod (ar F \<cdot> i) = ob F \<cdot> A"
  using valid_cod by blast

lemma res_monotone : 
  fixes F :: "('A,'a) Prealgebra" and i :: "'A Inclusion" and A B :: "'A Open" and a a' :: "'a"
  defines "FA \<equiv> Prealgebra.ob F \<cdot> A"
  defines "FB \<equiv> Prealgebra.ob F \<cdot> B"
  defines "Fi \<equiv> Prealgebra.ar F \<cdot> i"
  assumes F_valid : "valid F"
  and i_inc : "i \<in> Space.inclusions (space F)" 
  and A_open : "A = Space.cod i" and B_open : "B = Space.dom i"
  and a_elem : "a \<in> Poset.el FA" and a'_elem : "a' \<in> Poset.el FA" 
  and a_le_a' : "Poset.le FA a a'"
shows "Poset.le FB (Fi \<star> a) (Fi \<star> a')"
proof -
  have "Poset.valid_map Fi"
    using F_valid Fi_def i_inc valid_ar by blast 
 moreover have "FA = Poset.dom Fi"
   using A_open FA_def F_valid Fi_def i_inc by auto
moreover have "FB = Poset.cod Fi"
  using B_open FB_def F_valid Fi_def i_inc by force 
  moreover have "a \<in> Poset.el FA"
    using A_open FA_def F_valid Fi_def a_elem i_inc by auto
  moreover have "a' \<in> Poset.el FA"
    using A_open FA_def F_valid Fi_def a'_elem i_inc by auto 
  ultimately show ?thesis using assms Poset.valid_map_monotone [where ?f="ar F \<cdot> i" and ?a=a and
        ?a'=a']
    by fastforce 
qed

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
  by (metis (no_types, lifting) CollectD CollectI Function.const_app Prealgebra.Prealgebra.select_convs(3) Prealgebra.const_def UNIV_I) 

lemma const_value_res [simp] : "Space.valid T \<Longrightarrow> i \<in> Space.inclusions T \<Longrightarrow> a \<in> el (ob (const T) \<cdot> (Space.cod i)) 
\<Longrightarrow> (ar (const T) \<cdot> i) \<star> a = a"
  by (simp add: discrete_valid) 

lemma const_valid : "Space.valid T \<Longrightarrow> valid (const T)"
proof (intro validI, safe, goal_cases)
  case 1
  then show ?case
    by (simp add: Prealgebra.const_def)  
next
  case 2
  then show ?case
    by (metis (no_types, lifting) Function.const_valid Prealgebra.Prealgebra.select_convs(2) Prealgebra.const_def UNIV_I valid_universe) 
next
  case 3
  then show ?case
    by (metis (no_types, lifting) Function.const_valid Prealgebra.Prealgebra.select_convs(3) Prealgebra.const_def Space.valid_def UNIV_I valid_ident_inc) 
next
  case (4 A)
  then show ?case
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ob discrete_valid) 
next
  case (5 i)
  then show ?case
    by (metis (no_types, lifting) Poset.ident_valid Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar discrete_valid mem_Collect_eq) 
next
  case (6 i)
  then show ?case
    by (metis (no_types, lifting) Poset.ident_dom Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar const_ob mem_Collect_eq)  
next
  case (7 i)
  then show ?case
    by (metis (no_types, lifting) Poset.ident_cod Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar const_ob mem_Collect_eq) 
next
  case (8 A)
  then show ?case
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def const_ar const_ob valid_ident_inc) 
next
  case (9 i j)
  then show ?case
    by (smt (verit) Poset.compose_ident_left Poset.ident_cod Poset.ident_valid Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def cod_compose_inc compose_inc_valid const_ar discrete_valid dom_compose_inc mem_Collect_eq) 
qed 

abbreviation terminal :: "'A Space \<Rightarrow> ('A, unit) Prealgebra" where
"terminal \<equiv> const"

lemma terminal_ob [simp] : "Space.valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> ob (terminal T) \<cdot> A = Poset.discrete"
  by simp 

lemma terminal_ar [simp] : "Space.valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> ar (terminal T) \<cdot> i = Poset.ident Poset.discrete"
  by simp 

lemma terminal_value [simp] : "Space.valid T \<Longrightarrow> A \<in> Space.opens T \<Longrightarrow> Poset.el (ob (terminal T) \<cdot> A) = {()}"
  by (simp add: Poset.discrete_def UNIV_unit) 

lemma terminal_value_res [simp] : "Space.valid T \<Longrightarrow> i \<in> Space.inclusions T \<Longrightarrow> (ar (terminal T) \<cdot> i) \<star> a = ()"
  by simp

lemma terminal_valid : "Space.valid T \<Longrightarrow> valid (terminal T)"
  by (simp add: Prealgebra.const_valid) 

end
