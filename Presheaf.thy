section \<open> Presheaf.thy \<close>

theory Presheaf
imports Main Space Function
begin

(* Presheaf type *)

record ('A, 'x) Presheaf =
  space :: "'A Space"
  ob :: "('A Open, 'x set) Function"
  ar :: "('A Inclusion, ('x, 'x) Function) Function"

definition valid :: "('A, 'x) Presheaf \<Rightarrow> bool" where
  "valid F \<equiv>
    let
      welldefined = (Space.valid (space F))
                    \<and> (Function.valid_map (ob F)) \<and> (Function.valid_map (ar F))
                    \<and> (\<forall>i. i \<in> inclusions (space F) \<longrightarrow> valid_map (ar F \<cdot> i)
                           \<and>  Function.dom (ar F \<cdot> i) = ob F \<cdot> Space.cod i
                           \<and>  Function.cod (ar F \<cdot> i) = ob F \<cdot> Space.dom i );
      identity = (\<forall>A. A \<in> opens (space F) \<longrightarrow> (ar F \<cdot> (Space.ident A)) = Function.ident (ob F \<cdot> A));
      composition = (\<forall>j i. j \<in> inclusions (space F) \<longrightarrow> i \<in> inclusions (space F) \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  ar F \<cdot> (j \<propto> i) = (ar F \<cdot> i) \<bullet> (ar F \<cdot> j))
    in 
    welldefined \<and> identity \<and> composition"

(* PresheafMap type (natural transformation) *)

record ('A, 'x, 'y) PresheafMap =
  dom :: "('A, 'x) Presheaf"
  cod :: "('A, 'y) Presheaf"
  nat :: "('A Open, ('x, 'y) Function) Function"

abbreviation map_space :: "('A, 'x, 'y) PresheafMap \<Rightarrow> 'A Space" where
"map_space f \<equiv> space (dom f)"

definition valid_map :: "('A, 'x, 'y) PresheafMap \<Rightarrow> bool" where
 "valid_map f \<equiv>
    let
      welldefined = Space.valid (map_space f)
                    \<and> map_space f = space (cod f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> (Function.valid_map (nat f))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Function.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Function.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Function.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A));
      naturality = (\<forall>i. i \<in> inclusions (map_space f) \<longrightarrow>
          (nat f \<cdot> Space.dom i) \<bullet> (ar (dom f) \<cdot> i) = (ar (cod f) \<cdot> i) \<bullet> (nat f  \<cdot> Space.cod i))
    in
    (welldefined \<and> naturality)"

(* Presheaf validity *)

lemma validI [intro] :
  fixes F :: "('A,'x) Presheaf"
  assumes welldefined_space : "Space.valid (space F)"
  and welldefined_valid_ob : "Function.valid_map (ob F)"
  and welldefined_valid_ar : "Function.valid_map (ar F)"
  and welldefined_ar : "\<And> i. i \<in> inclusions (space F) \<Longrightarrow> Function.valid_map (ar F \<cdot> i)"
  and welldefined_ar_dom : "\<And> i. i \<in> inclusions (space F) \<Longrightarrow> Function.dom (ar F \<cdot> i) = (ob F \<cdot> Space.cod i)"
  and welldefined_ar_cod : "\<And> i. i \<in> inclusions (space F) \<Longrightarrow> Function.cod (ar F \<cdot> i) = (ob F \<cdot> Space.dom i)"
  and identity : "\<And> A. A \<in> opens (space F) \<Longrightarrow> (ar F \<cdot> (Space.ident A)) = Function.ident (ob F \<cdot> A)"
  and composition :"\<And> i j. j \<in> inclusions (space F) \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow>
        Space.dom j = Space.cod i \<Longrightarrow> ar F \<cdot> (j \<propto> i) = (ar F \<cdot> i) \<bullet> (ar F \<cdot> j)"
  shows "valid F"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  apply (simp add: welldefined_space)
  apply (simp add: welldefined_valid_ob)
  apply (simp add: welldefined_valid_ar)
  apply (simp add: welldefined_ar)
  apply (simp add: welldefined_ar_dom)
  apply (simp add: welldefined_ar_dom)
  apply (simp add: welldefined_ar_cod)
  apply (simp add: welldefined_ar_cod)
  using identity apply blast
  by (simp add: composition)

lemma valid_welldefined  : "valid F \<Longrightarrow> Space.valid (space F)
                    \<and> Function.valid_map (ob F) \<and> Function.valid_map (ar F)
                    \<and> (\<forall>i. i \<in> inclusions (space F) \<longrightarrow> Function.valid_map (ar F \<cdot> i)
                           \<and>  Function.dom (ar F \<cdot> i) = (ob F \<cdot> Space.cod i)
                           \<and>  Function.cod (ar F \<cdot> i) = (ob F \<cdot> Space.dom i))"
  unfolding valid_def by (simp add: Let_def)

lemma valid_space  : "valid F \<Longrightarrow> Space.valid (space F)"
  by (meson Presheaf.valid_welldefined)

lemma valid_ar  :
  fixes F :: "('A, 'x) Presheaf" and i :: "'A Inclusion"
  assumes "valid F"
  and "i \<in> inclusions (space F)"
  shows "Function.valid_map (ar F \<cdot> i)"
  by (meson Presheaf.valid_welldefined assms(1) assms(2))

lemma valid_dom : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Function.dom (ar F \<cdot> i) = ob F \<cdot> Space.cod i"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_cod : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Function.cod (ar F \<cdot> i)  = ob F \<cdot> Space.dom i"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_identity : "valid F \<Longrightarrow> A \<in> opens (space F) \<Longrightarrow> ar F \<cdot> (Space.ident A) = Function.ident (ob F \<cdot> A)"
  unfolding valid_def by (simp add: Let_def)

lemma valid_composition :
  "valid F \<Longrightarrow> j \<in> inclusions (space F) \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar F \<cdot> (j \<propto> i) = (ar F \<cdot> i) \<bullet> (ar F \<cdot> j)" 
  unfolding valid_def
  by meson 

(* Application *)

lemma ident_app [simp] :
 "valid F \<Longrightarrow> A \<in> opens (space F) \<Longrightarrow> 
  (ar F \<cdot> (Space.ident A)) \<cdot> x = Function.ident (ob F \<cdot> A) \<cdot> x"
  by (simp add: valid_identity)

lemma image : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> x \<in> ob F \<cdot> (Space.cod i) \<Longrightarrow>
    ((ar F \<cdot> i) \<cdot> x) \<in> ob F \<cdot> (Space.dom i) "
  using fun_app2 valid_ar valid_cod valid_dom by fastforce

(* Restriction *)

lemma diamond_rule :
  fixes F :: "('A, 'x) Presheaf" and A B C D :: "'A Open" and x :: "'x"
  assumes F_valid :"valid F"
  and A_open : "A \<in> opens (space F)" and B_open : "B \<in> opens (space F)" 
  and C_open : "C \<in> opens (space F)" and D_open : "D \<in> opens (space F)" 
  and B_le_A : "B \<subseteq> A" and C_le_A : "C \<subseteq> A" 
  and D_le_B : "D \<subseteq> B" and D_le_C : "D \<subseteq> C" 
  and x_el : "x \<in> ob F \<cdot> A"
  defines "i_BA \<equiv> make_inc B A"
  and "i_CA \<equiv> make_inc C A"
  and "i_DB \<equiv> make_inc D B"
  and "i_DC \<equiv> make_inc D C"
shows "(ar F \<cdot> i_DB) \<cdot> ((ar F \<cdot> i_BA) \<cdot>  x) = (ar F \<cdot> i_DC) \<cdot> ((ar F \<cdot> i_CA) \<cdot>  x)"
  by (smt (z3) CollectI F_valid Inclusion.select_convs(1) Inclusion.select_convs(2) assms(10) assms(11) assms(12) assms(13) assms(14) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) compose_app_assoc compose_inc_def inclusions_def valid_ar valid_cod valid_composition valid_dom)

lemma res_dom [simp] : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Function.dom (ar F \<cdot> i) = ob F \<cdot> (Space.cod i)"
  using valid_dom by blast

lemma res_cod [simp] : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> Function.cod (ar F \<cdot> i) = ob F \<cdot> (Space.dom i)"
  using valid_cod by blast

lemma restricted_element :
  fixes F :: "('A, 'x) Presheaf" and A B :: "'A Open" and x :: "'x"
  assumes F_valid :"valid F"
  and A_open : "A \<in> opens (space F)" and B_open : "B \<in> opens (space F)" 
  and B_le_A : "B \<subseteq> A"
  and x_el : "x \<in> ob F \<cdot> A"
defines "i \<equiv> make_inc B A"
shows "(ar F \<cdot> i) \<cdot> x \<in> ob F \<cdot> B"
  using valid_ar [where ?F=F and ?i=i] A_open B_le_A B_open F_valid fun_app2 i_def valid_cod valid_dom x_el inclusions_def  by fastforce

(* PresheafMap validity *)

lemma valid_mapI [intro] :
  fixes f :: "('A,'x,'y) PresheafMap"
  assumes welldefined_space : "Space.valid (map_space f)"
  and welldefined_spaces : "map_space f = space (cod f)"
  and welldefined_map : "Function.valid_map (nat f)"
  and welldefined_dom : "valid (dom f)"
  and welldefined_cod : "valid (cod f)"
  and welldefined_nat_val : "\<And>A. A \<in> opens (map_space f) \<Longrightarrow> Function.valid_map (nat f \<cdot> A)"
  and welldefined_nat_dom : "\<And>A. A \<in> opens (map_space f) \<Longrightarrow> Function.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A)"
  and welldefined_nat_cod : "\<And>A. A \<in> opens (map_space f) \<Longrightarrow> Function.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A)"
  and naturality : "\<And> i. i \<in> inclusions (map_space f) \<Longrightarrow>
          (nat f \<cdot> Space.dom i) \<bullet> (ar (dom f) \<cdot> i) = (ar (cod f) \<cdot> i) \<bullet> (nat f \<cdot> Space.cod i)"
  shows "valid_map f"
  unfolding valid_map_def
  apply (simp add: Let_def)
  apply safe
  apply (simp add: welldefined_space)
  apply (simp add: welldefined_spaces)
  apply (simp add: welldefined_dom)
  apply (simp add: welldefined_cod)
  apply (simp add: welldefined_map)
  using welldefined_nat_val apply blast
  using welldefined_nat_dom apply blast
  using welldefined_nat_dom apply blast
  using welldefined_nat_cod apply blast
  using welldefined_nat_cod apply blast
  by (simp add: naturality)

lemma valid_map_welldefined :
  "valid_map f \<Longrightarrow>   map_space f = space (cod f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> Function.valid_map (nat f)
                    \<and> (\<forall>A. A \<in> opens (map_space f) \<longrightarrow> Function.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f)  \<longrightarrow> Function.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens (map_space f)  \<longrightarrow> Function.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A))"
  unfolding valid_map_def
  by meson 

lemma valid_map_space : "valid_map f \<Longrightarrow> Space.valid (map_space f)"
  by (simp add: Presheaf.valid_map_welldefined valid_space)

lemma valid_map_spaces : "valid_map f \<Longrightarrow> space (dom f) = space (cod f)"
  by (meson valid_map_welldefined) 

lemma valid_map_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat : "valid_map f \<Longrightarrow> Function.valid_map (nat f)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_welldefined :
  "valid_map f \<Longrightarrow> A \<in> opens (map_space f) \<Longrightarrow> Function.valid_map (nat f \<cdot> A)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_nat_dom : "valid_map f \<Longrightarrow> A \<in> opens (map_space f) \<Longrightarrow> Function.dom ((nat f) \<cdot> A) = ob (dom f) \<cdot> A"
  by (meson Presheaf.valid_map_welldefined)

lemma valid_map_nat_cod : "valid_map f \<Longrightarrow> A \<in> opens (map_space f) \<Longrightarrow> Function.cod ((nat f) \<cdot> A) = ob (cod f) \<cdot> A"
  by (meson Presheaf.valid_map_welldefined)

lemma valid_map_naturality :
  "valid_map f \<Longrightarrow> i \<in> inclusions (map_space f) \<Longrightarrow>
     (ar (cod f) \<cdot> i) \<bullet> (nat f \<cdot> Space.cod i) = (nat f \<cdot> Space.dom i) \<bullet> (ar (dom f) \<cdot> i)"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_image :
  fixes f :: "('A, 'x, 'y) PresheafMap" and A :: "'A Open" and a :: "'x"
  defines "FA \<equiv> Presheaf.ob (dom f) \<cdot> A"
  and "F'A \<equiv> Presheaf.ob (cod f) \<cdot> A"
  and "fA \<equiv> (nat f) \<cdot> A"
  assumes f_valid :"valid_map f"
  and A_open : "A \<in> opens (map_space f)"
  and a_dom : "a \<in>  FA"
shows "fA \<cdot> a \<in>  F'A"
  by (metis A_open F'A_def FA_def a_dom fA_def f_valid fun_app2 valid_map_nat_cod valid_map_nat_dom valid_map_nat_welldefined)

end
