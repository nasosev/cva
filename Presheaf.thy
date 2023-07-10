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
      T = space F;
      F0 = ob F;
      F1 = ar F;

      welldefined = (Space.valid T)
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> valid_map (F1 \<cdot> i)
                           \<and>  Function.dom (F1 \<cdot> i) = F0 \<cdot> Space.cod i
                           \<and>  Function.cod (F1 \<cdot> i) = F0 \<cdot> Space.dom i );
      identity = (\<forall>A. A \<in> opens T \<longrightarrow> (F1 \<cdot> (Space.ident A)) = Function.ident (F0 \<cdot> A));
      composition = (\<forall>j i. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  F1 \<cdot> (j \<propto> i) = (F1 \<cdot> i) \<bullet> (F1 \<cdot> j))
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
      T = map_space f;

      welldefined = Space.valid T
                    \<and> T = space (cod f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> (Function.valid_map (nat f))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A));
      naturality = (\<forall>i. i \<in> inclusions T \<longrightarrow>
          (nat f \<cdot> Space.dom i) \<bullet> (ar (dom f) \<cdot> i) = (ar (cod f) \<cdot> i) \<bullet> (nat f  \<cdot> Space.cod i))
    in
    (welldefined \<and> naturality)"

(* Validity *)

lemma validI [intro] :
  fixes F :: "('A,'x) Presheaf"
  defines "T \<equiv> space F"
  defines "F0 \<equiv> ob F"
  defines "F1 \<equiv> ar F"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Function.valid_map (F1 \<cdot> i)
                           \<and>  Function.dom (F1 \<cdot> i) = (F0 \<cdot> Space.cod i)
                           \<and>  Function.cod (F1 \<cdot> i) = (F0 \<cdot> Space.dom i) )"
  assumes identity : "(\<forall>A. A \<in> opens T \<longrightarrow> (F1 \<cdot> (Space.ident A)) = Function.ident (F0 \<cdot> A))"
  assumes composition :" (\<forall> i j. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow> (F1 \<cdot> (j \<propto> i )) = (F1 \<cdot> i) \<bullet> (F1 \<cdot> j))"
  shows "valid F"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using F0_def welldefined apply blast
  using F1_def welldefined apply fastforce
  using T_def F1_def welldefined apply blast
  using T_def F0_def F1_def welldefined apply blast 
  using T_def F0_def F1_def welldefined apply blast
  using T_def F0_def F1_def welldefined apply blast
  using T_def F0_def F1_def welldefined apply blast
  using T_def F0_def F1_def identity apply blast
  using T_def F1_def composition by blast  

lemma valid_welldefined  : "valid F \<Longrightarrow> let T = space F; F0 = ob F; F1 = ar F in (Space.valid T)
                    \<and> (Function.valid_map F0) \<and> (Function.valid_map F1)
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Function.valid_map (F1 \<cdot> i)
                           \<and>  Function.dom (F1 \<cdot> i) = (F0 \<cdot> Space.cod i)
                           \<and>  Function.cod (F1 \<cdot> i) = (F0 \<cdot> Space.dom i) )"
  unfolding valid_def by (simp add: Let_def)

lemma valid_space  : "valid F \<Longrightarrow> T = space F \<Longrightarrow> Space.valid T"
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
  by (smt (z3) A_open B_le_A B_open C_le_A C_open D_le_B D_le_C D_open F_valid Inclusion.select_convs(1) Inclusion.select_convs(2) compose_app_assoc compose_inc_def i_BA_def i_CA_def i_DB_def i_DC_def mem_Collect_eq valid_ar valid_cod valid_composition valid_dom x_el)

lemma valid_mapI [intro] :
  fixes f :: "('A,'x,'y) PresheafMap"
  defines "T \<equiv> map_space f"
  defines "F \<equiv> dom f"
  defines "F' \<equiv> cod f"
  assumes welldefined : "(Space.valid T)
                    \<and> T = space F'
                    \<and> (Function.valid_map (nat f))
                    \<and> valid F \<and> valid F'
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.dom (nat f \<cdot> A) = (ob F \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.cod (nat f \<cdot> A) = (ob F' \<cdot> A))"
  assumes naturality : "(\<forall>i. i \<in> inclusions T \<longrightarrow>
          (nat f \<cdot> Space.dom i) \<bullet> (ar F \<cdot> i) = (ar F' \<cdot> i) \<bullet> (nat f \<cdot> Space.cod i))"
  shows "valid_map f"
  unfolding valid_map_def
  apply (simp add: Let_def)
  apply safe
  using T_def local.welldefined apply blast
  using F'_def T_def local.welldefined apply fastforce
  using F_def local.welldefined apply blast
  using F'_def local.welldefined apply blast
  using local.welldefined apply blast
  using T_def local.welldefined apply blast
  apply (simp add: F_def T_def local.welldefined)
  apply (simp add: F_def T_def local.welldefined)
  apply (simp add: F'_def T_def local.welldefined)
  apply (simp add: F'_def T_def local.welldefined)
  using F'_def F_def T_def naturality by blast 

lemma valid_map_welldefined :
  "valid_map f \<Longrightarrow> let T = map_space f in Space.valid T
                    \<and> T = space (cod f)
                    \<and> valid (dom f) \<and> valid (cod f)
                    \<and> (Function.valid_map (nat f))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.valid_map (nat f \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.dom (nat f \<cdot> A) = (ob (dom f) \<cdot> A))
                    \<and> (\<forall>A. A \<in> opens T \<longrightarrow> Function.cod (nat f \<cdot> A) = (ob (cod f) \<cdot> A))"
  unfolding valid_map_def
  by meson 

lemma valid_map_space : "valid_map f \<Longrightarrow> Space.valid (map_space f)"
  by (meson valid_map_welldefined) 

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
  defines "F'A \<equiv> Presheaf.ob (cod f) \<cdot> A"
  defines "fA \<equiv> (nat f) \<cdot> A"
  assumes f_valid :"valid_map f"
  and A_open : "A \<in> opens (map_space f)"
  and a_dom : "a \<in>  FA"
shows "fA \<cdot> a \<in>  F'A"
  by (metis A_open F'A_def FA_def a_dom fA_def f_valid fun_app2 valid_map_nat_cod valid_map_nat_dom valid_map_nat_welldefined)

lemma image : "valid F \<Longrightarrow> i \<in> inclusions (space F) \<Longrightarrow> a \<in>  (ob F \<cdot> Space.cod i) \<Longrightarrow>
    ((ar F \<cdot> i) \<cdot> a) \<in>  (ob F \<cdot> Space.dom i)"
  using fun_app2 valid_ar valid_dom valid_cod by fastforce 

end
