section \<open> Presheaf.thy \<close>

theory Presheaf
imports Main Space Function
begin

text \<open>
   This record introduces a presheaf @{term \<Phi>} over a topological space. 
   `space` is the underlying topological space, `ob` maps each open set to a poset, and `ar` maps each 
   inclusion (i.e., an injective continuous function) to a poset map, preserving the order structure. 
\<close>
record ('A, 'a) Presheaf =
  space :: "'A Space"
  ob :: "('A Open, 'a set) Function "
  ar :: "('A Inclusion, ('a, 'a) Function) Function"

text \<open>
   This definition introduces the notion of a valid presheaf. A presheaf is valid if it is well-defined, 
   respects identities, and respects composition of inclusions in the underlying space.
\<close>
definition valid :: "('A, 'a) Presheaf \<Rightarrow> bool" where
  "valid \<Phi> \<equiv>
    let
      T = space \<Phi>;
      \<Phi>0 = ob \<Phi>;
      \<Phi>1 = ar \<Phi>;

      welldefined = (Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> valid_map (\<Phi>1 \<cdot> i)
                           \<and>  Function.dom (\<Phi>1 \<cdot> i) = \<Phi>0 \<cdot> (Space.cod i)
                           \<and>  Function.cod (\<Phi>1 \<cdot> i) = \<Phi>0 \<cdot> (Space.dom i) );
      identity = (\<forall>A. A \<in> Space.opens T \<longrightarrow> (\<Phi>1 \<cdot> (Space.ident T A)) = Function.ident (\<Phi>0 \<cdot> A));
      composition = (\<forall>j i. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  \<Phi>1 \<cdot> (Space.compose j i) = (\<Phi>1 \<cdot> i) \<bullet> (\<Phi>1 \<cdot> j))
    in
    welldefined \<and> identity \<and> composition"

text \<open>
   This record introduces a presheaf map, which is a functor between two presheaves over the same 
   topological space. `map\_space` is the underlying space, `nat` is the natural transformation which maps 
   each open set to a poset map, `dom` is the domain presheaf, and `cod` is the codomain presheaf.
\<close>
record ('A, 'a, 'b) PresheafMap =
  map_space :: "'A Space"
  nat :: "('A Open, ('a, 'b) Function) Function"
  dom :: "('A, 'a) Presheaf"
  cod :: "('A, 'b) Presheaf"

text \<open>
   This definition introduces the notion of a valid presheaf map. A presheaf map is valid if it is 
   well-defined and natural, i.e., it commutes with the action of the presheaves on the inclusions 
   in the underlying space.
\<close>
definition valid_map :: "('A, 'a, 'b) PresheafMap \<Rightarrow> bool" where
 "valid_map \<phi> \<equiv>
    let
      space = (map_space \<phi>);
      f = nat \<phi>;

      welldefined = Space.valid space
                    \<and> valid (dom \<phi>) \<and> valid (cod \<phi>)
                    \<and> (Function.valid_map f)
                    \<and> (\<forall>A. A \<in> Space.opens space \<longrightarrow> Function.valid_map (f \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens space \<longrightarrow> Function.dom (f \<cdot> A) = (ob (dom \<phi>) \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens space \<longrightarrow> Function.cod (f \<cdot> A) = (ob (cod \<phi>) \<cdot> A));
      naturality = (\<forall>i. i \<in> inclusions space \<longrightarrow>
          (f \<cdot> Space.dom i) \<bullet> (ar (dom \<phi>) \<cdot> i) = (ar (cod \<phi>) \<cdot> i) \<bullet> (f \<cdot> Space.cod i))
    in
    (welldefined \<and> naturality)"

text \<open> LEMMAS \<close>

text \<open>
   This lemma states that if all components of a presheaf are well-defined and the presheaf respects 
   identities and composition, then the presheaf is valid.
\<close>
lemma validI :
  fixes \<Phi> :: "('A,'a) Presheaf"
  defines "T \<equiv> space \<Phi>"
  defines "\<Phi>0 \<equiv> ob \<Phi>"
  defines "\<Phi>1 \<equiv> ar \<Phi>"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Function.valid_map (\<Phi>1 \<cdot> i)
                           \<and>  Function.dom (\<Phi>1 \<cdot> i) = (\<Phi>0 \<cdot> (Space.cod i))
                           \<and>  Function.cod (\<Phi>1 \<cdot> i) = (\<Phi>0 \<cdot> (Space.dom i)) )"
  assumes identity : "(\<forall>A. A \<in> Space.opens T \<longrightarrow> (\<Phi>1 \<cdot> (Space.ident T A)) = Function.ident (\<Phi>0 \<cdot> A))"
  assumes composition :" (\<forall> i j. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow> (\<Phi>1 \<cdot> (Space.compose j i )) = (\<Phi>1 \<cdot> i) \<bullet> (\<Phi>1 \<cdot> j))"
  shows "valid \<Phi>"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using \<Phi>0_def welldefined apply blast
  using \<Phi>1_def welldefined apply fastforce
  using T_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def welldefined apply blast 
  using T_def \<Phi>0_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def welldefined apply blast
  using T_def \<Phi>0_def \<Phi>1_def identity apply blast
  using T_def \<Phi>1_def composition by blast  

text \<open>
   This lemma establishes that if a presheaf is valid, then all its components are well-defined.
\<close>
lemma valid_welldefined  : "valid \<Phi> \<Longrightarrow> let T = space \<Phi>; \<Phi>0 = ob \<Phi>; \<Phi>1 = ar \<Phi> in (Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Function.valid_map (\<Phi>1 \<cdot> i)
                           \<and>  Function.dom (\<Phi>1 \<cdot> i) = (\<Phi>0 \<cdot> (Space.cod i))
                           \<and>  Function.cod (\<Phi>1 \<cdot> i) = (\<Phi>0 \<cdot> (Space.dom i)) )"
  unfolding valid_def by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then its underlying space is a valid space.
\<close>
lemma valid_space  : "valid \<Phi> \<Longrightarrow> T = space \<Phi> \<Longrightarrow> (Space.valid T)"
  by (meson Presheaf.valid_welldefined)


text \<open>
   This lemma states that if a presheaf is valid, then the poset map associated to each inclusion 
   of the underlying space by the presheaf is a valid poset map.
\<close>
lemma valid_ar  :
  fixes \<Phi> :: "('A, 'a) Presheaf" and i :: "'A Inclusion" and f ::  "('a,'a) Function"
  assumes "valid \<Phi>"
  and "i \<in> Space.inclusions (space \<Phi>)"
  and "f  \<equiv> ar \<Phi> \<cdot> i" 
  shows "Function.valid_map f"
proof -
  define "\<Phi>1" where "\<Phi>1 = Presheaf.ar \<Phi>" 
  define "T" where "T = Presheaf.space \<Phi>" 
  have "(\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Function.valid_map (\<Phi>1 \<cdot> i))"  using valid_welldefined
    by (metis T_def \<Phi>1_def assms(1))
    moreover have "i \<in> Space.inclusions T"
      by (simp add: T_def assms(2))
    moreover have "Function.valid_map (\<Phi>1 \<cdot> i)"
      using calculation(1) calculation(2) by auto
    ultimately show ?thesis
      using \<Phi>1_def assms(3) by blast 
  qed

text \<open>
   This lemma establishes that if a presheaf is valid, then the domain of the poset map associated 
   to an inclusion by the presheaf is equal to the poset associated to the codomain of the inclusion.
\<close>
lemma valid_dom  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> \<cdot> i \<Longrightarrow> Function.dom ari = ob \<Phi> \<cdot> (Space.cod i)"
  unfolding valid_def
  by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then the codomain of the poset map associated 
   to an inclusion by the presheaf is equal to the poset associated to the domain of the inclusion.
\<close>
lemma valid_cod  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> \<cdot> i \<Longrightarrow> Function.cod ari = ob \<Phi> \<cdot> (Space.dom i)"
  unfolding valid_def
  by (simp add: Let_def)

text \<open>
   This lemma establishes that if a presheaf is valid, then the presheaf maps the identity of an 
   open set to the identity of the associated poFunction.
\<close>
lemma valid_identity  : "valid \<Phi> \<Longrightarrow> A \<in> Space.opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> \<cdot> A \<Longrightarrow> ar \<Phi> \<cdot> (Space.ident (space \<Phi>) A) = Function.ident obA"
  unfolding valid_def by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then the presheaf respects composition of 
   inclusions in the underlying space.
\<close>
lemma valid_composition :
  "valid \<Phi> \<Longrightarrow> j \<in> inclusions (space \<Phi>) \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar \<Phi> \<cdot> (Space.compose j i) = (ar \<Phi> \<cdot> i) \<bullet> (ar \<Phi> \<cdot> j)"
  by (metis Presheaf.valid_def)

text \<open>
   This lemma establishes conditions for a presheaf map to be valid. Specifically, it shows that if the 
   space, function, domain and codomain associated with the map are valid and adhere to certain 
   properties, then the map is valid.
\<close>
lemma valid_mapI :
  fixes \<phi> :: "('A,'a,'b) PresheafMap"
  defines "T \<equiv> map_space \<phi>"
  defines "f \<equiv> nat \<phi>"
  defines "\<Phi> \<equiv> dom \<phi>"
  defines "\<Phi>' \<equiv> cod \<phi>"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map f)
                    \<and> valid \<Phi> \<and> valid \<Phi>'
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Function.valid_map (f \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Function.dom (f \<cdot> A) = (ob \<Phi> \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Function.cod (f \<cdot> A) = (ob \<Phi>' \<cdot> A))"
  assumes naturality : "(\<forall>i. i \<in> inclusions T \<longrightarrow>
          (f \<cdot> Space.dom i) \<bullet> (ar \<Phi> \<cdot> i) = (ar \<Phi>' \<cdot> i) \<bullet> (f \<cdot> Space.cod i))"
  shows "valid_map \<phi>"
  unfolding valid_map_def
  apply (simp add: Let_def)
  apply safe
  using T_def welldefined apply blast
  using \<Phi>_def welldefined apply blast
  using \<Phi>'_def welldefined apply blast
  using f_def welldefined apply blast
  using T_def f_def welldefined apply blast
  using T_def \<Phi>_def f_def welldefined apply blast
  using T_def \<Phi>_def f_def welldefined apply blast
  using T_def \<Phi>'_def f_def welldefined apply blast
  using T_def \<Phi>'_def f_def welldefined apply blast
  using T_def \<Phi>'_def \<Phi>_def f_def naturality by presburger  

text \<open>
   This lemma demonstrates that if a presheaf map is valid, then the space, function, domain, and 
   codomain associated with that map must also be valid and adhere to specific properties.
\<close>
lemma valid_map_welldefined :
  "valid_map \<phi> \<Longrightarrow> let f = nat \<phi>; \<Phi> = dom \<phi>; \<Phi>' = cod \<phi>; T = map_space \<phi> in (Space.valid T)
                    \<and> (Function.valid_map f)
                    \<and> valid \<Phi> \<and> valid \<Phi>'
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Function.valid_map (f \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Function.dom (f \<cdot> A) = (ob \<Phi> \<cdot> A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Function.cod (f \<cdot> A) = (ob \<Phi>' \<cdot> A))"
  by (metis Presheaf.valid_map_def)

text \<open>
   This lemma states that if a presheaf map is valid, then the space associated with the map is also valid.
\<close>
lemma valid_map_space : "valid_map \<phi> \<Longrightarrow> Space.valid (map_space \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma shows that if a presheaf map is valid, then the domain of the map is also valid.
\<close>
lemma valid_map_dom : "valid_map \<phi> \<Longrightarrow> valid (dom \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma demonstrates that if a presheaf map is valid, then the codomain of the map is also valid.
\<close>
lemma valid_map_cod : "valid_map \<phi> \<Longrightarrow> valid (cod \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma shows that if a presheaf map is valid, then the function associated with the map is also valid.
\<close>
lemma valid_map_nat : "valid_map \<phi> \<Longrightarrow> Function.valid_map (nat \<phi>)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf map is valid and an open set belongs to the associated space, 
   then the function mapped to the open set is a valid poset map.
\<close>
lemma valid_map_nat_welldefined :
  "valid_map \<phi> \<Longrightarrow> A \<in> Space.opens (map_space \<phi>) \<Longrightarrow> Function.valid_map (nat \<phi> \<cdot> A)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma establishes that if a presheaf map is valid and an open set belongs to the associated 
   space, then the domain of the function mapped to the open set is equal to the value of the object 
   function at the open Function.
\<close>
lemma valid_map_nat_dom : "valid_map \<phi> \<Longrightarrow> A \<in> Space.opens (map_space \<phi>) \<Longrightarrow> Function.dom ((nat \<phi>) \<cdot> A) = ob (dom \<phi>) \<cdot> A"
  by (meson Presheaf.valid_map_welldefined)

text \<open>
   This lemma shows that if a presheaf map is valid and an open set belongs to the associated space, 
   then the codomain of the function mapped to the open set is equal to the value of the object function 
   at the open Function.
\<close>
lemma valid_map_nat_cod : "valid_map \<phi> \<Longrightarrow> A \<in> Space.opens (map_space \<phi>) \<Longrightarrow> Function.cod ((nat \<phi>) \<cdot> A) = ob (cod \<phi>) \<cdot> A"
  by (meson Presheaf.valid_map_welldefined)

text \<open>
   This lemma demonstrates the naturality of a valid presheaf map, showing that for each inclusion in 
   the associated space, the composition of the arrow at the codomain, the function at the codomain of 
   the inclusion, the function at the domain of the inclusion, and the arrow at the domain follows a 
   specific pattern.
\<close>
lemma valid_map_naturality :
  "valid_map \<phi> \<Longrightarrow> i \<in> inclusions (map_space \<phi>) \<Longrightarrow>
     (ar (cod \<phi>) \<cdot> i) \<bullet> (nat \<phi> \<cdot> Space.cod i) = (nat \<phi> \<cdot> Space.dom i) \<bullet> (ar (dom \<phi>) \<cdot> i)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma shows that if a presheaf map is valid, then the function's image of an element in the 
   poset of an open set is an element of the poset of the codomain at the open Function.
\<close>
lemma valid_map_image :
  fixes \<phi> :: "('A, 'a, 'b) PresheafMap" and A :: "'A Open" and a :: "'a"
  defines "\<Phi>A \<equiv> Presheaf.ob (dom \<phi>) \<cdot> A"
  defines "\<Phi>'A \<equiv> Presheaf.ob (cod \<phi>) \<cdot> A"
  defines "f \<equiv> (nat \<phi>) \<cdot> A"
  assumes \<phi>_valid :"valid_map \<phi>"
  and A_open : "A \<in> Space.opens (map_space \<phi>)"
  and a_dom : "a \<in>  \<Phi>A"
shows " f \<cdot> a \<in>  \<Phi>'A"
proof -
  have "valid_map \<phi>"
    using \<phi>_valid by force
  moreover have "A \<in> Space.opens (map_space \<phi>)"
    using A_open by blast
  moreover have "a \<in>  \<Phi>A"
    using a_dom by blast
  moreover have "Function.dom f = \<Phi>A"
    by (metis A_open Presheaf.valid_map_welldefined \<Phi>A_def \<phi>_valid f_def)
  moreover have "Function.valid_map f"
    by (metis A_open Presheaf.valid_map_welldefined \<phi>_valid f_def)
  moreover have "Function.cod f = \<Phi>'A"
    by (metis A_open Presheaf.valid_map_welldefined \<Phi>'A_def \<phi>_valid f_def)
  ultimately show ?thesis
    by (meson Function.fun_app2)
qed

text \<open>
   This lemma shows that if a presheaf is valid and an open set belongs to the associated space, then 
   the arrow function at the identity of the open set behaves as the identity function on elements of 
   the poset at the open Function.
\<close>
lemma ident_app [simp] :
 "valid \<Phi> \<Longrightarrow> A \<in> Space.opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> \<cdot> A \<Longrightarrow> a \<in> obA \<Longrightarrow>
  ((ar \<Phi>) \<cdot> (Space.ident (space \<Phi>) A)) \<cdot> a = Function.ident obA \<cdot> a"
  by (simp add: valid_identity)

text \<open>
   This lemma shows that if a presheaf is valid and an inclusion belongs to the inclusions of the 
   associated space, then the domain of the arrow function at the inclusion is equal to the poset at 
   the codomain of the inclusion.
\<close>
lemma dom_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> B = Space.cod i \<Longrightarrow> f = (ar \<Phi>) \<cdot> i \<Longrightarrow> obB = ((ob \<Phi>) \<cdot> B) \<Longrightarrow> Function.dom f = obB"
  by (metis Presheaf.valid_def)

text \<open>
   This lemma establishes that if a presheaf is valid and an inclusion belongs to the inclusions of 
   the associated space, then the codomain of the arrow function at the inclusion is equal to the poset 
   at the domain of the inclusion.
\<close>
lemma cod_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.dom i \<Longrightarrow> f = (ar \<Phi>) \<cdot> i \<Longrightarrow> obA = ((ob \<Phi>) \<cdot> A) \<Longrightarrow> Function.cod f = obA"
  by (metis Presheaf.valid_def)

text \<open>
   This lemma establishes that if a presheaf is valid, an inclusion belongs to the inclusions of the 
   associated space, and an element belongs to the poset of the codomain of the inclusion, then the image 
   of the element under the arrow function at the inclusion is an element of the poset at the domain of 
   the inclusion.
\<close>
lemma image : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i \<Longrightarrow> a \<in>  ((ob \<Phi>) \<cdot> A) \<Longrightarrow>
    (((ar \<Phi>) \<cdot> i) \<cdot> a) \<in>  ((ob \<Phi>) \<cdot> B) "
  by (metis Function.fun_app2 cod_proj dom_proj valid_ar)


end
