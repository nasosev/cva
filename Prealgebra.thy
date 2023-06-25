section \<open> Prealgebra.thy \<close>

text \<open>
   Theory      :  Prealgebra.thy

   This theory describes the concept of poset-valued presheaves on a topological space. It 
   introduces the records to define a presheaf and a presheaf map, along with  the definitions of 
   validity for a presheaf, a presheaf map (natural transformation)  and a terminal presheaf. 
   Furthermore, the theory provides a collection of lemmas which establish basic properties of presheaves.
--------------------------------------------------------------------------------
\<close>

theory Prealgebra
imports Main Poset Space Function
begin

text \<open>
   This record introduces a presheaf @{term \<Phi>} over a topological space. 
   `space` is the underlying topological space, `ob` maps each open set to a poset, and `ar` maps each 
   inclusion (i.e., an injective continuous function) to a poset map, preserving the order structure. 
\<close>
record ('A, 'a) Prealgebra =
  space :: "'A Space"
  ob :: "('A Open, 'a Poset) Function "
  ar :: "('A Inclusion, ('a, 'a) PosetMap) Function"

text \<open>
   This definition introduces the notion of a valid presheaf. A presheaf is valid if it is well-defined, 
   respects identities, and respects composition of inclusions in the underlying space.
\<close>
definition valid :: "('A, 'a) Prealgebra \<Rightarrow> bool" where
  "valid \<Phi> \<equiv>
    let
      T = space \<Phi>;
      \<Phi>0 = ob \<Phi>;
      \<Phi>1 = ar \<Phi>;

      welldefined = (Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = \<Phi>0 $ (Space.cod i)
                           \<and>  Poset.cod (\<Phi>1 $ i) = \<Phi>0 $ (Space.dom i) );
      identity = (\<forall>A. A \<in> Space.opens T \<longrightarrow> (\<Phi>1 $ (Space.ident T A)) = Poset.ident (\<Phi>0 $ A));
      composition = (\<forall>j i. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow>  Space.dom j = Space.cod i
        \<longrightarrow>  \<Phi>1 $ (Space.compose j i ) = (\<Phi>1 $ i) \<cdot> (\<Phi>1 $ j))
    in
    welldefined \<and> identity \<and> composition"

text \<open>
   This record introduces a presheaf map, which is a functor between two presheaves over the same 
   topological space. `map\_space` is the underlying space, `nat` is the natural transformation which maps 
   each open set to a poset map, `dom` is the domain presheaf, and `cod` is the codomain presheaf.
\<close>
record ('A, 'a, 'b) PrealgebraMap =
  map_space :: "'A Space"
  nat :: "('A Open, ('a, 'b) PosetMap) Function"
  dom :: "('A, 'a) Prealgebra"
  cod :: "('A, 'b) Prealgebra"

text \<open>
   This definition introduces the notion of a valid presheaf map. A presheaf map is valid if it is 
   well-defined and natural, i.e., it commutes with the action of the presheaves on the inclusions 
   in the underlying space.
\<close>
definition valid_map :: "('A, 'a, 'b) PrealgebraMap \<Rightarrow> bool" where
 "valid_map \<phi> \<equiv>
    let
      space = (map_space \<phi>);
      f = nat \<phi>;

      welldefined = Space.valid space
                    \<and> valid (dom \<phi>) \<and> valid (cod \<phi>)
                    \<and> (Function.valid_map f)
                    \<and> (\<forall>A. A \<in> Space.opens space \<longrightarrow> Poset.valid_map (f $ A))
                    \<and> (\<forall>A. A \<in> Space.opens space \<longrightarrow> Poset.dom (f $ A) = (ob (dom \<phi>) $ A))
                    \<and> (\<forall>A. A \<in> Space.opens space \<longrightarrow> Poset.cod (f $ A) = (ob (cod \<phi>) $ A));
      naturality = (\<forall>i. i \<in> inclusions space \<longrightarrow>
          (f $ Space.dom i) \<cdot> (ar (dom \<phi>) $ i) = (ar (cod \<phi>) $ i) \<cdot> (f $ Space.cod i))
    in
    (welldefined \<and> naturality)"

text \<open>
   This definition introduces the terminal presheaf over a space, mapping each open set to the discrete 
   poset on a single element and each inclusion to the identity on this element.
\<close>
definition terminal :: "'A Space \<Rightarrow> ('A, unit) Prealgebra" where
  "terminal T \<equiv>
    let
      space = T;
      ob = Function.const (Space.opens T) UNIV (Poset.discrete);
      ar = Function.const (Space.inclusions T) UNIV (Poset.ident Poset.discrete)
    in
    \<lparr> space = space, ob = ob, ar = ar \<rparr>
"

text \<open> LEMMAS \<close>

text \<open>
   This lemma states that if all components of a presheaf are well-defined and the presheaf respects 
   identities and composition, then the presheaf is valid.
\<close>
lemma validI :
  fixes \<Phi> :: "('A,'a) Prealgebra"
  defines "T \<equiv> space \<Phi>"
  defines "\<Phi>0 \<equiv> ob \<Phi>"
  defines "\<Phi>1 \<equiv> ar \<Phi>"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) )"
  assumes identity : "(\<forall>A. A \<in> Space.opens T \<longrightarrow> (\<Phi>1 $ (Space.ident T A)) = Poset.ident (\<Phi>0 $ A))"
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

text \<open>
   This lemma establishes that if a presheaf is valid, then all its components are well-defined.
\<close>
lemma valid_welldefined  : "valid \<Phi> \<Longrightarrow> let T = space \<Phi>; \<Phi>0 = ob \<Phi>; \<Phi>1 = ar \<Phi> in (Space.valid T)
                    \<and> (Function.valid_map \<Phi>0) \<and> (Function.valid_map \<Phi>1)
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid (\<Phi>0 $ A))
                    \<and> (\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.cod i))
                           \<and>  Poset.cod (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)) )"
  unfolding valid_def by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then its underlying space is a valid space.
\<close>
lemma valid_space  : "valid \<Phi> \<Longrightarrow> T = space \<Phi> \<Longrightarrow> (Space.valid T)"
  by (meson Prealgebra.valid_welldefined)

text \<open>
   This lemma establishes that if a presheaf is valid, then the poset associated to each open set 
   of the underlying space by the presheaf is a valid poset.
\<close>
lemma valid_ob  : "valid \<Phi> \<Longrightarrow> A \<in> Space.opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> Poset.valid obA"
  unfolding valid_def by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then the poset map associated to each inclusion 
   of the underlying space by the presheaf is a valid poset map.
\<close>
lemma valid_ar  :
  fixes \<Phi> :: "('A, 'a) Prealgebra" and i :: "'A Inclusion" and f ::  "('a,'a) PosetMap"
  assumes "valid \<Phi>"
  and "i \<in> Space.inclusions (space \<Phi>)"
  and "f  \<equiv> ar \<Phi> $ i" 
  shows "Poset.valid_map f"
proof -
  define "\<Phi>1" where "\<Phi>1 = Prealgebra.ar \<Phi>" 
  define "T" where "T = Prealgebra.space \<Phi>" 
  have "(\<forall>i. i \<in> Space.inclusions T \<longrightarrow> Poset.valid_map (\<Phi>1 $ i))"  using valid_welldefined
    by (metis T_def \<Phi>1_def assms(1))
    moreover have "i \<in> Space.inclusions T"
      by (simp add: T_def assms(2))
    moreover have "Poset.valid_map (\<Phi>1 $ i)"
      using calculation(1) calculation(2) by auto
    ultimately show ?thesis
      using \<Phi>1_def assms(3) by blast 
  qed

text \<open>
   This lemma establishes that if a presheaf is valid, then the domain of the poset map associated 
   to an inclusion by the presheaf is equal to the poset associated to the codomain of the inclusion.
\<close>
lemma valid_dom  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> $ i \<Longrightarrow> Poset.dom ari = ob \<Phi> $ (Space.cod i)"
  unfolding valid_def
  by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then the codomain of the poset map associated 
   to an inclusion by the presheaf is equal to the poset associated to the domain of the inclusion.
\<close>
lemma valid_cod  : "valid \<Phi> \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> ari = ar \<Phi> $ i \<Longrightarrow> Poset.cod ari = ob \<Phi> $ (Space.dom i)"
  unfolding valid_def
  by (simp add: Let_def)

text \<open>
   This lemma establishes that if a presheaf is valid, then the presheaf maps the identity of an 
   open set to the identity of the associated poset.
\<close>
lemma valid_identity  : "valid \<Phi> \<Longrightarrow> A \<in> Space.opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> ar \<Phi> $ (Space.ident (space \<Phi>) A) = Poset.ident obA"
  unfolding valid_def by (simp add: Let_def)

text \<open>
   This lemma states that if a presheaf is valid, then the presheaf respects composition of 
   inclusions in the underlying space.
\<close>
lemma valid_composition :
  "valid \<Phi> \<Longrightarrow> j \<in> inclusions (space \<Phi>) \<Longrightarrow> i \<in> inclusions (space \<Phi>) \<Longrightarrow> Space.dom j = Space.cod i \<Longrightarrow>
    ar \<Phi> $ (Space.compose j i) = (ar \<Phi> $ i) \<cdot> (ar \<Phi> $ j)"
  by (metis Prealgebra.valid_def)

text \<open>
   This lemma establishes conditions for a presheaf map to be valid. Specifically, it shows that if the 
   space, function, domain and codomain associated with the map are valid and adhere to certain 
   properties, then the map is valid.
\<close>
lemma valid_mapI :
  fixes \<phi> :: "('A,'a,'b) PrealgebraMap"
  defines "T \<equiv> map_space \<phi>"
  defines "f \<equiv> nat \<phi>"
  defines "\<Phi> \<equiv> dom \<phi>"
  defines "\<Phi>' \<equiv> cod \<phi>"
  assumes welldefined : "(Space.valid T)
                    \<and> (Function.valid_map f)
                    \<and> valid \<Phi> \<and> valid \<Phi>'
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid_map (f $ A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.dom (f $ A) = (ob \<Phi> $ A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.cod (f $ A) = (ob \<Phi>' $ A))"
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

text \<open>
   This lemma demonstrates that if a presheaf map is valid, then the space, function, domain, and 
   codomain associated with that map must also be valid and adhere to specific properties.
\<close>
lemma valid_map_welldefined :
  "valid_map \<phi> \<Longrightarrow> let f = nat \<phi>; \<Phi> = dom \<phi>; \<Phi>' = cod \<phi>; T = map_space \<phi> in (Space.valid T)
                    \<and> (Function.valid_map f)
                    \<and> valid \<Phi> \<and> valid \<Phi>'
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.valid_map (f $ A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.dom (f $ A) = (ob \<Phi> $ A))
                    \<and> (\<forall>A. A \<in> Space.opens T \<longrightarrow> Poset.cod (f $ A) = (ob \<Phi>' $ A))"
  by (metis Prealgebra.valid_map_def)

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
  "valid_map \<phi> \<Longrightarrow> A \<in> Space.opens (map_space \<phi>) \<Longrightarrow> Poset.valid_map (nat \<phi> $ A)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma establishes that if a presheaf map is valid and an open set belongs to the associated 
   space, then the domain of the function mapped to the open set is equal to the value of the object 
   function at the open set.
\<close>
lemma valid_map_nat_dom : "valid_map \<phi> \<Longrightarrow> A \<in> Space.opens (map_space \<phi>) \<Longrightarrow> Poset.dom ((nat \<phi>) $ A) = ob (dom \<phi>) $ A"
  by (meson Prealgebra.valid_map_welldefined)

text \<open>
   This lemma shows that if a presheaf map is valid and an open set belongs to the associated space, 
   then the codomain of the function mapped to the open set is equal to the value of the object function 
   at the open set.
\<close>
lemma valid_map_nat_cod : "valid_map \<phi> \<Longrightarrow> A \<in> Space.opens (map_space \<phi>) \<Longrightarrow> Poset.cod ((nat \<phi>) $ A) = ob (cod \<phi>) $ A"
  by (meson Prealgebra.valid_map_welldefined)

text \<open>
   This lemma demonstrates the naturality of a valid presheaf map, showing that for each inclusion in 
   the associated space, the composition of the arrow at the codomain, the function at the codomain of 
   the inclusion, the function at the domain of the inclusion, and the arrow at the domain follows a 
   specific pattern.
\<close>
lemma valid_map_naturality :
  "valid_map \<phi> \<Longrightarrow> i \<in> inclusions (map_space \<phi>) \<Longrightarrow>
     (ar (cod \<phi>) $ i) \<cdot> (nat \<phi> $ Space.cod i) = (nat \<phi> $ Space.dom i) \<cdot> (ar (dom \<phi>) $ i)"
  unfolding valid_map_def by (simp add: Let_def)

text \<open>
   This lemma shows that if a presheaf map is valid, then the function's image of an element in the 
   poset of an open set is an element of the poset of the codomain at the open set.
\<close>
lemma valid_map_image :
  fixes \<phi> :: "('A, 'a, 'b) PrealgebraMap" and A :: "'A Open" and a :: "'a"
  defines "\<Phi>A \<equiv> Prealgebra.ob (dom \<phi>) $ A"
  defines "\<Phi>'A \<equiv> Prealgebra.ob (cod \<phi>) $ A"
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
    by (metis A_open Prealgebra.valid_map_welldefined \<Phi>A_def \<phi>_valid f_def)
  moreover have "Poset.valid_map f"
    by (metis A_open Prealgebra.valid_map_welldefined \<phi>_valid f_def)
  moreover have "Poset.cod f = \<Phi>'A"
    by (metis A_open Prealgebra.valid_map_welldefined \<Phi>'A_def \<phi>_valid f_def)
  ultimately show ?thesis
    by (meson Poset.fun_app2)
qed

text \<open>
   This lemma shows that if a presheaf is valid and an open set belongs to the associated space, then 
   the arrow function at the identity of the open set behaves as the identity function on elements of 
   the poset at the open set.
\<close>
lemma ident_app [simp] :
 "valid \<Phi> \<Longrightarrow> A \<in> Space.opens (space \<Phi>) \<Longrightarrow> obA = ob \<Phi> $ A \<Longrightarrow> a \<in> el obA \<Longrightarrow>
  ar \<Phi> $ (Space.ident (space \<Phi>) A) $$ a = Poset.ident obA $$ a"
  by (simp add: valid_identity)

text \<open>
   This lemma shows that if a presheaf is valid and an inclusion belongs to the inclusions of the 
   associated space, then the domain of the arrow function at the inclusion is equal to the poset at 
   the codomain of the inclusion.
\<close>
lemma dom_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> B = Space.cod i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obB = ((ob \<Phi>) $ B) \<Longrightarrow> Poset.dom f = obB"
  by (metis Prealgebra.valid_def)

text \<open>
   This lemma establishes that if a presheaf is valid and an inclusion belongs to the inclusions of 
   the associated space, then the codomain of the arrow function at the inclusion is equal to the poset 
   at the domain of the inclusion.
\<close>
lemma cod_proj [simp] : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.dom i \<Longrightarrow> f = (ar \<Phi>) $ i \<Longrightarrow> obA = ((ob \<Phi>) $ A) \<Longrightarrow> Poset.cod f = obA"
  by (metis Prealgebra.valid_def)

text \<open>
   This lemma establishes that if a presheaf is valid, an inclusion belongs to the inclusions of the 
   associated space, and an element belongs to the poset of the codomain of the inclusion, then the image 
   of the element under the arrow function at the inclusion is an element of the poset at the domain of 
   the inclusion.
\<close>
lemma image : "valid \<Phi> \<Longrightarrow> i \<in> Space.inclusions (space \<Phi>) \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i \<Longrightarrow> a \<in> Poset.el ((ob \<Phi>) $ A) \<Longrightarrow>
    (((ar \<Phi>) $ i) $$ a) \<in> Poset.el ((ob \<Phi>) $ B) "
  by (metis Poset.fun_app2 cod_proj dom_proj valid_ar)

text \<open>
   This lemma demonstrates the monotonicity of the arrow function at an inclusion in a valid presheaf. It 
   establishes that if an element a is less than or equal to an element a' in the poset of the codomain 
   of the inclusion, then the image of a under the arrow function is less than or equal to the image of 
   a' under the arrow function in the poset of the domain of the inclusion.
\<close>
lemma prj_monotone : 
  fixes \<Phi> :: "('A,'a) Prealgebra" and i :: "'A Inclusion" and A B :: "'A Open" and a a' :: "'a"
  defines "\<Phi>A \<equiv> Prealgebra.ob \<Phi> $ A"
  defines "\<Phi>B \<equiv> Prealgebra.ob \<Phi> $ B"
  defines "\<Phi>i \<equiv> Prealgebra.ar \<Phi> $ i"
  assumes \<Phi>_valid : "valid \<Phi>"
  and i_inc : "i \<in> Space.inclusions (space \<Phi>)" 
  and A_open : "A = Space.cod i" and B_open : "B = Space.dom i"
  and a_elem : "a \<in> Poset.el \<Phi>A" and a'_elem : "a' \<in> Poset.el \<Phi>A" 
  and a_le_a' : "Poset.le \<Phi>A a a'"
shows "Poset.le \<Phi>B (\<Phi>i $$ a) (\<Phi>i $$ a')"
proof -
  have "Poset.valid_map \<Phi>i"
    by (metis Prealgebra.valid_welldefined \<Phi>_valid \<Phi>i_def i_inc)
 moreover have "\<Phi>A = Poset.dom \<Phi>i"
   using A_open \<Phi>A_def \<Phi>_valid \<Phi>i_def i_inc by auto
moreover have "\<Phi>B = Poset.cod \<Phi>i"
  using B_open \<Phi>B_def \<Phi>_valid \<Phi>i_def i_inc by force 
  moreover have "a \<in> Poset.el \<Phi>A"
    using A_open \<Phi>A_def \<Phi>_valid \<Phi>i_def a_elem i_inc by auto
  moreover have "a' \<in> Poset.el \<Phi>A"
    using A_open \<Phi>A_def \<Phi>_valid \<Phi>i_def a'_elem i_inc by auto 
  ultimately show ?thesis using assms Poset.valid_map_monotone [where ?f="ar \<Phi> $ i" and ?a=a and
        ?a'=a']
    by fastforce 
qed

text \<open>
   This lemma shows that the terminal presheaf associated with a valid space is also valid.
\<close>
lemma terminal_valid : "Space.valid T \<Longrightarrow> valid (terminal T)"
  unfolding valid_def terminal_def
  apply (simp add: Let_def)
  apply safe
       apply (simp_all add:   discrete_valid ident_valid)
     apply (simp_all add: Poset.ident_def  valid_inclusion_cod valid_inclusion_dom const_valid)
  apply (smt (verit) Inclusion.select_convs(1) Space.ident_def UNIV_I const_app inclusions_def mem_Collect_eq valid_ident)
  by (smt (verit, best) Inclusion.select_convs(1) Poset.ident_def PosetMap.select_convs(3) Space.compose_def Space.compose_valid UNIV_I const_app discrete_valid ident_left_neutral ident_valid inclusions_def mem_Collect_eq)

text \<open>
   This lemma states that if a space is valid and an open set belongs to the space, then the elements of 
   the poset at the open set in the terminal presheaf associated with the space are the singleton set 
   containing the unit element.
\<close>
lemma terminal_value : "Space.valid T \<Longrightarrow> A \<in> Space.opens T \<Longrightarrow> one = terminal T \<Longrightarrow> Poset.el (ob one $ A) = {()}"
  by (simp add: UNIV_unit discrete_def terminal_def)

text \<open>
   This lemma shows that if a space is valid, an inclusion belongs to the inclusions of the space, and 
   an element belongs to the poset of the codomain of the inclusion in the terminal presheaf associated 
   with the space, then the image of the element under the arrow function at the inclusion is the unit 
   element.
\<close>
lemma terminal_value_proj : "Space.valid T \<Longrightarrow> i \<in> Space.inclusions T \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i
\<Longrightarrow> a \<in> Poset.el (ob one $ A) \<Longrightarrow> prj = (ar one) $ i \<Longrightarrow> prj $$ a = ()"
  by simp

text \<open> EXAMPLES \<close>

text \<open>
   This definition introduces an example of a constant discrete presheaf. The space is a discrete space, 
   and both the object function and the arrow function are constant functions that map to a discrete 
   poset and the identity on the discrete poset, respectively.
\<close>
definition ex_constant_discrete :: "('A, 'a) Prealgebra" where
  "ex_constant_discrete  \<equiv>
    let
      space = Space.ex_discrete;
      discretePoset = Poset.discrete;
      ob = Function.const (opens space) UNIV discretePoset;
      ar = Function.const (inclusions space) UNIV (Poset.ident discretePoset)
    in
    (| space = space, ob = ob, ar = ar |)"

text \<open>
   This lemma establishes the validity of the example constant discrete presheaf.
\<close>
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
