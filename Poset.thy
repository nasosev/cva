section \<open> Poset.thy \<close>

text \<open>
   Theory      :  Poset.thy

   This theory provides the foundation of poset (partially ordered set) related constructs, operations,
   and properties that will be used in the formalization of concurrent valuation algebras.
   It includes definitions of posets, maps between posets (monoetone functions), various poset
   operations, as well as the properties and lemmas related to these constructs.
--------------------------------------------------------------------------------
\<close>

theory Poset
imports Main

begin

text \<open>
  This record introduces the basic structure of a partially ordered set (poset).
  @{term el} specifies the set of elements and @{term le_rel} defines the partial order relation on these elements.
\<close>
record 'a Poset =
  el :: "'a set"
  le_rel :: "('a \<times> 'a) set"

text \<open>
  This function returns @{term undefined} when called with elements that are not in the domain of the poset's
  partial order relation.
\<close>
definition "Poset_le_undefined_arg_not_in_domain a a' \<equiv> undefined"

text \<open>
  This abbreviation defines a partial order for a given poset. If 'a' and 'a'' are elements of the poset,
  it checks whether the pair (a, a') is in the poset's partial order relation.
  If either 'a' or 'a'' are not elements of the poset, it returns @{term undefined}.
\<close>
abbreviation le :: "'a Poset \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"le P a a' \<equiv>
  if a \<in> el P \<and> a' \<in> el P
  then (a, a') \<in> le_rel P
  else Poset_le_undefined_arg_not_in_domain a a'"

(*
abbreviation le_P :: "'a \<Rightarrow> 'a Poset \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<sqsubseteq>\<langle>_\<rangle> _") where
"le_P a P a' \<equiv> (a, a') \<in> le_rel P"
*)

text \<open>
  This definition specifies the validity of a poset. A poset is valid if:
  \begin{itemize}
  \item Every pair (x, y) in the relation is well-defined, i.e., x and y are elements of the poset.
  \item The relation is reflexive, antisymmetric, and transitive.
  \end{itemize}
\<close>
definition valid :: "'a Poset \<Rightarrow> bool" where
  "valid P \<equiv>
    let
      welldefined = (\<forall>x y. (x,y) \<in> le_rel P \<longrightarrow> x \<in> el P \<and> y \<in> el P);
      reflexivity = (\<forall>x. x \<in> el P \<longrightarrow> (x,x) \<in> le_rel P);
      antisymmetry = (\<forall>x y. x \<in> el P \<longrightarrow> y \<in> el P  \<longrightarrow>  (x,y) \<in> le_rel P \<longrightarrow> (y,x) \<in> le_rel P  \<longrightarrow> x = y);
      transitivity = (\<forall>x y z. x \<in> el P\<longrightarrow> y \<in> el P \<longrightarrow> z \<in> el P \<longrightarrow> (x,y) \<in> le_rel P \<longrightarrow> (y,z) \<in> le_rel P\<longrightarrow> (x,z) \<in> le_rel P)
    in
      welldefined \<and> reflexivity \<and> antisymmetry \<and> transitivity"

text \<open>
  This record introduces a poset map. A poset map 'f' from a poset 'A' to a poset 'B' is a function
  @{term func} that maps elements of 'A' to 'B', with @{term dom} representing the domain poset 'A' and @{term cod}
  representing the codomain poset 'B'.
\<close>
record ('a, 'b) PosetMap =
  func ::"('a \<times>'b) set"
  dom :: "'a Poset"
  cod :: "'b Poset"

text \<open>
  This function returns @{term undefined} when called with elements that are not in the domain of the poset map.
\<close>
definition "Poset_app_undefined_arg_not_in_domain a \<equiv> undefined"

text \<open>
  This definition describes the application of a poset map to an element of its domain.
  If 'a' is an element of the domain of 'f', then it returns the image of 'a' under 'f'.
  If 'a' is not in the domain, it returns @{term undefined}.
\<close>
definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$$" 997) where
"app f a \<equiv>
  if a \<in> el (dom f)
  then (THE b. (a, b) \<in> func f)
  else Poset_app_undefined_arg_not_in_domain a"

text \<open>
  This definition specifies the validity of a poset map. A poset map is valid if:
  \begin{itemize}
  \item The domain and codomain are valid posets.
  \item Every pair (a, b) in the function is well-defined, i.e., a is an element of the domain and b is an
    element of the codomain.
  \item The function is deterministic, i.e., each element of the domain is mapped to exactly one element of
    the codomain.
  \item The function is total, i.e., every element of the domain is mapped to some element of the codomain.
  \item The function is monotone, i.e., if $a \le a'$ in the domain, then $f(a) \le f(a')$ in the codomain.
  \end{itemize}
\<close>
definition valid_map :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"valid_map f \<equiv>
  let
      le_dom = le (dom f);
      le_cod = le (cod f);
      e_dom = el (dom f);
      e_cod = el (cod f);
      welldefined = valid (dom f) \<and> valid (cod f) \<and> (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> e_dom \<and> b \<in> e_cod);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> e_dom \<longrightarrow> (\<exists>b. (a, b) \<in> func f));
      monotone = (\<forall>a a'. a \<in> e_dom \<and> a' \<in> e_dom \<and> le_dom a a' \<longrightarrow> le_cod (f $$ a) (f $$ a'))

  in welldefined \<and> deterministic \<and> total \<and> monotone"

text \<open>
  The @{term Poset_compose_undefined_incomposable} definition is used when trying to compose two posets
  whose domains and codomains do not match. It yields an undefined result.
\<close>
definition "Poset_compose_undefined_incomposable g f \<equiv> undefined"

text \<open>
  `compose` is a function that combines two poset maps `g` and `f`. If the codomain of `f` matches
  the domain of `g`, then the result is a new poset map with `dom f` as its domain and `cod g` as
  its codomain. The function of the resulting poset map is the relational composition of the
  functions of `f` and `g`. If the codomain of `f` does not match the domain of `g`, the result
  is undefined.
\<close>
definition compose :: "('b, 'c) PosetMap \<Rightarrow> ('a, 'b) PosetMap \<Rightarrow> ('a, 'c) PosetMap" (infixl "\<cdot>" 55) where
  "compose g f \<equiv>
  if dom g = cod f
  then \<lparr> func = relcomp (func f) (func g), dom = dom f, cod = cod g \<rparr>
  else Poset_compose_undefined_incomposable g f"

text \<open>
  `ident` is a function that takes a poset `P` and returns a poset map whose domain and codomain
  are `P`, and whose function is the identity relation on the elements of `P`.
\<close>
definition ident :: "'a Poset \<Rightarrow> ('a, 'a) PosetMap" where
"ident P \<equiv> \<lparr> func = Id_on (el P), dom = P, cod = P \<rparr>"

text \<open>
  `is_surjective` is a predicate that takes a poset map `f` and returns true if `f` is surjective,
  i.e., if every element of the codomain of `f` is the image of some element of the domain of `f`.
\<close>
definition is_surjective :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall>b \<in> el (cod f). \<exists>a \<in> el (dom f). f $$ a = b"

text \<open>
  `is_injective` is a predicate that takes a poset map `f` and returns true if `f` is injective,
  i.e., if every element of the codomain of `f` is the image of at most one element of the domain
  of `f`.
\<close>
definition is_injective :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall>a a' . a \<in> el (dom f) \<longrightarrow> a' \<in> el (dom f) \<longrightarrow> f $$ a = f $$ a' \<longrightarrow> a = a'"

text \<open>
  `is_bijective` is a predicate that takes a poset map `f` and returns true if `f` is bijective,
  i.e., if `f` is both surjective and injective.
\<close>
definition is_bijective :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

text \<open>
  `product` is a function that takes two posets `P` and `Q` and returns a new poset whose
  elements are pairs of elements from `P` and `Q`, and whose less-than-or-equal-to relation
  contains a pair of pairs `(x, y)` if and only if `x` and `y` are in `P` and `Q`, respectively,
  and both the first element of `x` is less than or equal to the first element of `y` in `P` and
  the second element of `x` is less than or equal to the second element of `y` in `Q`.
\<close>
definition product :: "'a Poset \<Rightarrow> 'b Poset \<Rightarrow> ('a \<times> 'b) Poset" (infixl "\<times>\<times>" 55) where
"product P Q \<equiv> \<lparr> el = el P \<times> el Q, le_rel =
 {(x, y). fst x \<in> el P \<and> snd x \<in> el Q \<and> fst y \<in> el P \<and> snd y \<in> el Q \<and> (fst x, fst y) \<in> le_rel P \<and> (snd x, snd y) \<in> le_rel Q} \<rparr>"

text \<open>
  `discrete` is a poset whose elements are all possible values of the type `'a`, and whose
  less-than-or-equal-to relation contains a pair `(x, y)` if and only if `x` is equal to `y`.
  In other words, every element is less than or equal to itself and no other element.
\<close>
definition discrete :: "'a Poset" where
  "discrete \<equiv> \<lparr>  el = UNIV , le_rel = {x. fst x = snd x} \<rparr>"

text \<open>
  @{term is_inf} is a function that takes a poset `P`, a set `U` of elements from `P`, and an element `i`
  from `P`, and returns true if and only if `i` is a lower bound of `U` in `P` and if every other
  lower bound `z` of `U` in `P` is less than or equal to `i` in `P`. In other words, `i` is the
  greatest lower bound of `U` in `P`.
\<close>
definition is_inf :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_inf P U i \<equiv>  U \<subseteq> el P \<and> i \<in> el P \<and>  ((\<forall>u\<in>U. le P i u) \<and> (\<forall>z \<in> el P. (\<forall>u\<in>U. le P z u) \<longrightarrow> le P z i))"

text \<open>
  This definition formalizes the concept of supremum (@{term is_sup}) in a poset. It asserts that for an element
  's' to be the supremum of a set 'U' in poset 'P', 's' should be an element of 'P' and 'U' should be a subset
  of 'P'. Every element 'u' of 'U' should be less than or equal to 's' and for any element 'z' in 'P' that is
  greater than or equal to all elements of 'U', 's' should be less than or equal to 'z'.
\<close>
definition is_sup :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_sup P U s \<equiv> U \<subseteq> el P \<and> s \<in> el P \<and>  (s \<in> el P \<and> (\<forall>u\<in>U. le P u s) \<and> (\<forall>z \<in> el P. (\<forall>u\<in>U. le P u z) \<longrightarrow> le P s z))"

text \<open>
  The 'inf' function computes the infimum (greatest lower bound) of a set 'U' in a poset 'P'. It returns 'None'
  if no such infimum exists, and 'Some i' if 'i' is the infimum of 'U'. 'i' is selected non-deterministically
  among all possible infimums.
\<close>
definition inf :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a option" where
"inf P U \<equiv> if (\<exists>i. i \<in> el P \<and> is_inf P U i) then Some (SOME i. i \<in> el P \<and> is_inf P U i) else None"

text \<open>
  The 'sup' function computes the supremum (least upper bound) of a set 'U' in a poset 'P'. It returns 'None'
  if no such supremum exists, and 'Some s' if 's' is the supremum of 'U'. 's' is selected non-deterministically
  among all possible supremums.
\<close>
definition sup :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a option" where
"sup P U \<equiv> if (\<exists>s. s \<in> el P \<and> is_sup P U s) then Some (SOME s. s \<in> el P \<and> is_sup P U s) else None"

text \<open>
  This abbreviation defines a poset 'P' as being complete if it is valid and for all subsets 'U' of 'P', an
  infimum exists.
\<close>
abbreviation is_complete :: "'a Poset \<Rightarrow> bool" where
"is_complete P \<equiv> valid P \<and> (\<forall>U. U \<subseteq> el P \<longrightarrow> (\<exists>i. is_inf P U i))"

text \<open>
  This abbreviation defines a poset 'P' as being cocomplete if it is valid and for all subsets 'U' of 'P', a
  supremum exists.
\<close>
abbreviation is_cocomplete :: "'a Poset \<Rightarrow> bool" where
"is_cocomplete P \<equiv> valid P \<and> (\<forall>U. U \<subseteq> el P \<longrightarrow> (\<exists>s. is_sup P U s))"

text \<open>
  This defines the powerset of a set 'X' as a poset. The elements of the poset are all subsets of 'X' and the
  less-than-or-equal-to relation is the subset relation.
\<close>
definition powerset :: "'a set \<Rightarrow> ('a set) Poset" where
"powerset X = \<lparr> el = Pow X, le_rel = {(U, V). U \<in> Pow X \<and> V \<in> Pow X \<and> U \<subseteq> V} \<rparr>"

definition direct_image :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a set) Poset \<Rightarrow> ('b set) Poset \<Rightarrow> ('a set, 'b set) PosetMap" where
"direct_image f P Q \<equiv> \<lparr>
        func = {(p, {f x | x . x \<in> p}) | p . p \<in> el P},
        dom = P,
        cod = Q \<rparr>"

text \<open> ----------------- LEMMAS ----------------- \<close>

text \<open>
  This lemma formalizes the criteria for a poset map to be valid. It states that if the domain and codomain are
  both valid posets, each pair in the function relates elements in the domain to the codomain, the function is
  deterministic, total, and preserves order, then the poset map is valid.
\<close>
lemma valid_mapI: "valid (dom f) \<Longrightarrow> valid (cod f)  \<Longrightarrow> (\<And>a b. (a, b) \<in> func f \<Longrightarrow>  a \<in> el (dom f) \<and> b \<in> el (cod f)) \<Longrightarrow>
                   (\<And>a b b'. (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b') \<Longrightarrow>
                   (\<And>a. a \<in> el (dom f) \<Longrightarrow> (\<exists>b. (a, b) \<in> func f)) \<Longrightarrow>
                   (\<And>a a'. a \<in> el (dom f) \<and> a' \<in> el (dom f) \<and> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a'))
  \<Longrightarrow> valid_map f "
  by (smt (verit) Poset.valid_map_def)

text \<open>
  This lemma states that the Cartesian product of two valid posets is also a valid poset.
\<close>
lemma product_valid : "valid P \<Longrightarrow> valid Q \<Longrightarrow> valid (P \<times>\<times> Q)"
  unfolding valid_def product_def
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD case_prodI fst_conv mem_Collect_eq mem_Sigma_iff prod.collapse snd_conv)

text \<open>
  This lemma states that if two poset maps have the same domain, codomain, and function, they are equal.
\<close>
lemma pom_eqI: "cod f = cod g \<Longrightarrow> dom f = dom g \<Longrightarrow> func f = func g \<Longrightarrow> (f :: ('a, 'b) PosetMap) = g"
  by simp

text \<open>
  This theorem states that a poset 'P' is valid if it is well-defined, reflexive, antisymmetric, and transitive.
\<close>
theorem validI :
  fixes P :: "'a Poset"
  assumes welldefined : "(\<And>x y. (x,y) \<in> le_rel P \<Longrightarrow> x \<in> el P \<and> y \<in> el P)"
  assumes reflexivity : "(\<And>x. x \<in> el P \<Longrightarrow> le P x x)"
  assumes antisymmetry : "(\<And>x y. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow>  le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y)"
  assumes transitivity : "(\<And>x y z. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z)"
    shows "valid P"
  by (smt (verit, best) antisymmetry reflexivity transitivity valid_def welldefined)

text \<open>
  These lemmas are fundamental properties of valid posets: they are well-defined, reflexive, transitive, and
  antisymmetric.
\<close>
lemma valid_welldefined : "valid P \<Longrightarrow> (x,y) \<in> le_rel P \<Longrightarrow> x \<in> el P \<and> y \<in> el P"
  by (smt (verit) valid_def)

lemma valid_reflexivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> le P x x"
  by (smt (verit) valid_def)

lemma valid_transitivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z"
  by (smt (verit, ccfv_threshold) valid_def)

lemma valid_antisymmetry : "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> y \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y"
  by (smt (verit, ccfv_threshold) valid_def)

text \<open>
  These lemmas formalize essential properties of valid poset maps: they are well-defined, deterministic, total,
  and preserve order.
\<close>
lemma valid_map_welldefined : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod f)"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_total : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_monotone : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a')"
unfolding valid_map_def
  apply auto
  apply meson
   apply metis
  by metis

text \<open>
   This lemma asserts that for a valid poset map `f` and an element `a` in the domain of `f`,
   the pair `(a, f \$\$ a)` is an element of the function `f`. This is essentially a representation
   of the functionality of a poset map.
\<close>
lemma fun_app : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> (a, f $$ a) \<in> func f"
  by (metis app_def the_equality valid_map_deterministic valid_map_total)

text \<open>
   This lemma establishes that if `fa` is equivalent to `f \$\$ a` for a valid poset map `f` and an element
   `a` in the domain of `f`, then `fa` is an element of the codomain of `f`.
\<close>
lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> fa = f $$ a \<Longrightarrow> fa \<in> el (cod f)"
  by (meson fun_app valid_map_welldefined)

text \<open>
   This lemma is an extensionality result: If two valid poset maps `f` and `g` have the same
   domain and codomain, and map each element of their common domain to the same element in the
   codomain, then `f` and `g` are the same poset map.
\<close>
lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<forall>a \<in> el (dom f). f $$ a = g $$ a) \<Longrightarrow> f = g"
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp)
   apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  done

text \<open>
   This lemma establishes that for two valid poset maps `f` and `g`, where the domain of `g` is
   the codomain of `f`, the domain of the composition $g \cdot f$ is the same as the domain of `f`.
\<close>
lemma dom_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<cdot> f) = dom f"
  unfolding compose_def
  by (simp add: Let_def)

text \<open>
   This lemma states that for two valid poset maps `f` and `g`, where the domain of `g` is
   the codomain of `f`, the codomain of the composition $g \cdot f$ is the same as the codomain of `g`.
\<close>
lemma cod_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> cod (g \<cdot> f) = cod g"
  unfolding compose_def
  by (simp add: Let_def)

text \<open>
   This lemma defines the well-definedness of composition of two valid poset maps `f` and `g`.
   If the pair `(a, b)` is in the function of $g \cdot f$, then `a` is an element of the domain of `f`
   and `b` is an element of the codomain of `g`.
\<close>
lemma compose_welldefined : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<cdot> f) \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod g)"
  by (metis PosetMap.select_convs(1) compose_def relcomp.simps valid_map_welldefined)

text \<open>
   This lemma establishes the deterministic property of the composition of two valid poset maps.
   If `(a, b)` and `(a, b')` are both elements of the function $g \cdot f$, then `b` equals `b'`.
\<close>
lemma compose_deterministic : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<cdot> f) \<Longrightarrow> (a, b') \<in> func (g \<cdot> f) \<Longrightarrow> b = b'"
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) compose_def relcomp.simps valid_map_deterministic)

text \<open>
   This lemma asserts that for two valid poset maps `f` and `g`, where the domain of `g` is the
   codomain of `f`, and `a` is an element of the domain of `f`, there exists a `b` such that
   `(a, b)` is in the function $g \cdot f$.
\<close>
lemma compose_total : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func (g \<cdot> f)"
  unfolding compose_def
  by (smt (verit, best) PosetMap.select_convs(1) fun_app fun_app2 relcomp.relcompI)

text \<open>
   This lemma states that if `(a, b)` is an element of a valid poset map `f`, then `f \$\$ a` is equivalent to `b`.
\<close>
lemma fun_app_iff  : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (f $$ a) = b"
  by (meson fun_app valid_map_deterministic valid_map_welldefined)

text \<open>
   This lemma asserts that the domain of a valid poset map is also valid.
\<close>
lemma valid_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

text \<open>
   This lemma asserts that the codomain of a valid poset map is also valid.
\<close>
lemma valid_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

text \<open>
   This lemma states that for two valid poset maps `f` and `g`, where `a` is an element of the domain
   of `f` and the domain of `g` is the codomain of `f`, the value of $(g \cdot f) \$\$ a$ is the same as $g \$\$ (f \$\$ a)$.
\<close>
lemma compose_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<cdot> f) $$ a = g $$ (f $$ a)"
  apply (clarsimp simp: app_def, safe; clarsimp?)
   apply (smt (verit, del_insts) PosetMap.select_convs(1) compose_def compose_deterministic fun_app relcomp.relcompI theI valid_map_deterministic)
  by (metis app_def fun_app2)

text \<open>
  Lemma @{term compose_monotone} demonstrates the monotonicity of function composition. Given two valid
  poset maps `f` and `g`, and two elements `a` and `a'` from the domain of `f` such that `a` is less than or
  equal to `a'` under the partial order of the domain, and the domain of `g` equals the codomain of `f`,
  it shows that the application of the composition $(g \cdot f)$ on `a` is less than or equal to the application
  on `a'` under the partial order of the codomain of `g`.
\<close>
lemma compose_monotone :
  fixes f :: "('a,'b) PosetMap" and g :: "('b,'c) PosetMap" and a a' :: "'a"
  assumes f_valid : "valid_map f" and g_valid : "valid_map g"
  and a_elem : "a \<in> el (dom f)" and a'_elem : "a' \<in> el (dom f)"
  and le_aa' : "le (dom f) a a'"
  and dom_cod : "dom g = cod f"
shows "le (cod g) ((g \<cdot> f) $$ a) ((g \<cdot> f) $$ a')"
proof -
  have "le (cod f) (f $$ a) (f $$ a')" using valid_map_monotone
    by (metis a'_elem a_elem f_valid le_aa')
  moreover have  "le (cod g) (g $$ (f $$ a)) (g $$ (f $$ a'))" using valid_map_monotone
    by (metis a'_elem a_elem calculation dom_cod f_valid fun_app2 g_valid)
  ultimately show ?thesis using compose_app
    by (metis a'_elem a_elem dom_cod f_valid g_valid)
qed

text \<open>
  Lemma @{term compose_valid} establishes the validity of the composition of two valid poset maps `f` and `g`
  under the condition that the domain of `g` equals the codomain of `f`.
\<close>
lemma compose_valid : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<cdot> f)"
  apply (rule valid_mapI; clarsimp?)
       apply (simp add:  valid_dom)
  apply (simp add:  valid_cod)
  apply (simp add:  compose_welldefined )
  apply (simp add: compose_deterministic)
   apply (simp add: compose_total )
  by (simp add: compose_monotone)

text \<open>
  Lemma @{term comp_app} provides the result of the functional application of the composition of two valid poset
  maps `f` and `g` on an element `a`, given that `(a, b)` belongs to the function `f` and `(b, c)` belongs
  to the function `g`, and the domain of `g` equals the codomain of `f`. The result is equal to `c`.
\<close>
lemma comp_app [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<cdot> f) $$ a = c"
  apply (rule fun_app_iff)
  using compose_valid apply blast
  by (simp add: compose_def relcomp.relcompI)

text \<open>
  Lemma @{term ident_valid} verifies the validity of the identity map on a valid poset `P`.
\<close>
lemma ident_valid  : "valid P \<Longrightarrow> valid_map (ident P)"
  unfolding valid_map_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by blast

text \<open>
  Lemma @{term ident_app} describes the functional application of the identity map on an element `a` in a valid
  poset `P`. The result is equal to `a` itself.
\<close>
lemma ident_app [simp] :
  fixes a :: "'a" and P :: "'a Poset"
  assumes "valid P" and "a \<in> el P"
  shows "((ident P) $$ a) = a"
  unfolding ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by (simp add: assms)

text \<open>
  Lemma @{term valid_map_dom} asserts that for a valid map `f`, if `(a, b)` is an element of the function `f`,
  then `a` is an element of the domain of `f`.
\<close>
lemma valid_map_dom: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f)"
  by (meson valid_map_welldefined)

text \<open>
  Lemma @{term ident_right_neutral} states that the composition of a valid map `f` with the identity map on the
  domain of `f` is equal to `f` itself.
\<close>
lemma ident_right_neutral [simp] : "valid_map f \<Longrightarrow> dom f = x \<Longrightarrow> f \<cdot> (ident x) = f"
  unfolding compose_def ident_def
  apply (simp add: Let_def)
  apply safe
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp?)
  apply (frule (1) valid_map_welldefined)
  apply (erule relcompI[rotated])
  by blast

text \<open>
  Lemma @{term ident_left_neutral} states that the composition of the identity map on the codomain of `f` with
  a valid map `f` is equal to `f` itself.
\<close>
lemma ident_left_neutral [simp]  : "valid_map f \<Longrightarrow> cod f = x \<Longrightarrow> (ident x) \<cdot> f = f"
  unfolding compose_def ident_def
   apply (simp add: Let_def)
  apply safe
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp?)
  apply (frule (1) valid_map_welldefined)
  apply (erule relcompI)
  by blast

text \<open>
  Lemma @{term discrete_valid} confirms the validity of the discrete poset.
\<close>
lemma discrete_valid : "valid discrete"
  by (smt (verit, best) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) UNIV_I discrete_def fst_conv mem_Collect_eq snd_conv validI)

text \<open> Infima \& suprema \<close>

text \<open>
  Lemma @{term inf_unique} establishes the uniqueness of the infimum `i` for a set `U` in a valid poset `P`,
  given `i` and `i'` are both infima of `U`. If `i` and `i'` are infima of `U`, then `i = i'`.
\<close>
lemma inf_unique : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> i \<in> el P\<Longrightarrow> i' \<in> el P \<Longrightarrow> is_inf P U i \<Longrightarrow> is_inf P U i' \<Longrightarrow> i = i'"
  unfolding is_inf_def
  by (metis valid_antisymmetry)

text \<open>
  Lemma @{term sup_unique} establishes the uniqueness of the supremum `s` for a set `U` in a valid poset `P`,
  given `s` and `s'` are both suprema of `U`. If `s` and `s'` are suprema of `U`, then `s = s'`.
\<close>
lemma sup_unique : "valid P  \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> s \<in> el P\<Longrightarrow> s' \<in> el P \<Longrightarrow> is_sup P U s \<Longrightarrow> is_sup P U s' \<Longrightarrow> s = s'"
  unfolding is_sup_def
  by (metis valid_antisymmetry)

text \<open>
  Lemma @{term inf_is_glb} states that in a valid poset `P`, if `i` is the infimum of a set `U`, and `z` is less
  than or equal to all elements of `U`, then `z` is also less than or equal to `i`.
\<close>
lemma inf_is_glb : "valid P  \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> i \<in> el P \<Longrightarrow> is_inf P U i
\<Longrightarrow> \<forall>u\<in>U. le P z u \<Longrightarrow> le P z i"
  by (simp add: is_inf_def)

text \<open>
  Lemma @{term sup_is_lub} states that in a valid poset `P`, if `s` is the supremum of a set `U`, and `z` is
  greater than or equal to all elements of `U`, then `s` is also less than or equal to `z`.
\<close>
lemma sup_is_lub : "valid P  \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> s \<in> el P \<Longrightarrow> is_sup P U s
\<Longrightarrow> \<forall>u\<in>U. le P u z \<Longrightarrow> le P s z"
  by (simp add: is_sup_def)

text \<open>
  Lemma @{term inf_smaller} asserts that in a valid poset `P`, if `i` is the infimum of a set `U`, then `i` is
  less than or equal to every element in `U`.
\<close>
lemma inf_smaller : "valid P  \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> i \<in> el P \<Longrightarrow> is_inf P U i \<Longrightarrow> \<forall> u \<in> U. le P i u"
  unfolding is_inf_def
  by blast

text \<open>
  Lemma @{term sup_greater} asserts that in a valid poset `P`, if `s` is the supremum of a set `U`, then `s` is
  greater than or equal to every element in `U`.
\<close>
lemma sup_greater : "valid P  \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> s \<in> el P  \<Longrightarrow> is_sup P U s \<Longrightarrow> \<forall> u \<in> U. le P u s"
  unfolding is_sup_def
  by blast

text \<open>
  Lemma @{term some_inf_is_inf} asserts that in a valid poset `P`, if `inf P U = Some i`, then `i` is the infimum
  of `U`.
\<close>
lemma some_inf_is_inf : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> i \<in> el P \<Longrightarrow> inf P U = Some i \<Longrightarrow> is_inf P U i"
  unfolding inf_def
  by (metis (no_types, lifting) option.distinct(1) option.inject someI_ex)

text \<open>
  Lemma @{term some_sup_is_sup} asserts that in a valid poset `P`, if `sup P U = Some s`, then `s` is the supremum
  of `U`.
\<close>
lemma some_sup_is_sup : "valid P\<Longrightarrow> U \<subseteq> el P \<Longrightarrow> sup P U = Some s \<Longrightarrow> is_sup P U s"
  unfolding sup_def
  by (metis (no_types, lifting) Poset.sup_unique option.distinct(1) option.inject some_equality)

text \<open>
  Lemma @{term complete_inf_not_none} shows that in a complete poset `P`, `inf P U` cannot be `None`.
\<close>
lemma complete_inf_not_none : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> is_complete P \<Longrightarrow> inf P U \<noteq> None"
  by (simp add: inf_def is_inf_def)

text \<open>
  Lemma @{term cocomplete_sup_not_none} shows that in a cocomplete poset `P`, `sup P U` cannot be `None`.
\<close>
lemma cocomplete_sup_not_none : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> is_cocomplete P \<Longrightarrow> sup P U \<noteq> None"
  by (simp add: is_sup_def sup_def)

text \<open>
  Lemma @{term complete_equiv_cocomplete} proves that a poset `P` is complete if and only if it is cocomplete.
\<close>
lemma complete_equiv_cocomplete : "is_complete P \<longleftrightarrow> is_cocomplete P"
proof
  assume "is_complete P"
  fix U
  define "s" where "s = inf P {a \<in> Poset.el P . (\<forall> u \<in> U . le P u a)}"
  have "s = sup P U"
    oops

text \<open>
  Lemma @{term surjection_is_right_cancellative} states that in a valid map `f`, if `f` is surjective, and `g` and
  `h` are valid maps such that `dom g = cod f` and `dom h = cod f`, and `g \<cdot> f = h \<cdot> f`, then `g = h`.
\<close>
lemma surjection_is_right_cancellative : "valid_map f \<Longrightarrow> is_surjective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h \<Longrightarrow>  g \<cdot> f = h \<cdot> f \<Longrightarrow> g = h"
  by (metis cod_compose compose_app fun_ext is_surjective_def)

text \<open>
  Lemma @{term injection_is_left_cancellative} states that in a valid map `f`, if `f` is injective, and `g` and
  `h` are valid maps such that `cod g = dom f` and `cod h = dom f`, and $`f \<cdot> g = f \<cdot> h`$, then `g = h`.
\<close>
lemma injection_is_left_cancellative : "valid_map f \<Longrightarrow> is_injective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f \<Longrightarrow>  f \<cdot> g = f \<cdot> h \<Longrightarrow> g = h"
  by (smt (verit, best) compose_app dom_compose fun_app2 fun_ext is_injective_def)

text \<open>
  Lemma @{term powerset_valid} states that the powerset poset is valid.
\<close>
lemma powerset_valid : "valid (powerset A)"
  unfolding powerset_def
  using valid_def by fastforce

lemma direct_image_valid : "\<And> f A B  .  P = powerset A \<Longrightarrow> Q = powerset B \<Longrightarrow> (\<forall> x . x \<in> A \<longrightarrow> f x \<in> B) \<Longrightarrow> valid_map (direct_image f P Q)"
proof (rule valid_mapI)
  show "\<And>f A B. P = powerset A \<Longrightarrow> Q = powerset B \<Longrightarrow> \<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow> valid (PosetMap.dom
 (direct_image f P Q))"
    by (simp add: direct_image_def powerset_valid)
  show "\<And>f A B. P = powerset A \<Longrightarrow> Q = powerset B \<Longrightarrow> \<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow> valid (cod (direct_image f P
 Q))"
    by (simp add: direct_image_def powerset_valid)
  show "\<And>f A B a b.
       P = powerset A \<Longrightarrow>
       Q = powerset B \<Longrightarrow>
       \<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow>
       (a, b) \<in> func (direct_image f P Q) \<Longrightarrow>
       a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> b \<in> el (cod (direct_image f P Q))"
  proof -
    fix f :: "'a \<Rightarrow> 'b"
    fix A :: "'a set"
    fix B :: "'b set"
    fix P Q
    fix a b 
    assume "P = powerset A"
    assume Q: "Q = powerset B"
    assume "\<forall>x. x \<in> A \<longrightarrow> f x \<in> B"
    assume  "(a, b) \<in> func (direct_image f P Q)"

    have "PosetMap.dom (direct_image f P Q) = P"
      by (simp add: direct_image_def)
    moreover have "PosetMap.cod (direct_image f P Q) = Q"
      by (simp add: direct_image_def) 
    moreover have "a \<in> el P"
      by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) \<open>(a, b) \<in> func (direct_image f P Q)\<close> direct_image_def fst_conv mem_Collect_eq) 
    moreover have "b \<in> el Q" using  powerset_def [where ?X=B] Q
      by (smt (z3) Pair_inject Poset.Poset.select_convs(1) PosetMap.select_convs(1) PowD PowI \<open>(a, b) \<in> func (direct_image f P Q)\<close> \<open>P = powerset A\<close> \<open>\<forall>x. x \<in> A \<longrightarrow> f x \<in> B\<close> direct_image_def mem_Collect_eq powerset_def subset_eq)  
    ultimately show "a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> b \<in> el (cod (direct_image f P Q))"
      by presburger
  qed
  show "\<And>f A B a b b'.
       P = powerset A \<Longrightarrow>
       Q = powerset B \<Longrightarrow>
       \<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow> (a, b) \<in> func (direct_image f P Q) \<Longrightarrow> (a, b') \<in> func (direct_image f P
 Q) \<Longrightarrow> b = b'"
    by (simp add: direct_image_def)
  show "\<And>f A B a.
       P = powerset A \<Longrightarrow>
       Q = powerset B \<Longrightarrow>
       \<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow> a \<in> el (PosetMap.dom (direct_image f P Q)) \<Longrightarrow> \<exists>b. (a, b) \<in> func
 (direct_image f P Q)"
    by (simp add: direct_image_def) 
  show "\<And>f A B a a'.
       P = powerset A \<Longrightarrow>
       Q = powerset B \<Longrightarrow>
       \<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow>
       a \<in> el (PosetMap.dom (direct_image f P Q)) \<and>
       a' \<in> el (PosetMap.dom (direct_image f P Q)) \<and> le (PosetMap.dom (direct_image f P Q)) a a' \<Longrightarrow>
       le (cod (direct_image f P Q)) (direct_image f P Q $$ a) (direct_image f P Q $$ a')" 
  proof -
    fix f :: "'a \<Rightarrow> 'b"
    fix A :: "'a set"
    fix B :: "'b set"
    fix a :: "'a set"
    fix a' :: "'a set" 
   (* define "P" where "P  = powerset A"
    define "Q" where "Q = powerset B"*)
    assume "P = powerset A"
    assume "Q = powerset B"
    assume "\<forall>x. x \<in> A \<longrightarrow> f x \<in> B"
    assume " a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> a' \<in> el (PosetMap.dom (direct_image f P Q)) \<and> le (PosetMap.dom (direct_image f P Q)) a a'"


    have "PosetMap.dom (direct_image f P Q) = P"
      by (simp add: direct_image_def)
    moreover have "PosetMap.cod (direct_image f P Q) = Q"
      by (simp add: direct_image_def) 
    moreover have "a \<in> el P"
      using \<open>a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> a' \<in> el (PosetMap.dom (direct_image f P Q)) \<and> le (PosetMap.dom (direct_image f P Q)) a a'\<close> calculation(1) by auto 
    moreover have "a' \<in> el P"
      using \<open>a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> a' \<in> el (PosetMap.dom (direct_image f P Q)) \<and> le (PosetMap.dom (direct_image f P Q)) a a'\<close> calculation(1) by auto 
    moreover have "a \<subseteq> a'"
      by (metis (no_types, lifting) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD \<open>P = powerset A\<close> \<open>a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> a' \<in> el (PosetMap.dom (direct_image f P Q)) \<and> le (PosetMap.dom (direct_image f P Q)) a a'\<close> calculation(1) fst_conv powerset_def snd_conv) 
    moreover have "(direct_image f P Q) $$ a = {f x | x . x \<in> a}"  using direct_image_def 
        [where ?f=f and ?P=P and ?Q=Q]   app_def [where ?a=a and ?f=" (direct_image f P Q)"]
      by (simp add: calculation(3)) 
    moreover have "(direct_image f P Q) $$ a' = {f x | x . x \<in> a'}"  using direct_image_def 
        [where ?f=f and ?P=P and ?Q=Q]   app_def [where ?a=a' and ?f=" (direct_image f P Q)"]
      by (simp add: calculation(4)) 
    moreover have "(direct_image f P Q $$ a) \<subseteq> (direct_image f P Q $$ a')" using direct_image_def
        [where ?f=f and ?P=P and ?Q=Q] fun_app2
      using calculation(5) calculation(6) calculation(7) by auto
    moreover have "le (cod (direct_image f P Q)) (direct_image f P Q $$ a) (direct_image f P Q $$
      a')" using direct_image_def powerset_def [where ?X=B]
      by (smt (z3) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) PowD PowI \<open>P = powerset A\<close> \<open>Q = powerset B\<close> \<open>\<forall>x. x \<in> A \<longrightarrow> f x \<in> B\<close> \<open>a \<in> el (PosetMap.dom (direct_image f P Q)) \<and> a' \<in> el (PosetMap.dom (direct_image f P Q)) \<and> le (PosetMap.dom (direct_image f P Q)) a a'\<close> calculation(1) calculation(2) calculation(7) calculation(8) case_prodI mem_Collect_eq powerset_def subset_eq) 
   
    ultimately show "le (cod (direct_image f P Q)) (direct_image f P Q $$ a) (direct_image f P Q $$
      a')"
      by force  
  qed
qed

text \<open> EXAMPLES \<close>

text \<open>
  Definition @{term ex_naturals} is an example of a poset that includes all natural numbers with the less than
  or equal to relation.
\<close>
definition ex_naturals :: "nat Poset" where
  "ex_naturals \<equiv> \<lparr>  el = UNIV , le_rel = {(x,y). x \<le> y}  \<rparr>"

text \<open>
  Lemma @{term ex_naturals_valid} validates the @{term ex_naturals} poset.
\<close>
lemma ex_naturals_valid : "valid ex_naturals"
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) UNIV_I dual_order.refl ex_naturals_def mem_Collect_eq old.prod.case order_antisym order_trans valid_def)

text \<open>
  Definition @{term ex_divisibility} is an example of a poset that includes all natural numbers with the
  divisibility relation.
\<close>
definition ex_divisibility :: "nat Poset" where
  "ex_divisibility \<equiv> \<lparr>  el = UNIV , le_rel = {(x,y). x dvd y }  \<rparr>"

text \<open>
  Lemma @{term ex_divisibility_valid} validates the @{term ex_divisibility} poset.
\<close>
lemma ex_divisibility_valid : "valid ex_divisibility"
  by (smt (verit, ccfv_threshold) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) UNIV_I case_prod_conv dvd_antisym ex_divisibility_def gcd_nat.refl gcd_nat.trans mem_Collect_eq valid_def)

text \<open> TESTS \<close>

(* Warning: this tuple builder syntax gives unexpected result (defines the total relation)
definition discrete_fake :: "bool Poset" where
  "discrete_fake \<equiv> \<lparr>  el = UNIV , le_rel = {(x,x) . True} \<rparr>"

value discrete_fake
*)

(*
definition test :: "nat Poset" where
  "test \<equiv> \<lparr>  el = {0} , le_rel = {(0,0)} \<rparr>"

lemma  "le test 0 0"
  by (simp add: test_def)

lemma "le test 0 1"
  apply auto
*)
end
