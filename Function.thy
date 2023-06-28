section \<open> Function.thy \<close>

text \<open>
   Theory      :  Function.thy

   This theory formalizes the mathematical concept of functions as mappings between sets. It provides definitions
   for key properties and operations on functions, such as the domain, codomain, application, and the creation of 
   a constant function. It also introduces the concept of a 'valid' function, which satisfies the conditions of 
   well-definedness, determinism, and totality. The theory also contains a number of lemmas that specify properties 
   of these valid functions.
--------------------------------------------------------------------------------
\<close>

theory Function
imports Main
begin

text \<open> 
   This record defines a type for mapping between sets. The `cod` field represents
   the codomain of the function, while `func` is a set of tuples each corresponding
   to a mapping from an element of the domain to an element of the codomain.
\<close>
record ('a, 'b) Function =
  cod :: "'b set"
  func :: "('a \<times> 'b) set"

text \<open> 
   The `dom` function determines the domain of a function. It returns the set of all
   elements that are mapped to some element in the codomain.
\<close>
definition dom :: "('a, 'b) Function \<Rightarrow> 'a set" where
"dom f \<equiv> {a. \<exists>b. (a, b) \<in> func f}"

text \<open> 
   `valid\_map` is a predicate that checks whether a function satisfies the conditions of 
   being well-defined, deterministic, and total. These conditions ensure that the function
   is properly defined for all inputs from its domain and consistently produces outputs in its codomain.
\<close>
definition valid_map :: "('a, 'b) Function \<Rightarrow> bool" where
"valid_map f \<equiv>
  let welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom f \<and> b \<in> cod f);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');                    
      total = (\<forall>a. a \<in> dom f \<longrightarrow> (\<exists>b. (a, b) \<in> func f))

  in welldefined \<and> deterministic \<and> total"

text \<open> 
   The `app` function represents the application of a function to an element. If the element is 
   in the domain of the function, it returns the corresponding element in the codomain; otherwise, 
   it returns 'undefined'.
\<close>
definition "Function_app_undefined_arg_not_in_domain a \<equiv> undefined"

definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<cdot>" 998) where
"app f a \<equiv> 
  if a \<in> dom f
   then (THE b. (a, b) \<in> func f) 
  else Function_app_undefined_arg_not_in_domain a"

text \<open> 
   The `const` function creates a constant function over a specified domain and codomain. All elements 
   in the domain are mapped to a fixed element in the codomain. If the fixed element is not in the 
   codomain, the function returns 'undefined'.
\<close>
definition "Function_const_undefined_arg_not_in_codomain b \<equiv> undefined"

definition const :: "'a set \<Rightarrow>  'b set  \<Rightarrow> 'b \<Rightarrow>  ('a, 'b) Function" where
"const A B b \<equiv> 
  if b \<in> B
  then  \<lparr> cod = B, func = { (a, b) | a. a \<in> A }\<rparr> 
  else Function_const_undefined_arg_not_in_codomain b"

definition ident :: "'a set \<Rightarrow> ('a, 'a) Function" where
"ident X \<equiv> \<lparr> cod = X, func = Id_on X \<rparr>"

definition "Function_compose_undefined_incomposable g f \<equiv> undefined"

definition compose :: "('b, 'c) Function \<Rightarrow> ('a, 'b) Function \<Rightarrow> ('a, 'c) Function" (infixl "\<bullet>" 55) where
  "compose g f \<equiv>
  if dom g = cod f
  then \<lparr> cod = cod g, func = relcomp (func f) (func g) \<rparr>
  else Function_compose_undefined_incomposable g f"

abbreviation is_surjective :: "('a, 'b) Function \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall> b . b \<in> cod f \<longrightarrow> (\<exists> a . a \<in> dom f \<and> f \<cdot> a = b)"

text \<open>
  `is_injective` is a predicate that takes a poset map `f` and returns true if `f` is injective,
  i.e., if every element of the codomain of `f` is the image of at most one element of the domain
  of `f`.
\<close>
abbreviation is_injective :: "('a, 'b) Function \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall>a a' . a \<in> dom f \<longrightarrow> a' \<in> dom f \<longrightarrow> f \<cdot> a = f \<cdot> a' \<longrightarrow> a = a'"

abbreviation is_bijective :: "('a, 'b) Function \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

text \<open>
   The following lemmas specify various properties of valid functions.
\<close>

text \<open> 
   `valid\_map\_welldefined` states that if a function is valid, then for any pair (a, b) in the 
   function mapping, 'a' is in the domain and 'b' is in the codomain of the function.
\<close>
lemma valid_map_welldefined : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> dom f \<and> b \<in> cod f"
  unfolding valid_map_def by (simp add: Let_def)

text \<open> 
   `valid\_map\_deterministic` states that if a function is valid, then for any 'a' in the domain, 
   there is exactly one 'b' such that (a, b) is in the function mapping.
\<close>
lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def by (simp add: Let_def)

text \<open> 
   `valid\_map\_total` states that if a function is valid, then for any 'a' in the domain, there is 
   some 'b' such that (a, b) is in the function mapping.
\<close>
lemma valid_map_total : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_mapI: "(\<And>a b. (a, b) \<in> func f \<Longrightarrow>  a \<in> dom f \<and> b \<in> cod f) \<Longrightarrow>
                   (\<And>a b b'. (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b') \<Longrightarrow>
                   (\<And>a. a \<in> el (dom f) \<Longrightarrow> (\<exists>b. (a, b) \<in> func f))
  \<Longrightarrow> valid_map f " unfolding valid_map_def
  using Function.dom_def by fastforce 


text \<open> 
   `fun\_app` states that for a valid function, if an element 'a' is in its domain, applying the function 
   to 'a' will produce a pair (a, b) in the function mapping.
\<close>
lemma fun_app : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> (a, f \<cdot> a) \<in> func f"
  by (metis app_def theI' valid_map_deterministic valid_map_total)

text \<open> 
   `fun\_app2` states that for a valid function, if an element 'a' is in its domain, applying the function 
   to 'a' will produce a value 'b' in the codomain.
\<close>
lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> fa = f \<cdot> a \<Longrightarrow> fa \<in> cod f"
  by (meson fun_app valid_map_welldefined)

lemma fun_app3 [simp] : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> f \<cdot> a = (THE b. (a, b) \<in> func f) "
  by (simp add: app_def)

text \<open> 
   `fun\_ext` states that if two valid functions have the same domain and codomain, and they map 
   every element in the domain to the same value, then their function mappings are equal.
\<close>
lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f \<cdot> a = g \<cdot> a) \<Longrightarrow> func f = func g"
  unfolding  dom_def 
  apply (simp_all add: Let_def)
  apply auto
  apply (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)
  by (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)

text \<open> 
   `fun\_ext2` states that if two valid functions have the same domain and codomain, and they map 
   every element in the domain to the same value, then the functions are equal.
\<close>
lemma fun_ext2 : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f \<cdot> a = g \<cdot> a) \<Longrightarrow> f = g"
  apply simp
  apply (frule fun_ext)
      apply auto
  done

lemma fun_app_iff  : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (f \<cdot> a) = b"
  by (meson fun_app valid_map_deterministic valid_map_welldefined)

text \<open> 
   `const\_app` states that applying the constant function to any element in its domain will produce 
   the fixed value.
\<close>
lemma const_app [simp] : "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ((const A B b) \<cdot> a) = b"
  unfolding const_def
  by (simp add: Function.dom_def app_def)

text \<open> 
   `const\_valid` states that the constant function is a valid function as long as the fixed value is in the codomain.
\<close>
lemma const_valid : "b \<in> B \<Longrightarrow> valid_map (const A B b)"
  unfolding valid_map_def const_def
  by (simp add: Function.dom_def app_def)

lemma ident_valid : "valid_map (ident X)"
  by (simp add: Function.dom_def Id_on_iff ident_def valid_map_def)

lemma ident_app [simp] :
  fixes x :: "'x" and X :: "'x set"
  assumes "x \<in> X"
  shows "ident X \<cdot> x = x"
  unfolding ident_def app_def Id_on_def
  apply auto
  using assms apply blast
  by (simp add: Function.dom_def assms)

lemma ident_dom [simp] : "dom (ident X) = X"
  by (simp add: Function.dom_def Id_on_iff ident_def) 

lemma ident_cod [simp] : "cod (ident X) = X"
  by (simp add: ident_def)

lemma const_dom [simp] : "y \<in> Y \<Longrightarrow> dom (const X Y y) = X"
  by (smt (z3) Collect_cong Collect_mem_eq Function.dom_def Pair_inject const_def mem_Collect_eq select_convs(2)) 

lemma const_cod [simp] : "y \<in> Y \<Longrightarrow> cod (const X Y y) = Y"
  by (simp add: const_def)

lemma dom_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<bullet> f) = dom f"
  unfolding compose_def dom_def
  apply clarsimp
  by (metis Function.dom_def relcomp.simps valid_map_total valid_map_welldefined)

lemma cod_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> cod (g \<bullet> f) = cod g"
  unfolding compose_def
  by force 

lemma compose_welldefined : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<bullet> f) \<Longrightarrow> a \<in> dom f \<and> b \<in> cod g"
  unfolding compose_def dom_def valid_map_def
  by clarsimp


lemma compose_deterministic : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<bullet> f) \<Longrightarrow> (a, b') \<in> func (g \<bullet> f) \<Longrightarrow> b = b'"
  unfolding compose_def dom_def valid_map_def
  apply clarsimp
  by metis

lemma compose_total : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> dom f \<Longrightarrow> \<exists>b. (a, b) \<in> func (g \<bullet> f)"
  unfolding compose_def
  by (smt (verit, ccfv_threshold) fun_app fun_app2 relcomp.relcompI select_convs(2))

lemma compose_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> a \<in> dom f \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<bullet> f) \<cdot> a = g \<cdot> (f \<cdot> a)"
  unfolding valid_map_def dom_def compose_def app_def
  apply (simp add: Let_def)
  apply clarsimp
  apply safe
     apply auto
     apply (smt (verit, best) relcomp.simps the_equality)
    apply (metis (mono_tags, lifting) theI_unique)
  apply (meson relcomp.relcompI)
  by (metis Function_app_undefined_arg_not_in_domain_def)

lemma compose_valid : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<bullet> f)"
  apply (rule valid_mapI)
  unfolding valid_map_def
    apply (simp_all add :Let_def)
  apply (smt (verit, del_insts) Function.dom_def compose_def mem_Collect_eq relcomp.simps select_convs(1) select_convs(2))
   apply (metis (no_types, lifting) compose_def relcomp.simps select_convs(2))
  by auto

lemma comp_app [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<bullet> f) \<cdot> a = c"
  apply (rule fun_app_iff)
  using compose_valid apply blast
  by (simp add: compose_def relcomp.relcompI)

lemma surjection_is_right_cancellative : "valid_map f \<Longrightarrow> is_surjective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h \<Longrightarrow>  g \<bullet> f = h \<bullet> f \<Longrightarrow> g = h"
  by (metis cod_compose compose_app fun_ext2)

lemma injection_is_left_cancellative : "valid_map f \<Longrightarrow> is_injective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f \<Longrightarrow>  f \<bullet> g = f \<bullet> h \<Longrightarrow> g = h"
  by (metis compose_app dom_compose fun_app2 fun_ext2) 

end
