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
  func :: "('a \<times> 'b) set"
  cod :: "'b set"

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

definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 998) where
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
  then  \<lparr> func = { (a, b) | a. a \<in> A }, cod = B\<rparr> 
  else Function_const_undefined_arg_not_in_codomain b"

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

text \<open> 
   `fun\_app` states that for a valid function, if an element 'a' is in its domain, applying the function 
   to 'a' will produce a pair (a, b) in the function mapping.
\<close>
lemma fun_app : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> (a, f $ a) \<in> func f"
  by (metis app_def theI' valid_map_deterministic valid_map_total)

text \<open> 
   `fun\_app2` states that for a valid function, if an element 'a' is in its domain, applying the function 
   to 'a' will produce a value 'b' in the codomain.
\<close>
lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> fa = f $ a \<Longrightarrow> fa \<in> cod f"
  by (meson fun_app valid_map_welldefined)

text \<open> 
   `fun\_ext` states that if two valid functions have the same domain and codomain, and they map 
   every element in the domain to the same value, then their function mappings are equal.
\<close>
lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> func f = func g"
  unfolding  dom_def 
  apply (simp_all add: Let_def)
  apply auto
  apply (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)
  by (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)

text \<open> 
   `fun\_ext2` states that if two valid functions have the same domain and codomain, and they map 
   every element in the domain to the same value, then the functions are equal.
\<close>
lemma fun_ext2 : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> f = g"
  apply simp
  apply (frule fun_ext)
      apply auto
  done

text \<open> 
   `const\_app` states that applying the constant function to any element in its domain will produce 
   the fixed value.
\<close>
lemma const_app [simp] : "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ((const A B b) $ a) = b"
  unfolding const_def
  by (simp add: Function.dom_def app_def)

text \<open> 
   `const\_valid` states that the constant function is a valid function as long as the fixed value is in the codomain.
\<close>
lemma const_valid : "b \<in> B \<Longrightarrow> valid_map (const A B b)"
  unfolding valid_map_def const_def
  by (simp add: Function.dom_def app_def)

end
