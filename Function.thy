(*
 Theory      :  Function.thy

 This theory provides a formalization of mathematical functions as mappings between sets, including
 definitions of a function's domain, codomain, and application, as well as the definition of a 
 constant function. It also introduces the concept of a 'valid' function that satisfies conditions 
 of well-definedness, determinism, and totality. A number of lemmas are provided that specify properties 
 of these valid functions.
--------------------------------------------------------------------------------
*)

theory Function
imports Main
begin

(* 
   This record introduces a type for mapping between sets. It contains two fields: 'cod' representing
   the codomain of the function, and 'func' encapsulating the set of tuples each of which corresponds
   to a mapping from a domain element to a codomain element. 
*)
record ('a, 'b) Function =
  cod :: "'b set"
  func :: "('a \<times> 'b) set"

(* 
   This definition establishes the domain of a function. It returns the set of all 'a' such that there exists 
   a 'b' for which the tuple (a, b) exists in the function mapping.
*)
definition dom :: "('a, 'b) Function \<Rightarrow> 'a set" where
"dom f \<equiv> {a. \<exists>b. (a, b) \<in> func f}"

(* 
   This predicate checks the well-definedness of a function by verifying three conditions:
     - 'welldefined': every (a, b) in the function mapping is valid, with 'a' in the domain and 'b' in the codomain.
     - 'deterministic': the function is deterministic, i.e., every 'a' maps to exactly one 'b'.
     - 'total': the function is total, i.e., every 'a' in the domain has a corresponding 'b' in the function mapping.
*)
definition valid_map :: "('a, 'b) Function \<Rightarrow> bool" where
"valid_map f \<equiv>
  let welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom f \<and> b \<in> cod f);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');                    
      total = (\<forall>a. a \<in> dom f \<longrightarrow> (\<exists>b. (a, b) \<in> func f))

  in welldefined \<and> deterministic \<and> total"

(* 
   This definition models the application of a function to an element. If the element belongs to the domain, 
   it returns the unique 'b' that 'a' maps to; otherwise, it returns 'undefined'.
*)
definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 998) where
"app f a \<equiv> if a \<in> dom f then (THE b. (a, b) \<in> func f) else undefined"

(* 
   This definition creates a constant function over a given domain 'A' and codomain 'B', mapping every element 'a' 
   in 'A' to a fixed element 'b' in 'B'.
*)
definition const :: "'a set \<Rightarrow>  'b set  \<Rightarrow> 'b \<Rightarrow>  ('a, 'b) Function" where
"const A B b \<equiv> if b \<in> B then  \<lparr>cod = B, func = { (a, b) | a. a \<in> A }\<rparr> else undefined"

(*
   This section includes various lemmas that specify properties of valid functions.
*)

(* 
   This lemma asserts that if a function 'f' is valid, then any pair (a, b) in its function mapping implies 
   that 'a' is in the domain and 'b' is in the codomain.
*)
lemma valid_map_welldefined : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> dom f \<and> b \<in> cod f"
  unfolding valid_map_def by (simp add: Let_def)

(* 
   This lemma asserts that if a function 'f' is valid, then for any 'a' in its domain, there is exactly 
   one 'b' such that (a, b) is in the function mapping.
*)
lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def by (simp add: Let_def)

(* 
   This lemma asserts that if a function 'f' is valid, then for any 'a' in its domain, there exists 
   a 'b' such that (a, b) is in the function mapping.
*)
lemma valid_map_total : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def by (simp add: Let_def)

(* 
   This lemma asserts that for a valid function 'f', if 'a' is in its domain, then applying 'f' to 'a' results 
   in a pair (a, b) in the function mapping.
*)
lemma fun_app : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> (a, f $ a) \<in> func f"
  by (metis app_def theI' valid_map_deterministic valid_map_total)

(* 
   This lemma asserts that for a valid function 'f', if 'a' is in its domain, then applying 'f' to 'a' results 
   in a value in the codomain.
*)
lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> fa = f $ a \<Longrightarrow> fa \<in> cod f"
  by (meson fun_app valid_map_welldefined)

(* 
   This lemma asserts that if two valid functions 'f' and 'g' have the same domain and codomain, and they map 
   every 'a' in the domain to the same 'b', then their function mappings are equal.
*)
lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> func f = func g"
  unfolding  dom_def 
  apply (simp_all add: Let_def)
  apply auto
  apply (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)
  by (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)

(* 
   This lemma asserts that if two valid functions 'f' and 'g' have the same domain and codomain, and they map 
   every 'a' in the domain to the same 'b', then the functions 'f' and 'g' are equal.
*)
lemma fun_ext2 : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> f = g"
  apply simp
  apply (frule fun_ext)
      apply auto
  done

(* 
   This lemma asserts that the constant function, when applied to any 'a' in its domain, will return 
   the fixed value 'b'.
*)
lemma const_app [simp] : "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ((const A B b) $ a) = b"
  unfolding const_def
  by (simp add: Function.dom_def app_def)

(* 
   This lemma asserts that the constant function is a valid function, assuming 'b' is in 'B'.
*)
lemma const_valid : "b \<in> B \<Longrightarrow> valid_map (const A B b)"
  unfolding valid_map_def const_def
  by (simp add: Function.dom_def app_def)

end
