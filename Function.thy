(*
 The Function module formalizes the definition of a function, operations on a function, and properties of a function. The functions are 
 defined as mappings between sets. The definition includes domains and codomains, and introduces well-definedness conditions for a function.
 The module also contains a number of lemmas that specify properties of valid functions.
--------------------------------------------------------------------------------
*)

theory Function
imports Main
begin

(* The Function record defines a type for mapping between sets. 'cod' is the codomain of 
   the function, while 'func' represents the set of tuples, where each tuple (a, b) corresponds 
   to a mapping from a to b. *)
record ('a, 'b) Function =
  cod :: "'b set"
  func :: "('a \<times> 'b) set"

(* 'dom' defines the domain of the function. It returns the set of all 'a' such that there exists 
   a 'b' for which the tuple (a, b) exists in the function mapping. *)
definition dom :: "('a, 'b) Function \<Rightarrow> 'a set" where
"dom f \<equiv> {a. \<exists>b. (a, b) \<in> func f}"

(* 'valid_map' is a predicate to ensure the well-definedness of the function. It checks three properties:
   - 'welldefined': ensures every (a, b) in the function mapping is valid, with a in the domain and b in the codomain.
   - 'deterministic': ensures the function is deterministic, i.e., every 'a' is mapped to exactly one 'b'.
   - 'total': ensures the function is total, i.e., every 'a' in the domain has a corresponding 'b' in the function mapping. *)
definition valid_map :: "('a, 'b) Function \<Rightarrow> bool" where
"valid_map f \<equiv>
  let welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom f \<and> b \<in> cod f);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');                    
      total = (\<forall>a. a \<in> dom f \<longrightarrow> (\<exists>b. (a, b) \<in> func f))

  in welldefined \<and> deterministic \<and> total"

(* 'app' defines the application of a function to an element. If the element is in the domain, 
   it returns the unique 'b' mapped to by 'a', else it returns 'undefined'. *)
definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 998) where
"app f a \<equiv> if a \<in> dom f then (THE b. (a, b) \<in> func f) else undefined"

(* 'const' defines a constant function over a given domain 'A' and codomain 'B', mapping every 'a' in 'A' to a fixed 'b' in 'B'. *)
definition const :: "'a set \<Rightarrow>  'b set  \<Rightarrow> 'b \<Rightarrow>  ('a, 'b) Function" where
"const A B b \<equiv> if b \<in> B then  \<lparr>cod = B, func = { (a, b) | a. a \<in> A }\<rparr> else undefined"

(* LEMMAS *)

(* If a function 'f' is valid, then any (a, b) in its function mapping implies that 'a' is in the domain 
   and 'b' is in the codomain. *)
lemma valid_map_welldefined  : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> dom f \<and> b \<in> cod f"
  unfolding valid_map_def by (simp add: Let_def)

(* If a function 'f' is valid, then for any 'a' in its domain, there is exactly one 'b' such that (a, b) is in the function mapping. *)
lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def by (simp add: Let_def)

(* If a function 'f' is valid, then for any 'a' in its domain, there exists a 'b' such that (a, b) is in the function mapping. *)
lemma valid_map_total  : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def by (simp add: Let_def)

(* For a valid function 'f', if 'a' is in its domain, then applying 'f' to 'a' results in a pair (a, b) in the function mapping. *)
lemma fun_app : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> (a, f $ a) \<in> func f"
  by (metis app_def theI' valid_map_deterministic valid_map_total)

(* For a valid function 'f', if 'a' is in its domain, then applying 'f' to 'a' results in a value in the codomain. *)
lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> f $ a \<in> cod f"
  by (meson fun_app valid_map_welldefined)

(* If two valid functions 'f' and 'g' have the same domain and codomain, and they map every 'a' in the domain to the same 'b', 
   then their function mappings are equal. *)
lemma fun_ext: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> func f = func g"
  unfolding  dom_def 
  apply (simp_all add: Let_def)
  apply auto
  apply (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)
  by (metis Function.dom_def fun_app valid_map_deterministic valid_map_welldefined)

(* If two valid functions 'f' and 'g' have the same domain and codomain, and they map every 'a' in the domain to the same 'b', 
   then the functions 'f' and 'g' are equal. *)
lemma fun_ext2 : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> f = g"
  apply simp
  apply (frule fun_ext)
      apply auto
  done

(* The constant function, when applied to any 'a' in its domain, will return the fixed value 'b'. *)
lemma const_app [simp] : "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ((const A B b) $ a) = b"
  unfolding const_def
  by (simp add: Function.dom_def app_def)

(* The constant function is a valid function, assuming 'b' is in 'B'. *)
lemma const_valid  : "b \<in> B \<Longrightarrow> valid_map (const A B b)"
  unfolding valid_map_def const_def
  by (simp add: Function.dom_def app_def)

end
