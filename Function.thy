theory Function
imports Main
begin

declare [[show_types]]

record ('a, 'b) Function =
  cod :: "'b set"
  func :: "('a \<times> 'b) set"

definition dom :: "('a, 'b) Function \<Rightarrow> 'a set" where
"dom f \<equiv> {a. \<exists>b. (a, b) \<in> func f}"

definition valid_map :: "('a, 'b) Function \<Rightarrow> bool" where
"valid_map f \<equiv>
  let welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom f \<and> b \<in> cod f);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> dom f \<longrightarrow> (\<exists>b. (a, b) \<in> func f))

  in welldefined \<and> deterministic \<and> total"

definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 998) where
"app f a \<equiv> if a \<in> dom f then (THE b. (a, b) \<in> func f) else undefined"

definition const :: "'a set \<Rightarrow>  'b set  \<Rightarrow> 'b \<Rightarrow>  ('a, 'b) Function" where
"const A B b \<equiv> if b \<in> B then  \<lparr>cod = B, func = { (a, b) | a. a \<in> A }\<rparr> else undefined"

(* LEMMAS *)

lemma valid_map_welldefined [simp] : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> dom f \<and> b \<in> cod f"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_deterministic [simp]: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def by (simp add: Let_def)

lemma valid_map_total [simp] : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def by (simp add: Let_def)

lemma fun_app [simp] : "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> (a, f $ a) \<in> func f"
  by (metis app_def theI' valid_map_deterministic valid_map_total)

lemma fun_app2 [simp]: "valid_map f \<Longrightarrow> a \<in> dom f \<Longrightarrow> f $ a \<in> cod f"
  by (meson fun_app valid_map_welldefined)

lemma fun_ext [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> f $ a = g $ a) \<Longrightarrow> f = g"
  unfolding valid_map_def
  apply simp
  apply auto
  sorry

(* nitpick finds counterexample? *)
lemma fun_ext2 [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> dom f \<Longrightarrow> (a, f $ a) \<in> func f \<longleftrightarrow> (a, g $ a) \<in> func g) \<Longrightarrow> f = g"
  oops

lemma const_app [simp]: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ((const A B b) $ a) = b"
  unfolding const_def
  by (simp add: Function.dom_def app_def)

lemma const_valid [simp] : "b \<in> B \<Longrightarrow> valid_map (const A B b)"
  unfolding valid_map_def const_def
  by (simp add: Function.dom_def app_def)

end