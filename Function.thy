theory Function
imports Main  
begin

record ('a, 'b) Function =
  cod :: "'b set"
  func :: "('a \<times> 'b) set" 

definition dom :: "('a, 'b) Function \<Rightarrow> 'a set" where
"dom f \<equiv> {a. \<exists>b. (a, b) \<in> func f}"

definition isValidMap :: "('a, 'b) Function \<Rightarrow> bool" where
"isValidMap f \<equiv> 
  let welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom f \<and> b \<in> cod f);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> dom f \<longrightarrow> (\<exists>b. (a, b) \<in> func f))
  
  in welldefined \<and> deterministic \<and> total"
  

definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 0) where 
"app f a \<equiv> if a \<in> dom f then (THE b. (a, b) \<in> func f) else undefined"

definition const :: "'a set \<Rightarrow>  'b set  \<Rightarrow> 'b \<Rightarrow>  ('a, 'b) Function" where
"const A B b \<equiv> \<lparr>cod = B, func = { (a, b) | a. a \<in> A }\<rparr>"

(* 
lemma fun_app [simp]: "a \<in> dom f \<Longrightarrow> (f $ a) = func f a"
  by (simp add: app_def)  *)
  



end