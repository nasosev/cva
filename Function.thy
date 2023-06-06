theory Function
imports Main  
begin

record ('a, 'b) Function =
  dom :: "'a set"
  cod :: "'b set"
  func :: "'a \<Rightarrow> 'b" 

definition isValidMap :: "('a, 'b) Function \<Rightarrow> bool" where
"isValidMap f \<equiv> \<forall>x. x \<in> dom f \<longrightarrow> func f x \<in> cod f"

definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 0) where 
"app f x \<equiv> if x \<in> dom f then func f x else undefined"


end