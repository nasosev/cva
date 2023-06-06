theory Function
imports Main  
begin

record ('a, 'b) Function =
  dom :: "'a set"
  cod :: "'b set"
  func :: "'a \<Rightarrow> 'b" 

definition isValidMap :: "('a, 'b) Function \<Rightarrow> bool" where
"isValidMap f \<equiv> \<forall>a. a \<in> dom f \<longrightarrow> func f a \<in> cod f"

definition app :: "('a, 'b) Function \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 0) where 
"app f a \<equiv> if a \<in> dom f then func f a else undefined"


end