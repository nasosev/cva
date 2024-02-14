section \<open> SemigroupExamples.thy \<close>

theory SemigroupExamples
  imports Main  Poset PosetExamples Semigroup
begin 


definition bools_and :: "bool Semigroup" where
  "bools_and \<equiv> \<lparr> mult = PosetExamples.bools_and \<rparr>"

lemma bools_and_valid : "valid bools_and"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (smt (verit, best) PosetExamples.bools_and_def PosetMap.select_convs(1) PosetMap.select_convs(2) Semigroup.select_convs(1) SemigroupExamples.bools_and_def bools_and_valid comp_apply)
next
  case (2 a b c)
  then show ?case 
    unfolding bools_and_def PosetExamples.bools_and_def Poset.product_def PosetExamples.bools_def
    apply clarsimp
    by (simp add: Poset.app_def)
qed

definition bools_or :: "bool Semigroup" where
  "bools_or \<equiv> \<lparr> mult = PosetExamples.bools_or \<rparr>"

lemma bools_or_valid : "valid bools_or"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (smt (verit, best) PosetExamples.bools_or_def PosetMap.select_convs(1) PosetMap.select_convs(2) Semigroup.select_convs(1) SemigroupExamples.bools_or_def bools_or_valid comp_apply)
next
  case (2 a b c)
  then show ?case 
    unfolding bools_or_def PosetExamples.bools_or_def Poset.product_def PosetExamples.bools_def
    apply clarsimp
    by (simp add: Poset.app_def)
qed 

end
