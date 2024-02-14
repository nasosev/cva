section \<open> SemiringExamples.thy \<close>

theory SemiringExamples
  imports Main Semiring Semigroup  SemigroupExamples PosetExamples
begin

definition bools :: "bool Semiring" where
  "bools \<equiv> \<lparr> 
    zero = False, 
    one = True, 
    plus = \<lparr> Semigroup.mult = PosetExamples.bools_or  \<rparr>,
    mult = \<lparr> Semigroup.mult = PosetExamples.bools_and  \<rparr> 
  \<rparr>"

lemma valid_bools : "valid bools" 
proof (standard, goal_cases)
  case 1
  then show ?case
    by (smt (verit, ccfv_threshold) Poset.Poset.select_convs(1) PosetExamples.bools_and_def PosetExamples.bools_def PosetExamples.bools_or_def PosetMap.select_convs(2) Semigroup.simps(1) SemigroupExamples.bools_and_def SemigroupExamples.bools_and_valid SemigroupExamples.bools_or_def SemigroupExamples.bools_or_valid Semiring.select_convs(3) Semiring.select_convs(4) SemiringExamples.bools_def UNIV_I comp_def)
next
  case 2
  then show ?case 
    unfolding commutative_def bools_def bools_and_def PosetExamples.bools_or_def product_def PosetExamples.bools_def Poset.app_def
    apply clarsimp
     by fastforce
next
  case 3
  then show ?case 
    unfolding bools_def bools_and_def PosetExamples.bools_or_def product_def PosetExamples.bools_def Poset.app_def
    apply clarsimp
    by (smt (verit, del_insts) theI_unique)
next
  case 4
  then show ?case     
    unfolding bools_def bools_and_def PosetExamples.bools_or_def product_def PosetExamples.bools_def Poset.app_def PosetExamples.bools_and_def
    apply clarsimp
    by (smt (verit, del_insts) the_equality)
next
  case 5
  then show ?case 
    unfolding bools_def bools_and_def PosetExamples.bools_or_def product_def PosetExamples.bools_def Poset.app_def PosetExamples.bools_and_def
    apply clarsimp
    by (smt (verit, ccfv_threshold) the_equality)
next
  case 6
  then show ?case   
    unfolding bools_def bools_and_def PosetExamples.bools_or_def product_def PosetExamples.bools_def Poset.app_def PosetExamples.bools_and_def
    apply clarsimp
    by blast
next
  case 7
  then show ?case 
    unfolding bools_def bools_and_def PosetExamples.bools_or_def product_def PosetExamples.bools_def Poset.app_def PosetExamples.bools_and_def
    apply clarsimp
    by blast
qed