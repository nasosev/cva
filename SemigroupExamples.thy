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
    by (metis (no_types, lifting) PosetExamples.bools_and_def PosetMap.select_convs(1) PosetMap.select_convs(2) Semigroup.Semigroup.select_convs(1) SemigroupExamples.bools_and_def bools_and_valid comp_apply)
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
    by (metis (no_types, lifting) PosetExamples.bools_or_def PosetMap.select_convs(1) PosetMap.select_convs(2) Semigroup.Semigroup.select_convs(1) SemigroupExamples.bools_or_def bools_or_valid comp_apply)
next
  case (2 a b c)
  then show ?case 
    unfolding bools_or_def PosetExamples.bools_or_def Poset.product_def PosetExamples.bools_def
    apply clarsimp
    by (simp add: Poset.app_def)
qed 


definition posreals_plus :: "real Semigroup" where
  "posreals_plus \<equiv> \<lparr> mult = PosetExamples.posreals_plus \<rparr>"

lemma posreals_plus_valid : "valid posreals_plus"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (metis (no_types, lifting) PosetExamples.posreals_plus_def PosetMap.select_convs(1) PosetMap.select_convs(2) Semigroup.Semigroup.select_convs(1) SemigroupExamples.posreals_plus_def comp_apply reals_plus_valid)
next
  case (2 a b c)
  then show ?case 
    unfolding posreals_plus_def PosetExamples.posreals_plus_def Poset.product_def PosetExamples.posreals_plus_def PosetExamples.posreals_def Poset.app_def
    by clarsimp
qed

definition posreals_mult :: "real Semigroup" where
  "posreals_mult \<equiv> \<lparr> mult = PosetExamples.posreals_mult \<rparr>"


lemma posreals_mult_valid : "valid posreals_mult"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (metis (no_types, lifting) PosetExamples.posreals_mult_def PosetMap.select_convs(1) PosetMap.select_convs(2) Semigroup.Semigroup.select_convs(1) SemigroupExamples.posreals_mult_def comp_eq_dest_lhs reals_mult_valid)
next
  case (2 a b c)
  then show ?case 
    unfolding posreals_mult_def PosetExamples.posreals_mult_def Poset.product_def PosetExamples.posreals_mult_def PosetExamples.posreals_def Poset.app_def
    by clarsimp
qed


end
