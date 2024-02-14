section \<open> PosetExamples.thy \<close>

theory PosetExamples

imports Main Poset

begin

definition bools :: "bool Poset" where
  "bools \<equiv> \<lparr> el = UNIV , le_rel = {(x,y). x \<le> y} \<rparr>"

lemma bools_valid : "valid bools"
  by (simp add: bools_def order_antisym valid_def)

definition bools_and :: "(bool \<times> bool, bool) PosetMap" where
  "bools_and \<equiv> \<lparr> dom = bools \<times>\<times> bools, cod = bools, func = {((a, b), a \<and> b) | a b . (a, b) \<in> el (bools \<times>\<times> bools)} \<rparr>"

lemma bools_and_valid : "valid_map bools_and"
proof (standard, goal_cases)
  case 1
  then show ?case
    by (simp add: bools_and_def bools_valid product_valid)
next
  case 2
  then show ?case
    by (simp add: bools_and_def bools_valid)
next
  case (3 a b)
  then show ?case
    by (smt (z3) Pair_inject PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) bools_and_def mem_Collect_eq product_el_1 product_el_2)
next
  case (4 a b b')
  then show ?case
    by (smt (z3) CollectD Pair_inject PosetMap.select_convs(3) bools_and_def)
next
  case (5 a)
  then show ?case
    by (smt (z3) PosetMap.select_convs(1) PosetMap.select_convs(3) bools_and_def mem_Collect_eq old.prod.exhaust)
next
  case (6 a a')
  then show ?case
    unfolding bools_and_def app_def bools_def product_def
    apply clarsimp
    by (smt (z3) fst_conv prod_eq_iff snd_conv the_equality)
qed

definition bools_or :: "(bool \<times> bool, bool) PosetMap" where
  "bools_or \<equiv> \<lparr> dom = bools \<times>\<times> bools, cod = bools, func = {((a, b), a \<or> b) | a b . (a, b) \<in> el (bools \<times>\<times> bools)} \<rparr>"

lemma bools_or_valid : "valid_map bools_or"
proof (standard, goal_cases)
  case 1
  then show ?case
    by (simp add: bools_or_def bools_valid product_valid)
next
  case 2
  then show ?case
    by (simp add: bools_or_def bools_valid)
next
  case (3 a b)
  then show ?case
    by (smt (z3) Pair_inject PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) bools_or_def mem_Collect_eq product_el_1 product_el_2)
next
  case (4 a b b')
  then show ?case
    by (smt (z3) CollectD Pair_inject PosetMap.select_convs(3) bools_or_def)
next
  case (5 a)
  then show ?case
    by (smt (z3) PosetMap.select_convs(1) PosetMap.select_convs(3) bools_or_def mem_Collect_eq old.prod.exhaust)
next
  case (6 a a')
  then show ?case
    unfolding bools_or_def app_def bools_def product_def
    apply clarsimp
    by (smt (z3) fst_conv prod_eq_iff snd_conv the_equality)
qed

definition naturals :: "nat Poset" where
  "naturals \<equiv> \<lparr> el = UNIV , le_rel = {(x,y). x \<le> y} \<rparr>"

lemma naturals_valid : "valid naturals"
  by (smt (verit, best) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD UNIV_I case_prodI naturals_def fst_conv linorder_linear mem_Collect_eq order_antisym order_trans snd_conv validI)

definition divisibility :: "nat Poset" where
  "divisibility \<equiv> \<lparr> el = UNIV , le_rel = {(x,y). x dvd y } \<rparr>"

lemma divisibility_valid : "valid divisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD UNIV_I case_prodI dvd_antisym divisibility_def fst_conv gcd_nat.refl gcd_nat.trans mem_Collect_eq snd_conv valid_def)

end
