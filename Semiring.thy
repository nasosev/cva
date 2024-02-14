section \<open> Semiring.thy \<close>

theory Semiring
  imports Main Semigroup
begin

record 'a Semiring =
  zero :: "'a"
  one :: "'a"
  plus :: "'a Semigroup"
  mult :: "'a Semigroup"

abbreviation poset :: "'a Semiring \<Rightarrow> 'a Poset" where
"poset S \<equiv> Poset.cod (Semigroup.mult (plus S))"

abbreviation elems :: "'a Semiring \<Rightarrow> 'a set" where
"elems S \<equiv> Poset.el (poset S)"

abbreviation mul :: "'a Semiring \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"mul S a b \<equiv> Semigroup.mult (mult S) \<star> (a,b)"

abbreviation add :: "'a Semiring \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"add S a b \<equiv> Semigroup.mult (plus S) \<star> (a,b)" 

definition valid :: "'a Semiring \<Rightarrow> bool" where
"valid S \<equiv>
  let
   welldefined = Semigroup.valid (plus S) 
                \<and> Semigroup.valid (mult S) 
                \<and> Semigroup.poset (plus S) = Semigroup.poset (mult S)
                \<and> (one S) \<in> elems S \<and> (zero S) \<in> elems S;
   commutative_add = Semigroup.commutative (plus S);
   monoid_add = (\<forall> a . a \<in> elems S \<longrightarrow> add S (zero S) a = a \<and> add S a (zero S) = a);
   monoid_mul = (\<forall> a . a \<in> elems S \<longrightarrow> mul S (one S) a = a \<and> mul S a (one S) = a);
   annihilator = (\<forall> a . a \<in> elems S \<longrightarrow> mul S (zero S) a = zero S \<and> mul S a (zero S) = zero S);
   distrib_left = (\<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S \<longrightarrow> mul S a (add S b c) = add S (mul S a b) (mul S a c));
   distrib_right = (\<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S \<longrightarrow> mul S (add S b c) a = add S (mul S b a) (mul S c a))
  in
    welldefined \<and> commutative_add \<and> monoid_add \<and> monoid_mul \<and> annihilator \<and> distrib_left \<and> distrib_right"

(* Validity *)

lemma validI [intro] :
  fixes S :: "'a Semiring"
  assumes welldefined : "Semigroup.valid (plus S) 
                \<and> Semigroup.valid (mult S) 
                \<and> Semigroup.poset (plus S) = Semigroup.poset (mult S)
                \<and> (one S) \<in> elems S \<and> (zero S) \<in> elems S"
  and commutative_add : "Semigroup.commutative (plus S)"
  and monoid_add : "(\<forall> a . a \<in> elems S \<longrightarrow> add S (zero S) a = a \<and> add S a (zero S) = a)"
  and monoid_mul : "(\<forall> a . a \<in> elems S \<longrightarrow> mul S (one S) a = a \<and> mul S a (one S) = a)"
  and annihilator : "(\<forall> a . a \<in> elems S \<longrightarrow> mul S (zero S) a = zero S \<and> mul S a (zero S) = zero S)"
  and distrib_left : "(\<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S \<longrightarrow> mul S a (add S b c) = add S (mul S a b) (mul S a c))"
  and distrib_right : "(\<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S \<longrightarrow> mul S (add S b c) a = add S (mul S b a) (mul S c a))"
shows "valid S" 
  unfolding valid_def
  using annihilator commutative_add local.distrib_left local.distrib_right monoid_add monoid_mul welldefined by presburger

lemma valid_welldefined : "valid S \<Longrightarrow> Semigroup.valid (plus S) 
                \<and> Semigroup.valid (mult S) 
                \<and> Semigroup.poset (plus S) = Semigroup.poset (mult S)
                \<and> (one S) \<in> elems S \<and> (zero S) \<in> elems S" 
  unfolding valid_def
  by presburger

lemma commutative_add : "valid S \<Longrightarrow> Semigroup.commutative (plus S)" 
  unfolding valid_def
  by presburger

lemma monoid_add : "valid S \<Longrightarrow> (\<forall> a . a \<in> elems S \<longrightarrow> add S (zero S) a = a \<and> add S a (zero S) = a)" 
  unfolding valid_def
  by presburger

lemma monoid_mul : "valid S \<Longrightarrow> (\<forall> a . a \<in> elems S \<longrightarrow> mul S (one S) a = a \<and> mul S a (one S) = a)" 
  unfolding valid_def
  by presburger

lemma annihilator : "valid S \<Longrightarrow> (\<forall> a . a \<in> elems S \<longrightarrow> mul S (zero S) a = zero S \<and> mul S a (zero S) = zero S)" 
  unfolding valid_def
  by presburger

lemma distrib_left : "valid S \<Longrightarrow> (\<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S \<longrightarrow> mul S a (add S b c) = add S (mul S a b) (mul S a c))" 
  unfolding valid_def
  by presburger

lemma distrib_right : "valid S \<Longrightarrow> (\<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S \<longrightarrow> mul S (add S b c) a = add S (mul S b a) (mul S c a))"
  unfolding valid_def
  by presburger

(* Examples *)

definition bools :: "bool Semiring" where
  "bools \<equiv> \<lparr> 
    zero = False, 
    one = True, 
    plus = \<lparr> Semigroup.mult = Poset.bools_or  \<rparr>,
    mult = \<lparr> Semigroup.mult = Poset.bools_and  \<rparr> 
  \<rparr>"

lemma valid_bools : "valid bools" 
proof (standard, goal_cases)
  case 1
  then show ?case
    by (smt (verit) Poset.Poset.select_convs(1) Poset.bools_and_def Poset.bools_def Poset.bools_or_def PosetMap.select_convs(2) Semigroup.bools_and_def Semigroup.bools_and_valid Semigroup.bools_or_def Semigroup.bools_or_valid Semigroup.simps(1) Semiring.bools_def Semiring.select_convs(3) Semiring.select_convs(4) UNIV_I comp_eq_dest_lhs)
next
  case 2
  then show ?case 
    unfolding commutative_def bools_def bools_and_def Poset.bools_or_def product_def Poset.bools_def Poset.app_def
    apply clarsimp
     by fastforce
next
  case 3
  then show ?case 
    unfolding bools_def bools_and_def Poset.bools_or_def product_def Poset.bools_def Poset.app_def
    apply clarsimp
    by (smt (verit, del_insts) theI_unique)
next
  case 4
  then show ?case     
    unfolding bools_def bools_and_def Poset.bools_or_def product_def Poset.bools_def Poset.app_def Poset.bools_and_def
    apply clarsimp
    by (smt (verit, del_insts) the_equality)
next
  case 5
  then show ?case 
    unfolding bools_def bools_and_def Poset.bools_or_def product_def Poset.bools_def Poset.app_def Poset.bools_and_def
    apply clarsimp
    by (smt (verit, ccfv_threshold) the_equality)
next
  case 6
  then show ?case   
    unfolding bools_def bools_and_def Poset.bools_or_def product_def Poset.bools_def Poset.app_def Poset.bools_and_def
    apply clarsimp
    by blast
next
  case 7
  then show ?case 
    unfolding bools_def bools_and_def Poset.bools_or_def product_def Poset.bools_def Poset.app_def Poset.bools_and_def
    apply clarsimp
    by blast
qed


end