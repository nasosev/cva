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

(* Semiring map *)

record ('a, 'b) SemiringMap =
  dom :: "'a Semiring"
  cod :: "'b Semiring"
  plus_func :: "('a, 'b) SemigroupMap"
  mult_func :: "('a, 'b) SemigroupMap"

(*
definition valid_map :: "('a, 'b) SemiringMap \<Rightarrow> bool" where
"valid_map f \<equiv>
  let
    welldefined = Semigroup.valid_map (plus_map f) \<and> Semigroup.valid_map (mult_map f)
                  \<and> Semigroup.poset (Semigroup.dom (plus_map f)) = Semigroup.poset (Semigroup.dom (mult_map f))
                  \<and> Semigroup.func (plus_map f) = Semigroup.func (plus_map f);
    unital = Semigroup.app (plus_map f) (zero (
  in                                 
    welldefined"

lemma valid_mapI [intro] :
  fixes f :: "('a, 'b) SemigroupMap"
  assumes welldefined : "valid (dom f) \<and> valid (cod f) \<and> Poset.valid_map (func f)
                  \<and> Poset.dom (func f) = poset (dom f) \<and>  Poset.cod (func f) = poset (cod f)"
  and lax_morphism : "\<forall> a b . a \<in> elems (dom f) \<longrightarrow> b \<in> elems (dom f)
                  \<longrightarrow> le (poset (cod f)) (func f \<star> (mul (dom f) a b)) (mul (cod f) (func f \<star> a) (func f \<star> b))"
shows "valid_map f" 
  using assms
  by (simp add: Semigroup.valid_map_def) 

                            
lemma valid_map_welldefined : "valid_map f \<Longrightarrow> (valid (dom f) \<and> valid (cod f) \<and> Poset.valid_map (func f)
                  \<and> Poset.dom (func f) = poset (dom f) \<and> Poset.cod (func f) = poset (cod f))"
  by (simp add: Semigroup.valid_map_def)

lemma valid_map_lax_morphism : "valid_map f \<Longrightarrow> \<forall> a b . a \<in> elems (dom f) \<longrightarrow> b \<in> elems (dom f)
                  \<longrightarrow> le (poset (cod f)) (func f \<star> (mul (dom f) a b)) (mul (cod f) (func f \<star> a) (func f \<star> b))"
  using Semigroup.valid_map_def by fastforce
*)
end