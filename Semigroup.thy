section \<open> Semigroup.thy \<close>

theory Semigroup
  imports Main Poset
begin

(* Semigroup type (ordered semigroup *)

record 'a Semigroup =
  mult :: "('a \<times> 'a,'a) PosetMap"

abbreviation poset :: "'a Semigroup \<Rightarrow> 'a Poset" where
"poset \<equiv> Poset.cod o mult"

abbreviation elems :: "'a Semigroup \<Rightarrow> 'a set" where
"elems S \<equiv> Poset.el (poset S)"

abbreviation mul :: "'a Semigroup \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"mul S a b \<equiv> mult S \<star> (a,b)"

definition valid :: "'a Semigroup \<Rightarrow> bool" where
"valid S \<equiv>
  let
    welldefined = Poset.valid_map (mult S)
                  \<and> dom (mult S) = poset S \<times>\<times> poset S;
    associative = \<forall> a b c . a \<in> elems S \<longrightarrow> b \<in> elems S \<longrightarrow> c \<in> elems S
                  \<longrightarrow> mul S (mul S a b) c = mul S a (mul S b c)
  in
    welldefined \<and> associative"

definition commutative :: "'a Semigroup \<Rightarrow> bool" where
"commutative S \<equiv> \<forall> a b . a \<in> elems S \<longrightarrow> b \<in> elems S
                  \<longrightarrow> mul S a b = mul S b a"

(* Validity *)

lemma validI [intro] :
  fixes S :: "'a Semigroup"
  assumes welldefined : "Poset.valid_map (mult S) \<and> dom (mult S) = poset S \<times>\<times> poset S"
  and associative : "\<And> a b c . a \<in> elems S \<Longrightarrow> b \<in> elems S \<Longrightarrow> c \<in> elems S \<Longrightarrow> mul S (mul S a b) c = mul S a (mul S b c)"
  shows "valid S"
  using Semigroup.valid_def associative welldefined by fastforce

lemma valid_welldefined_dom : "valid S \<Longrightarrow> dom (mult S) = poset S \<times>\<times> poset S"
  by (metis Semigroup.valid_def)

lemma valid_welldefined_map : "valid S \<Longrightarrow> Poset.valid_map (mult S)"
  by (metis Semigroup.valid_def)

lemma valid_welldefined : "valid S \<Longrightarrow> Poset.valid_map (mult S) \<and> dom (mult S) = poset S \<times>\<times> poset S"
  by (metis Semigroup.valid_def)

lemma valid_poset : "valid S \<Longrightarrow> Poset.valid (poset S)"
  by (simp add: Poset.valid_map_welldefined_cod valid_welldefined_map)

lemma valid_associative :
  fixes S :: "'a Semigroup"
  fixes a b c :: "'a"
  assumes "valid S"
  assumes "a \<in> elems S" and "b \<in> elems S" and "c \<in> elems S"
  shows " mul S (mul S a b) c = mul S a (mul S b c)"
  by (metis Semigroup.valid_def assms(1) assms(2) assms(3) assms(4))

lemma valid_monotone :
  fixes S :: "'a Semigroup"
  fixes a1 a2 b1 b2 :: "'a"
  assumes S_valid : "valid S"
  and a1_elem : "a1 \<in> elems S" and a2_elem : "a2 \<in> elems S" and b1_elem : "b1 \<in> elems S" and b2_elem : "b2 \<in> elems S"
  and a1_le_a2: "Poset.le (poset S) a1 a2" and b1_le_b2: "Poset.le (poset S) b1 b2"
  shows "Poset.le (poset S) (mul S a1 b1) (mul S a2 b2)"
proof -
  have "(a1,b1) \<in> Poset.el (Poset.dom (mult S))"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def S_valid SigmaI a1_elem b1_elem valid_welldefined_dom)
  moreover have "(a2,b2) \<in> Poset.el (Poset.dom (mult S))"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def S_valid SigmaI a2_elem b2_elem valid_welldefined_dom)
    moreover have "Poset.le (poset S) a1 a2"
    using a1_le_a2 by blast
  moreover have "Poset.le (poset S) b1 b2"
    using b1_le_b2 by blast
  moreover have "Poset.le (Poset.dom (mult S)) (a1,b1) (a2,b2)" using Poset.product_def
  proof -
    have f1: "b1 \<in> el (poset S) \<and> b2 \<in> el (poset S)"
      using b1_elem b2_elem by blast
    moreover have "a1 \<in> el (poset S) \<and> a2 \<in> el (poset S)"
      using a1_elem a2_elem by blast
    ultimately show ?thesis
      by (smt (verit) Poset.Poset.select_convs(2) Poset.product_def S_valid \<open>(a1, b1) \<in> el (PosetMap.dom (mult S))\<close> \<open>(a2, b2) \<in> el (PosetMap.dom (mult S))\<close> a1_le_a2 b1_le_b2 case_prodI mem_Collect_eq prod.sel(1) prod.sel(2) valid_welldefined_dom)
  qed
  ultimately show ?thesis
    by (metis S_valid comp_apply valid_map_monotone valid_welldefined_map)
qed


end
