section \<open> Semigroup.thy \<close>

text \<open>
   Theory      :  Semigroup.thy

   This theory presents a formalization of ordered semigroups. Ordered semigroups are algebraic structures
   that combine both semigroups and partially ordered sets. The file introduces the notion of a valid
   ordered semigroup and presents several lemmas regarding its well-definedness, associativity, and
   monotonicity.
--------------------------------------------------------------------------------
\<close>
theory Semigroup
  imports Main  Poset
begin

text \<open>
   This record introduces ordered semigroups as algebraic structures combining both semigroups and
   partially ordered sets. 'poset' captures the partial order, and 'mult' captures the semigroup operation.
\<close>
record 'a Semigroup =
  poset :: "'a Poset"
  mult :: "('a \<times> 'a,'a) PosetMap"

text \<open>
   This definition introduces the concept of a valid ordered semigroup. A valid ordered semigroup is
   one that is well-defined and associative.
\<close>
definition valid :: "'a Semigroup \<Rightarrow> bool" where
"valid S \<equiv>
  let
    welldefined = (Poset.valid (poset S))
                  \<and> (Poset.valid_map (mult S))
                  \<and> (dom (mult S)) = (poset S) \<times>\<times> (poset S)
                  \<and> cod (mult S) = (poset S);

    mul = \<lambda> a b . (mult S) \<cdot> (a,b);
    elems = Poset.el (poset S);
    associative = \<forall> a b c . a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow> c \<in> elems \<longrightarrow> mul (mul a b) c = mul a (mul b c)
  in
    (welldefined \<and> associative)"

text \<open>
   These are abbreviations for the elements and the multiplication operation of an ordered semigroup.
\<close>
abbreviation elems :: "'a Semigroup \<Rightarrow> 'a set" where
"elems S \<equiv> Poset.el (poset S)"

abbreviation mul :: "'a Semigroup \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"mul S a b\<equiv> (mult S) \<cdot> (a,b)"
text \<open> LEMMAS \<close>

text \<open>
   This lemma establishes that if an ordered semigroup is well-defined and associative, then it qualifies
   as a valid ordered semigroup.
\<close>
lemma validI :
  fixes S :: "'a Semigroup"
  assumes welldefined : "(Poset.valid (poset S)) \<and> (Poset.valid_map (mult S)) \<and> (dom (mult S)) = (poset S) \<times>\<times> (poset S) \<and> cod (mult S) = (poset S)"
  assumes associative : "\<And> a b c . a \<in> elems S \<Longrightarrow> b \<in> elems S \<Longrightarrow> c \<in> elems S \<Longrightarrow> mul S (mul S a b) c = mul S a (mul S b c)"
  shows "valid S"
  using Semigroup.valid_def associative  welldefined by fastforce

text \<open>
   This series of lemmas states that if an ordered semigroup is valid, then it is well-defined, the
   domain of the multiplication operation equals the cartesian product of the semigroup with itself, and
   the codomain of the multiplication operation equals the semigroup.
\<close>
lemma valid_welldefined : "valid S \<Longrightarrow> (Poset.valid (poset S)) \<and> (Poset.valid_map (mult S))
\<and> (dom (mult S)) = (poset S) \<times>\<times> (poset S) \<and> cod (mult S) = (poset S)"
  by (metis Semigroup.valid_def)

lemma valid_poset : "valid S \<Longrightarrow> Poset.valid (poset S)"
  by (metis Semigroup.valid_def)

lemma valid_map : "valid S \<Longrightarrow> Poset.valid_map (mult S)"
  by (metis Semigroup.valid_def)

lemma valid_dom : "valid S \<Longrightarrow> dom (mult S) = (poset S) \<times>\<times> (poset S)"
  by (metis Semigroup.valid_def)

lemma valid_cod : "valid S \<Longrightarrow> cod (mult S) = (poset S)"
  by (metis Semigroup.valid_def)

text \<open>
   This lemma establishes that if an ordered semigroup is valid, then it is associative.
\<close>
lemma valid_associative :
  fixes S :: "'a Semigroup"
  fixes a b c :: "'a"
  assumes "valid S"
  assumes "a \<in> elems S" and "b \<in> elems S" and "c \<in> elems S"
  shows " mul S (mul S a b) c = mul S a (mul S b c)"
  by (metis Semigroup.valid_def assms(1) assms(2) assms(3) assms(4))


text \<open>
   This lemma states that if an ordered semigroup is valid, then its multiplication operation is
   monotone.
\<close>
lemma valid_monotone :
  fixes S :: "'a Semigroup"
  fixes a1 a2 b1 b2 :: "'a"
  assumes "valid S"
  and a1_elem : "a1 \<in> elems S" and a2_elem : "a2 \<in> elems S" and b1_elem : "b1 \<in> elems S" and b2_elem : "b2 \<in> elems S"
  and a1_le_a2: "Poset.le (poset S) a1 a2" and b1_le_b2: "Poset.le (poset S) b1 b2"
  shows "Poset.le (poset S) (mul S a1 b1) (mul S a2 b2)"
proof -
  have "Poset.valid_map (mult S)"
    by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Poset.product_def Semigroup.valid_cod Semigroup.valid_dom SigmaI a1_elem a1_le_a2 a2_elem assms(1) b1_elem b1_le_b2 b2_elem mem_Collect_eq old.prod.case prod.sel(1) prod.sel(2) valid_map valid_map_monotone) 
  moreover have "(a1,b1) \<in> Poset.el (Poset.dom (mult S))"
    by (simp add: Poset.product_def Semigroup.valid_dom a1_elem assms(1) b1_elem) 
  moreover have "(a2,b2) \<in> Poset.el (Poset.dom (mult S))"
    by (simp add: Poset.product_def Semigroup.valid_dom a2_elem assms(1) b2_elem) 
    moreover have "Poset.le (poset S) a1 a2"
    using a1_le_a2 by blast
  moreover have "Poset.le (poset S) b1 b2"
    using b1_le_b2 by blast
  moreover have "Poset.le (Poset.dom (mult S)) (a1,b1) (a2,b2)" using Poset.product_def
  proof -
    have f1: "b1 \<in> el (poset S) \<and> b2 \<in> el (poset S)"
      by (simp add: b1_elem b2_elem) 
    have "a1 \<in> el (poset S) \<and> a2 \<in> el (poset S)"
      by (simp add: a1_elem a2_elem) 
    then show ?thesis
      using f1 by (simp add: Semigroup.valid_welldefined Poset.product_def a1_le_a2 assms(1) b1_le_b2)
  qed
  ultimately show "Poset.le (poset S) ((mult S) \<cdot> (a1,b1)) ((mult S) \<cdot> (a2,b2))"
    by (metis Semigroup.valid_cod assms(1) valid_map_monotone)
qed

end
