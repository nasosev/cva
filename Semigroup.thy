(*
 Theory      :  Semigroup.thy

 This theory presents a formalization of ordered semigroups. Ordered semigroups are algebraic structures
 that combine both semigroups and partially ordered sets. The file introduces the notion of a valid
 ordered semigroup and presents several lemmas regarding its well-definedness, associativity, and
 monotonicity.
--------------------------------------------------------------------------------
*)
theory Semigroup
  imports Main  Poset
begin

(*
   This record introduces ordered semigroups as algebraic structures combining both semigroups and
   partially ordered sets. 'poset' captures the partial order, and 'mult' captures the semigroup operation.
*)
record 'a Semigroup =
  poset :: "'a Poset"
  mult :: "('a \<times> 'a,'a) PosetMap"

(*
   This definition introduces the concept of a valid ordered semigroup. A valid ordered semigroup is
   one that is well-defined and associative.
*)
definition valid :: "'a Semigroup \<Rightarrow> bool" where
"valid S \<equiv>
  let
    welldefined = (Poset.valid (poset S))
                  \<and> (Poset.valid_map (mult S))
                  \<and> (dom (mult S)) = (poset S) \<times>\<times> (poset S)
                  \<and> cod (mult S) = (poset S);

    mul = \<lambda> a b . (mult S) $$ (a,b);
    elems = Poset.el (poset S);
    associative = \<forall> a b c . a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow> c \<in> elems \<longrightarrow> mul (mul a b) c = mul a (mul b c)
  in
    (welldefined \<and> associative)"

(* LEMMAS *)

(*
   This lemma establishes that if an ordered semigroup is well-defined and associative, then it qualifies
   as a valid ordered semigroup.
*)
lemma validI :
  fixes S :: "'a Semigroup"
  assumes welldefined : "(Poset.valid (poset S)) \<and> (Poset.valid_map (mult S)) \<and> (dom (mult S)) = (poset S) \<times>\<times> (poset S) \<and> cod (mult S) = (poset S)"
  defines "mul \<equiv> \<lambda> a b . (mult S) $$ (a,b)"
  defines "elems \<equiv> Poset.el (poset S)"
  assumes associative : "\<And> a b c . a \<in> elems \<Longrightarrow> b \<in> elems \<Longrightarrow> c \<in> elems \<Longrightarrow> mul (mul a b) c = mul a (mul b c)"
  shows "valid S"
  using Semigroup.valid_def associative elems_def mul_def welldefined by fastforce

(*
   This lemma states that if an ordered semigroup is valid, then it is well-defined.
*)
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

(*
   This lemma establishes that if an ordered semigroup is valid, then it is associative.
*)
lemma valid_associative :
  fixes S :: "'a Semigroup"
  fixes a :: "'a" and b :: "'a" and c :: "'a"
  assumes "valid S"
  defines "elems \<equiv> Poset.el (poset S)"
  assumes "a \<in> elems" and "b \<in> elems" and "c \<in> elems"
  defines "mul \<equiv> \<lambda> a b . (mult S) $$ (a,b)"
  shows " mul (mul a b) c = mul a (mul b c)"
  by (metis Semigroup.valid_def assms(1) assms(3) assms(4) assms(5) elems_def mul_def)

(*
   This lemma states that if an ordered semigroup is valid, then its multiplication operation is
   monotone.
*)
lemma valid_monotone :
  fixes S :: "'a Semigroup"
  fixes a1 :: "'a" and a2 :: "'a" and b1 :: "'a" and b2:: "'a"
  assumes "valid S"
  defines "elems \<equiv> Poset.el (poset S)"
  assumes "a1 \<in> elems" and "a1 \<in> elems" and "b1 \<in> elems" and "b2 \<in> elems"
  defines "mul \<equiv> \<lambda> a b . (mult S) $$ (a,b)"
  assumes a1_le_a2: "Poset.le (poset S) a1 a2" and b1_le_b2: "Poset.le (poset S) b1 b2"
  shows "Poset.le (poset S) (mul a1 b1) (mul a2 b2)"
  unfolding mul_def
proof -
  have "Poset.valid_map (mult S)"
    using Semigroup.valid_welldefined assms(1) by blast
  moreover have "(a1,b1) \<in> Poset.el (Poset.dom (mult S))"
    by (metis (no_types, lifting) Semigroup.valid_welldefined Poset.Poset.select_convs(1) Poset.product_def SigmaI assms(1) assms(3) assms(5) elems_def)
  moreover have "(a2,b2) \<in> Poset.el (Poset.dom (mult S))"
    by (metis (no_types, lifting) Semigroup.valid_welldefined Poset.Poset.select_convs(1) Poset.product_def Poset.valid_welldefined SigmaI a1_le_a2 assms(1) assms(6) elems_def)
  moreover have "Poset.le (poset S) a1 a2"
    using a1_le_a2 by blast
  moreover have "Poset.le (poset S) b1 b2"
    using b1_le_b2 by blast
  moreover have "Poset.le (Poset.dom (mult S)) (a1,b1) (a2,b2)" using Poset.product_def
  proof -
    have f1: "b1 \<in> el (poset S) \<and> b2 \<in> el (poset S)"
      by (metis (no_types) Semigroup.valid_welldefined Poset.valid_welldefined assms(1) b1_le_b2)
    have "a1 \<in> el (poset S) \<and> a2 \<in> el (poset S)"
      by (meson Semigroup.valid_welldefined Poset.valid_welldefined a1_le_a2 assms(1))
    then show ?thesis
      using f1 by (simp add: Semigroup.valid_welldefined Poset.product_def a1_le_a2 assms(1) b1_le_b2)
  qed
  ultimately show "Poset.le (poset S) ((mult S) $$ (a1,b1)) ((mult S) $$ (a2,b2))"
    by (simp add: Semigroup.valid_welldefined assms(1) valid_monotonicity)
qed

end
