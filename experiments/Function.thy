theory Function
imports Main "HOL-Library.Adhoc_Overloading"
begin

fun exten_equal where
 "exten_equal (A, f, B) (A', g, B') = 
   ((A \<inter> vimage f B = A' \<inter> vimage g B') \<and>  (B = B') \<and> (\<forall>x\<in>(A \<inter> vimage f B). f x  = g x) \<and> (\<forall>x\<in>(A' \<inter> vimage g B'). f x  = g x)) "

quotient_type ('a, 'b) p_function = "('a set \<times> ('a \<Rightarrow> 'b) \<times> 'b set)" / exten_equal
  apply (rule equivpI)
    apply (rule reflpI, clarsimp simp: )
   apply (rule sympI )
   apply (clarsimp)
  by (simp add: exten_equal.elims(2)  transp_def)  

type_notation  p_function (infixr "\<rightharpoondown>" 0)

lift_definition restrict :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) p_function" is "\<lambda>f S S'. (S, f, S')"
  done

lift_definition app :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b" is 
                      "\<lambda>(A, f, B) x. if x \<in> (A \<inter> vimage f B) then f x else undefined"
  apply (rule ext; clarsimp simp:)
  by blast


lift_definition dom :: "('a, 'b) p_function \<Rightarrow> 'a set" is "\<lambda>(A, f, B). A \<inter> (vimage f B)"
  by (clarsimp)

lift_definition cod :: "('a, 'b) p_function \<Rightarrow> 'b set" is "\<lambda>f. snd (snd f)"
  by (clarsimp)

abbreviation "total_f f == (restrict f UNIV UNIV)"

abbreviation "on_domain_f f A == (restrict f A UNIV)"

notation app (infixl "$" 54)

definition range :: "('a, 'b) p_function \<Rightarrow> 'b set"
  where "range f = {x. \<exists>y\<in>dom f. f $ y = x \<and> x \<in> cod f}"

lemma range_sub_cod: "range f \<subseteq> cod f"
  by (clarsimp simp: range_def)

syntax
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_ \<rightarrow> _./ _)" [0,0,3] 3)
  "_lam_dom" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
  "_lam_free" :: "pttrn \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_!./ _)" [0,3] 3)

translations 
 "\<lambda>x!. f" \<rightleftharpoons> "CONST total_f (\<lambda>x. f) "
 "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST on_domain_f (\<lambda>x. f) A"
 "\<lambda>x\<in>A \<rightarrow> B. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A B"


lemma "dom f = dom g \<Longrightarrow> cod f = cod g  \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f $ x = g $ x) \<Longrightarrow> range f = range g "
  by (simp add: range_def)

lemma ext_restrict: "dom f = dom g \<Longrightarrow> cod f = cod g  \<Longrightarrow> 
   (\<And>x. x \<in> dom f \<Longrightarrow> f $ x = g $ x) \<Longrightarrow> f = g" 
  apply (clarsimp simp: range_def)
  apply (transfer)
  apply (clarsimp)
  apply (subst (asm) set_eq_iff)
  apply (erule_tac x=x in allE, clarsimp)
  apply (atomize)
  apply (erule_tac x=x in allE, drule mp, clarsimp)
    apply (clarsimp)
  done


lemma app_subst[simp,trans]: "x \<in> A \<Longrightarrow> P (f x) \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $ x)"
  by (transfer, clarsimp)

lemma app_subst'[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow>  P (f x) \<Longrightarrow> P ((\<lambda>x\<in>A \<rightarrow> B. f x) $ x)"
  by (transfer, clarsimp)

lemma app_subst''[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow>  P (f x) \<Longrightarrow> P ((\<lambda>x!. f x) $ x)"
  by (transfer, clarsimp)

lemma app_iff[simp]: "x \<in> A \<Longrightarrow> ((\<lambda>x\<in>A. f x) $ x) =  (f x) "
  by (transfer, clarsimp)

lemma app_iff'[simp]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> ((\<lambda>x\<in>A \<rightarrow> B. f x) $ x) =  (f x) "
  by (transfer, clarsimp)

lemma app_iff''[simp]: " ((\<lambda>x!. f x) $ x) =  (f x) "
  by (transfer, clarsimp)

lemma app_ssubst: "x \<in> A \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $ x) \<Longrightarrow> P (f x) "
  by (transfer, clarsimp)

lemma dom_simp[simp]: "dom (\<lambda>x\<in>A. f x) = A"
  by (transfer, clarsimp)

lemma dom_simp'[simp]: "dom (\<lambda>x\<in>A \<rightarrow> B. f x) = A \<inter> (vimage f B)"
  by (transfer, clarsimp)


definition add :: "nat \<rightharpoondown> nat \<rightharpoondown> nat" (* Addition on increasing pairs of natural numbers such that the first argument is less than 20 and the combination less than 50 *)
  where "add = (\<lambda>x\<in>{n. n \<le> 20}. \<lambda>y\<in>{n. (n :: nat) \<ge> x} \<rightarrow> {n. n \<le> 50}. x + y)"

lemma example: "(add $ 3) $ 5 = (add $ 2 $ 6)"
  by (unfold add_def, clarsimp)

lemma example': "(add $ 100) $ 5 = (add $ 99 $ 6)"
  apply (clarsimp simp: add_def)
  apply (subst app_iff) (* not in the domain *)
  oops
 
lemma total: "a \<in> dom f \<Longrightarrow> f $ a \<in> (cod f)"
  by (transfer, clarsimp)

definition const :: "'a set \<Rightarrow> 'b set \<Rightarrow> 'a \<rightharpoondown> 'b \<rightharpoondown> 'a"
  where "const A B = (\<lambda>x\<in>A.\<lambda>y\<in>B \<rightarrow> {x}. x)" 

lemma const_is_const: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> const A B $ a $ b = a"
  by (clarsimp simp: const_def)

definition const_alt :: "'a set \<rightharpoondown> 'b set \<rightharpoondown> 'a \<rightharpoondown> 'b \<rightharpoondown> 'a" (* Unnecessary, but possible *)
  where "const_alt = (\<lambda>A!.\<lambda>B!. \<lambda>x\<in>A. \<lambda>y\<in>B \<rightarrow> {x}. x)" 

definition compose :: "('a \<rightharpoondown> 'b) \<rightharpoondown> ('b \<rightharpoondown> 'c) \<rightharpoondown> ('a \<rightharpoondown> 'c)"
  where "compose = (\<lambda>f!.\<lambda>g\<in>{g. cod f \<subseteq> dom g}. \<lambda>x\<in>(dom f) \<rightarrow> (cod g). g $ (f $ x))"  

abbreviation "cmp f g \<equiv> (compose $ f) $ g"

notation cmp (infixl "\<cdot>" 55)

term "f \<cdot> g $ x"



end