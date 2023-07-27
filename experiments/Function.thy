theory Function
imports Main "HOL-Library.Monad_Syntax"
begin

fun exten_equal where
 "exten_equal (A, f, B) (A', g, B') = 
   ((A \<inter> vimage f B = A' \<inter> vimage g B') \<and> 
      (B = B') \<and> (\<forall>x\<in>(A \<inter> vimage f B). f x  = g x) \<and> (\<forall>x\<in>(A' \<inter> vimage g B'). f x  = g x)) "

quotient_type ('a, 'b) p_function = "('a set \<times> ('a \<Rightarrow> 'b) \<times> 'b set)" / exten_equal
  apply (rule equivpI)
    apply (rule reflpI, clarsimp simp: )
   apply (rule sympI )
   apply (clarsimp)
  by (simp add: exten_equal.elims(2)  transp_def)  


type_notation p_function (infixr "\<rightharpoondown>" 0)

lift_definition restrict :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) p_function" is "\<lambda>f S S'. (S, f, S')"
  done

lift_definition safe_app :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b option " is 
                      "\<lambda>(A, f, B) x. if x \<in> (A \<inter> vimage f B) then Some (f x) else None"
  apply (rule ext; clarsimp simp:)
  by blast

lift_definition app :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b" is 
                      "\<lambda>(A, f, B) x. if x \<in> (A \<inter> vimage f B) then f x else undefined"
  apply (rule ext; clarsimp simp:)
  by blast


lift_definition dom :: "('a, 'b) p_function \<Rightarrow> 'a set" is 
                      "\<lambda>(A, f, B). A \<inter> (vimage f B)" 
  by (clarsimp simp:)


(* lift_definition dom :: "('a, 'b) p_function \<Rightarrow> 'a set" is "\<lambda>(A, f, B). A"
  by (clarsimp)
*)

lift_definition cod :: "('a, 'b) p_function \<Rightarrow> 'b set" is "\<lambda>f. snd (snd f)"
  by (clarsimp)

lift_definition func :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b" is 
                      "\<lambda>(A, f, B) x. if x \<in> (A \<inter> vimage f B) then f x else undefined"
  apply (rule ext; clarsimp simp:)
  by blast



abbreviation (input) "total_f f == (restrict f UNIV UNIV)"

abbreviation (input) "on_domain_f f A == (restrict f A UNIV)"


notation safe_app (infixl "$$" 54)


(* definition n_dom :: "('a, 'b) p_function \<Rightarrow> 'a set" 
  where "n_dom f =  dom f \<inter> (inv_image (f) (cod f))"
*)


(* definition range :: "('a, 'b) p_function \<Rightarrow> 'b set"
  where "range f = {x. \<exists>y\<in>dom f. f $$ y = Some x \<and> x \<in> cod f}"
*)


(* definition n_dom :: "('a, 'b) p_function \<Rightarrow> 'a set"
  where "n_dom f = {x. x \<in> dom f \<and> (\<exists>y. f $$ x = Some y \<and> y \<in> cod f)}" *)




syntax
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_ \<rightarrow> _./ _)" [0,0,3] 3)
  "_lam_dom" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
  "_lam_free" :: "pttrn \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_!./ _)" [0,3] 3)


translations 
 "\<lambda>x!. f" \<rightleftharpoons> "CONST total_f (\<lambda>x. f ) "
 "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST on_domain_f (\<lambda>x. f) A"
 "\<lambda>x\<in>A \<rightarrow> B. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A (B)"


lemma exists_fun: "\<exists>g. f = (\<lambda>x\<in>(dom f) \<rightarrow> (cod f). g x)"
  apply (transfer)
  apply (clarsimp)
  by blast

definition "quot_app f \<equiv> (SOME g. f = (\<lambda>x\<in>(dom f) \<rightarrow> (cod f). g x))"

notation quot_app (infixl "$" 54)


notation restrict ("_ \<Ztypecolon> _ \<rightarrow> _" 1)  

definition preimage :: "('a, 'b) p_function \<Rightarrow> 'b set \<rightharpoondown> 'a set"
  where "preimage f = (\<lambda>S\<in>{S. S \<subseteq> cod f} \<rightarrow> {S'. S' \<subseteq> dom f}. {x. x \<in> dom f \<and> (\<exists>y\<in>S. f $$ x = Some y)})"

definition image :: "('a, 'b) p_function \<Rightarrow> 'a set \<rightharpoondown> 'b set"
  where "image f = (\<lambda>S\<in>{S. S \<subseteq> dom f} \<rightarrow> {S'. S' \<subseteq> cod f}. {x. x \<in> cod f \<and> (\<exists>y\<in>S. f $$ y = Some x)})"

definition range :: "('a, 'b) p_function \<Rightarrow> 'b set" 
  where "range f = image f $ (dom f)"

definition n_dom :: "('a, 'b) p_function \<Rightarrow> 'a set" 
  where "n_dom f = preimage f $ (cod f)"


lemma app_intro[intro]: "(\<And>g. f = (\<lambda>x\<in>(dom f) \<rightarrow> (cod f). g x) \<Longrightarrow> P (g x)) \<Longrightarrow>  P (f $ x)"
  apply (clarsimp simp: quot_app_def)
  apply (rule someI2_ex[OF exists_fun])
  apply (blast)
  done


lemma safe_app_cong: "f = g \<Longrightarrow> f $$ x = g $$ x"
  by (clarsimp)


lemma app_intro'[intro]: "(\<And>g. (\<forall>x. (f $$ x) = (\<lambda>x\<in>(dom f) \<rightarrow> (cod f). g x) $$ x) \<Longrightarrow>  P (g x) )  \<Longrightarrow>  P (f $ x)"
  apply (clarsimp simp: quot_app_def)
  apply (rule someI2_ex[OF exists_fun])
  by force


lemma safe_app_iff[simp]: " ((\<lambda>x\<in>A. f x) $$ x) = (Some y) \<longleftrightarrow> (x \<in> A \<and> y = (f x))"
  apply (safe)
    apply (transfer, clarsimp split: if_splits)
   apply (transfer, clarsimp split: if_splits)
  by (simp add: restrict.abs_eq safe_app.abs_eq)


lemma safe_app_iff_rev[simp]: " (Some y) = ((\<lambda>x\<in>A. f x) $$ x)   \<longleftrightarrow> (x \<in> A \<and> y = (f x))"
  apply (safe)
    apply (transfer, clarsimp split: if_splits)
   apply (transfer, clarsimp split: if_splits)
  by (simp add: restrict.abs_eq safe_app.abs_eq)

lemma safe_app_iff'[simp]: "((\<lambda>x\<in>A \<rightarrow> B. f x) $$ x) = (Some y) \<longleftrightarrow> (x \<in> vimage f B \<inter> A \<and> (f x) = y) "
    apply (safe)
    apply (transfer, clarsimp split: if_splits)
    apply (transfer, clarsimp split: if_splits)
  apply (transfer, clarsimp split: if_splits)
  by (simp add: restrict.abs_eq safe_app.abs_eq)


lemma safe_app_iff'_rev[simp]: " (Some y) = ((\<lambda>x\<in>A \<rightarrow> B. f x) $$ x) \<longleftrightarrow> (x \<in> vimage f B \<inter> A \<and> (f x) = y) "
    apply (safe)
    apply (transfer, clarsimp split: if_splits)
    apply (transfer, clarsimp split: if_splits)
  apply (transfer, clarsimp split: if_splits)
  by (simp add: restrict.abs_eq safe_app.abs_eq)



lemma safe_app[simp]: "x \<in> vimage f B \<inter> A \<Longrightarrow> ((\<lambda>x\<in>A \<rightarrow> B. f x) $$ x) = (Some (f x)) "
    apply (safe)
  by (transfer, clarsimp split: if_splits)

lemma safe_app_iff''[simp]: " ((\<lambda>x!. f x) $$ x) = Some y \<longleftrightarrow>  y = (f x) "
  by (clarsimp, safe)


lemma cod_simp[simp]: "cod (\<lambda>x\<in>A \<rightarrow> B. f x) = B"
  by (transfer, clarsimp)

lemma dom_simp[simp]: "dom (\<lambda>x\<in>A \<rightarrow> B. f x) = (vimage f B \<inter> A)"
  by (transfer, blast)


lemma "x \<in> A \<Longrightarrow> (\<lambda>x\<in>A. f x) $ x = f x"
  by (rule app_intro', drule spec[where x=x], clarsimp)


lemma app_subst'[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow>  P (f x) \<Longrightarrow> P ((\<lambda>x\<in>A \<rightarrow> B. f x) $ x)"
  by (rule app_intro', drule spec[where x=x], clarsimp)


lemma app_subst[simp,trans]: "x \<in> A \<Longrightarrow> P (f x) \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $ x)"
  by (clarsimp)


lemma app_subst''[simp,trans]: "P (f x) \<Longrightarrow> P ((\<lambda>x!. f x) $ x)"
  by (clarsimp)

lemma app_iff'[simp]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> ((\<lambda>x\<in>A \<rightarrow> B. f x) $ x) =  (f x) "
  by (rule app_subst'; clarsimp)

lemma app_iff[simp]: "x \<in> A \<Longrightarrow> ((\<lambda>x\<in>A. f x) $ x) = (f x) "
  by (clarsimp)

lemma app_iff''[simp]: " ((\<lambda>x!. f x) $ x) =  (f x) "
  by (clarsimp)

lemma app_ssubst: "x \<in> A \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $ x) \<Longrightarrow> P (f x) "
  by (clarsimp)

lemma safe_app_subst[simp,trans]: "x \<in> A \<Longrightarrow> P (Some (f x)) \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $$ x) "
  by (clarsimp)

lemma safe_app_subst'[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow>  P (Some (f x)) \<Longrightarrow> P ((\<lambda>x\<in>A \<rightarrow> B. f x) $$ x)"
  by (clarsimp)

lemma safe_app_subst''[simp,trans]: " P (Some (f x)) \<Longrightarrow> P ((\<lambda>x!. f x) $$ x)"
  by (clarsimp)



lemma ndom_simp: " dom f = n_dom f"
  apply (clarsimp simp: n_dom_def preimage_def)
  apply (safe)
  apply (transfer)
  apply (clarsimp)
  done



lemma range_sub_cod[simp]: "range f \<subseteq> cod f"
  by (clarsimp simp: range_def image_def)

lemma "C \<subseteq> cod f \<Longrightarrow> preimage f $ C = S \<Longrightarrow> S \<subseteq> n_dom f "
  apply (clarsimp simp: n_dom_def preimage_def)
  by blast

lemma ext_restrict: " cod f = cod g  \<Longrightarrow> dom f = dom g \<Longrightarrow>
   (\<And>x.  f $$  x = g $$ x) \<Longrightarrow> f = g" 
  apply (transfer)
  apply (clarsimp)
  by (metis option.distinct(1) option.inject)


  

lemma app_determ: "f $$ x = Some y \<Longrightarrow> f $ x = y"
  by (rule app_intro', clarsimp)

lemma ndom_simp'[simp]: "n_dom (\<lambda>x\<in>A \<rightarrow> B. f x) = A \<inter> (vimage f B)"
  by (metis dom_simp inf.commute ndom_simp)

lemma n_dom_le_dom: "n_dom f \<subseteq> dom f"
  by (simp add: n_dom_def preimage_def)

lemma None_not_in_nat_dom:
 "f $$ x = None \<longleftrightarrow> x \<notin> n_dom f"
  apply (safe)
   apply (clarsimp simp: n_dom_def preimage_def)
  apply (clarsimp simp: n_dom_def preimage_def)
  apply (transfer)
  apply (clarsimp)
  apply (blast)
  done


definition add :: "nat \<rightharpoondown> nat \<rightharpoondown> nat" (* Addition on increasing pairs of natural numbers such that the first argument is less than 20 and the combination less than 50 *)
  where "add = (\<lambda>x\<in>{n. n \<le> 20}. \<lambda>y\<in>{n. (n :: nat) \<ge> x} \<rightarrow> {n. n \<le> 50}. x + y)"

lemma example: "(add $ 3) $ 5 = (add $ 2 $ 6)"
  by (unfold add_def, clarsimp)

lemma example': "(add $ 100) $ 5 = (add $ 99 $ 6)"
  apply (clarsimp simp: add_def)
  apply (subst app_iff) (* not in the domain *)
  oops

lemma example': "(add $ 5) $ 4 = (add $ 4 $ 5)"
  apply (clarsimp simp: add_def)
  apply (subst app_iff') (* not in the domain *)
  oops
 
lemma total: "a \<in> n_dom f \<Longrightarrow> f $ a \<in> (cod f)"
  apply (clarsimp simp: n_dom_def preimage_def)
  by (simp add: app_determ)


lemma total_r: "a \<in> n_dom f \<Longrightarrow> f $ a \<in> (range f)"
  apply (clarsimp simp: n_dom_def range_def preimage_def app_determ image_def)
  by (rule_tac x=a in bexI; clarsimp simp: app_determ)

hide_fact app_def

definition const :: "'a set \<Rightarrow> 'b set \<Rightarrow> 'a \<rightharpoondown> 'b \<rightharpoondown> 'a"
  where "const A B = (\<lambda>x\<in>A.\<lambda>y\<in>B \<rightarrow> {x}. x)" 

lemma const_is_const: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> const A B $ a $ b = a"
  by (clarsimp simp: const_def)

definition const_alt :: "'a set \<rightharpoondown> 'b set \<rightharpoondown> 'a \<rightharpoondown> 'b \<rightharpoondown> 'a" (* Unnecessary, but possible *)
  where "const_alt = (\<lambda>A!.\<lambda>B!. \<lambda>x\<in>A. \<lambda>y\<in>B \<rightarrow> {x}. x)" 

definition compose :: "('a \<rightharpoondown> 'b) \<rightharpoondown> ('b \<rightharpoondown> 'c) \<rightharpoondown> ('a \<rightharpoondown> 'c)"
  where "compose = (\<lambda>f!.\<lambda>g\<in>{g. cod f \<subseteq> dom g}. \<lambda>x\<in>(dom f) \<rightarrow> (cod g). g $ (f $ x))"  

definition extend ::  "('a \<rightharpoondown> 'b) \<Rightarrow> 'b set \<rightharpoondown> ('a \<rightharpoondown> 'b)"
  where "extend f = (\<lambda>S\<in>{S. S \<supseteq> cod f}. \<lambda>x\<in>dom f \<rightarrow> S. f $ x)"


lemma dom_extend: "cod f \<subseteq> S \<Longrightarrow> dom (extend f $ S) = dom f"
  apply (clarsimp simp: extend_def)
  apply (safe; clarsimp)
  by (simp add: ndom_simp subsetD total)

lemma cod_extend: "cod f \<subseteq> S \<Longrightarrow> cod (extend f $ S) =  S"
  by (clarsimp simp: extend_def)

definition rest ::  "('a \<rightharpoondown> 'b) \<Rightarrow> 'a set \<rightharpoondown> ('a \<rightharpoondown> 'b)" 
  where "rest f = (\<lambda>S\<in>{S. S \<subseteq> dom f}. \<lambda>x\<in>S \<rightarrow> cod f. f $ x)"


definition embed ::  "('a \<rightharpoondown> 'b) \<Rightarrow> 'a set \<rightharpoondown> ('a \<rightharpoondown> 'b)" 
  where "embed f = (\<lambda>S\<in>{S. S \<supseteq> dom f}. \<lambda>x\<in>S \<rightarrow> cod f. f $ x)"


lemma in_nat_dom_iff: "x \<in> n_dom f \<longleftrightarrow> (\<exists>y\<in>cod f. f $$ x = Some y)"
  by (metis None_not_in_nat_dom app_determ not_Some_eq total)


lemma in_range_iff: "y \<in> range f \<longleftrightarrow> (\<exists>x\<in>dom f. f $$ x = Some y)"
  apply (safe; clarsimp?)
  apply (clarsimp simp: range_def image_def)
  by (metis app_determ ndom_simp total_r)

lemma applyE[elim, trans]: "P (f $ x) \<Longrightarrow> (\<And>g . f = (g \<Ztypecolon> dom f \<rightarrow> cod f) \<Longrightarrow> P (g x) \<Longrightarrow>  Q ) \<Longrightarrow>  Q"
  apply (erule contrapos_pp)
  apply (rule app_intro, clarsimp)
  by blast

lemma f_is_app_f: "f = (\<lambda>x\<in>(dom f) \<rightarrow> (cod f). f $ x)"
  apply (rule ext_restrict; clarsimp?)
   apply (safe; clarsimp)
   apply (simp add: ndom_simp total)
  apply (case_tac "f $$ x"; simp)
   apply (rule sym, subst None_not_in_nat_dom)
   apply (simp add: ndom_simp total)
   apply (clarsimp simp: None_not_in_nat_dom )
  by (metis None_not_in_nat_dom app_determ ndom_simp option.discI total)

abbreviation rest_ap (infixl "|`"  110) where
            "rest_ap f S \<equiv> rest f $ S" 

lemma dom_rest: "S \<subseteq> dom f \<Longrightarrow> dom (rest f $ S) = S"
  apply (clarsimp simp: rest_def)
  by (simp add: Int_absorb1 in_mono ndom_simp subsetI total vimageI)

lemma cod_rest: "S \<subseteq> dom f \<Longrightarrow> cod (rest f $ S) = cod f"
  by (clarsimp simp: rest_def)

abbreviation "cmp f g \<equiv> (compose $ f) $ g "

notation cmp (infixl "\<cdot>" 55)

definition "composable f g \<longleftrightarrow> cod f \<subseteq> dom g"


lemma total'[simp, intro]: "x \<in> Function.dom f \<Longrightarrow> f $ x \<in> cod f"
  by (simp add: ndom_simp total)


lemma total_ind[simp, elim]: "x \<in> S \<Longrightarrow> S \<subseteq> dom f \<Longrightarrow> cod f \<subseteq> S' \<Longrightarrow> f $ x \<in> S'"
  by auto

lemma total_trans[trans]: " f $ x = y \<Longrightarrow> x \<in> S \<Longrightarrow>  S \<subseteq> dom f \<Longrightarrow> cod f \<subseteq> S' \<Longrightarrow> y \<in> S'"
  by auto


lemma dom_comp[simp]: "composable f g \<Longrightarrow> dom (f \<cdot> g) = dom f"
  apply (clarsimp simp: compose_def ndom_simp)
  apply (subst app_iff, clarsimp simp: composable_def)
  apply (simp add: in_mono ndom_simp)
  by (simp add: composable_def subset_antisym subset_iff total total_r)

lemma "ran f \<subseteq> Map.dom g \<Longrightarrow> Map.dom (map_comp g f) = Map.dom f"
  apply (safe)
   apply (meson map_comp_Some_iff)
  by (simp add: domD in_mono ranI)

lemma cod_cmp[simp]: "composable f g \<Longrightarrow> cod (f \<cdot> g) = cod g"
  apply (clarsimp simp: compose_def)
  apply (subst app_iff, clarsimp simp: composable_def)
  apply (simp add: in_mono ndom_simp)
  done


lemma safe_app_Some_iff: "f $$ x = Some y \<longleftrightarrow> x \<in> dom f \<and> y = f $ x"
  apply (safe)
    apply (metis None_not_in_nat_dom ndom_simp option.distinct(1))
   apply (clarsimp simp: app_determ)
  by (metis dom_simp f_is_app_f safe_app)

lemma range_lam[simp]: "range (\<lambda>x\<in>A \<rightarrow> B. f x) = f ` A \<inter> B"
  apply (clarsimp simp: range_def image_def, safe; clarsimp)
  apply (blast)
  done

lemma range_comp[simp]: "composable f g \<Longrightarrow> range (f \<cdot> g) = image g $ range f"
  apply (clarsimp simp: compose_def)
  apply (subst app_iff, clarsimp simp: composable_def)
  apply (clarsimp simp: range_def image_def, safe)
    apply (clarsimp)
    apply (subst app_iff'; clarsimp)
     apply (meson composable_def in_range_iff subset_iff)
    apply (rule_tac x="f $ y" in exI, clarsimp)
  apply (meson composable_def in_mono safe_app_Some_iff total')
   apply (subst (asm) app_iff'; clarsimp)
    apply (metis composable_def ndom_simp safe_app_Some_iff subset_iff total_r)
   apply (subst (asm) app_iff'; clarsimp)
    apply (metis composable_def ndom_simp safe_app_Some_iff subset_iff total_r)
 apply (clarsimp simp: safe_app_Some_iff)
  apply (rule_tac x=ya in bexI; clarsimp)
  done

lemma range_le[simp]: "composable f g \<Longrightarrow> range (f \<cdot> g) \<subseteq> range g"
  apply (clarsimp simp: compose_def)
  apply (subst (asm) app_iff, clarsimp simp: composable_def)
  apply (clarsimp simp: range_def image_def)
  by (meson composable_def in_mono safe_app_Some_iff total')




lemma comp_apply[simp]: "x \<in> dom f \<Longrightarrow> cod f \<subseteq> dom g \<Longrightarrow>   f \<cdot> g $ x = g $ ( f $ x)"
  apply (clarsimp simp: compose_def)
  apply (subst app_iff') 
    apply (clarsimp)
    apply (simp add: ndom_simp subset_iff total)
  apply (simp add: total total_r)
  apply (clarsimp)
  done

lemma comp_apply'[simp]: "x \<in> dom f \<Longrightarrow> composable f g \<Longrightarrow>   f \<cdot> g $ x = g $ ( f $ x)"
  apply (clarsimp simp: compose_def composable_def comp_apply)
  apply (subst app_iff') 
    apply (clarsimp)
    apply (simp add: ndom_simp subset_iff total)
  apply (simp add: total total_r)
  apply (clarsimp)
  done


lemma comp_apply_simp[simp]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> composable (\<lambda>x\<in>A \<rightarrow> B. f x) g \<Longrightarrow>  (\<lambda>x\<in>A \<rightarrow> B. f x) \<cdot> g $ x = g $ ( f x)"
  apply (clarsimp simp: compose_def composable_def ndom_simp)
  apply (subst app_iff') back
    apply (clarsimp)
   apply (clarsimp)
  apply (simp add: subset_eq total)
  apply (clarsimp)
  done


lemma comp_safe_apply[simp]: "composable f g \<Longrightarrow>  (f \<cdot> g $$ x) = Some y \<longleftrightarrow>  (x \<in> dom f \<and> g $$ (f $ x) = Some y)" 
  apply (clarsimp simp: compose_def range_def image_def composable_def ndom_simp)
  apply (safe; (clarsimp simp: ndom_simp)?)
  apply (clarsimp simp: in_nat_dom_iff)
  apply (smt (verit, ccfv_threshold) in_mono mem_Collect_eq ndom_simp safe_app_Some_iff)
  by (simp add: safe_app_Some_iff)
  by (simp add: app_determ)


lemma extensionality: " cod f = cod g  \<Longrightarrow> dom f = dom g \<Longrightarrow>
   (\<And>x.  x \<in> dom f \<Longrightarrow> f $ x = g $ x) \<Longrightarrow> f = g" 
  apply (rule ext_restrict; clarsimp?)
  apply (case_tac "f $$ x", clarsimp)
   apply (metis None_not_in_nat_dom ndom_simp)
  by (metis safe_app_Some_iff)

lemma composable_iff_l[simp]: "composable (\<lambda>x\<in>A \<rightarrow> B. f x) g \<longleftrightarrow> B \<subseteq> (dom g) "
  by (clarsimp simp: composable_def ndom_simp)


lemma composable_iff_r[simp]: "composable g (\<lambda>x\<in>A \<rightarrow> B. f x) \<longleftrightarrow> cod g \<subseteq> A \<inter> (vimage f B) "
  by (clarsimp simp: composable_def ndom_simp)

lemma composable_total[simp]: "composable (\<lambda>x\<in>A \<rightarrow> B. f x) (\<lambda>x\<in>C \<rightarrow> D. g x) \<longleftrightarrow>  B \<subseteq> (C \<inter> (vimage g D)) "
  by (clarsimp simp: composable_def ndom_simp)


lemma composableI[intro, simp]: "cod f \<subseteq> dom g \<Longrightarrow> composable f g"
  by (clarsimp simp: composable_def ndom_simp)

lemma composable_complI[intro, simp]: "composable f g \<Longrightarrow>  composable g h \<Longrightarrow> composable (f \<cdot> g) h"
  apply (rule composableI)
  by (clarsimp simp: composable_def)


lemma composable_comprI[intro, simp]: "composable f g \<Longrightarrow>  composable g h \<Longrightarrow> composable f (g \<cdot> h)"
  apply (rule composableI)
  by (simp add: composable_def)


definition "swap S = (\<lambda>x\<in>S \<rightarrow> (converse S). (snd x, fst x))"


lemma swap_vimage_converse[simp]: "(\<lambda>x. (snd x, fst x)) -`  S = converse S"
  by (safe; clarsimp)

lemma dom_swap[simp]: "dom (swap S) = S" by (clarsimp simp: swap_def) 

lemma cod_swap[simp]: "cod (swap S) = converse S" by (clarsimp simp: swap_def) 

lemma swap_iff[simp]: "x \<in> S \<Longrightarrow> swap S $ x = (a, b) \<longleftrightarrow> x = (b, a)"
  by (metis (no_types, lifting) app_iff' converseI prod.collapse swap_def swap_simp)


lemma swap_iff'[simp]: "x \<in> S \<Longrightarrow> (a, b) = swap S $ x   \<longleftrightarrow> x = (b, a)"
  by (metis (no_types, lifting) app_iff' converseI prod.collapse swap_def swap_simp)



definition compose_alt :: "('a \<rightharpoondown> 'b) \<rightharpoondown> ('b \<rightharpoondown> 'c) \<rightharpoondown> ('a \<rightharpoondown> 'c option)"
  where "compose_alt = (\<lambda>f!.\<lambda>g\<in>{g. range f \<subseteq> n_dom g}. \<lambda>x\<in>(dom f) \<rightarrow> (Some ` (cod g)). do {y <- f $$ x; g $$ y})"  



end