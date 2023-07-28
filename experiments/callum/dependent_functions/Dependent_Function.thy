theory Dependent_Function
imports Main "HOL-Library.Monad_Syntax" "HOL-Eisbach.Eisbach_Tools"
begin


definition "dep_vimage f B \<equiv> {x. f x \<in> B x}"


lemma dep_vimage_eq[simp]: "x \<in> dep_vimage f B \<longleftrightarrow> f x \<in> B x"
  by (clarsimp simp: dep_vimage_def)



fun exten_equal where
 "exten_equal (A, f, i, B) (A', g, j, B') =
  (B = B' \<and> (let 
      univ    = A \<inter> vimage i (Pow B);
      univ'   = A' \<inter> vimage j (Pow B');
      domain  = univ \<inter> dep_vimage f i;
      domain' = univ' \<inter> dep_vimage g j in 
     domain = domain' \<and> (\<forall>x\<in>(domain). f x = g x) \<and> (\<forall>x\<in>(domain). i x = j x)))   "


quotient_type ('a, 'b) p_function = "('a set \<times> ('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b set) \<times> 'b set)" / exten_equal
  apply (rule equivpI)
    apply (rule reflpI, clarsimp simp: )
   apply (rule sympI )
   apply (clarsimp simp: )
  apply metis
  apply (clarsimp simp add: exten_equal.elims(2) transp_def)  
  by metis

type_notation p_function (infixr "\<rightharpoondown>" 0)


lift_definition 
     restrict :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) p_function"
         is "\<lambda>f S i S'. (S, f, i,  S')"
  done


(*
lift_definition app :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b" is 
                      "\<lambda>(A, f, B) x. if x \<in> (A \<inter> dep_vimage f B) then f x else undefined"
  apply (rule ext; clarsimp simp:)
  by (metis Int_iff dep_vimage_eq)
*)



lift_definition dom :: "('a, 'b) p_function \<Rightarrow> 'a set" is 
                      "\<lambda>(A, f, i, B). (A \<inter> vimage i (Pow B)) \<inter> (dep_vimage f i) " 
  by (clarsimp simp: Let_unfold)


lift_definition safe_app :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b option " is 
                      "\<lambda>(A, f, i,  B) x. if x \<in> (A \<inter> vimage i (Pow B)) \<inter> (dep_vimage f i) then Some (f x) else None"
  apply (rule ext; clarsimp simp: )
  apply (safe)
        apply (smt (verit, ccfv_threshold) IntI Pow_iff dep_vimage_eq subset_iff vimageI2)
      apply (smt (verit, ccfv_threshold) IntI Pow_iff dep_vimage_eq subset_iff vimageI2)
      apply (metis (mono_tags, lifting) Int_iff PowI dep_vimage_eq vimageI)
  apply (metis (mono_tags, lifting) Int_iff PowI dep_vimage_eq vimageI)

    apply (smt (verit, ccfv_threshold) IntI Pow_iff dep_vimage_eq subset_iff vimageI2)
  apply (metis (mono_tags, lifting) Int_iff PowI dep_vimage_eq vimageI)

  by (smt (verit, ccfv_threshold) IntI Pow_iff dep_vimage_eq subset_iff vimageI2)



abbreviation (input) "total_f f == (restrict f UNIV (\<lambda>x. {f x}) UNIV)"

abbreviation (input) "on_domain_f f A == (restrict f A (\<lambda>x. {f x}) UNIV)"

abbreviation (input) "non_dependent f A B == (restrict f A (\<lambda>x. {f x}) B)"



lift_definition cod :: "('a, 'b) p_function \<Rightarrow> ('a \<times> 'b) set " is 
                      "\<lambda>(A, f, i, B). Sigma ((A \<inter> vimage i (Pow B)) \<inter> (dep_vimage f i)) i" 
  apply (clarsimp simp: Let_unfold)
  by (safe; clarsimp)


notation safe_app (infixl "$$" 54)

lift_definition codomain :: "('a, 'b) p_function \<Rightarrow> ('b set)" is 
  "\<lambda>(A, f, i, B).  B"
  by (clarsimp)

lemma exten_equalI: "dom f = dom g \<Longrightarrow> codomain f = codomain g \<Longrightarrow>  (\<And>x. f $$ x = g $$ x) \<Longrightarrow> cod f = cod g \<Longrightarrow> f = g" 
  apply (transfer; clarsimp simp: Let_unfold)
  apply (safe)
    apply (metis dep_vimage_eq option.distinct(1) option.inject)
   apply (atomize, erule_tac x=x in allE)
   apply (clarsimp split: if_splits)
   apply (clarsimp simp: set_eq_iff)
   apply blast
  apply blast
  done
  

(* lift_definition dom :: "('a, 'b) p_function \<Rightarrow> 'a set" is "\<lambda>(A, f, B). A"
  by (clarsimp)
*)

(*
lift_definition func :: "('a, 'b) p_function \<Rightarrow> 'a \<Rightarrow> 'b" is 
                      "\<lambda>(A, f, B) x. if x \<in> (A \<inter> vimage f B) then f x else undefined"
  apply (rule ext; clarsimp simp:)
  by blast
*)




(* definition n_dom :: "('a, 'b) p_function \<Rightarrow> 'a set" 
  where "n_dom f =  dom f \<inter> (inv_image (f) (cod f))"
*)


(* definition range :: "('a, 'b) p_function \<Rightarrow> 'b set"
  where "range f = {x. \<exists>y\<in>dom f. f $$ y = Some x \<and> x \<in> cod f}"
*)


(* definition n_dom :: "('a, 'b) p_function \<Rightarrow> 'a set"
  where "n_dom f = {x. x \<in> dom f \<and> (\<exists>y. f $$ x = Some y \<and> y \<in> cod f)}" *)




syntax
  "_Pi" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('b set)  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<Pi>_\<in>_ \<rightarrow> _ ./ _)" [0,0,3] 3)
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('b set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_ \<rightarrow> _ ./ _)" [0,0,3] 3)
  "_lam_dom" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
  "_lam_free" :: "pttrn \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_!./ _)" [0,3] 3)



translations 
 "\<lambda>x!. f" \<rightleftharpoons> "CONST total_f (\<lambda>x. f ) "
 "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST on_domain_f (\<lambda>x. f) A"
 "\<lambda>x\<in>A \<rightarrow> B. f" \<rightleftharpoons> "CONST non_dependent (\<lambda>x. f) A B"
 "\<Pi> x\<in>A \<rightarrow> i : B. f" \<rightharpoonup> "CONST restrict (\<lambda>x. f) A (\<lambda>x. i) B"
 
definition "cod_of f x = cod f `` {x}"

lemma exists_fun: "\<exists>g. f = (\<Pi> x\<in>(dom f) \<rightarrow> cod_of f x : codomain f . g x)" 
  apply (clarsimp simp: cod_of_def)
  apply (transfer)
  apply (rule_tac x= "(\<lambda>(A, f, i, x). f)  ( f)" in exI)
  apply (clarsimp simp: Let_unfold, safe; clarsimp?)
  by blast

definition "quot_app f \<equiv> (SOME g. f = (\<Pi> x\<in>(dom f) \<rightarrow> cod_of f x : codomain f . g x))"

notation quot_app (infixl "$" 54)

notation restrict ("\<guillemotleft>_\<guillemotright> : _ \<rightarrow> _ : _" 1)  

definition preimage :: "('a, 'b) p_function \<Rightarrow> 'b set \<rightharpoondown> 'a set"
  where "preimage f = (\<lambda>S\<in>{S. S \<subseteq> codomain f } \<rightarrow> {S'. S' \<subseteq> dom f}. {x. x \<in> dom f \<and> (\<exists>y\<in>S. f $$ x = Some y)})"

definition image :: "('a, 'b) p_function \<Rightarrow> 'a set \<rightharpoondown> 'b set"
  where "image f = (\<lambda>S\<in>{S. S \<subseteq> dom f} \<rightarrow> {S'. S' \<subseteq> codomain f}. {x. x \<in> codomain f \<and> (\<exists>y\<in>S. f $$ y = Some x)})"

definition range :: "('a, 'b) p_function \<Rightarrow> 'b set" 
  where "range f = image f $ (dom f)"

definition n_dom :: "('a, 'b) p_function \<Rightarrow> 'a set" 
  where "n_dom f = preimage f $ (codomain f)"


lemma app_intro: "(\<And>g. f = (\<Pi> x\<in>(dom f) \<rightarrow> cod_of f x : codomain f . g x) \<Longrightarrow> P (g x)) \<Longrightarrow>  P (f $ x)"
  apply (clarsimp simp: quot_app_def)
  apply (rule someI2_ex[OF exists_fun])
  apply (blast)
  done

lemma app_intro_2: "(\<And>g. f = (\<Pi> x\<in>(dom f) \<rightarrow> cod_of f x : codomain f . g x) \<Longrightarrow> P (\<Pi> x\<in>(dom f) \<rightarrow> cod_of f x : codomain f . g x)) \<Longrightarrow>  P f"
  apply (clarsimp simp: quot_app_def)
  apply (rule someI2_ex[OF exists_fun])
  apply (blast)
  done


lemma safe_app_cong: "f = g \<Longrightarrow> f $$ x = g $$ x"
  by (clarsimp)


lemma app_intro': "(\<And>g. (\<forall>x. (f $$ x) = (\<Pi> x\<in>(dom f) \<rightarrow> cod_of f x : codomain f . g x) $$ x) \<Longrightarrow>  P (g x) )  \<Longrightarrow>  P (f $ x)"
  apply (clarsimp simp: quot_app_def)
  apply (rule someI2_ex[OF exists_fun])
  by force

lemma safe_app_iff_rev[simp]: " (Some (y)) = ((\<Pi> x\<in>A \<rightarrow> i x : B . f x) $$ x) \<longleftrightarrow> x \<in> (A \<inter> vimage i (Pow B) \<inter> (dep_vimage f i)) \<and> (f x) = y "
    apply (safe)
    apply (transfer, clarsimp split: if_splits)
    apply (transfer, clarsimp split: if_splits)
    apply (transfer, clarsimp split: if_splits)
  apply (transfer, clarsimp split: if_splits)
  by (simp add: restrict.abs_eq safe_app.abs_eq)

lemma safe_app_iff_none[simp]: " (None) = ((\<Pi> x\<in>A \<rightarrow> i x : B . f x) $$ x) \<longleftrightarrow> x \<notin>  (A \<inter> vimage i (Pow B) \<inter> (dep_vimage f i)) "
    apply (safe)
    apply (transfer, clarsimp split: if_splits)
    apply (transfer, clarsimp split: if_splits)
    apply (transfer, clarsimp split: if_splits)
  by (transfer, clarsimp split: if_splits)


lemma safe_app_iff: " ((\<Pi> x\<in>A \<rightarrow> i x : B . f x) $$ x) = (Some (y))  \<longleftrightarrow> x \<in> (A \<inter> vimage i (Pow B) \<inter> (dep_vimage f i)) \<and> (f x) = y "
  by (intro iffI, drule sym, clarsimp, rule sym, clarsimp)


lemma safe_app_iff_total[simp]: " ((\<lambda>x\<in>A. f x) $$ x) = (Some y) \<longleftrightarrow> (x \<in> A \<and> y = (f x))"
  by (subst safe_app_iff, clarsimp, blast)


lemma safe_app_iff_total_rev[simp]: " (Some y) = ((\<lambda>x\<in>A. f x) $$ x)   \<longleftrightarrow> (x \<in> A \<and> y = (f x))"
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

lemma dep_vimage_vimage[simp]: "dep_vimage f (\<lambda>x. B) = vimage f B"
  by (safe; clarsimp simp: dep_vimage_def)

lemma cod_simp[simp]: "cod (\<Pi> x\<in>A \<rightarrow> i x : B. f x) = Sigma ((A \<inter> vimage i (Pow B)) \<inter> (dep_vimage f i)) i"
  by (transfer, clarsimp)

lemma dom_simp[simp]: "dom (\<Pi> x\<in>A \<rightarrow> i x : B. f x) = (A \<inter> vimage i (Pow B)) \<inter> (dep_vimage f i)"
  by (transfer, clarsimp)

lemma app_subst'[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> P (f x) \<Longrightarrow> P ((\<lambda>x\<in>A \<rightarrow> B. f x) $ x)"
  by (rule app_intro', drule spec[where x=x], clarsimp simp: cod_of_def)

lemma app_subst[simp,trans]: "x \<in> A \<Longrightarrow> P (f x) \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $ x)"
  by (clarsimp)

lemma app_subst''[simp,trans]: "P (f x) \<Longrightarrow> P ((\<lambda>x!. f x) $ x)"
  by (clarsimp)

term "restrict f A i B" 

lemma codomain_simp[simp]:"codomain (\<guillemotleft>f\<guillemotright> : A \<rightarrow> i : B) = B"
  by (transfer, clarsimp)

lemma app_iff[simp]: "x \<in> A \<Longrightarrow> f x \<in> i x \<Longrightarrow> i x \<subseteq> B \<Longrightarrow> ((\<Pi> x\<in>A \<rightarrow> i x : B . f x) $ x) =  (f x) "
  apply (rule app_intro', clarsimp?)
  apply (erule_tac x=x in allE)
  apply (case_tac "(\<guillemotleft>f\<guillemotright> : A \<rightarrow> i : B) $$ x"; clarsimp)
  apply (clarsimp simp: cod_of_def)
   apply (metis IntI PowI dep_vimage_eq safe_app_iff_none vimageI)
  apply (clarsimp simp: cod_of_def)
  by (simp add: safe_app_iff)

lemma app_iff'[simp]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> ((\<lambda>x\<in>A \<rightarrow> B . f x) $ x) = (f x)"
  by (clarsimp)

lemma app_iff_simple[simp]: "x \<in> A \<Longrightarrow> ((\<lambda>x\<in>A. f x) $ x) = (f x) "
  by (clarsimp)

lemma app_iff''[simp]: " ((\<lambda>x!. f x) $ x) =  (f x) "
  by (clarsimp)

lemma app_ssubst: "x \<in> A \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $ x) \<Longrightarrow> P (f x) "
  by (clarsimp)

lemma safe_app_subst[simp,trans]: "x \<in> A \<Longrightarrow> P (Some (f x)) \<Longrightarrow> P ((\<lambda>x\<in>A. f x) $$ x) "
  by (clarsimp)

lemma safe_app_subst'[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow>  P (Some (f x)) \<Longrightarrow> P ((\<lambda>x\<in>A \<rightarrow> B. f x) $$ x)"
  by (clarsimp)


lemma safe_app_subst_full[simp,trans]: "x \<in> A \<Longrightarrow> f x \<in> i x \<Longrightarrow> i x \<subseteq> B \<Longrightarrow>  P (Some (f x)) \<Longrightarrow> P ((\<Pi> x\<in>A \<rightarrow> i x : B . f x) $$ x)"
  by (transfer, clarsimp)

lemma safe_app_subst''[simp,trans]: " P (Some (f x)) \<Longrightarrow> P ((\<lambda>x!. f x) $$ x)"
  by (clarsimp)

lemma safe_app_app_iff: "x \<in> Dependent_Function.dom f \<Longrightarrow> f $$ x = Some y \<longleftrightarrow> f $ x = y"
   apply (rule app_intro')
   apply (erule_tac x=x in allE, clarsimp)
  apply (metis dom_simp exists_fun safe_app_iff_rev)
  done

lemma in_dom_in_codomain[simp]: "x \<in> Dependent_Function.dom f \<Longrightarrow> f $ x \<in> codomain f"
  apply (rule app_intro)
 apply (clarsimp simp: cod_of_def)
   apply (transfer)
  apply (clarsimp)
   apply (smt (verit) IntI PowI dep_vimage_eq subset_iff vimageI)
  done


lemma ndom_simp: " dom f = n_dom f"
  apply (clarsimp simp: n_dom_def preimage_def, safe)
  by (subst safe_app_app_iff; fastforce simp: in_dom_in_codomain)


lemma range_sub_cod[simp]: "range f \<subseteq> codomain f"
  by (clarsimp simp: range_def image_def)

lemma "C \<subseteq> codomain f \<Longrightarrow> preimage f $ C = S \<Longrightarrow> S \<subseteq> n_dom f "
  apply (clarsimp simp: n_dom_def preimage_def)
  by blast


lemma app_determ: "f $$ x = Some y \<Longrightarrow> f $ x = y"
  apply (rule app_intro', clarsimp)
  apply (erule_tac x=x in allE, clarsimp)
  by (simp add: safe_app_iff)

lemma ndom_simp'[simp]: "dom (\<lambda>x\<in>A \<rightarrow> B. f x) = A \<inter> (vimage f B)"
  apply (clarsimp)
  by (safe; clarsimp)

lemma n_dom_le_dom: "n_dom f \<subseteq> dom f"
  by (simp add: n_dom_def preimage_def)

lemma None_not_in_nat_dom:
 "f $$ x = None \<longleftrightarrow> x \<notin> dom f"
  apply (safe, simp add: ndom_simp)
   apply (clarsimp simp: n_dom_def preimage_def)
  apply (transfer)
   apply (clarsimp)
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
 
lemma total[simp]: "a \<in> dom f \<Longrightarrow> f $ a \<in> (cod_of f a)"
  apply (clarsimp simp: cod_of_def)
  by (metis Image_singleton_iff Int_iff cod_of_def dep_vimage_eq exists_fun safe_app_app_iff safe_app_iff_rev)



lemma total_r[simp]: "a \<in> dom f \<Longrightarrow> f $ a \<in> (range f)"
  apply (subst (asm) ndom_simp)
  apply (clarsimp simp: n_dom_def range_def preimage_def app_determ image_def)
  by (rule_tac x=a in bexI; clarsimp simp: app_determ)

(* hide_fact app_def *)

definition const :: "'a set \<Rightarrow> 'b set \<Rightarrow> 'a \<rightharpoondown> 'b \<rightharpoondown> 'a"
  where "const A B = (\<lambda>x\<in>A.\<lambda>y\<in>B \<rightarrow> {x}. x)" 

lemma const_is_const: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> const A B $ a $ b = a"
  by (clarsimp simp: const_def)

definition const_alt :: "'a set \<rightharpoondown> 'b set \<rightharpoondown> 'a \<rightharpoondown> 'b \<rightharpoondown> 'a" (* Unnecessary, but possible *)
  where "const_alt = (\<lambda>A!.\<lambda>B!. \<lambda>x\<in>A. \<lambda>y\<in>B \<rightarrow> {x}. x)" 


definition compose :: "('a \<rightharpoondown> 'b) \<rightharpoondown> ('b \<rightharpoondown> 'c) \<rightharpoondown> ('a \<rightharpoondown> 'c)"
  where "compose = (\<lambda>f!.\<lambda>g\<in>{g. codomain f \<subseteq> dom g}. \<Pi> x\<in>(dom f) \<rightarrow> cod g `` (cod_of f x) : (codomain g). g $ (f $ x))"  

term "codomain g"

(* definition extend ::  "('a \<rightharpoondown> 'b) \<Rightarrow> 'b set \<rightharpoondown> ('a \<rightharpoondown> 'b)"
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

*)
lemma in_nat_dom_iff: "x \<in> dom f \<longleftrightarrow> (\<exists>(x',y)\<in>cod f. x = x' \<and> f $$ x = Some y)"
  apply (safe)
  apply (frule total, clarsimp simp: cod_of_def)
   apply (smt (verit) None_not_in_nat_dom app_determ case_prodI not_Some_eq)
  apply (clarsimp simp: ndom_simp)
  by (metis None_not_in_nat_dom ndom_simp option.distinct(1))


lemma cod_iff: "x \<in> cod f \<longleftrightarrow> fst x \<in> dom f \<and> (\<exists>y. f $ y \<in> cod_of f (fst x) \<and> snd x \<in> cod_of f (fst x))"
  apply (safe)
    apply (metis cod_simp dom_simp exists_fun mem_Sigma_iff prod.collapse)
   apply (clarsimp simp: cod_of_def) 
   apply (rule app_intro[where f=f])
   apply (metis cod_simp dom_simp exists_fun mem_Sigma_iff prod.collapse total)
  apply (clarsimp simp: cod_of_def)
  done
  


lemma in_range_iff: "y \<in> range f \<longleftrightarrow> (\<exists>x\<in>dom f. f $$ x = Some y)"
  apply (safe; clarsimp?)
  apply (clarsimp simp: range_def image_def)
  by (metis app_determ ndom_simp total_r)

(* lemma applyE[elim, trans]: "P (f $ x) \<Longrightarrow> (\<And>g . f = (g \<Ztypecolon> dom f \<rightarrow> cod_of f) \<Longrightarrow> P (g x) \<Longrightarrow>  Q ) \<Longrightarrow>  Q"
  apply (erule contrapos_pp)
  apply (rule app_intro, clarsimp)
  by blast *)

lemma cod_of_iff: "f $ a \<in> cod_of f a \<longleftrightarrow> a \<in> dom f \<and> (a, f $ a) \<in> cod f"
  apply (safe; clarsimp simp: cod_of_def)
  by (metis cod_simp dom_simp exists_fun mem_Sigma_iff)

lemma dom_cod_of_codomain: 
 "x \<in> dom f \<Longrightarrow> y \<in> cod_of f x \<Longrightarrow> y \<in> codomain f"
  apply (clarsimp simp: cod_of_def)
  apply (transfer, clarsimp)
  by blast

lemma f_is_app_f: "f = (\<Pi> x\<in>(dom f) \<rightarrow> (cod_of f x) : codomain f. f $ x)"
  apply (rule exten_equalI; clarsimp?)
    apply (safe; clarsimp simp: dom_cod_of_codomain)
   apply (case_tac "f $$ x"; clarsimp)
    apply (simp add: None_not_in_nat_dom)
   apply (metis None_not_in_nat_dom app_determ 
                dom_cod_of_codomain option.distinct(1) subsetI total)
  
  apply (safe; clarsimp simp: cod_iff)
   apply (meson dom_cod_of_codomain)
  apply (rule_tac x=a in exI)
  by (simp)
 

(*
abbreviation rest_ap (infixl "|`"  110) where
            "rest_ap f S \<equiv> rest f $ S" 

lemma dom_rest: "S \<subseteq> dom f \<Longrightarrow> dom (rest f $ S) = S"
  apply (clarsimp simp: rest_def)
  by (simp add: Int_absorb1 in_mono ndom_simp subsetI total vimageI)

lemma cod_rest: "S \<subseteq> dom f \<Longrightarrow> cod (rest f $ S) = cod f"
  by (clarsimp simp: rest_def)

*)

abbreviation "cmp f g \<equiv> (compose $ f) $ g "

notation cmp (infixl "\<cdot>" 55)

definition "composable f g \<longleftrightarrow> codomain f \<subseteq> dom g"


lemma total'[simp, intro]: "x \<in> dom f \<Longrightarrow> f $ x \<in> cod_of f x"
  by (simp add: ndom_simp total)


lemma total_ind[simp, elim]: "x \<in> S \<Longrightarrow> S \<subseteq> dom f \<Longrightarrow> cod_of f x \<subseteq> S' \<Longrightarrow> f $ x \<in> S'"
  by auto

lemma total_trans[trans]: " f $ x = y \<Longrightarrow> x \<in> S \<Longrightarrow>  S \<subseteq> dom f \<Longrightarrow> cod_of f x \<subseteq> S' \<Longrightarrow> y \<in> S'"
  by auto


lemma dom_comp[simp]: "composable f g \<Longrightarrow> dom (f \<cdot> g) = dom f"
  apply (clarsimp simp: compose_def )
  apply (subst app_iff, clarsimp simp: composable_def)
  apply (clarsimp simp: composable_def codomain_def)
   apply (safe; clarsimp )
  apply (clarsimp)
  apply (safe)
   apply (clarsimp simp: cod_of_def)
   apply (metis cod_iff dom_cod_of_codomain snd_eqD)
  apply (clarsimp simp: cod_of_def Image_iff)
  apply (simp add: composable_def  subsetD  Bex_def)
  thm Image_singleton_iff
  by (meson Image_singleton_iff cod_of_iff in_dom_in_codomain subsetD total)


lemma "ran f \<subseteq> Map.dom g \<Longrightarrow> Map.dom (map_comp g f) = Map.dom f"
  apply (safe)
   apply (meson map_comp_Some_iff)
  by (simp add: domD in_mono ranI)

lemma cod_cmp[simp]: "composable f g \<Longrightarrow> codomain (f \<cdot> g) = codomain g" 
  apply (clarsimp simp: compose_def)
  apply (subst app_iff, clarsimp simp: composable_def )
  apply (clarsimp simp: cod_of_def composable_def codomain_def)
  apply (clarsimp simp: cod_of_def composable_def ) 
  apply (simp add: in_mono ndom_simp)
  done


lemma safe_app_Some_iff: "f $$ x = Some y \<longleftrightarrow> x \<in> dom f \<and> y = f $ x"
  apply (safe)
    apply (metis None_not_in_nat_dom ndom_simp option.distinct(1))
   apply (clarsimp simp: app_determ)
  by (simp add: safe_app_app_iff)

lemma range_lam[simp]: "range (\<lambda>x\<in>A \<rightarrow> B. f x) = f ` A \<inter> B"
  apply (clarsimp simp: range_def image_def)
  apply (subst app_iff; clarsimp?)
   apply (safe; clarsimp?)
  apply (safe; clarsimp)
  using PowI singletonD by fastforce


lemma range_comp[simp]: "composable f g \<Longrightarrow> range (f \<cdot> g) = image g $ range f"
  apply (clarsimp simp: compose_def)
  apply (subst app_iff, clarsimp simp: composable_def)
  apply (clarsimp simp: range_def image_def, safe)
    apply (clarsimp simp: image_def range_def)
    apply (clarsimp simp: image_def range_def)

    apply (subst app_iff'; clarsimp)
    apply (meson composable_def in_range_iff subset_iff)
   apply (subst (asm) app_iff'; clarsimp)
  apply (safe; clarsimp?)
  apply (simp add: composable_def safe_app_app_iff subsetD)

    apply (rule_tac x="(f $ y)" in exI; clarsimp)
   apply (meson composable_def in_mono safe_app_Some_iff total')
   apply (simp add: composable_def safe_app_app_iff subsetD)
   apply (simp add: safe_app_iff)
  apply (clarsimp simp: range_def image_def)
  apply (subst app_iff; clarsimp?)
   apply (subst (asm) app_iff; clarsimp)
    apply (simp add: composable_def subsetD)
   apply fastforce
  apply (simp add: composable_def safe_app_app_iff subsetD)
  apply (subst (asm) app_iff; clarsimp)
   apply (fastforce)
  apply (simp add: composable_def safe_app_app_iff subsetD)
  apply (clarsimp)
  apply (rule_tac x=ya in bexI)
  apply blast
  apply (safe; clarsimp simp: cod_of_def)
   apply (metis cod_iff dom_cod_of_codomain snd_eqD)
  apply (clarsimp simp: Image_iff Bex_def)
  by (meson cod_of_iff in_dom_in_codomain subset_eq total')



lemma range_le[simp]: "composable f g \<Longrightarrow> range (f \<cdot> g) \<subseteq> range g"
  apply (subst range_comp, clarsimp)
  apply (clarsimp simp: range_def image_def)+
  apply (subst (asm) app_iff'; clarsimp)
  apply (simp add: composable_def subsetD)
  by (meson composable_def in_dom_in_codomain safe_app_Some_iff subsetD)




lemma comp_apply[simp]: "x \<in> dom f \<Longrightarrow> codomain f \<subseteq> dom g \<Longrightarrow>   f \<cdot> g $ x = g $ ( f $ x)"
  apply (clarsimp simp: compose_def)
  apply (subst app_iff; clarsimp?) 
   apply (simp add:  subset_iff )
   apply (meson Image_iff cod_of_iff in_dom_in_codomain total')
  by (metis cod_iff dom_cod_of_codomain snd_eqD)


lemma comp_apply'[simp]: "x \<in> dom f \<Longrightarrow> composable f g \<Longrightarrow>   f \<cdot> g $ x = g $ ( f $ x)"
  apply (clarsimp simp: compose_def composable_def )
  apply (subst app_iff; clarsimp?) 
   apply (simp add:  subset_iff )

   apply (meson Image_iff cod_of_iff in_dom_in_codomain total')
  by (metis cod_iff dom_cod_of_codomain snd_eqD)

lemma comp_apply_simp[simp]: "x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> composable (\<lambda>x\<in>A \<rightarrow> B. f x) g \<Longrightarrow>  (\<lambda>x\<in>A \<rightarrow> B. f x) \<cdot> g $ x = g $ ( f x)"
  apply (clarsimp simp: compose_def composable_def)
  apply (subst app_iff) back back
  apply (clarsimp)
    apply simp
  sorry
   apply (clarsimp)
   apply (metis dom_cod_of_codomain subsetD)
  apply (clarsimp)
  done



lemma comp_safe_apply[simp]: "composable f g \<Longrightarrow>  (f \<cdot> g $$ x) = Some y \<longleftrightarrow>  (x \<in> dom f \<and> g $$ (f $ x) = Some y)" 
  apply (clarsimp simp: compose_def range_def image_def composable_def )
  apply (safe; (clarsimp simp: safe_app_Some_iff )?)
  apply (meson in_dom_in_codomain safe_app_Some_iff subset_eq)
  apply (clarsimp simp: in_nat_dom_iff)
  apply (simp add: safe_app_Some_iff)
  sorry
  by (simp add: dom_cod_of_codomain subsetI)


lemma extensionality: " codomain f = codomain g  \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow>
   (\<And>x.  x \<in> dom f \<Longrightarrow> f $ x = g $ x) \<Longrightarrow> f = g" 
  apply (rule exten_equalI; clarsimp?)
  apply (case_tac "f $$ x", clarsimp)
   apply (metis None_not_in_nat_dom ndom_simp)
  by (metis safe_app_Some_iff)

lemma composable_iff_l[simp]: "composable (\<Pi> x\<in>A \<rightarrow> i x:  B. f x) g \<longleftrightarrow> B \<subseteq> (dom g) "
  by (clarsimp simp: composable_def ndom_simp)

thm dom_simp

lemma composable_iff_r[simp]: "composable g (\<Pi> x\<in>A \<rightarrow> i x:  B. f x) \<longleftrightarrow> codomain g \<subseteq> A \<inter> i -` Pow B \<inter> dep_vimage f i "
  by (clarsimp simp: composable_def )

lemma composable_total[simp]: "composable (\<Pi> x\<in>A \<rightarrow> i x:  B. f x) (\<Pi> x\<in>C \<rightarrow> j x:  D. g x) \<longleftrightarrow>  B \<subseteq> C \<inter> j -` Pow D \<inter> dep_vimage g j "
  by (clarsimp simp: composable_def )


lemma composableI[intro, simp]: "codomain f \<subseteq> dom g \<Longrightarrow> composable f g"
  by (clarsimp simp: composable_def )

lemma composable_complI[intro, simp]: "composable f g \<Longrightarrow>  composable g h \<Longrightarrow> composable (f \<cdot> g) h"
  apply (rule composableI)
  by (clarsimp simp: composable_def)


lemma composable_comprI[intro, simp]: "composable f g \<Longrightarrow>  composable g h \<Longrightarrow> composable f (g \<cdot> h)"
  apply (rule composableI)
  by (simp add: composable_def)


definition "swap S = (\<lambda>x\<in>S \<rightarrow> (converse S). (snd x, fst x))"


lemma swap_vimage_converse[simp]: "(\<lambda>x. (snd x, fst x)) -`  S = converse S"
  by (safe; clarsimp)

lemma dep_vimage_id[simp]: "dep_vimage (\<lambda>y. f y) (\<lambda>y. {f y}) = UNIV"
  by (safe; clarsimp)

lemma vimage_pow[simp]: "f -` Pow x = {y. f y \<subseteq> x}"
  apply (safe; clarsimp)
  done

lemma Id_sigma[simp]: "(SIGMA x:S. {x}) = Id_on S"
  by (safe; clarsimp)

lemma dom_swap[simp]: "dom (swap S) = S" by (clarsimp simp: swap_def) 

lemma cod_swap[simp]: "codomain (swap S) = converse S" by (clarsimp simp: swap_def) 

lemma swap_iff[simp]: "x \<in> S \<Longrightarrow> swap S $ x = (a, b) \<longleftrightarrow> x = (b, a)"
  by (clarsimp simp: swap_def, fastforce)


lemma swap_iff'[simp]: "x \<in> S \<Longrightarrow> (a, b) = swap S $ x   \<longleftrightarrow> x = (b, a)"
  by (clarsimp simp: swap_def, fastforce)



(*

definition compose_alt :: "('a \<rightharpoondown> 'b) \<rightharpoondown> ('b \<rightharpoondown> 'c) \<rightharpoondown> ('a \<rightharpoondown> 'c option)"
where "compose_alt = (\<lambda>f!.\<lambda>g\<in>{g. range f \<subseteq> n_dom g}. \<lambda>x\<in>(dom f) \<rightarrow> (Some ` (cod g)). do {y <- f $$ x; g $$ y})"  

*)

definition "typ_judg f A i B \<equiv> dom f = A \<and> codomain f = B \<and> cod f = Sigma A i"

syntax
  "_PiTyp" :: "('a \<rightharpoondown> 'b) \<Rightarrow>  pttrn \<Rightarrow>  'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> bool"  ("(3_ : \<Pi>_\<in>_ \<rightarrow> _ : _)" [0,0,3] 3)
  "_Typ" :: "('a \<rightharpoondown> 'b) \<Rightarrow>  pttrn \<Rightarrow>  'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> bool"  ("(3_ :  _ \<rightarrow> _ )" [0,0,3] 3)

abbreviation (input) "simple_typ f A B == (typ_judg f A (\<lambda>x. {f $ x}) B)"


translations 
 "f : \<Pi> x\<in>A \<rightarrow> i : B" \<rightharpoonup> "CONST typ_judg f A (\<lambda>x. i) B"
 "f : A \<rightarrow> B" \<rightharpoonup> "CONST simple_typ f A B"


lemma dom_typ_iff[simp, dest]: "f : \<Pi> x\<in>A \<rightarrow> i x : B \<Longrightarrow> dom f = A"
  apply (clarsimp simp: typ_judg_def)
  done

lemma codomain_typ_iff[simp, dest]: "f : \<Pi> x\<in>A \<rightarrow> i x : B \<Longrightarrow> codomain f = B"
  apply (unfold typ_judg_def, elim conjE, clarsimp)
  done


lemma cod_typ_iff[simp, dest]: "f : \<Pi> x\<in>A \<rightarrow> i x : B \<Longrightarrow> cod f = Sigma A i"
  by (meson typ_judg_def)

lemma cod_of_typ_iff[simp, dest]: "f : \<Pi> x\<in>A \<rightarrow> i x : B \<Longrightarrow> x \<in> A \<Longrightarrow> cod_of f x = i x"
  apply (unfold typ_judg_def, elim conjE, clarsimp)
  by (metis Pair_vimage_Sigma cod_simp dom_simp f_is_app_f) 


lemma cod_of_typ_codomain[simp, dest]: "f : \<Pi> x\<in>A \<rightarrow> i x : B \<Longrightarrow> x \<in> A \<Longrightarrow> cod_of f x \<subseteq> B"
  apply (unfold typ_judg_def, elim conjE, clarsimp)
  by (meson dom_cod_of_codomain)

lemma typ_judgI[intro]:"dom f = A \<Longrightarrow> codomain f = B \<Longrightarrow> cod f = Sigma A i \<Longrightarrow> typ_judg f A i B"
  apply (unfold typ_judg_def)
  apply (safe; clarsimp?)
  done

lemmas type_iffs = dom_typ_iff codomain_typ_iff cod_typ_iff 

lemma cod_comp[simp]: "composable f g \<Longrightarrow> cod (f \<cdot> g) = Sigma (dom f) (\<lambda>x.  cod g `` (cod_of f x))"
  apply (clarsimp simp: compose_def)
  apply (safe; clarsimp?)
    apply (simp add: composable_def )
  apply (simp add: composable_def )
  apply (simp add: composable_def fst_conv mem_Collect_eq)
  apply (safe; clarsimp?)
    apply (metis cod_iff dom_cod_of_codomain snd_eqD)
   apply (meson Image_iff cod_of_iff in_dom_in_codomain subset_iff total')
  apply (meson Image_iff cod_of_iff in_dom_in_codomain subset_iff total')
  done


lemma in_dom_iff[simp]: "x \<in> dom (\<Pi> x\<in>A \<rightarrow> i x : B. f x) \<longleftrightarrow> f x \<in> i x \<and> x \<in> A \<and> i x \<subseteq> B"
  apply (safe; clarsimp)
  apply (blast)
  done

lemma cod_of_iff_typ[simp]: "a \<in> cod_of (\<Pi> x\<in>A \<rightarrow> i x : B. f x) x \<longleftrightarrow> x \<in> dom (\<Pi> x\<in>A \<rightarrow> i x : B. f x) \<and> a \<in> i x "
  apply (simp only: cod_of_def)
  by (safe; clarsimp simp: cod_of_def)


lemma in_cod_iff[simp]: "x \<in> cod (\<Pi> x\<in>A \<rightarrow> i x : B. f x) \<longleftrightarrow> fst x \<in> dom (\<Pi> x\<in>A \<rightarrow> i x : B. f x) \<and> snd x \<in> i (fst x) "
  apply (safe; clarsimp?)
  by (metis (no_types, lifting) IntI Int_Collect SigmaI dep_vimage_eq prod.collapse)

lemma vimage_eqI[intro]: "(\<And>x. x \<in> S' \<longleftrightarrow> f x \<in> S) \<Longrightarrow> vimage f S = S'"
  by (safe; clarsimp)


lemma dep_vimage_eqI[intro, simp]: "(\<And>x. x \<in> S' \<longleftrightarrow> f x \<in> S x) \<Longrightarrow> dep_vimage f S = S'"
  by (safe; clarsimp)



lemma cod_dest_dom[dest, simp]: "(a, b) \<in> cod g \<Longrightarrow> a \<in> Dependent_Function.dom g"
  by (clarsimp simp: cod_iff)


lemma cod_dest_codomain[dest, simp]: "(a, b) \<in> cod g \<Longrightarrow> b \<in> codomain g"
  apply (clarsimp simp: cod_iff)
  by (meson dom_cod_of_codomain)


lemma dep_vimage_id'[simp]: "dep_vimage (\<lambda>a. a) S = {x. x \<in> S x}"
  by (safe; clarsimp)

abbreviation "reverse_app x f \<equiv> f $ x"

notation reverse_app (infixr "|>" 54) 

abbreviation "cmp_lr f g \<equiv> g |> (f |> compose)"

notation cmp_lr (infixr "\<Zcomp>" 54) 

lemma cod_cong: "(\<And>x. x \<in> A \<Longrightarrow> i x = j x) \<Longrightarrow>  (f : \<Pi> x\<in>A \<rightarrow> i x : B) = (f : \<Pi> x\<in>A \<rightarrow> j x : B) "
  by (metis Sigma_cong typ_judg_def)

definition lift ("\<guillemotleft>_\<guillemotright>")
  where "lift f = (SOME g. \<exists>A B i. restrict f A B i = g)"

lemma rewrite_restrict: "(\<And>g. \<forall>x\<in>(dom (restrict f A i B)). g $ x = f x \<Longrightarrow> (g : \<Pi> x\<in>(dom (restrict f A i B)) \<rightarrow> cod_of (restrict f A i B) x : B) \<Longrightarrow> P g) \<Longrightarrow> P (restrict f A i B) "
  by (smt (verit, ccfv_SIG) app_iff app_intro_2 cod_simp codomain_simp dom_simp in_dom_iff typ_judg_def)

lemma app_iff_alt: "x \<in> A \<and> f x \<in> i x \<and> i x \<subseteq> B \<Longrightarrow> ((\<Pi> x\<in>A \<rightarrow> i x : B . f x) $ x) =  (f x) "
  by (clarsimp)

named_theorems types


method rewrite_apps uses simp declares types  = 
  
 (((subst app_iff_alt | subst (asm) app_iff_alt), solves \<open>(intro conjI; auto simp: simp)\<close>) |
 ((subst comp_apply' | subst (asm) comp_apply'), fastforce simp: simp, fastforce simp: simp) |
 ((subst dom_comp cod_comp cod_cmp | subst (asm) dom_comp cod_comp cod_cmp), fastforce) |
  ((subst cod_of_typ_iff | subst (asm) cod_of_typ_iff) ,fastforce simp: simp intro: types, fastforce )) 

method use_types declares types = ((subst type_iffs | subst (asm) type_iffs), rule types)


lemma cod_cmpI[intro]: "composable f g \<Longrightarrow> codomain g = x \<Longrightarrow>  codomain (f \<cdot> g) = x" 
  apply (clarsimp)
  done

lemma cod_of_simp[simp]: "cod_of (restrict A f i B) = (\<lambda>x. cod (restrict A f i B) `` {x})"
  apply (rule ext)
  by (clarsimp simp: cod_of_def)

lemma Sigma_arg_cong: "(\<And>x. x \<in> A \<Longrightarrow> C x = D x) \<Longrightarrow> (SIGMA x:A. C x) = (SIGMA x:A. D x)"
  by auto

lemma int_Collect[simp]: "A \<inter> {x. P x} =  {x \<in> A.  P x}"
  by (safe; clarsimp)

lemma BCollect_subs[simp]: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> {x \<in> A. P x} = A"
  by (safe; clarsimp)

lemma insert_goal: " R \<Longrightarrow> (R \<Longrightarrow> Q) \<Longrightarrow> Q" 
  by (clarsimp)


lemma dep_appI: "(f : \<Pi> x\<in>A \<rightarrow> i x : B) \<Longrightarrow> x \<in> A \<Longrightarrow> (f $ x \<in> i x \<Longrightarrow> P (f $ x)) \<Longrightarrow> P (f $ x)"
  by simp

definition "family f \<equiv> SOME i. f = (\<guillemotleft>($) f \<guillemotright> : Dependent_Function.dom f \<rightarrow> i : codomain f)"

lemma ex_family: "\<exists>i. f = (\<guillemotleft>($) f \<guillemotright> : Dependent_Function.dom f \<rightarrow> i : codomain f)"
  apply (rule_tac x="cod_of f" in exI, rule extensionality; clarsimp?)
    apply (safe; clarsimp?)
    apply (meson dom_cod_of_codomain)
   apply (safe; clarsimp?)
     apply (meson cod_dest_dom dom_cod_of_codomain)
    apply (clarsimp simp: cod_of_def)
   apply (clarsimp simp: cod_of_def)
  by (metis f_is_app_f)


lemma family_intro: "(\<And>i. f = (\<guillemotleft>($) f\<guillemotright> : Dependent_Function.dom f \<rightarrow> i : codomain f) \<Longrightarrow> P (i x)) \<Longrightarrow> P (family f x)"
  apply (clarsimp simp: family_def)
  using ex_family 
  by (metis (mono_tags, lifting) some_eq_imp)

lemma cod_of_cong: "f = g \<Longrightarrow> cod_of f x = cod_of g x"
  by fastforce

lemma family_iff[simp]: "x \<in> A \<Longrightarrow> f x \<in> i x \<Longrightarrow> i x \<subseteq> B \<Longrightarrow> family (\<guillemotleft>f\<guillemotright> : A \<rightarrow> i : B) x = i x"
  apply (rule family_intro; clarsimp)
  apply (drule cod_of_cong[where x=x])
  by (clarsimp simp: set_eq_iff)

lemma cod_of_cmp[simp]:"x \<in> Dependent_Function.dom f \<Longrightarrow> composable f g \<Longrightarrow> cod_of (f \<Zcomp> g) x  = \<Union>(cod_of g ` cod_of f x)"
  apply (clarsimp simp: compose_def)
apply (subst app_iff; clarsimp?) 
   apply (meson composable_def subsetD)
  apply (safe; clarsimp?)
    apply (metis Image_singleton_iff cod_of_def)
   apply (meson Dependent_Function.cod_of_iff ImageI composable_def in_dom_in_codomain subsetD total)
  by (simp add: ImageI Image_singleton_iff cod_of_def)


lemma family_eq_dom_eq_cod_eq: "(\<And>x. x \<in> Dependent_Function.dom f \<Longrightarrow> family f x = family g x) \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g"
  apply (subst f_is_app_f)
  apply (subst f_is_app_f[where f=g])
 apply (subst (asm) f_is_app_f) back
  apply (subst (asm) f_is_app_f[where f=g])
  apply (clarsimp)
  apply (safe; clarsimp)
     apply (meson dom_cod_of_codomain)
    apply (drule_tac x=a in meta_spec, clarsimp)
    apply (metis f_is_app_f family_iff in_dom_iff)
   apply (drule_tac x=a in meta_spec, clarsimp)
   apply (metis dom_cod_of_codomain)
   apply (drule_tac x=a in meta_spec, clarsimp)
  by (metis f_is_app_f family_iff in_dom_iff)

   

lemma extensionality': " codomain f = codomain g  \<Longrightarrow> dom f = dom g \<Longrightarrow> (\<And>x y. x \<in> dom f \<Longrightarrow> x \<in> dom g \<Longrightarrow> y \<in> codomain f \<Longrightarrow> y \<in> codomain g \<Longrightarrow>  y \<in> cod_of f x \<longleftrightarrow> y \<in> cod_of g x) \<Longrightarrow>
   (\<And>x.  x \<in> dom f \<Longrightarrow> x \<in> dom f \<Longrightarrow> x \<in> dom g \<Longrightarrow> cod_of f x \<subseteq> codomain f \<Longrightarrow> cod_of g x \<subseteq> codomain g \<Longrightarrow> f $ x = g $ x) \<Longrightarrow> f = g" 
  apply (rule exten_equalI; clarsimp?)
  apply (case_tac "f $$ x", clarsimp)
    apply (metis None_not_in_nat_dom ndom_simp)
   apply (metis f_is_app_f in_dom_iff safe_app_Some_iff)
  sorry
  sledgehammer
  oops
  by (metis (no_types, lifting) f_is_app_f family_eq_dom_eq_cod_eq family_iff in_dom_iff)


method typesimp uses simp =  ((rewrite_apps simp: simp | clarsimp simp: simp | solves \<open>auto\<close>)+)[1]

method typesimp_step uses simp =  ((rewrite_apps simp: simp | clarsimp simp: simp | solves \<open>auto\<close>))[1]

end