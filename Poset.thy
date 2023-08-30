section \<open> thy \<close>

theory Poset
imports Main Function

begin

(* Poset type *)

record 'a Poset =
  el :: "'a set"
  le_rel :: "('a \<times> 'a) set"

definition "Poset_le_undefined_arg_not_in_domain a a' \<equiv> undefined"

abbreviation le :: "'a Poset \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"le P a a' \<equiv>
  if a \<in> el P \<and> a' \<in> el P
  then (a, a') \<in> le_rel P
  else Poset_le_undefined_arg_not_in_domain a a'"

(*
abbreviation le_P :: "'a \<Rightarrow> 'a Poset \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<sqsubseteq>\<langle>_\<rangle> _") where
"le_P a P a' \<equiv> (a, a') \<in> le_rel P"
*)

definition valid :: "'a Poset \<Rightarrow> bool" where
  "valid P \<equiv>
    let
      welldefined = \<forall>x y. (x,y) \<in> le_rel P \<longrightarrow> x \<in> el P \<and> y \<in> el P;
      reflexivity = \<forall>x. x \<in> el P \<longrightarrow> (x,x) \<in> le_rel P;
      antisymmetry = \<forall>x y. x \<in> el P \<longrightarrow> y \<in> el P  \<longrightarrow>  (x,y) \<in> le_rel P \<longrightarrow> (y,x) \<in> le_rel P  \<longrightarrow> x = y;
      transitivity = \<forall>x y z. x \<in> el P \<longrightarrow> y \<in> el P \<longrightarrow> z \<in> el P \<longrightarrow> (x,y) \<in> le_rel P \<longrightarrow> (y,z) \<in> le_rel P\<longrightarrow> (x,z) \<in> le_rel P
    in
      welldefined \<and> reflexivity \<and> antisymmetry \<and> transitivity"

(* PosetMap type (monotone function *)

record ('a, 'b) PosetMap =
  dom :: "'a Poset"
  cod :: "'b Poset"
  func ::"('a \<times>'b) set"

definition "Poset_app_undefined_arg_not_in_domain a \<equiv> undefined"

(* Map application *)

definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<star>" 997) where
"app f a \<equiv>
  if a \<in> el (dom f)
  then (THE b. (a, b) \<in> func f)
  else Poset_app_undefined_arg_not_in_domain a"

definition valid_map :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"valid_map f \<equiv>
  let
      le_dom = le (dom f);
      le_cod = le (cod f);
      e_dom = el (dom f);
      e_cod = el (cod f);
      welldefined = valid (dom f) \<and> valid (cod f) \<and> (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> e_dom \<and> b \<in> e_cod);
      deterministic = \<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b';
      total = \<forall>a. a \<in> e_dom \<longrightarrow> (\<exists>b. (a, b) \<in> func f);
      monotone = \<forall>a a'. a \<in> e_dom \<and> a' \<in> e_dom \<and> le_dom a a' \<longrightarrow> le_cod (f \<star> a) (f \<star> a')

  in welldefined \<and> deterministic \<and> total \<and> monotone"

(* Validity *)

lemma validI [intro]:
  fixes P :: "'a Poset"
  assumes welldefined : "(\<And>x y. (x,y) \<in> le_rel P \<Longrightarrow> x \<in> el P \<and> y \<in> el P)"
  and reflexivity : "(\<And>x. x \<in> el P \<Longrightarrow> le P x x)"
  and antisymmetry : "(\<And>x y. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow>  le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y)"
  and transitivity : "(\<And>x y z. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z)"
    shows "valid P"
  by (smt (verit, best) antisymmetry reflexivity transitivity valid_def welldefined)

lemma valid_welldefined : "valid P \<Longrightarrow> (x,y) \<in> le_rel P \<Longrightarrow> x \<in> el P \<and> y \<in> el P"
  by (smt (verit) valid_def)

lemma valid_reflexivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> le P x x"
  by (smt (verit) valid_def)

lemma valid_transitivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z"
  by (smt (verit, ccfv_threshold) valid_def)

lemma valid_antisymmetry : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> y \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y"
  by (smt (verit, ccfv_threshold) valid_def)

lemma valid_mapI [intro] : "valid (dom f) \<Longrightarrow> valid (cod f)  \<Longrightarrow> (\<And>a b. (a, b) \<in> func f \<Longrightarrow>  a \<in> el (dom f) \<and> b \<in> el (cod f)) \<Longrightarrow>
                   (\<And>a b b'. (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b') \<Longrightarrow>
                   (\<And>a. a \<in> el (dom f) \<Longrightarrow> (\<exists>b. (a, b) \<in> func f)) \<Longrightarrow>
                   (\<And>a a'. a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod f) (f \<star> a) (f \<star> a'))
  \<Longrightarrow> valid_map f" unfolding valid_map_def
  by auto

lemma valid_map_welldefined_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

lemma valid_map_welldefined_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

lemma valid_map_welldefined_func : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod f)"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_welldefined : "valid_map f \<Longrightarrow> valid (dom f) \<and> valid (cod f) \<and> (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in>
 el (dom f) \<and> b \<in> el (cod f))"
  by (simp add: valid_map_welldefined_cod valid_map_welldefined_dom valid_map_welldefined_func)

lemma valid_map_dom: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f)"
  by (meson valid_map_welldefined)

lemma valid_map_cod: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> b \<in> el (cod f)"
  by (meson valid_map_welldefined)

lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_total : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_monotone : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod f) (f \<star> a) (f \<star> a')"
unfolding valid_map_def
  by metis

lemma valid_map_eqI: "cod f = cod g \<Longrightarrow> dom f = dom g \<Longrightarrow> func f = func g \<Longrightarrow> (f :: ('a, 'b) PosetMap) = g"
  by simp

(* Map application *)

lemma fun_app : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> (a, f \<star> a) \<in> func f"
  by (metis app_def the_equality valid_map_deterministic valid_map_total)

lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> f \<star> a \<in> el (cod f)"
  by (meson fun_app valid_map_welldefined)

lemma fun_app3 : "a \<in> el (dom f) \<Longrightarrow> f \<star> a = (THE b. (a, b) \<in> func f) "
  by (simp add: app_def)

lemma fun_ext_raw : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>a. a \<in> el (dom f) \<Longrightarrow> f \<star> a = g \<star> a) \<Longrightarrow> func f = func g"
  by (metis Poset.fun_app pred_equals_eq2 valid_map_deterministic valid_map_welldefined_func)

lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And> a . a \<in> el (dom f) \<Longrightarrow> f \<star> a = g \<star> a) \<Longrightarrow> f = g"
  by (meson Poset.fun_ext_raw valid_map_eqI)

lemma fun_app_iff  : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> f \<star> a = b"
  by (meson fun_app valid_map_deterministic valid_map_welldefined)

(* Map composition *)

definition "Poset_compose_undefined_incomposable g f \<equiv> undefined"

definition compose :: "('b, 'c) PosetMap \<Rightarrow> ('a, 'b) PosetMap \<Rightarrow> ('a, 'c) PosetMap" (infixl "\<diamondop>" 55) where
  "compose g f \<equiv>
  if dom g = cod f
  then \<lparr> dom = dom f, cod = cod g, func = relcomp (func f) (func g) \<rparr>
  else Poset_compose_undefined_incomposable g f"

lemma compose_welldefined_cod : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<diamondop> f) \<Longrightarrow> b \<in> el (cod g)"
  unfolding compose_def
  using Poset.valid_map_welldefined by auto               

lemma compose_welldefined_dom : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<diamondop> f) \<Longrightarrow> a \<in> el (dom f)"
  unfolding compose_def
  using Poset.valid_map_welldefined by auto               

lemma compose_welldefined : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<diamondop> f) \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod g)"
  by (metis Poset.valid_map_welldefined PosetMap.select_convs(3) compose_def relcomp.cases)

lemma compose_deterministic : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<diamondop> f) \<Longrightarrow> (a, b') \<in> func (g \<diamondop> f) \<Longrightarrow> b = b'"
  by (metis (no_types, opaque_lifting) Poset.valid_map_deterministic PosetMap.select_convs(3) compose_def relcomp.cases)

lemma compose_total : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func (g \<diamondop> f)"
  unfolding compose_def
  by (smt (z3) Poset.fun_app Poset.fun_app2 PosetMap.select_convs(3) relcomp.relcompI)

lemma dom_compose [simp] : "dom g = cod f \<Longrightarrow> dom (g \<diamondop> f) = dom f"
  unfolding compose_def
  by (simp add: Let_def)

lemma cod_compose [simp] : "dom g = cod f \<Longrightarrow> cod (g \<diamondop> f) = cod g"
  unfolding compose_def
  by (simp add: Let_def)

lemma compose_app_assoc: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<diamondop> f) \<star> a = g \<star> (f \<star> a)"
  apply (clarsimp simp: app_def, safe)
  apply (smt (z3) Poset.fun_app PosetMap.select_convs(3) compose_def compose_deterministic fun_app_iff relcomp.relcompI theI')
  by (metis app_def fun_app2)
                   
lemma compose_monotone :
  fixes f :: "('a,'b) PosetMap" and g :: "('b,'c) PosetMap" and a a' :: "'a"
  assumes f_valid : "valid_map f" and g_valid : "valid_map g"
  and a_elem : "a \<in> el (dom f)" and a'_elem : "a' \<in> el (dom f)"
  and le_aa' : "le (dom f) a a'"
  and dom_cod : "dom g = cod f"
shows "le (cod g) ((g \<diamondop> f) \<star> a) ((g \<diamondop> f) \<star> a')"
  by (metis (no_types, opaque_lifting) Poset.compose_app_assoc Poset.fun_app2 a'_elem a_elem dom_cod f_valid g_valid le_aa' valid_map_monotone)

lemma compose_valid : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<diamondop> f)"
proof (intro valid_mapI, safe, goal_cases)
  case 1
  then show ?case
    by (simp add: Poset.valid_map_welldefined_dom) 
next
  case 2
  then show ?case
    by (simp add: Poset.valid_map_welldefined_cod) 
next
  case (3 a b)
  then show ?case
    by (simp add: Poset.compose_welldefined_dom) 
next
  case (4 a b)
  then show ?case
    by (simp add: Poset.compose_welldefined_cod) 
next
  case (5 a b b')
  then show ?case
    by (meson Poset.compose_deterministic) 
next
  case (6 a)
  then show ?case
    by (simp add: Poset.compose_total) 
next
  case (7 a a')
  then show ?case 
    by (simp add: compose_monotone) 
qed

lemma compose_app [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<diamondop> f) \<star> a = c"
  apply (rule fun_app_iff)
  using compose_valid apply blast
  by (simp add: compose_def relcomp.relcompI)

lemma compose_assoc : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> dom g = cod f \<Longrightarrow> dom h = cod g 
\<Longrightarrow> (h \<diamondop> g) \<diamondop> f = h \<diamondop> (g \<diamondop> f)"
  by (smt (verit) Poset.cod_compose Poset.compose_app_assoc Poset.compose_valid Poset.dom_compose Poset.fun_app2 Poset.fun_ext) 

(* Proof techniques *)

lemma indirect_inequality_lower : 
  fixes P :: "'a Poset" and a b :: "'a"
  assumes P_valid : "valid P"
  and "a \<in> el P" and "b \<in> el P"
shows "le P a b = (\<forall> c \<in> el P . (le P b c \<longrightarrow> le P a c))"
  by (smt (verit, best) P_valid assms(2) assms(3) valid_reflexivity valid_transitivity)

lemma indirect_inequality_higher : 
  fixes P :: "'a Poset" and a b :: "'a"
  assumes P_valid : "valid P"
  and "a \<in> el P" and "b \<in> el P"
shows "le P a b = (\<forall> c \<in> el P . (le P c a \<longrightarrow> le P c b))"
  by (smt (verit, best) P_valid assms(2) assms(3) valid_reflexivity valid_transitivity)

lemma indirect_equality_lower : 
  fixes P :: "'a Poset" and a b :: "'a"
  assumes P_valid : "valid P"
  and "a \<in> el P" and "b \<in> el P"
shows "a = b = (\<forall> c \<in> el P . (le P b c = le P a c))"
  by (smt (verit, del_insts) P_valid assms(2) assms(3) valid_antisymmetry valid_reflexivity) 

lemma indirect_equality_higher : 
  fixes P :: "'a Poset" and a b :: "'a"
  assumes P_valid : "valid P"
  and "a \<in> el P" and "b \<in> el P"
shows "a = b = (\<forall> c \<in> el P . (le P c a = le P c b))"
  by (smt (verit, del_insts) P_valid assms(2) assms(3) valid_antisymmetry valid_reflexivity) 

(* Properties *)

definition is_surjective :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall> b . b \<in> el (cod f) \<longrightarrow> (\<exists> a . a \<in> el (dom f) \<and> f \<star> a = b)"

definition is_injective :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall>a a' . a \<in> el (dom f) \<longrightarrow> a' \<in> el (dom f) \<longrightarrow> f \<star> a = f \<star> a' \<longrightarrow> a = a'"

definition is_bijective :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

lemma surjection_is_right_cancellative : "valid_map f \<Longrightarrow> is_surjective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h \<Longrightarrow>  g \<diamondop> f = h \<diamondop> f \<Longrightarrow> g = h"
  by (metis Poset.cod_compose Poset.compose_app_assoc Poset.fun_ext Poset.is_surjective_def)

lemma injection_is_left_cancellative : "valid_map f \<Longrightarrow> is_injective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f \<Longrightarrow>  f \<diamondop> g = f \<diamondop> h \<Longrightarrow> g = h"
  by (smt (verit, ccfv_threshold) Poset.compose_app_assoc Poset.dom_compose Poset.fun_app2 Poset.fun_ext Poset.is_injective_def)

(* Identity maps *)

definition ident :: "'a Poset \<Rightarrow> ('a, 'a) PosetMap" where
"ident P \<equiv> \<lparr> dom = P, cod = P, func = Id_on (el P) \<rparr>"

lemma ident_valid  : "valid P \<Longrightarrow> valid_map (ident P)"
  unfolding valid_map_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by blast

lemma ident_dom [simp] : "dom (ident P) = P"
  by (simp add: ident_def)

lemma ident_cod [simp] : "cod (ident P) = P"
  by (simp add: ident_def)

lemma ident_func [simp] : "func (ident P) = Id_on (el P)"
  by (simp add: ident_def)

lemma ident_app [simp] :
  fixes a :: "'a" and P :: "'a Poset"
  assumes "valid P" and "a \<in> el P"
  shows "ident P \<star> a = a"
  by (metis Id_onI Poset.fun_app_iff Poset.ident_def Poset.ident_valid PosetMap.select_convs(3) assms(1) assms(2))

lemma compose_ident_left [simp]  : "valid_map f \<Longrightarrow> ident (cod f) \<diamondop> f = f"
  by (smt (verit, best) Poset.cod_compose Poset.compose_app_assoc Poset.compose_valid Poset.dom_compose Poset.fun_app2 Poset.fun_ext Poset.ident_app Poset.ident_cod Poset.ident_dom Poset.ident_valid valid_map_welldefined_cod) 

lemma compose_ident_right [simp] : "valid_map f  \<Longrightarrow> f \<diamondop> ident (dom f) = f"
  by (smt (verit, ccfv_SIG) Poset.cod_compose Poset.compose_app_assoc Poset.compose_valid Poset.dom_compose Poset.fun_ext Poset.ident_app Poset.ident_cod Poset.ident_dom Poset.ident_valid valid_map_welldefined_dom)

(* Constant maps *)

definition "PosetMap_const_undefined_arg_not_in_codomain b \<equiv> undefined"

definition const :: "'a Poset \<Rightarrow>  'b Poset  \<Rightarrow> 'b \<Rightarrow>  ('a, 'b) PosetMap" where
"const P Q q \<equiv>
  if q \<in> el Q
  then  \<lparr> dom = P, cod = Q,  func = { (p, q) | p . p \<in> el P } \<rparr>
  else PosetMap_const_undefined_arg_not_in_codomain q"

lemma const_dom [simp] : "q \<in> el Q \<Longrightarrow> dom (const P Q q) = P"
  by (simp add: const_def)

lemma const_cod [simp] : "q \<in> el Q \<Longrightarrow> cod (const P Q q) = Q"
  by (simp add: const_def)

lemma const_app [simp] : "valid P \<Longrightarrow> valid Q \<Longrightarrow> p \<in> el P \<Longrightarrow> q \<in> el Q \<Longrightarrow> ((const P Q q) \<star> p) = q"
  unfolding const_def app_def
  by auto

lemma const_valid : "valid P \<Longrightarrow> valid Q \<Longrightarrow> q \<in> el Q \<Longrightarrow> valid_map (const P Q q)"
proof (intro valid_mapI,goal_cases)
  case 1
  then show ?case
    by simp 
next
  case 2
  then show ?case
    by simp 
next
  case (3 a b)
  then show ?case
    by (simp add: Poset.const_def) 
next
  case (4 a b b')
  then show ?case
    by (simp add: Poset.const_def) 
next
  case (5 a)
  then show ?case by (simp add: const_def)
next
  case (6 a a')
  then show ?case
    by (simp add: valid_reflexivity) 
qed

(* Cartesian product of posets *)

definition product :: "'a Poset \<Rightarrow> 'b Poset \<Rightarrow> ('a \<times> 'b) Poset" (infixl "\<times>\<times>" 55) where
"product P Q \<equiv> \<lparr> el = el P \<times> el Q, le_rel =
 {(x, y). fst x \<in> el P \<and> snd x \<in> el Q \<and> fst y \<in> el P \<and> snd y \<in> el Q \<and> (fst x, fst y) \<in> le_rel P \<and> (snd x, snd y) \<in> le_rel Q} \<rparr>"

lemma product_valid : "valid P \<Longrightarrow> valid Q \<Longrightarrow> valid (P \<times>\<times> Q)"
  unfolding valid_def product_def
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD SigmaE SigmaI case_prodI fst_conv mem_Collect_eq prod.collapse snd_conv)

lemma product_el_1 : "(a,b) \<in> el (P \<times>\<times> Q) \<Longrightarrow> a \<in> el P"
  by (simp add: Poset.product_def)

lemma product_el_2 : "(a,b) \<in> el (P \<times>\<times> Q) \<Longrightarrow> b \<in> el Q"
  by (simp add: Poset.product_def)

lemma product_le_1 : "valid P \<Longrightarrow> valid Q \<Longrightarrow> ((a, b),(a', b')) \<in> le_rel (P \<times>\<times> Q) \<Longrightarrow> (a,a') \<in> le_rel P"
  by (simp add: Poset.product_def) 
                                               
lemma product_le_2 : "valid P \<Longrightarrow> valid Q \<Longrightarrow> ((a, b),(a', b')) \<in> le_rel (P \<times>\<times> Q) \<Longrightarrow> (b,b') \<in> le_rel Q"
  by (simp add: Poset.product_def) 

(* Discrete poset *)

definition discrete :: "'a Poset" where
  "discrete \<equiv> \<lparr>  el = UNIV , le_rel = {x. fst x = snd x} \<rparr>"

lemma discrete_valid : "valid discrete"
  by (simp add: discrete_def valid_def)

(* Infima and suprema *)

definition is_inf :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_inf P U i \<equiv> U \<subseteq> el P \<and> i \<in> el P \<and> (\<forall>u\<in>U. le P i u) \<and> (\<forall>z \<in> el P. (\<forall>u\<in>U. le P z u) \<longrightarrow> le P z i)"

definition is_sup :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_sup P U s \<equiv> U \<subseteq> el P \<and> s \<in> el P \<and> (\<forall>u\<in>U. le P u s) \<and> (\<forall>z \<in> el P. (\<forall>u\<in>U. le P u z) \<longrightarrow> le P s z)"

abbreviation is_bot :: "'a Poset \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bot P b \<equiv> b \<in> el P \<and> (\<forall>p \<in> el P. le P b p)"

abbreviation is_top :: "'a Poset \<Rightarrow> 'a \<Rightarrow> bool" where
"is_top P t \<equiv> t \<in> el P \<and> (\<forall>p \<in> el P. le P p t)"

definition inf :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a " where
"inf P U \<equiv> SOME i. is_inf P U i"

definition sup :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a " where
"sup P U \<equiv> SOME s. is_sup P U s"

definition meet :: "'a Poset \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> 'a " where
"meet P a b \<equiv> inf P {a,b}"

definition join :: "'a Poset \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> 'a " where
"join P a b \<equiv> sup P {a,b}"

definition is_complete :: "'a Poset \<Rightarrow> bool" where
"is_complete P \<equiv> valid P \<and> (\<forall>U. U \<subseteq> el P \<longrightarrow> (\<exists> i. is_inf P U i) \<and> inf P U \<in> el P)"

definition is_cocomplete :: "'a Poset \<Rightarrow> bool" where
"is_cocomplete P \<equiv> valid P \<and> (\<forall>U. U \<subseteq> el P \<longrightarrow> (\<exists> i. is_sup P U i) \<and> sup P U \<in> el P)"

lemma inf_unique : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> i \<in> el P\<Longrightarrow> i' \<in> el P \<Longrightarrow> is_inf P U i \<Longrightarrow> is_inf P U i' \<Longrightarrow> i = i'"
  unfolding is_inf_def
  by (metis valid_antisymmetry)

lemma sup_unique : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> s \<in> el P\<Longrightarrow> s' \<in> el P \<Longrightarrow> is_sup P U s \<Longrightarrow> is_sup P U s' \<Longrightarrow> s = s'"
  unfolding is_sup_def
  by (metis valid_antisymmetry)

lemma is_inf_is_glb : "valid P \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> i \<in> el P \<Longrightarrow> is_inf P U i
\<Longrightarrow> \<forall>u\<in>U. le P z u \<Longrightarrow> le P z i"
  by (simp add: is_inf_def)

lemma is_sup_is_lub : "valid P \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> s \<in> el P \<Longrightarrow> is_sup P U s
\<Longrightarrow> \<forall>u\<in>U. le P u z \<Longrightarrow> le P s z"
  by (simp add: is_sup_def)

lemma is_inf_smaller : "valid P \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> i \<in> el P \<Longrightarrow> is_inf P U i \<Longrightarrow> \<forall> u \<in> U. le P i u"
  unfolding is_inf_def
  by blast

lemma is_sup_greater : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> s \<in> el P  \<Longrightarrow> is_sup P U s \<Longrightarrow> \<forall> u \<in> U. le P u s"
  unfolding is_sup_def
  by blast

lemma inf_is_glb : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> \<forall>u\<in>U. le P z u \<Longrightarrow> le P z (inf P U)"
  by (simp add: inf_def is_inf_is_glb is_complete_def someI_ex) 

lemma sup_is_lub : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> \<forall>u\<in>U. le P u z \<Longrightarrow> le P (sup P U) z"
  by (simp add: sup_def is_sup_is_lub is_cocomplete_def someI_ex) 

lemma complete_inf_exists : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> \<exists>i \<in> el P. is_inf P U i"
  by (smt (verit, best) is_complete_def is_inf_def)

lemma cocomplete_sup_exists : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> \<exists>s \<in> el P. is_sup P U s"
  by (smt (verit, del_insts) is_cocomplete_def is_sup_def)

lemma sup_greater : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> a \<in> U \<Longrightarrow> \<forall> u \<in> U. le P a (sup P U)"
  by (metis is_cocomplete_def is_sup_greater someI_ex sup_def) 

lemma inf_smaller : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> a \<in> U \<Longrightarrow> \<forall> u \<in> U. le P (inf P U) a"
  by (metis inf_def is_complete_def is_inf_smaller someI_ex) 

lemma complete_meet_is_inf : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> is_inf P {a, b} (meet P a b)"
  by (simp add: inf_def is_complete_def meet_def someI_ex)

lemma cocomplete_join_is_sup: "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> is_sup P {a, b} (join P a b)"
  by (simp add: is_cocomplete_def join_def someI_ex sup_def)

lemma meet_smaller1 : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> le P (meet P a b) a"
  by (smt (verit) complete_meet_is_inf insertCI is_inf_def) 

lemma meet_smaller2 : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> le P (meet P a b) b"
  by (smt (verit, ccfv_threshold) complete_meet_is_inf insertCI is_inf_def)

lemma meet_smaller : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> le P (meet P a b) a \<and> le P (meet P a b) b"
  by (simp add: meet_smaller1 meet_smaller2)

lemma join_greater1 : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> le P a (join P a b)"
  by (smt (verit) cocomplete_join_is_sup insertCI is_sup_def)

lemma join_greater2 : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> le P b (join P a b)"
  by (smt (verit, ccfv_threshold) cocomplete_join_is_sup insertCI is_sup_def)

lemma join_greater : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> le P a (join P a b) \<and> le P b (join P a b)"
  by (simp add: join_greater1 join_greater2)

lemma meet_el : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> meet P a b \<in> el P"
  by (simp add: is_complete_def meet_def) 

lemma join_el : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> join P a b \<in> el P"
  by (simp add: is_cocomplete_def join_def)

lemma sup_el : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> sup P U \<in> el P"
  using is_cocomplete_def by blast

lemma inf_el : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> inf P U \<in> el P" using inf_def
  using is_complete_def by blast

lemma meet_property : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> c \<in> el P \<Longrightarrow> le P c a \<Longrightarrow> le P c b \<Longrightarrow> le P c (meet P a b)"
  using complete_meet_is_inf is_inf_def
  by (smt (verit, ccfv_threshold) insert_iff meet_el singleton_iff) 

lemma join_property : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> c \<in> el P \<Longrightarrow> le P a c \<Longrightarrow> le P b c \<Longrightarrow> le P (join P a b) c"
  using cocomplete_join_is_sup is_sup_def
  by (smt (verit, ccfv_threshold) insert_iff singleton_iff)

lemma meet_mono : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> a' \<in> el P \<Longrightarrow> b' \<in> el P \<Longrightarrow> le P a a' \<Longrightarrow> le P b b' 
\<Longrightarrow> le P (meet P a b) (meet P a b')"
  by (smt (verit, ccfv_threshold) is_complete_def meet_el meet_property meet_smaller1 meet_smaller2 valid_def) 

lemma join_mono : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> a' \<in> el P \<Longrightarrow> b' \<in> el P \<Longrightarrow> le P a a' \<Longrightarrow> le P b b' 
\<Longrightarrow> le P (join P a b) (join P a b')"
  by (smt (verit, best) is_cocomplete_def join_el join_greater1 join_greater2 join_property valid_transitivity) 

lemma meet_comm : "a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> meet P a b = meet P b a"
  by (simp add: insert_commute meet_def)

lemma join_comm : "a \<in> el P \<Longrightarrow> b \<in> el P \<Longrightarrow> join P a b = join P b a"
  by (simp add: insert_commute join_def)

lemma inf_is_inf : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> is_inf P U (inf P U)"
  by (metis complete_inf_exists inf_def someI_ex)

lemma sup_is_sup : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> is_sup P U (sup P U)"
  by (metis cocomplete_sup_exists sup_def someI_ex)

lemma inf_antimono : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> V \<subseteq> el P \<Longrightarrow> U \<subseteq> V \<Longrightarrow> le P (inf P V) (inf P U)"
  by (smt (verit) inf_el inf_is_glb inf_smaller subsetD)

lemma sup_mono : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> V \<subseteq> el P \<Longrightarrow> U \<subseteq> V \<Longrightarrow> le P (sup P U) (sup P V)"
  by (smt (verit, del_insts) in_mono sup_el sup_greater sup_is_lub)

lemma sup_singleton : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> sup P {a} = a"
  by (smt (verit) insert_absorb2 is_cocomplete_def join_def join_el join_greater1 join_property valid_antisymmetry valid_reflexivity)

lemma inf_singleton : "is_complete P \<Longrightarrow> a \<in> el P \<Longrightarrow> inf P {a} = a" 
  using insert_absorb2 is_complete_def inf_def inf_el meet_smaller1 meet_property inf_smaller is_inf_is_glb valid_antisymmetry valid_reflexivity
  by (smt (verit, del_insts) meet_def meet_el)

lemma sup_el_le : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> a \<in> el P \<Longrightarrow> \<exists> u \<in> U . le P a u \<Longrightarrow> le P a (sup P U)"
  by (smt (verit, ccfv_threshold) in_mono is_cocomplete_def sup_greater valid_transitivity)

lemma inf_el_le : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> a \<in> el P \<Longrightarrow> \<exists> u \<in> U . le P u a \<Longrightarrow> le P (inf P U) a"
  by (smt (verit, ccfv_SIG) inf_smaller is_complete_def subsetD valid_def)

lemma sup_mono_pointwise : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> V \<subseteq> el P \<Longrightarrow> (\<forall> u \<in> U. \<exists> v \<in> V. le P u v) \<Longrightarrow> le P (sup P U) (sup P V)"
  by (simp add: is_cocomplete_def subsetD sup_el_le sup_is_lub)

lemma inf_mono_pointwise : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> V \<subseteq> el P \<Longrightarrow> (\<forall> v \<in> V. \<exists> u \<in> U. le P u v) \<Longrightarrow> le P (inf P U) (inf P V)"
  by (simp add: inf_el_le inf_is_glb is_complete_def subsetD)

lemma inf_as_sup : "is_complete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> sup P U = inf P {a \<in> el P . (\<forall> u \<in> U . le P u a)}"
  proof -
    assume "is_complete P "
    fix U 
    assume "U \<subseteq> el P"
    define "s" where "s = inf P {a \<in> el P . (\<forall> u \<in> U . le P u a)}"
    have "is_sup P U s"
    proof (simp add: is_sup_def, safe, goal_cases)
      case (1 x)
      then show ?case
        using \<open>U \<subseteq> el P\<close> by blast 
    next
      case 2
      then show ?case
        by (simp add: \<open>is_complete P\<close> inf_el s_def) 
    next
      case (3 u)
      then show ?case
        by (simp add: \<open>is_complete P\<close> inf_is_glb s_def) 
    next
      case (4 u)
      then show ?case
        using \<open>U \<subseteq> el P\<close> by blast 
    next
      case (5 u)
      then show ?case
        by (simp add: \<open>is_complete P\<close> inf_el s_def)
    next
      case (6 z)
      then show ?case
        by (smt (verit) \<open>is_complete P\<close> inf_smaller is_complete_def mem_Collect_eq s_def subset_eq) 
    next
      case (7 z)
      then show ?case 
        by (simp add: \<open>is_complete P\<close> inf_el s_def) 
    qed
    moreover have "sup P U = s"
      by (smt (verit) Poset.sup_unique \<open>is_complete P\<close> calculation is_complete_def is_sup_def someI_ex sup_def)
    thus "Poset.sup P U = Poset.inf P {a \<in> el P. \<forall>u\<in>U. le P u a}"
      using s_def by blast 
  qed

lemma sup_as_inf : "is_cocomplete P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> inf P U = sup P {a \<in> el P . (\<forall> u \<in> U . le P a u)}"
   proof -
    assume "is_cocomplete P "
    fix U 
    assume "U \<subseteq> el P"
    define "i" where "i = sup P {a \<in> el P . (\<forall> u \<in> U . le P a u)}"
    have "is_inf P U i"
    proof (simp add: is_inf_def, safe, goal_cases)
      case (1 x)
      then show ?case
        using \<open>U \<subseteq> el P\<close> by blast 
    next
      case 2
      then show ?case
        by (simp add: \<open>is_cocomplete P\<close> sup_el i_def) 
    next
      case (3 u)
      then show ?case
        by (simp add: \<open>is_cocomplete P\<close> sup_is_lub i_def) 
    next
      case (4 u)
      then show ?case
        by (simp add: \<open>is_cocomplete P\<close> i_def sup_el)
    next
      case (5 u)
      then show ?case
        using \<open>U \<subseteq> el P\<close> by auto
    next
      case (6 z)
      then show ?case
        by (smt (verit) \<open>is_cocomplete P\<close> sup_greater is_cocomplete_def mem_Collect_eq i_def subset_eq) 
    next
      case (7 z)
      then show ?case 
        by (simp add: \<open>is_cocomplete P\<close> sup_el i_def) 
    qed
    moreover have "inf P U = i"
      by (smt (verit) Poset.inf_unique \<open>is_cocomplete P\<close> calculation is_cocomplete_def is_inf_def someI_ex inf_def)
    thus "inf P U = sup P {a \<in> el P. \<forall>u\<in>U. le P a u}"
      using i_def by blast 
  qed

lemma complete_equiv_cocomplete : "is_complete P = is_cocomplete P"
proof (safe, goal_cases)
  case 1
  then show ?case 
  proof (simp add: is_cocomplete_def)
    assume "is_complete P"
    show "valid P \<and> (\<forall>U\<subseteq>el P. (\<exists>i. is_sup P U i) \<and> Poset.sup P U \<in> el P) " 
    proof (rule conjI, goal_cases)
      case 1
      then show ?case
        using \<open>is_complete P\<close> is_complete_def by blast 
    next
      case 2
      then show ?case 
      proof (rule allI, rule impI)
        fix U
        assume "U \<subseteq> el P"
        define "s" where "s = inf P {a \<in> el P . (\<forall> u \<in> U . le P u a)}"
        have "is_sup P U s"
        proof (simp add: is_sup_def, safe, goal_cases)
          case (1 x)
          then show ?case
            using \<open>U \<subseteq> el P\<close> by blast
        next
          case 2
          then show ?case
            by (simp add: "1" inf_el s_def) 
        next
          case (3 u)
          then show ?case
            by (simp add: "1" inf_is_glb s_def) 
        next
          case (4 u)
          then show ?case
            using \<open>U \<subseteq> el P\<close> by blast
        next
          case (5 u)
          then show ?case
            by (simp add: "1" inf_el s_def) 
        next
          case (6 z)
          then show ?case
            by (smt (verit) "1" inf_smaller is_complete_def mem_Collect_eq s_def subset_eq) 
        next
          case (7 z)
          then show ?case 
            by (simp add: "1" inf_el s_def) 
        qed
        then show "(\<exists>i. is_sup P U i) \<and> Poset.sup P U \<in> el P"
          by (smt (verit, best) is_sup_def someI_ex sup_def)
      qed
    qed
  qed
    next
 case 2
  then show ?case 
  proof (simp add: is_complete_def)
    assume "is_cocomplete P"
    show "valid P \<and> (\<forall>U\<subseteq>el P. (\<exists>i. is_inf P U i) \<and> Poset.inf P U \<in> el P)"
    proof (rule conjI, goal_cases)
      case 1
      then show ?case
        using \<open>is_cocomplete P\<close> is_cocomplete_def by blast 
    next
      case 2
      then show ?case 
      proof (rule allI, rule impI)
        fix U
        assume "U \<subseteq> el P"
        define "i" where "i = sup P {a \<in> el P . (\<forall> u \<in> U . le P a u)}"
        have "is_inf P U i"
        proof (simp add: is_inf_def, safe, goal_cases)
          case (1 x)
          then show ?case
            using \<open>U \<subseteq> el P\<close> by blast 
        next
          case 2
          then show ?case
            by (simp add: \<open>is_cocomplete P\<close> i_def sup_el)
        next
          case (3 u)
          then show ?case
            by (simp add: \<open>is_cocomplete P\<close> i_def sup_is_lub)
        next
          case (4 u)
          then show ?case
            by (simp add: \<open>is_cocomplete P\<close> i_def sup_el)
        next
          case (5 u)
          then show ?case
            using \<open>U \<subseteq> el P\<close> by blast
        next
          case (6 z)
          then show ?case
            by (smt (verit, ccfv_SIG) \<open>is_cocomplete P\<close> i_def mem_Collect_eq subset_iff sup_greater) 
        next
          case (7 z)
          then show ?case
            by (simp add: \<open>is_cocomplete P\<close> i_def sup_el) 
        qed
        then show "(\<exists>i. is_inf P U i) \<and> Poset.inf P U \<in> el P"
          by (smt (verit, best) inf_def is_inf_def someI_ex) 
      qed
    qed
  qed
qed

lemma sup_dist_join1 :
  fixes P :: "'a Poset" and U :: "'a set" and a :: "'a"
  assumes P_cocomplete : "is_cocomplete P" and U_els : "U \<subseteq> el P" and U_inhabited : "U \<noteq> {}" and a_el : "a \<in> el P"
  shows "join P a (sup P U) = sup P {join P a u | u. u \<in> U}"
proof -
  define "aU" where "aU = {join P a u | u. u \<in> U}"
  then have "aU \<subseteq> el P" using aU_def 
    by (smt (verit) P_cocomplete U_els a_el join_el mem_Collect_eq subset_eq)
  moreover have "join P a (sup P U) \<in> el P"
    by (simp add: P_cocomplete U_els a_el join_el sup_el) 
  moreover have "sup P aU \<in> el P"
    by (smt (verit, ccfv_threshold) P_cocomplete U_els a_el in_mono join_el mem_Collect_eq subsetI sup_el aU_def) 
  moreover have left: "le P (join P a (sup P U)) (sup P aU)" 
    proof -
      have "\<exists> u . u \<in> U \<and> join P a u \<in> aU \<and> le P a (join P a u)"
        using P_cocomplete U_els U_inhabited a_el join_greater1 aU_def by fastforce 
      moreover have "le P a (sup P aU)"
        using P_cocomplete U_els a_el calculation join_el mem_Collect_eq subset_iff sup_el_le aU_def
        by (smt (verit, ccfv_threshold)) 
      moreover have "\<forall>u\<in>U. \<exists>v\<in>aU. le P u v" using aU_def
        by (smt (verit) P_cocomplete U_els a_el join_greater mem_Collect_eq subsetD)
      moreover have "le P (sup P U) (sup P aU)" using sup_mono_pointwise [where ?P=P and ?U=U and ?V=aU]
        using P_cocomplete U_els \<open>aU \<subseteq> el P\<close> calculation(3) by fastforce
      ultimately show ?thesis
        by (simp add: P_cocomplete U_els \<open>Poset.sup P aU \<in> el P\<close> a_el join_property sup_el)
    qed
  moreover have right: "le P (sup P aU) (join P a (sup P U))" 
    proof -
      have "\<forall>v \<in> aU. le P v (join P a (sup P U))" using aU_def
        by (smt (verit, ccfv_threshold) P_cocomplete U_els \<open>aU \<subseteq> el P\<close> a_el in_mono join_greater1 join_mono mem_Collect_eq sup_el sup_greater) 
      thus ?thesis
        by (simp add: P_cocomplete \<open>aU \<subseteq> el P\<close> \<open>join P a (Poset.sup P U) \<in> el P\<close> sup_is_lub) 
    qed
  ultimately show ?thesis using aU_def P_cocomplete is_cocomplete_def valid_antisymmetry
    by fastforce
qed

lemma sup_dist_join2 :
  fixes P :: "'a Poset" and U :: "'a set" and a :: "'a"
  assumes P_cocomplete : "is_cocomplete P" and U_els : "U \<subseteq> el P" and U_inhabited : "U \<noteq> {}" and a_el : "a \<in> el P"
  shows "join P (sup P U) a = sup P {join P u a | u. u \<in> U}" 
proof -
  have "join P (sup P U) a = join P a (sup P U)"
    by (simp add: P_cocomplete U_els a_el join_comm sup_el)
  moreover have "sup P {join P u a | u. u \<in> U} = sup P {join P a u | u. u \<in> U}"
    by (metis U_els a_el in_mono join_comm)
  ultimately show ?thesis
    by (simp add: P_cocomplete U_els U_inhabited a_el sup_dist_join1)
qed

(* Constants *)

definition top :: "'a Poset \<Rightarrow> 'a" where
"top P = sup P (el P) "

definition bot :: "'a Poset \<Rightarrow> 'a" where
"bot P = sup P {} "

lemma top_max : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> le P a (top P)"
  by (simp add: sup_greater top_def) 

lemma bot_min : "is_cocomplete P \<Longrightarrow> a \<in> el P \<Longrightarrow> le P (bot P) a"
  by (simp add: bot_def sup_is_lub)

lemma top_as_inf : "is_complete P \<Longrightarrow> top P = inf P {}"
  by (smt (verit) Poset.inf_unique complete_equiv_cocomplete dual_order.refl empty_iff empty_subsetI inf_def is_complete_def is_inf_def someI_ex sup_el sup_greater top_def)

lemma bot_as_inf : "is_complete P \<Longrightarrow> bot P = inf P (el P)"
  by (smt (verit) Poset.sup_unique bot.extremum bot_def dual_order.refl empty_iff inf_smaller is_complete_def is_sup_def someI_ex sup_def) 

(* Fixed points. C.f. https://isabelle.in.tum.de/library/HOL/HOL/Inductive.html *)

(* Least fixed point *)

definition lfp :: "('a , 'a) PosetMap \<Rightarrow> 'a" where
"lfp f \<equiv> inf (cod f) {a \<in> el (dom f) . le (cod f) (f \<star> a) a}" 

lemma lfp_is_el : "is_complete P \<Longrightarrow> valid_map f \<Longrightarrow> dom f = P \<Longrightarrow> cod f = P \<Longrightarrow> lfp f \<in> el P"
  by (simp add: Poset.lfp_def inf_el)

lemma lfp_lowerbound :
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap" and a :: "'a"
  assumes P_complete : "is_complete P" and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and "a \<in> el P" and "le P (f \<star> a) a"
  shows "le P (lfp f) a"
  using  Poset.lfp_def assms inf_is_inf is_inf_def
  by (smt (verit, del_insts) mem_Collect_eq subset_iff)

lemma lfp_greatest :
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap" and a :: "'a"
  assumes P_complete : "is_complete P" and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and "a \<in> el P" and "le P (f \<star> a) a"
shows "(\<And>u . u  \<in> el P \<and> le P (f \<star> u) u \<Longrightarrow> le P a u) \<Longrightarrow> le P a (lfp f)"  
  using assms lfp_def [where ?f=f] inf_is_glb [where ?P=P]
  by (metis (no_types, lifting) mem_Collect_eq subsetI) 

lemma lfp_is_fp :
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap"
  assumes P_complete : "is_complete P" and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
shows "f \<star> (lfp f) = lfp f"
proof -
  define "H" where "H = {x \<in> el (dom f) . le (cod f) (f \<star> x) x}"
  define "a" where "a = inf (cod f) H"
  have "lfp f = a"
    using H_def Poset.lfp_def a_def by blast 
  have "a \<in> el P \<and> f \<star> a \<in> el P"
    by (metis P_complete Poset.fun_app2 \<open>Poset.lfp f = a\<close> f_endo f_valid lfp_is_el)
  moreover have "le P (f \<star> a) a"
    by (smt (verit) H_def P_complete Poset.fun_app2 a_def calculation f_endo f_valid inf_is_glb inf_smaller is_complete_def mem_Collect_eq subset_eq valid_map_monotone valid_transitivity) 
  moreover have "le P  a (f \<star> a)"
  proof -
    have "le P (f \<star> (f \<star> a)) (f \<star> a)"
      by (metis calculation(1) calculation(2) f_endo f_valid valid_map_monotone) 
    moreover have  "f \<star> a \<in> H"
      by (simp add: H_def \<open>a \<in> el P \<and> f \<star> a \<in> el P\<close> calculation f_endo) 
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) H_def P_complete a_def f_endo inf_is_inf is_inf_def mem_Collect_eq subset_eq) 
  qed
  ultimately show ?thesis
    by (metis P_complete \<open>Poset.lfp f = a\<close> is_complete_def valid_antisymmetry) 
qed

lemma lfp_unfold :
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap"
  assumes P_complete : "is_complete P" and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  shows "f \<star> (lfp f) = lfp f"
  using P_complete f_endo f_valid lfp_is_fp by blast

lemma lfp_const :
  fixes P :: "'a Poset" and a :: "'a"
  assumes P_complete : "is_complete P"
  and "a \<in> el P"
  shows "lfp (const P P a) = a"
  by (metis P_complete Poset.const_app Poset.const_cod Poset.const_dom Poset.const_valid Poset.lfp_unfold assms(2) is_complete_def lfp_is_el) 

lemma lfp_eqI :
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap" and a :: "'a"
  assumes P_complete : "is_complete P" and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and a_el : "a \<in> el P" and fp : "f \<star> a = a" and "\<And>b. b \<in> el P \<and>  f \<star> b = b \<Longrightarrow> le P a b" 
  shows "lfp f = a"
  by (metis P_complete Poset.lfp_lowerbound Poset.lfp_unfold a_el assms(6) f_endo f_valid fp is_complete_def lfp_is_el valid_antisymmetry)

lemma lfp_induct :
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap" and a :: "'a"
  assumes P_complete : "is_complete P" and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and a_el : "a \<in> el P"
  and ind : "le P (f \<star> (meet P (lfp f) a)) a"
shows "le P (lfp f) a"
  by (smt (verit) P_complete Poset.fun_app2 Poset.lfp_lowerbound Poset.lfp_unfold a_el f_endo f_valid ind is_complete_def lfp_is_el meet_el meet_property meet_smaller valid_map_monotone valid_transitivity)

(* Greatest fixed point *)

definition gfp :: "('a , 'a) PosetMap \<Rightarrow> 'a" where
"gfp f \<equiv> sup (cod f) {a \<in> el (dom f) . le (cod f) a (f \<star> a)}" 

lemma gfp_is_el : "is_cocomplete P \<Longrightarrow> valid_map f \<Longrightarrow> dom f = P \<Longrightarrow> cod f = P \<Longrightarrow> gfp f \<in> el P"
  by (simp add: Poset.gfp_def sup_el)

(* Fusion *)

lemma right_subfusion : 
  fixes P :: "'a Poset" and f g h :: "('a, 'a) PosetMap" 
  assumes P_complete : "is_complete P" 
  and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and g_valid : "valid_map g" and g_endo : "dom g = P \<and> cod g = P"
  and h_valid : "valid_map h" and h_endo : "dom h = P \<and> cod h = P"
  and fg_le_gh : "\<And> a. a \<in> el P \<Longrightarrow> le P ((f \<diamondop> g) \<star> a) ((g \<diamondop> h) \<star> a)" 
shows "le P (lfp f) (g \<star> (lfp h))"
  by (metis (no_types, lifting) P_complete Poset.compose_app_assoc Poset.fun_app2 Poset.lfp_lowerbound Poset.lfp_unfold f_endo f_valid fg_le_gh g_endo g_valid h_endo h_valid lfp_is_el) 

lemma left_subfusion :
  fixes P :: "'a Poset" and f g h :: "('a, 'a) PosetMap" 
  assumes P_complete : "is_cocomplete P" 
  and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and g_valid : "valid_map g" and g_endo : "dom g = P \<and> cod g = P"
  and h_valid : "valid_map h" and h_endo : "dom h = P \<and> cod h = P"
  and fg_le_gh : "\<And> a. a \<in> el P \<Longrightarrow> le P ((f \<diamondop> g) \<star> a) ((h \<diamondop> f) \<star> a)" 
  and f_cont : "\<And> A . A \<subseteq> el P \<Longrightarrow> f \<star> (sup P A) = sup P {f \<star> a | a . a \<in> A}"
shows "le P (f \<star> (lfp g)) (lfp h)"
  oops

lemma fusion : 
  fixes P :: "'a Poset" and f g h :: "('a, 'a) PosetMap" 
  assumes P_complete : "is_complete P" 
  and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and g_valid : "valid_map g" and g_endo : "dom g = P \<and> cod g = P"
  and h_valid : "valid_map h" and h_endo : "dom h = P \<and> cod h = P"
  and fg_eq_gh : "\<And> a. a \<in> el P \<Longrightarrow> ((f \<diamondop> g) \<star> a) = ((h \<diamondop> f) \<star> a)" 
  and f_cont : "\<And> A . A \<subseteq> el P \<Longrightarrow> f \<star> (sup P A) = sup P {f \<star> a | a . a \<in> A}"
shows "(f \<star> (lfp g)) = (lfp h)" 
  oops

(* Kleene *)

primrec iter :: "('a, 'a) PosetMap \<Rightarrow> nat \<Rightarrow> ('a, 'a) PosetMap" where
  "iter f 0 = ident (dom f)" 
| "iter f (Suc n) = f \<diamondop> (iter f n)"

lemma cod_iter :  "valid_map f \<Longrightarrow> dom f = cod f \<Longrightarrow> cod (iter f n) = cod f"
  apply (induct n)
   apply simp
  by fastforce

lemma dom_iter :  "valid_map f \<Longrightarrow> dom f = cod f \<Longrightarrow> dom (iter f n) = dom f"
  apply (induct n)
   apply simp
  by (simp add: cod_iter)

lemma iter_valid : "valid_map f \<Longrightarrow> dom f = cod f \<Longrightarrow> valid_map (iter f n)"
  apply (induct n)
   apply simp
  using Poset.ident_valid valid_map_welldefined_cod apply blast
  by (simp add: Poset.compose_valid cod_iter)

lemma iter_el : "valid_map f \<Longrightarrow> dom f = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> (iter f n) \<star> a \<in> el (dom f)"
  by (metis Poset.fun_app2 cod_iter dom_iter iter_valid) 

lemma iter_app : "valid_map f \<Longrightarrow> dom f = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> f \<star> ((iter f n) \<star> a) = iter f (n + 1) \<star> a"
  by (simp add: Poset.compose_app_assoc cod_iter dom_iter iter_valid) 

(* Todo: weaken precondition to preservation of directed suprema (Scott-continuous) *)
lemma kleene_lfp : 
  fixes P :: "'a Poset" and f :: "('a, 'a) PosetMap"
  assumes P_complete : "is_complete P" 
  and f_valid : "valid_map f" and f_endo : "dom f = P \<and> cod f = P"
  and f_cont : "\<And> A . A \<subseteq> el P \<Longrightarrow> A \<noteq> {} \<Longrightarrow>  f \<star> (sup P A) = sup P {f \<star> a | a . a \<in> A}"
shows "lfp f = sup P { (iter f n) \<star> (bot P) | n . n \<in> UNIV }" 
proof -
  define "U" where "U = { (iter f n) \<star> (bot P) | n . n \<in> UNIV }"
  have "U \<noteq> {}" using U_def
    by blast 
  moreover have "lfp f \<in> el P"
    using P_complete f_endo f_valid lfp_is_el by blast 
  moreover have "sup P U \<in> el P"
    by (smt (verit, best) P_complete U_def bot_def complete_equiv_cocomplete empty_def f_endo f_valid iter_el mem_Collect_eq subset_iff sup_el) 
  moreover have "le P (lfp f) (sup P U)" 
  proof -
    have "f \<star> (sup P U) = sup P {f \<star> u | u. u \<in> U}"
      by (smt (verit, ccfv_SIG) Collect_cong P_complete U_def bot_def calculation(1) complete_equiv_cocomplete empty_subsetI f_cont f_endo f_valid is_cocomplete_def iter_el mem_Collect_eq subsetI) 
    moreover have "{f \<star> u | u. u \<in> U} \<subseteq> U"
    proof 
      fix x
      assume "x \<in> {f \<star> u |u. u \<in> U}" 
      then have "\<exists> n . x = iter f n \<star> bot P"
        by (smt (verit) P_complete U_def bot_as_inf dual_order.refl f_endo f_valid is_complete_def iter_app mem_Collect_eq) 
      thus "x \<in> U"
        using U_def by blast 
    qed
    moreover have "le P (sup P {f \<star> u | u. u \<in> U}) (sup P U)" using U_def sup_mono [where ?P=P and ?U="{f \<star> u | u. u \<in> U}" and ?V=U] complete_equiv_cocomplete [where ?P=P]
      by (smt (verit) P_complete bot_as_inf calculation(2) f_endo f_valid inf_el iter_el mem_Collect_eq subsetD subsetI)
    moreover have "le P (f \<star> (meet P (lfp f) (sup P U))) (sup P U)"
      by (smt (verit) P_complete Poset.fun_app2 \<open>Poset.lfp f \<in> el P\<close> \<open>Poset.sup P U \<in> el P\<close> calculation(1) calculation(3) f_endo f_valid is_complete_def meet_el meet_smaller2 valid_map_monotone valid_transitivity) 
    ultimately show ?thesis
      using P_complete Poset.lfp_induct \<open>Poset.sup P U \<in> el P\<close> f_endo f_valid by fastforce  
  qed
moreover have "le P (sup P U) (lfp f)"
  proof -
    have "\<And> n . le P ((iter f n) \<star> (bot P)) (lfp f)"  
      apply (induct_tac n)
      apply (metis P_complete Poset.ident_app Poset.iter.simps(1) bot_as_inf bot_min calculation(2) complete_equiv_cocomplete f_endo is_complete_def set_eq_subset)
      by (smt (verit) P_complete Poset.compose_app_assoc Poset.fun_app2 Poset.iter.simps(2) Poset.lfp_unfold bot_as_inf calculation(2) cod_iter dom_iter f_endo f_valid inf_el iter_valid subset_eq valid_map_monotone) 
    moreover have "\<And> a . a \<in> U \<Longrightarrow> le P a (lfp f)"
      using U_def calculation by blast 
    thus ?thesis using sup_is_lub [where ?P=P and ?U=U and ?z="Poset.lfp f"]
      by (smt (verit, best) P_complete U_def \<open>Poset.lfp f \<in> el P\<close> bot_def complete_equiv_cocomplete empty_subsetI f_endo f_valid iter_el mem_Collect_eq subset_iff sup_el) 
  qed
  ultimately show ?thesis
    using P_complete U_def \<open>Poset.sup P U \<in> el P\<close> is_complete_def valid_antisymmetry by fastforce
qed

(* Powerset *)

definition powerset :: "'a set \<Rightarrow> ('a set) Poset" where
"powerset X \<equiv> \<lparr> el = Pow X, le_rel = {(U, V). U \<in> Pow X \<and> V \<in> Pow X \<and> U \<subseteq> V} \<rparr>"

lemma powerset_valid : "valid (powerset A)"
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD case_prodI dual_order.refl fst_conv mem_Collect_eq order_trans powerset_def snd_conv subset_antisym valid_def)

lemma powerset_le : "a \<in> el (powerset A) \<Longrightarrow> a' \<in> el (powerset A) \<Longrightarrow> le (powerset A) a a' = (a \<subseteq> a')"
  by (simp add: powerset_def)

lemma powerset_el : "(a \<in> el (powerset A)) = (a \<subseteq> A)"
  by (simp add: powerset_def)

lemma powerset_is_complete : "is_complete (powerset X)" 
proof (simp add: is_complete_def, rule conjI[rotated],rule allI, rule impI, goal_cases )
  case (1 U)
  then show ?case 
proof -
    assume "U \<subseteq> el (powerset X)"
    define "i" where "i = (if U = {} then X else \<Inter> U)"
    have "is_inf (powerset X) U i" 
    proof (simp add: is_inf_def, safe, goal_cases)
      case (1 x)
      then show ?case
        using \<open>U \<subseteq> el (powerset X)\<close> by blast 
    next
      case 2
      then show ?case
        by (metis Inter_subset \<open>U \<subseteq> el (powerset X)\<close> i_def in_mono order_refl powerset_el) 
    next
      case (3 u)
      then show ?case
        by (metis Inter_lower equals0D i_def powerset_le) 
    next
      case (4 u)
      then show ?case
        by (metis Inf_lower \<open>U \<subseteq> el (powerset X)\<close> dual_order.trans empty_iff i_def in_mono powerset_el) 
    next
      case (5 u)
      then show ?case
        using \<open>U \<subseteq> el (powerset X)\<close> by blast 
    next
      case (6 z)
      then show ?case
        by (metis Inf_greatest \<open>U \<subseteq> el (powerset X)\<close> i_def powerset_el powerset_le subsetD) 
    next
      case (7 z)
      then show ?case
        by (metis Inter_subset \<open>U \<subseteq> el (powerset X)\<close> i_def powerset_el subset_iff) 
    qed
    moreover have "\<exists>i. is_inf (powerset X) U i"
      using calculation by blast 
    moreover have "Poset.inf (powerset X) U \<in> el (powerset X)"
      by (smt (verit, best) calculation(2) inf_def is_inf_def someI_ex)  
    ultimately show ?thesis
      by auto 
  qed
next
  case 2
  then show ?case
    by (simp add: powerset_valid) 
qed

(* Direct image *)

definition direct_image :: "('x, 'y) Function \<Rightarrow> ('x set, 'y set) PosetMap" where
"direct_image f \<equiv> \<lparr>
        dom = powerset (Function.dom f),
        cod = powerset (Function.cod f),
        func = {(a, {f \<cdot> x | x . x \<in> a}) | a . a \<subseteq> Function.dom f}
 \<rparr>"

lemma direct_image_dom : "dom (direct_image f) = powerset (Function.dom f)"
  by (simp add: direct_image_def)

lemma direct_image_cod : "cod (direct_image f) = powerset (Function.cod f)"
  by (simp add: direct_image_def)

lemma direct_image_app : "Function.valid_map f \<Longrightarrow> a \<subseteq> Function.dom f \<Longrightarrow> (direct_image f) \<star> a = {f \<cdot> x | x . x \<in> a}"
  unfolding Function.valid_map_def app_def direct_image_def
  apply (simp add: Let_def)
  by (simp add: powerset_def)

lemma direct_image_mono_raw: "Function.valid_map f \<Longrightarrow> a \<subseteq> Function.dom f \<Longrightarrow> a' \<subseteq> Function.dom f
 \<Longrightarrow> a \<subseteq> a' \<Longrightarrow> (direct_image f) \<star> a \<subseteq> (direct_image f) \<star> a'"
  unfolding Function.valid_map_def app_def direct_image_def
  apply (simp add: Let_def)
  by (smt (verit, del_insts) Collect_mono_iff Poset.Poset.select_convs(1) PowI powerset_def subset_eq)

lemma direct_image_valid :
  fixes f :: "('x, 'y) Function"
  assumes f_valid : "Function.valid_map f"
  shows "valid_map (direct_image f)"
proof (intro valid_mapI, safe, goal_cases)
  case 1
  then show ?case
    by (simp add: direct_image_dom powerset_valid) 
next
  case 2
  then show ?case
    by (simp add: direct_image_cod powerset_valid) 
next
  case (3 a b)
  then show ?case
    by (simp add: direct_image_def powerset_def) 
next
  case (4 a b)
  then show ?case
    by (smt (verit) Function.fun_app2 Poset.Poset.select_convs(1) PosetMap.select_convs(3) PowI direct_image_cod direct_image_def f_valid mem_Collect_eq powerset_def snd_conv subset_eq) 
next
  case (5 a b b' x)
  then show ?case
    by (simp add: direct_image_def) 
next
  case (6 a b b' x)
  then show ?case
    by (smt (z3) CollectD PosetMap.select_convs(3) direct_image_def fst_conv snd_conv) 
next
  case (7 a)
  then show ?case
    by (simp add: direct_image_def powerset_def) 
next
  case (8 a a')
  then show ?case 
  proof -
    fix a a'
    assume "a \<in> el (PosetMap.dom (direct_image f))"
    assume "a'\<in> el (PosetMap.dom (direct_image f))"
    assume "le (PosetMap.dom (direct_image f)) a a'"

    have "(direct_image f) \<star> a = {f \<cdot> x | x . x \<in> a}" using direct_image_def [where ?f=f] app_def
        [where ?f="direct_image f" and ?a=a]
      by (smt (verit) Collect_cong \<open>a \<in> el (PosetMap.dom (direct_image f))\<close> direct_image_app direct_image_dom f_valid powerset_el)

    moreover have "(direct_image f) \<star> a' = {f \<cdot> x | x . x \<in> a'}" using direct_image_def [where ?f=f] app_def
        [where ?f="direct_image f" and ?a=a']
      by (smt (verit) Collect_cong PosetMap.select_convs(1) \<open>a' \<in> el (PosetMap.dom (direct_image f))\<close> direct_image_app f_valid powerset_el)

    moreover have "{f \<cdot> x | x . x \<in> a} \<subseteq> {f \<cdot> x | x . x \<in> a'}" using direct_image_def [where ?f=f]
        calculation
      by (smt (verit) Poset.Poset.select_convs(2) Pow_iff \<open>a \<in> el (PosetMap.dom (direct_image f))\<close> \<open>a' \<in> el (PosetMap.dom (direct_image f))\<close> \<open>le (PosetMap.dom (direct_image f)) a a'\<close> case_prod_unfold direct_image_dom direct_image_mono_raw f_valid fst_conv mem_Collect_eq powerset_def snd_conv)

    ultimately show "le (PosetMap.cod (direct_image f)) (direct_image f \<star> a) (direct_image f \<star>
      a')" using direct_image_def [where ?f=f] powerset_def [where ?X="Function.cod f"]
      by (smt (verit) Function.fun_app2 Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) PosetMap.select_convs(1) PosetMap.select_convs(2) Pow_iff \<open>a' \<in> el (PosetMap.dom (direct_image f))\<close> case_prodI f_valid mem_Collect_eq powerset_def subsetD subsetI)
  qed
qed

lemma direct_image_mono:
  fixes f :: "('a, 'b) Function" and a a' :: "'a set"
  defines "pf \<equiv> direct_image f"
  assumes f_valid : "Function.valid_map f"
  and a_el : "a \<in> el (dom pf)" and a'_el : "a' \<in> el (dom pf)" and a_le_a' : "le (dom pf) a a'"
shows "le (cod pf) (pf \<star> a) (pf \<star> a')"
  by (metis a'_el a_el a_le_a' direct_image_valid f_valid pf_def valid_map_monotone)

lemma direct_image_ident : "direct_image (Function.ident X) = ident (powerset X)"
proof -
  fix X :: "'x set"
  have " {(p, p) |p . p \<subseteq> X} =  Id_on (Pow X)" using Id_on_def [where ?A="Pow X"]   Pow_def
      [where ?A=X] set_eqI [where ?A="Id_on (Pow X)" and ?B="{(p, p) |p. p \<subseteq> X}"]
    by blast
  moreover have "func (ident (powerset X)) = {(p, p) |p . p \<subseteq> X}"
    by (simp add: Poset.ident_def calculation powerset_def)
  moreover have "dom (direct_image (Function.ident X)) = powerset X"
    by (simp add: direct_image_dom)
  moreover have "cod (direct_image (Function.ident X)) = powerset X"
    by (simp add: Function.ident_def direct_image_cod)

  moreover have "\<forall> p . p \<subseteq> X \<longrightarrow> {Function.ident X \<cdot> x |x. x \<in> p} = p" using Function.ident_app [where
        ?X=X]
    by (smt (verit, ccfv_threshold) Collect_cong Collect_mem_eq in_mono)
  moreover have "func (direct_image (Function.ident X)) = {(p, p) |p . p \<subseteq> X}" using calculation
      direct_image_def
    [where ?f="Function.ident X"] Function.ident_app [where ?X=X]
    by force
   ultimately show "direct_image (Function.ident X) = ident (powerset X)"
     by (simp add: Poset.ident_def)
 qed

lemma direct_image_trans :
  fixes g :: "('y, 'z) Function" and f :: "('x , 'y) Function"
  assumes f_valid : "Function.valid_map f"
  and g_valid : "Function.valid_map g"
  and cod_eq_dom : "Function.cod f = Function.dom g"
shows "direct_image g \<diamondop> direct_image f = direct_image (g \<bullet> f)"
proof (rule fun_ext, goal_cases)
  case 1
  then show ?case
    by (simp add: Poset.compose_valid cod_eq_dom direct_image_cod direct_image_dom direct_image_valid f_valid g_valid) 
next
  case 2
  then show ?case
    using Function.compose_valid cod_eq_dom direct_image_valid f_valid g_valid by blast 
next
  case 3
  then show ?case
    by (simp add: cod_eq_dom direct_image_cod direct_image_dom direct_image_valid f_valid g_valid) 
next
  case 4
  then show ?case
    by (simp add: cod_eq_dom  direct_image_cod direct_image_dom direct_image_valid f_valid g_valid)
next
  case (5 a)
  then show ?case 
    proof -
    fix a
    assume "a \<in> el (PosetMap.dom (direct_image g \<diamondop> direct_image f))"
    have "a \<subseteq> Function.dom f"
      by (metis Poset.dom_compose \<open>a \<in> el (PosetMap.dom (direct_image g \<diamondop> direct_image f))\<close> cod_eq_dom direct_image_cod direct_image_dom  powerset_el)
    have "(a, {f \<cdot> x |x. x \<in> a}) \<in> {(b, {f \<cdot> x |x. x \<in> b}) |b. b \<subseteq> Function.dom f} "
      using \<open>a \<subseteq> Function.dom f\<close> by blast
    moreover have "{f \<cdot> x |x. x \<in> a} \<subseteq> Function.cod f"
      using Function.fun_app2 \<open>a \<subseteq> Function.dom f\<close> f_valid by fastforce
    moreover have "({f \<cdot> x |x. x \<in> a}, {g \<cdot> (f \<cdot> x) |x. x \<in> a}) \<in> {(b, {g \<cdot> x |x. x \<in> b}) |b. b \<subseteq>
      Function.cod f}"
      using calculation(2) by blast
    moreover have "(a, {g \<cdot> (f \<cdot> x) |x. x \<in> a}) \<in>
  {(p, {f \<cdot> x |x. x \<in> p}) |p. p \<subseteq> Function.dom f} O {(p, {g \<cdot> x |x. x \<in> p}) |p. p  \<subseteq> Function.cod f}"
      using calculation(1) calculation(3) by auto
    ultimately show "(direct_image g \<diamondop> direct_image f) \<star> a = direct_image (g \<bullet> f) \<star> a"
      by (smt (verit) CollectD Collect_cong Function.compose_app_assoc Function.compose_valid Function.dom_compose Poset.compose_app_assoc cod_eq_dom direct_image_app direct_image_cod direct_image_dom direct_image_valid f_valid fst_conv g_valid powerset_el snd_conv subsetD)
  qed
qed

lemma surj_imp_direct_image_surj :
  fixes f :: "('a, 'b) Function"
  assumes f_valid : "Function.valid_map f"
  and f_surj : "Function.is_surjective f"
shows "Poset.is_surjective (direct_image f)"
  unfolding is_surjective_def
proof safe
  fix b
  define "X" where "X = Function.dom f"
  define "Y" where "Y = Function.cod f"

  assume "b \<in> el (PosetMap.cod (direct_image f))"
  have "b \<subseteq> Y"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) PowD Y_def \<open>b \<in> el (PosetMap.cod (direct_image f))\<close> direct_image_cod powerset_def)
  moreover have "\<forall> y \<in> b . (\<exists> x . x \<in> X \<and> f \<cdot> x = y)"
    by (metis Function.is_surjective_def X_def Y_def calculation f_surj subsetD)
  define "pre" where "pre = (\<lambda> y. (SOME x. (y \<in> b) \<longrightarrow> (f \<cdot> x = y \<and> x \<in> X) ))"
  moreover have "\<forall> y . (y \<in> b \<longrightarrow> f \<cdot> (pre y) = y)"
    by (smt (verit, best) \<open>\<forall>y\<in>b. \<exists>x. x \<in> X \<and> f \<cdot> x = y\<close> pre_def someI_ex)
  moreover have "\<forall> y . y \<in> b \<longrightarrow> pre y \<in> X"
    by (smt (verit) \<open>\<forall>y\<in>b. \<exists>x. x \<in> X \<and> f \<cdot> x = y\<close> pre_def someI)
  define "a" where "a = { pre y | y . y \<in> b }"
  moreover have "a \<subseteq> X"
    using \<open>\<forall>y. y \<in> b \<longrightarrow> pre y \<in> X\<close> a_def by fastforce
  moreover have "a \<in> el (PosetMap.dom (direct_image f))"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) PowI X_def calculation(5) direct_image_dom powerset_def)
  moreover have "\<forall> y . (y \<in> b \<longrightarrow> ( y = f \<cdot>  (pre y)))" using calculation
  by presburger
  moreover have "\<forall> y . (y \<in> b \<longrightarrow> (\<exists> x \<in> a . y = f \<cdot> x))" using calculation
    by blast
  moreover have "((\<cdot>) f) ` a = b" using a_def pre_def using calculation
    by (smt (verit, ccfv_threshold) image_Collect_subsetI image_iff subsetI subset_antisym)
  show "\<exists>a. a \<in> el (PosetMap.dom (direct_image f)) \<and> direct_image f \<star> a = b"
    by (metis Setcompr_eq_image X_def \<open>(\<cdot>) f ` a = b\<close> calculation(5) calculation(6) direct_image_app f_valid)
  qed

lemma fibre_from_image :
  fixes f :: "('a, 'b) Function" and a :: "'a set"
  assumes f_valid : "Function.valid_map f"
  and a_el : "a \<subseteq> Function.dom f"
  and t_el : "t \<in> (direct_image f) \<star> a"
  shows "\<exists> t' . t' \<in> a \<and> f \<cdot> t' = t"
  using a_el direct_image_app f_valid t_el by fastforce

(* Preimage *)

definition preimage :: "('x, 'y) Function \<Rightarrow> ('y set, 'x set) PosetMap" where
"preimage f \<equiv> \<lparr>
        dom = powerset (Function.cod f),
        cod = powerset (Function.dom f),
        func = {(b, {x \<in> Function.dom f . f \<cdot> x \<in> b}) | b . b \<subseteq> Function.cod f} 
 \<rparr>"

lemma preimage_dom : "dom (preimage f) = powerset (Function.cod f)"
  by (simp add: preimage_def)

lemma preimage_cod : "cod (preimage f) = powerset (Function.dom f)"
  by (simp add: preimage_def)

lemma preimage_app : "Function.valid_map f \<Longrightarrow> b \<subseteq> Function.cod f \<Longrightarrow> (preimage f) \<star> b = {x . x \<in> Function.dom f \<and> f \<cdot> x \<in> b}"
  unfolding Function.valid_map_def app_def preimage_def
  by (simp add: powerset_el)

lemma preimage_mono_raw: "Function.valid_map f \<Longrightarrow> b \<subseteq> Function.cod f \<Longrightarrow> b' \<subseteq> Function.cod f
 \<Longrightarrow> b \<subseteq> b' \<Longrightarrow> (preimage f) \<star> b \<subseteq> (preimage f) \<star> b'"
  using preimage_app by fastforce

(* Example debug with bad definition of preimage: *)
(*
definition preimage :: "('x, 'y) Function \<Rightarrow> ('y set, 'x set) PosetMap" where
"preimage f \<equiv> \<lparr>
        dom = powerset (Function.cod f),
        cod = powerset (Function.dom f),
        func = {(b, {x . f \<cdot> x \<in> b}) | b . b \<subseteq> Function.cod f} 
 \<rparr>"

lemma debug :
  fixes f :: "('x, 'y) Function"
  assumes f_valid : "Function.valid_map f"
  assumes def : "f = \<lparr>Function.cod = {y\<^sub>1}, func = {}\<rparr>"
  shows "\<And> a b . (a, b) \<in> func (preimage f) \<Longrightarrow> b \<in> el (cod (preimage f))"
  apply (simp add: def)
  unfolding preimage_def
  apply clarsimp
  unfolding Function.app_def
  apply clarsimp
  unfolding powerset_def
  apply clarsimp
  unfolding Function.dom_def
  apply clarsimp
*)

lemma preimage_valid :
  fixes f :: "('x, 'y) Function"
  assumes f_valid : "Function.valid_map f"
  shows "valid_map (preimage f)"
proof (intro valid_mapI, safe, goal_cases)
  case 1
  then show ?case
    by (simp add: preimage_dom powerset_valid) 
next
  case 2
  then show ?case
    by (simp add: preimage_cod powerset_valid) 
next
  case (3 b a)
  then show ?case
    by (simp add: preimage_def powerset_def) 
next
  case (4 b a)
  then show ?case
    by (simp add: powerset_def preimage_def) 
next
  case (5 b a a' x)
  then show ?case
    by (smt (verit) CollectD PosetMap.select_convs(3) fst_conv preimage_def snd_conv)
next
  case (6 b a a' x)
  then show ?case
    by (smt (z3) CollectD PosetMap.select_convs(3) preimage_def fst_conv snd_conv) 
next
  case (7 b)
  then show ?case
    by (simp add: preimage_def powerset_def) 
next
  case (8 b b')
  then show ?case 
  proof -
    fix b b'
    assume "b \<in> el (PosetMap.dom (preimage f))"
    assume "b'\<in> el (PosetMap.dom (preimage f))"
    assume "le (PosetMap.dom (preimage f)) b b'"

    have "(preimage f) \<star> b = {x . x \<in> Function.dom f \<and> f \<cdot> x \<in> b}" using preimage_def [where ?f=f] app_def
        [where ?f="preimage f" and ?a=b]
      by (smt (verit, best) Collect_cong PosetMap.select_convs(1) \<open>b \<in> el (PosetMap.dom (preimage f))\<close> f_valid powerset_el preimage_app)
    moreover have "(preimage f) \<star> b' = {x . x \<in> Function.dom f \<and> f \<cdot> x \<in> b'}" using preimage_def [where ?f=f] app_def
        [where ?f="preimage f" and ?a=b']
      by (smt (verit) Collect_cong PosetMap.select_convs(1) \<open>b' \<in> el (PosetMap.dom (preimage f))\<close> f_valid powerset_el preimage_app)
    moreover have "{x . x \<in> Function.dom f \<and> f \<cdot> x \<in> b} \<subseteq> {x . x \<in> Function.dom f \<and> f \<cdot> x \<in> b'}" using preimage_def [where ?f=f]
        calculation
      using \<open>b \<in> el (PosetMap.dom (preimage f))\<close> \<open>b' \<in> el (PosetMap.dom (preimage f))\<close> \<open>le (PosetMap.dom (preimage f)) b b'\<close> powerset_le by fastforce
    ultimately show "le (PosetMap.dom (preimage f)) b b' \<Longrightarrow> le (PosetMap.cod (preimage f)) (preimage f \<star> b) (preimage f \<star> b')"
      by (simp add: powerset_def preimage_cod) 
  qed
qed

lemma preimage_mono:
  fixes f :: "('a, 'b) Function" and b b' :: "'b set"
  defines "pf \<equiv> preimage f"
  assumes f_valid : "Function.valid_map f"
  and b_el : "b \<in> el (dom pf)" and b'_el : "b' \<in> el (dom pf)" and b_le_b' : "le (dom pf) b b'"
shows "le (cod pf) (pf \<star> b) (pf \<star> b')"
  by (metis b'_el b_el b_le_b' f_valid pf_def preimage_valid valid_map_monotone)

lemma preimage_ident : "preimage (Function.ident X) = ident (powerset X)"
proof -
  fix X :: "'x set"
  have " {(p, p) |p . p \<subseteq> X} =  Id_on (Pow X)" using Id_on_def [where ?A="Pow X"]   Pow_def
      [where ?A=X] set_eqI [where ?A="Id_on (Pow X)" and ?B="{(p, p) |p. p \<subseteq> X}"]
    by blast
  moreover have "func (ident (powerset X)) = {(p, p) |p . p \<subseteq> X}"
    by (simp add: Poset.ident_def calculation powerset_def)
  moreover have "dom (preimage (Function.ident X)) = powerset X"
    by (simp add: preimage_dom)
  moreover have "cod (preimage (Function.ident X)) = powerset X"
    by (simp add: preimage_cod)
  moreover have "\<forall> p . p \<subseteq> X \<longrightarrow> {x . x \<in> X \<and> Function.ident X \<cdot> x \<in> p} = p" using Function.ident_app [where
        ?X=X]
    by force
  moreover have "func (preimage (Function.ident X)) = {(p, p) |p . p \<subseteq> X}" using calculation
      preimage_def
    [where ?f="Function.ident X"] Function.ident_app [where ?X=X]
    by force
   ultimately show "preimage (Function.ident X) = ident (powerset X)"
     by (simp add: Poset.ident_def)
 qed

lemma preimage_trans :
  fixes g :: "('y, 'z) Function" and f :: "('x , 'y) Function"
  assumes f_valid : "Function.valid_map f"
  and g_valid : "Function.valid_map g"
  and cod_eq_dom : "Function.cod f = Function.dom g"
shows "preimage f \<diamondop> preimage g = preimage (g \<bullet> f)"
proof (rule fun_ext, goal_cases)
  case 1
  then show ?case
    by (simp add: Poset.compose_valid cod_eq_dom preimage_cod preimage_dom preimage_valid f_valid g_valid) 
next
  case 2
  then show ?case
    using Function.compose_valid cod_eq_dom preimage_valid f_valid g_valid by blast 
next
  case 3
  then show ?case
    by (simp add: cod_eq_dom preimage_cod preimage_dom preimage_valid f_valid g_valid) 
next
  case 4
  then show ?case
    by (simp add: cod_eq_dom  preimage_cod preimage_dom preimage_valid f_valid g_valid)
next
  case (5 c)
  then show ?case
    oops

(* Intersection and union as poset maps *)

definition intersection ::  "'x set \<Rightarrow> ('x set \<times> 'x set, 'x set) PosetMap" where
"intersection X \<equiv> 
   \<lparr> dom = powerset X \<times>\<times> powerset X, 
     cod = powerset X, 
     func = {((a, b), a \<inter> b) | a b . (a, b) \<in> el (powerset X \<times>\<times> powerset X)} \<rparr>" 

lemma intersection_valid : "valid_map (intersection X)" 
  unfolding intersection_def 
  apply (intro valid_mapI)
       apply clarsimp
  apply (simp add: powerset_valid product_valid)
  apply (simp add: powerset_valid)
     apply (smt (verit) CollectD Int_commute PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) fst_conv inf.absorb_iff2 inf_left_commute powerset_el product_el_1 snd_conv)
  apply fastforce
   apply fastforce
  apply (simp add: powerset_def product_def app_def)
  by auto

definition union ::  "'x set \<Rightarrow> ('x set \<times> 'x set, 'x set) PosetMap" where
"union X \<equiv> 
   \<lparr> dom = powerset X \<times>\<times> powerset X, 
     cod = powerset X, 
     func = {((a, b), a \<union> b) | a b . (a, b) \<in> el (powerset X \<times>\<times> powerset X)} \<rparr>" 

lemma union_valid : "valid_map (union X)" 
  unfolding union_def 
  apply (intro valid_mapI)
       apply clarsimp
  apply (simp add: powerset_valid product_valid)
  apply (simp add: powerset_valid)
  apply (smt (verit, ccfv_SIG) CollectD PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) Un_subset_iff fst_conv powerset_el product_el_1 product_el_2 snd_conv)
  apply fastforce
   apply fastforce
  apply (simp add: powerset_def product_def app_def)
  by auto

(* Forgetful functor from Pos to Set *)

definition forget_map ::  "('a, 'b) PosetMap \<Rightarrow> ('a, 'b) Function" where
"forget_map f \<equiv> \<lparr> Function.cod = el (cod f), func = func f \<rparr>" 

lemma forget_map_valid : "valid_map f \<Longrightarrow> Function.valid_map (forget_map f)"
  unfolding valid_map_def forget_map_def
  apply (simp add:Let_def)
  by (smt (verit) CollectD Function.dom_def Function.select_convs(1) Function.select_convs(2) Function.valid_map_def) 


(* Examples *)

definition naturals :: "nat Poset" where
  "naturals \<equiv> \<lparr> el = UNIV , le_rel = {(x,y). x \<le> y} \<rparr>"

lemma naturals_valid : "valid naturals"
  by (smt (verit, best) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD UNIV_I case_prodI naturals_def fst_conv linorder_linear mem_Collect_eq order_antisym order_trans snd_conv validI)

definition divisibility :: "nat Poset" where
  "divisibility \<equiv> \<lparr> el = UNIV , le_rel = {(x,y). x dvd y } \<rparr>"

lemma divisibility_valid : "valid divisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD UNIV_I case_prodI dvd_antisym divisibility_def fst_conv gcd_nat.refl gcd_nat.trans mem_Collect_eq snd_conv valid_def)

end
