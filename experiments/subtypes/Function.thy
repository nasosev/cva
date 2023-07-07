section \<open> Function.thy \<close>

theory Function
  imports Main
begin

(* Types *)

record ('x, 'y) RawFunction =
  raw_cod :: "'y set"
  raw_func :: "('x \<times> 'y) set"

definition raw_dom :: "('x, 'y) RawFunction \<Rightarrow> 'x set" where
 "raw_dom rf \<equiv> {x. \<exists>y. (x, y) \<in> raw_func rf}"

definition valid_map :: "('x, 'y) RawFunction \<Rightarrow> bool" where
"valid_map rf \<equiv>
  let
      welldefined = (\<forall>x y. (x, y) \<in> raw_func rf \<longrightarrow> x \<in> raw_dom rf\<and> y \<in> raw_cod rf);
      deterministic = (\<forall>x y y'. (x, y) \<in> raw_func rf \<and> (x, y') \<in> raw_func rf \<longrightarrow> y = y');
      total = (\<forall>x. x \<in> raw_dom rf \<longrightarrow> (\<exists>y. (x, y) \<in> raw_func rf))

  in welldefined \<and> deterministic \<and> total"

typedef ('x, 'y) Function = "{ rf :: ('x, 'y) RawFunction . valid_map rf}"
proof
  define "empty_function" where "empty_function = \<lparr> raw_cod = {}, raw_func = {} \<rparr>"
  have "valid_map empty_function"
    by (simp add: empty_function_def valid_map_def raw_dom_def)
  thus "empty_function \<in> {rf. valid_map rf}" by auto
qed

(* find_theorems Abs_Function Rep_Function*)

setup_lifting type_definition_Function (* This warning is apparently not a problem. *)

lift_definition cod :: "('x, 'y) Function \<Rightarrow> 'y set" is raw_cod done

lift_definition func :: "('x, 'y) Function \<Rightarrow> ('x \<times> 'y) set" is raw_func done

lift_definition dom :: "('x, 'y) Function \<Rightarrow> 'x set" is raw_dom done

(* Validity *)

lemma welldefined_dom : "(x, y) \<in> func f \<Longrightarrow> x \<in> dom f"
  using dom.rep_eq func.rep_eq raw_dom_def by fastforce 

lemma welldefined_cod : "(x, y) \<in> func f \<Longrightarrow> y \<in> cod f"
  by (transfer, simp add: valid_map_def)

lemma welldefined : "(x, y) \<in> func f \<Longrightarrow> x \<in> dom f \<and> y \<in> cod f"
  by (simp add: welldefined_cod welldefined_dom) 

lemma deterministic : "(x, y) \<in> func f \<Longrightarrow> (x, y') \<in> func f \<Longrightarrow> y = y'"
  using Rep_Function func.rep_eq valid_map_def by fastforce 

lemma total : " x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func f"
  by (simp add: dom.rep_eq func.rep_eq raw_dom_def) 

lemma valid_mapI: "((\<And>x y. (x, y) \<in> raw_func rf \<Longrightarrow>  x \<in> raw_dom rf \<and> y \<in> raw_cod rf) \<Longrightarrow>
                   (\<And>x y y'. (x, y) \<in> raw_func rf \<Longrightarrow> (x, y') \<in> raw_func rf \<Longrightarrow> y = y') \<Longrightarrow>
                   (\<And>x. x \<in> raw_dom rf \<Longrightarrow> (\<exists>y. (x, y) \<in> raw_func rf))
                   \<Longrightarrow> valid_map rf) "
  by (metis valid_map_def)

(* Function application *)

definition "Function_app_undefined_arg_not_in_domain _ \<equiv> undefined"

definition raw_app :: "('x, 'y) RawFunction \<Rightarrow> 'x \<Rightarrow> 'y"  where
"raw_app rf x \<equiv> 
   if x \<in> raw_dom rf
   then  (THE y. (x, y) \<in> raw_func rf)
  else Function_app_undefined_arg_not_in_domain x" 

lift_definition app :: "('x, 'y) Function \<Rightarrow> 'x \<Rightarrow> 'y" (infixr "\<cdot>" 998) is "raw_app"  done

lemma fun_app : "x \<in> dom f \<Longrightarrow> (x, f \<cdot> x) \<in> func f" 
  apply transfer
  by (smt (verit) raw_app_def the_equality valid_map_def)

lemma fun_app2 : "x \<in> dom f \<Longrightarrow> f \<cdot> x  \<in> cod f"
  by (meson fun_app welldefined)

lemma fun_app3 [simp] : "x \<in> dom f \<Longrightarrow> f \<cdot> x = (THE y. (x, y) \<in> func f) "
  by (metis deterministic fun_app the_equality)

lemma fun_ext : "dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> func f = func g"
  unfolding  dom_def
  apply (simp_all add: Let_def, auto)
  apply (metis deterministic dom.rep_eq fun_app welldefined)
  by (metis deterministic dom.rep_eq fun_app welldefined) 

lemma fun_ext2 : "dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> f = g"
  apply (transfer, simp)
  by (metis (full_types) Abs_Function_inverse CollectI app.rep_eq cod.rep_eq dom.rep_eq equality fun_ext func.rep_eq old.unit.exhaust)

lemma fun_app_iff  : "(x, y) \<in> func f \<Longrightarrow> (f \<cdot> x) = y"
  by (meson fun_app deterministic welldefined)

(* Properties *)

abbreviation is_surjective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall> y . y \<in> cod f \<longrightarrow> (\<exists> x . x \<in> dom f \<and> f \<cdot> x = y)"

abbreviation is_injective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall>x x' . x \<in> dom f \<longrightarrow> x' \<in> dom f \<longrightarrow> f \<cdot> x = f \<cdot> x' \<longrightarrow> x = x'"

abbreviation is_bijective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

(* Composition of functions *)

definition "Function_compose_undefined_incomposable _ _ \<equiv> undefined"

definition raw_compose :: "('y, 'z) RawFunction \<Rightarrow> ('x, 'y) RawFunction \<Rightarrow> ('x, 'z) RawFunction" where
  "raw_compose rg rf \<equiv>
    if raw_dom rg = raw_cod rf
    then \<lparr> raw_cod = raw_cod rg, raw_func = relcomp (raw_func rf) (raw_func rg) \<rparr>
    else Rep_Function (Function_compose_undefined_incomposable rg rf)"

lift_definition compose :: "('y, 'z) Function \<Rightarrow> ('x, 'y) Function \<Rightarrow> ('x, 'z) Function" (infixl "\<bullet>"
    55) is raw_compose
proof (intro valid_mapI conjI, goal_cases)
  case (1 g f x y)
  then show ?case
    using raw_dom_def by fastforce 
next
  case (2 g f x y)
  then show ?case
    by (metis cod.rep_eq func.rep_eq raw_compose_def relcompEpair select_convs(1) select_convs(2) valid_map_def welldefined_cod) 
next
  case (3 g f x y y')
  then show ?case
    by (metis (no_types, opaque_lifting) fun_app_iff func.rep_eq raw_compose_def relcompEpair select_convs(2) valid_map_def) 
next
  case (4 g f x)
  then show ?case
    by (simp add: raw_dom_def) 
qed

lemma compose_welldefined_cod : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> y \<in> cod g"
  by (metis (no_types) cod.rep_eq compose.rep_eq dom.rep_eq func.rep_eq raw_compose_def select_convs(1) welldefined_cod)

lemma compose_welldefined_dom : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f"
  apply transfer
  by (metis raw_compose_def relcomp.cases select_convs(2) valid_map_def)

lemma compose_welldefined : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f \<and> y \<in> cod g"
  by (simp add: compose_welldefined_cod compose_welldefined_dom)

lemma compose_deterministic : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> (x, y') \<in> func (g \<bullet> f) \<Longrightarrow> y = y'"
  by (simp add: deterministic)

lemma compose_total : "dom g = cod f \<Longrightarrow> x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func (g \<bullet> f)"
  apply transfer
  by (metis (no_types, lifting) raw_compose_def relcomp.simps select_convs(2) valid_map_def)

lemma cod_compose [simp] : "dom g = cod f \<Longrightarrow> cod (g \<bullet> f) = cod g"
  by (transfer, simp add: raw_compose_def)

lemma dom_compose [simp] : "dom g = cod f \<Longrightarrow> dom (g \<bullet> f) = dom f"
  apply transfer
  by (smt (verit) Collect_cong raw_compose_def raw_dom_def relcomp.simps select_convs(2) valid_map_def)

lemma compose_assoc : "dom h = cod g \<Longrightarrow> dom g = cod f \<Longrightarrow> (h \<bullet> g) \<bullet> f = h \<bullet> (g \<bullet> f)"
  apply (transfer, simp_all add: raw_dom_def valid_map_def raw_compose_def)
  apply (safe, blast, blast, blast)
  by (smt (verit) mem_Collect_eq relcomp.simps)

lemma compose_app [simp] : "(x, y) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow> (y, z) \<in> func g 
 \<Longrightarrow> (g \<bullet> f) \<cdot> x = z"
  apply (rule fun_app_iff, transfer)
  by (simp add: raw_compose_def relcomp.relcompI)

lemma compose_app_assoc : "x \<in> dom f \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<bullet> f) \<cdot> x = g \<cdot> (f \<cdot> x)"
  apply transfer
  unfolding valid_map_def raw_dom_def raw_compose_def raw_app_def
  apply (simp add: Let_def,safe)
     apply (smt (verit, best) relcomp.simps the_equality)
    apply (metis (mono_tags, lifting) theI_unique)
  apply (meson relcomp.relcompI)
  by (metis Function_app_undefined_arg_not_in_domain_def)

lemma surjection_is_right_cancellative : "is_surjective f \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h
 \<Longrightarrow> g \<bullet> f = h \<bullet> f \<Longrightarrow> g = h"
  by (metis cod_compose compose_app_assoc fun_ext2)

lemma injection_is_left_cancellative : "is_injective f \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f 
 \<Longrightarrow> f \<bullet> g = f \<bullet> h \<Longrightarrow> g = h"
  by (metis compose_app_assoc dom_compose fun_app2 fun_ext2) 

(* Identity functions *)

definition raw_ident :: "'x set \<Rightarrow> ('x, 'x) RawFunction" where
"raw_ident X \<equiv>  \<lparr> raw_cod = X, raw_func = Id_on X \<rparr>"

lift_definition ident :: "'x set \<Rightarrow> ('x, 'x) Function" is raw_ident
  by (simp add: Id_on_iff raw_dom_def raw_ident_def valid_map_def) 

lemma ident_dom [simp] : "dom (ident X) = X" 
  by (transfer, simp add: Id_on_iff raw_dom_def raw_ident_def)

lemma ident_cod [simp] : "cod (ident X) = X"
  by (transfer, simp add: raw_ident_def)

lemma ident_app [simp] : "x \<in> X \<Longrightarrow> ident X \<cdot> x = x"
  by (transfer, metis Id_onI app.rep_eq fun_app_iff func.rep_eq ident.rep_eq raw_ident_def select_convs(2))

lemma compose_ident_left [simp] : "ident (cod f) \<bullet> f = f"
  by (smt (verit, ccfv_SIG) cod_compose compose_app_assoc dom_compose fun_app2 fun_ext2 ident_app ident_cod ident_dom)

lemma compose_ident_right [simp] : "f \<bullet> ident (dom f) = f"
  by (smt (verit, ccfv_SIG) cod_compose compose_app_assoc dom_compose fun_app2 fun_ext2 ident_app ident_cod ident_dom)

(* Constant functions *)

definition "Function_const_undefined_arg_not_in_codomain _ \<equiv> undefined"

definition raw_const :: "'x set \<Rightarrow>  'y set  \<Rightarrow> 'y \<Rightarrow>  ('x, 'y) RawFunction" where
"raw_const X Y y \<equiv> 
  if y \<in> Y
  then \<lparr> raw_cod = Y, raw_func = { (x, y) | x. x \<in> X }\<rparr>
  else Rep_Function (Function_const_undefined_arg_not_in_codomain y)" 

lift_definition const :: "'x set \<Rightarrow>  'y set  \<Rightarrow> 'y \<Rightarrow> ('x, 'y) Function" is raw_const
proof (intro valid_mapI, goal_cases)
  case (1 X Y y x ya)
  then show ?case
    by (smt (verit) cod.rep_eq func.rep_eq mem_Collect_eq raw_const_def raw_dom_def select_convs(1) select_convs(2) snd_conv welldefined) 
next
  case (2 X Y y x ya y')
  then show ?case
    by (smt (verit, ccfv_SIG) CollectD deterministic func.rep_eq raw_const_def select_convs(2) snd_conv) 
next
  case (3 X Y y x)
  then show ?case
    by (simp add: raw_dom_def) 
qed

lemma const_dom [simp] : "y \<in> Y \<Longrightarrow> dom (const X Y y) = X"  
  by (transfer, simp add: raw_const_def raw_dom_def)

lemma const_cod [simp] : "y \<in> Y \<Longrightarrow> cod (const X Y y) = Y"
  by (transfer, simp add: raw_const_def)

lemma const_app [simp] : "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> (const X Y y) \<cdot> x = y"
  apply transfer
  by (smt (verit, best) CollectD app.rep_eq const.rep_eq const_dom fun_app func.rep_eq raw_const_def select_convs(2) snd_conv)

lemma const_func : "y \<in> Y \<Longrightarrow> func (const X Y y) = {(x, y) | x . x \<in> X }"
  by (transfer, simp add: raw_const_def)


end
