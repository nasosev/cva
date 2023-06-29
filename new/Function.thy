section \<open> Function.thy \<close>

theory Function
  imports Main

begin

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
  define "rf" where "rf = (\<lparr> raw_cod = {}, raw_func = {} \<rparr> :: ('x,'y) RawFunction)"
  have "valid_map rf"
    by (simp add: rf_def valid_map_def raw_dom_def)
  thus "rf \<in> {rf. valid_map rf}" by auto
qed

(* find_theorems Abs_Function Rep_Function*)

setup_lifting type_definition_Function

lift_definition cod :: "('x, 'y) Function \<Rightarrow> 'y set" is raw_cod done

lift_definition func :: "('x, 'y) Function \<Rightarrow> ('x \<times> 'y) set" is raw_func done

lift_definition dom :: "('x, 'y) Function \<Rightarrow> 'x set" is raw_dom done

(* Validity *)

lemma welldefined_dom : "(x, y) \<in> func f \<Longrightarrow> x \<in> dom f"
  using dom.rep_eq func.rep_eq raw_dom_def by fastforce 

lemma welldefined_cod : "(x, y) \<in> func f \<Longrightarrow> y \<in> cod f"
  apply transfer
  by (simp add: valid_map_def)

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

definition "Function_app_undefined_arg_not_in_domain a \<equiv> undefined"

definition app :: "('x, 'y) Function \<Rightarrow> 'x \<Rightarrow> 'y" (infixr "\<cdot>" 998) where
"app f x \<equiv>
  if x \<in> dom f
   then (THE y. (x, y) \<in> func f)
  else Function_app_undefined_arg_not_in_domain x"

lemma fun_app : "x \<in> dom f \<Longrightarrow> (x, f \<cdot> x) \<in> func f"
  by (metis app_def theI' deterministic total)

lemma fun_app2 : "x \<in> dom f \<Longrightarrow> f \<cdot> x  \<in> cod f"
  by (meson fun_app welldefined)

lemma fun_app3 [simp] : "x \<in> dom f \<Longrightarrow> f \<cdot> x = (THE y. (x, y) \<in> func f) "
  by (simp add: app_def)

lemma fun_ext : "dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> func f = func g"
  unfolding  dom_def
  apply (simp_all add: Let_def)
  apply auto
  apply (metis deterministic dom.rep_eq fun_app welldefined)
  by (metis deterministic dom.rep_eq fun_app welldefined) 

lemma fun_ext2 : "dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> f = g"
  apply simp
  apply (frule fun_ext)
    apply auto
  by (metis (full_types) Rep_Function_inject cod.rep_eq equality func.rep_eq old.unit.exhaust) 

lemma fun_app_iff  : "(x, y) \<in> func f \<Longrightarrow> (f \<cdot> x) = y"
  by (meson fun_app deterministic welldefined)

(* Properties *)

abbreviation is_surjective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall> y . y \<in> cod f \<longrightarrow> (\<exists> x . x \<in> dom f \<and> f \<cdot> x = y)"

abbreviation is_injective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall>x x' . x \<in> dom f \<longrightarrow> x' \<in> dom f \<longrightarrow> f \<cdot> x = f \<cdot> x' \<longrightarrow> x = x'"

abbreviation is_bijective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

(* Constant functions *)

definition raw_const :: "'x set \<Rightarrow>  'y set  \<Rightarrow> 'y \<Rightarrow>  ('x, 'y) RawFunction" where
"raw_const X Y y \<equiv>  \<lparr> raw_cod = Y, raw_func = { (x, y) | x. x \<in> X }\<rparr>"

definition "Function_const_undefined_arg_not_in_codomain y \<equiv> undefined"

lift_definition const :: "'x set \<Rightarrow>  'y set  \<Rightarrow> 'y \<Rightarrow>  ('x, 'y) Function" is 
"\<lambda> X Y y . 
  if y \<in> Y
  then raw_const X Y y
  else Rep_Function (Function_const_undefined_arg_not_in_codomain y)" 
proof auto
  fix X Y y
  assume "y \<in> Y"
  show "valid_map (raw_const X Y y)"
  proof (rule valid_mapI)
    show "\<And>x ya. (x, ya) \<in> raw_func (raw_const X Y y) \<Longrightarrow> x \<in> raw_dom (raw_const X Y y) \<and> ya \<in> raw_cod
 (raw_const X Y y)"
      by (simp add: \<open>y \<in> Y\<close> raw_const_def raw_dom_def) 
    show "\<And>x ya y'. (x, ya) \<in> raw_func (raw_const X Y y) \<Longrightarrow> (x, y') \<in> raw_func (raw_const X Y y) \<Longrightarrow> ya
 = y'"
      by (simp add: raw_const_def)
    show "\<And>x. x \<in> raw_dom (raw_const X Y y) \<Longrightarrow> \<exists>ya. (x, ya) \<in> raw_func (raw_const X Y y)"
      by (simp add: raw_dom_def) 
  qed
next
  fix X Y y
  assume "y \<notin> Y"
  show " valid_map (Rep_Function (Function_const_undefined_arg_not_in_codomain y)) "
    using Rep_Function by fastforce 
qed

lemma const_dom [simp] : "y \<in> Y \<Longrightarrow> dom (const X Y y) = X"  
  apply transfer  
  by (simp add: raw_const_def raw_dom_def)

lemma const_cod [simp] : "y \<in> Y \<Longrightarrow> cod (const X Y y) = Y"
  apply transfer  
  by (simp add: raw_const_def)

lemma const_app [simp] : "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> (const X Y y) \<cdot> x = y"
  unfolding raw_const_def app_def
  apply transfer
  apply auto
  apply (simp add: raw_const_def)
  by (metis const.rep_eq const_dom dom.rep_eq)

(* Identity functions *)

definition raw_ident :: "'x set \<Rightarrow> ('x, 'x) RawFunction" where
"raw_ident X \<equiv>  \<lparr> raw_cod = X, raw_func = Id_on X \<rparr>"

lift_definition ident :: "'x set \<Rightarrow> ('x, 'x) Function" is raw_ident
  by (simp add: Id_on_iff raw_dom_def raw_ident_def valid_map_def) 

lemma ident_dom [simp] : "dom (ident X) = X" 
  apply transfer
  apply safe
  apply (smt (verit, del_insts) Id_on_iff eq_onp_def fun_app func.abs_eq mem_Collect_eq raw_dom_def raw_ident_def select_convs(1) select_convs(2) valid_mapI)
  by (smt (verit, del_insts) Id_on_iff dom.abs_eq eq_onp_def mem_Collect_eq raw_dom_def raw_ident_def select_convs(1) select_convs(2) valid_mapI)

lemma ident_cod [simp] : "cod (ident X) = X"
  apply transfer
  by (smt (verit, best) Id_on_iff cod.abs_eq eq_onp_def mem_Collect_eq raw_dom_def raw_ident_def select_convs(1) select_convs(2) valid_mapI)

lemma ident_app [simp] : "x \<in> X \<Longrightarrow> ident X \<cdot> x = x"
  unfolding fun_app3 ident_def app_def
  apply transfer
  apply clarsimp
  apply safe
  apply (metis Id_on_iff func.rep_eq ident.abs_eq ident.rep_eq raw_ident_def select_convs(2) the_equality)
  by (metis ident.abs_eq ident_dom)

(* Composition of functions *)

definition raw_compose :: "('y, 'z) RawFunction \<Rightarrow> ('x, 'y) RawFunction \<Rightarrow> ('x, 'z) RawFunction"where
  "raw_compose g f \<equiv>  \<lparr> raw_cod = raw_cod g, raw_func = relcomp (raw_func f) (raw_func g) \<rparr>"

definition "Function_compose_undefined_incomposable g f \<equiv> undefined"

lift_definition compose :: "('y, 'z) Function \<Rightarrow> ('x, 'y) Function \<Rightarrow> ('x, 'z) Function" (infixl "\<bullet>" 55) is
  "\<lambda> g f .
    if dom g = cod f
    then raw_compose (Rep_Function g) (Rep_Function f)
    else Rep_Function (Function_compose_undefined_incomposable g f)"
proof (intro valid_mapI conjI, goal_cases)
  case (1 g f x y)
  then show ?case 
apply transfer
    by (metis Domain.DomainI Domain_unfold raw_dom_def)
next
  case (2 g f x y)
  then show ?case 
apply transfer
    by (smt (verit) cod.rep_eq func.rep_eq raw_compose_def relcompEpair select_convs(1) select_convs(2) welldefined) 
next
  case (3 g f x y y')
  then show ?case 
    by (smt (verit) deterministic fun_app func.rep_eq raw_compose_def relcomp.cases select_convs(2))
next
  case (4 g f x)
  then show ?case
    by (simp add: raw_dom_def) 
qed

lemma compose_welldefined_cod : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> y \<in> cod g"
  apply transfer

lemma compose_welldefined_dom : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f"
  apply transfer

lemma compose_welldefined : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f \<and> y \<in> cod g"

lemma compose_deterministic : "dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> (x, y') \<in> func (g \<bullet> f) \<Longrightarrow> y = y'"
  apply transer

lemma compose_total : "dom g = cod f \<Longrightarrow> x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func (g \<bullet> f)"
  apply transer

lemma cod_compose [simp] : "dom g = cod f \<Longrightarrow> cod (g \<bullet> f) = cod g"
  apply transfer
proof -
  fix g f
  assume "valid_map g" 
  assume "valid_map f "

lemma dom_compose [simp] : "dom g = cod f \<Longrightarrow> dom (g \<bullet> f) = dom f"
  apply transfer

lemma compose_app_assoc: "x \<in> dom f \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<bullet> f) \<cdot> x = g \<cdot> (f \<cdot> x)"
  unfolding valid_map_def dom_def compose_def app_def
  apply (simp add: Let_def)
  apply clarsimp
  apply safe
     apply auto
     apply (smt (verit, best) relcomp.simps the_equality)
    apply (metis (mono_tags, lifting) theI_unique)
  apply (meson relcomp.relcompI)
  by (metis Function_app_undefined_arg_not_in_domain_def)

lemma compose_assoc "(g \<bullet> f) \<bullet> h = g \<bullet> (f \<bullet> h)"

lemma compose_app [simp] : "(x, y) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow> (b, c) \<in> func g 
 \<Longrightarrow> (g \<bullet> f) \<cdot> a = c"
  apply (rule fun_app_iff)
  using compose_valid apply blast
  by (simp add: compose_def relcomp.relcompI)

lemma surjection_is_right_cancellative : "is_surjective f \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h
 \<Longrightarrow> g \<bullet> f = h \<bullet> f \<Longrightarrow> g = h"
  by (metis cod_compose compose_app_assoc fun_ext2)

lemma injection_is_left_cancellative : "is_injective f \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f 
 \<Longrightarrow> f \<bullet> g = f \<bullet> h \<Longrightarrow> g = h"
  by (metis compose_app_assoc dom_compose fun_app2 fun_ext2)

end
