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

definition cod :: "('x, 'y) Function \<Rightarrow> 'y set" where
"cod f \<equiv> RawFunction.raw_cod (Rep_Function f)"

definition func :: "('x, 'y) Function \<Rightarrow> ('x \<times> 'y) set" where
"func f \<equiv> RawFunction.raw_func (Rep_Function f)"

definition dom :: "('x, 'y) Function \<Rightarrow> 'x set" where
"dom f \<equiv> {x. \<exists>y. (x, y) \<in> func f}"

definition "Function_app_undefined_arg_not_in_domain a \<equiv> undefined"

definition app :: "('x, 'y) Function \<Rightarrow> 'x \<Rightarrow> 'y" (infixr "\<cdot>" 998) where
"app f x \<equiv>
  if x \<in> dom f
   then (THE y. (x, y) \<in> func f)
  else Function_app_undefined_arg_not_in_domain x"

definition "Function_const_undefined_arg_not_in_codomain b \<equiv> undefined"

definition const :: "'x set \<Rightarrow>  'y set  \<Rightarrow> 'y \<Rightarrow>  ('x, 'y) Function" where
"const X Y y\<equiv>
  if y \<in> Y
  then  Abs_Function \<lparr> raw_cod = Y, raw_func = { (x, y) | x. x \<in> X }\<rparr>
  else Function_const_undefined_arg_not_in_codomain y"

definition ident :: "'x set \<Rightarrow> ('x, 'x) Function" where
"ident X \<equiv> Abs_Function \<lparr> raw_cod = X, raw_func = Id_on X \<rparr>"

definition "Function_compose_undefined_incomposable g f \<equiv> undefined"

definition compose :: "('y, 'z) Function \<Rightarrow> ('x, 'y) Function \<Rightarrow> ('x, 'z) Function" (infixl "\<bullet>" 55) where
  "compose g f \<equiv>
  if dom g = cod f
  then  Abs_Function \<lparr> raw_cod = cod g, raw_func = relcomp (func f) (func g) \<rparr>
  else Function_compose_undefined_incomposable g f"

abbreviation is_surjective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall> y . y \<in> cod f \<longrightarrow> (\<exists> x . x \<in> dom f \<and> f \<cdot> x = y)"

abbreviation is_injective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall>x x' . x \<in> dom f \<longrightarrow> x' \<in> dom f \<longrightarrow> f \<cdot> x = f \<cdot> x' \<longrightarrow> x = x'"

abbreviation is_bijective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

lemma welldefined : "(x, y) \<in> func f \<Longrightarrow> x \<in> dom f \<and> y \<in> cod f" 
proof -
  fix f
  assume "(x, y) \<in> func f"
  have "x \<in> dom f"
    using Function.dom_def \<open>(x, y) \<in> Function.func f\<close> by fastforce 
  moreover have "y \<in> cod f" using valid_map_def [where ?rf="Rep_Function f"]
    using Function.cod_def Function.func_def Rep_Function \<open>(x, y) \<in> Function.func f\<close> by fastforce 
  show "x \<in> dom f \<and> y \<in> cod f"
    by (simp add: \<open>y \<in> Function.cod f\<close> calculation)
qed

lemma deterministic : "(x, y) \<in> func f \<Longrightarrow> (x, y') \<in> func f \<Longrightarrow> y = y'"
  using Function.func_def Rep_Function valid_map_def by fastforce

lemma total : " x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func f"
  by (simp add: Function.dom_def) 

lemma valid_mapI: "((\<And>x y. (x, y) \<in> raw_func rf \<Longrightarrow>  x \<in> raw_dom rf \<and> y \<in> raw_cod rf) \<Longrightarrow>
                   (\<And>x y y'. (x, y) \<in> raw_func rf \<Longrightarrow> (x, y') \<in> raw_func rf \<Longrightarrow> y = y') \<Longrightarrow>
                   (\<And>x. x \<in> raw_dom rf \<Longrightarrow> (\<exists>y. (x, y) \<in> raw_func rf))
                   \<Longrightarrow> valid_map rf) "
  by (metis valid_map_def)

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
  apply (metis Function.dom_def fun_app deterministic welldefined)
  by (metis Function.dom_def fun_app deterministic welldefined)

lemma fun_ext2 : "dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> f = g"
  apply simp
  apply (frule fun_ext)
    apply auto
  by (metis (full_types) Rep_Function_inject cod_def equality func_def old.unit.exhaust)

lemma fun_app_iff  : "(x, y) \<in> func f \<Longrightarrow> (f \<cdot> x) = y"
  by (meson fun_app deterministic welldefined)


lemma const_dom [simp] : "y \<in> Y \<Longrightarrow> dom (const X Y y) = X" 
lemma const_cod [simp] : "y \<in> Y \<Longrightarrow> cod (const X Y y) = Y"
  by (simp add: const_def)

lemma const_app [simp] : "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> (const X Y y) \<cdot> x = y"
proof -
  fix x y X Y
  assume "x \<in> X" 
  assume "y \<in> Y"
  have "dom (const X Y y) = X" using const_def [where ?X=X and ?Y=Y and
        ?y=y]
    by (meson \<open>y \<in> Y\<close> const_dom)
  have "const X Y y \<cdot> x = y" using const_def [where ?X=X and ?Y=Y and
        ?y=y] using app_def [where ?f="const X Y y" and ?x=x] 
   


lemma const_valid : "y \<in> B \<Longrightarrow> valid_map (const A B b)"
  unfolding valid_map_def const_def
  by (simp add: Function.dom_def app_def)

lemma ident_valid : "valid_map (ident X)"
  by (simp add: Function.dom_def Id_on_iff ident_def valid_map_def)

lemma ident_app [simp] :
  fixes x :: "'x" and X :: "'x set"
  assumes "x \<in> X"
  shows "ident X \<cdot> x = x"
  unfolding ident_def app_def Id_on_def
  apply auto
  using assms apply blast
  by (simp add: Function.dom_def assms)

lemma ident_dom [simp] : "dom (ident X) = X"
  by (simp add: Function.dom_def Id_on_iff ident_def)

lemma ident_cod [simp] : "cod (ident X) = X"
  by (simp add: ident_def)


lemma dom_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<bullet> f) = dom f"
  unfolding compose_def dom_def
  apply clarsimp
  by (metis Function.dom_def relcomp.simps valid_map_total valid_map_welldefined)

lemma cod_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> cod (g \<bullet> f) = cod g"
  unfolding compose_def
  by force

lemma compose_welldefined : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f \<and> y \<in> cod g"
  unfolding compose_def dom_def valid_map_def
  by clarsimp


lemma compose_deterministic : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> (x, y') \<in> func (g \<bullet> f) \<Longrightarrow> y = y'"
  unfolding compose_def dom_def valid_map_def
  apply clarsimp
  by metis

lemma compose_total : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func (g \<bullet> f)"
  unfolding compose_def
  by (smt (verit, ccfv_threshold) fun_app fun_app2 relcomp.relcompI select_convs(2))

lemma compose_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> x \<in> dom f \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<bullet> f) \<cdot> a = g \<cdot> (f \<cdot> x)"
  unfolding valid_map_def dom_def compose_def app_def
  apply (simp add: Let_def)
  apply clarsimp
  apply safe
     apply auto
     apply (smt (verit, best) relcomp.simps the_equality)
    apply (metis (mono_tags, lifting) theI_unique)
  apply (meson relcomp.relcompI)
  by (metis Function_app_undefined_arg_not_in_domain_def)

lemma compose_valid : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<bullet> f)"
  apply (rule valid_mapI)
  unfolding valid_map_def
    apply (simp_all add :Let_def)
  apply (smt (verit, del_insts) Function.dom_def compose_def mem_Collect_eq relcomp.simps select_convs(1) select_convs(2))
   apply (metis (no_types, lifting) compose_def relcomp.simps select_convs(2))
  by auto

lemma comp_app [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (x, y) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<bullet> f) \<cdot> a = c"
  apply (rule fun_app_iff)
  using compose_valid apply blast
  by (simp add: compose_def relcomp.relcompI)

lemma surjection_is_right_cancellative : "valid_map f \<Longrightarrow> is_surjective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h \<Longrightarrow>  g \<bullet> f = h \<bullet> f \<Longrightarrow> g = h"
  by (metis cod_compose compose_app fun_ext2)

lemma injection_is_left_cancellative : "valid_map f \<Longrightarrow> is_injective f \<Longrightarrow>
  valid_map g \<Longrightarrow> valid_map h \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f \<Longrightarrow>  f \<bullet> g = f \<bullet> h \<Longrightarrow> g = h"
  by (metis compose_app dom_compose fun_app2 fun_ext2)

end
