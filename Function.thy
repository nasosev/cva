section \<open> Function.thy \<close>

theory Function
  imports Main
begin

(* Types *)

record ('x, 'y) Function =
  cod :: "'y set"
  func :: "('x \<times> 'y) set"

definition dom :: "('x, 'y) Function \<Rightarrow> 'x set" where
 "dom f \<equiv> {x. \<exists>y. (x, y) \<in> func f}"

definition valid_map :: "('x, 'y) Function \<Rightarrow> bool" where
"valid_map f \<equiv>
  let
      welldefined = \<forall>x y. (x, y) \<in> func f \<longrightarrow> y \<in> cod f;
      deterministic = \<forall>x y y'. (x, y) \<in> func f \<and> (x, y') \<in> func f \<longrightarrow> y = y'
  in welldefined \<and> deterministic"

(* Validity *)

lemma dom : "(x, y) \<in> func f \<Longrightarrow> x \<in> dom f" 
  unfolding dom_def
  by blast

lemma map_total : "x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func f"
  by (simp add: Function.dom_def)

lemma valid_map_welldefined : "valid_map f \<Longrightarrow> (x, y) \<in> func f \<Longrightarrow> y \<in> cod f"
  by (simp add: valid_map_def) 

lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (x, y) \<in> func f \<Longrightarrow> (x, y') \<in> func f \<Longrightarrow> y = y'"
  by (simp add: valid_map_def) 

lemma valid_mapI [intro] : "((\<And>x y. (x, y) \<in> func f \<Longrightarrow> y \<in> cod f) \<Longrightarrow>
                   (\<And>x y y'. (x, y) \<in> func f \<Longrightarrow> (x, y') \<in> func f \<Longrightarrow> y = y')
                   \<Longrightarrow> valid_map f) "
  by (metis valid_map_def)

lemma valid_map_eqI: "cod f = cod g \<Longrightarrow> dom f = dom g \<Longrightarrow> func f = func g \<Longrightarrow> (f :: ('x, 'y) Function) = g"
  by simp

(* Function application *)

definition "Function_app_undefined_arg_not_in_domain _ \<equiv> undefined"

definition app :: "('x, 'y) Function \<Rightarrow> 'x \<Rightarrow> 'y" (infixr "\<cdot>" 998) where
"app f x \<equiv> 
   if x \<in> dom f
   then (THE y. (x, y) \<in> func f)
  else Function_app_undefined_arg_not_in_domain x" 

lemma fun_app : "valid_map f \<Longrightarrow> x \<in> dom f \<Longrightarrow> (x, f \<cdot> x) \<in> func f"
  by (metis app_def map_total theI' valid_map_deterministic)

lemma fun_app2 : "valid_map f \<Longrightarrow> x \<in> dom f \<Longrightarrow> f \<cdot> x  \<in> cod f"
  by (meson fun_app valid_map_welldefined)

lemma fun_app3 [simp] : "x \<in> dom f \<Longrightarrow> f \<cdot> x = (THE y. (x, y) \<in> func f) "
  by (simp add: app_def)

lemma fun_ext_raw : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> func f = func g"
  by (metis dom fun_app pred_equals_eq2 valid_map_deterministic)

lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<And>x. x \<in> dom f \<Longrightarrow> f \<cdot> x = g \<cdot> x) \<Longrightarrow> f = g"
  by (metis (full_types) equality fun_ext_raw old.unit.exhaust)

lemma fun_app_iff : "valid_map f \<Longrightarrow> (x, y) \<in> func f \<Longrightarrow> (f \<cdot> x) = y"
  by (meson valid_map_deterministic fun_app dom) 

(* Composition of functions *)

definition "Function_compose_undefined_incomposable _ _ \<equiv> undefined"

definition compose :: "('y, 'z) Function \<Rightarrow> ('x, 'y) Function \<Rightarrow> ('x, 'z) Function"  (infixl "\<bullet>" 55) 
  where
  "compose g f \<equiv>
    if dom g = cod f
    then \<lparr> cod = cod g, func = relcomp (func f) (func g) \<rparr>
    else Function_compose_undefined_incomposable g f"

lemma compose_welldefined_cod : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> y \<in> cod g"
  by (metis compose_def relcompEpair select_convs(2) valid_map_def)

lemma compose_welldefined_dom : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f"
  by (metis compose_def dom relcomp.cases select_convs(2))

lemma compose_welldefined : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> x \<in> dom f \<and> y \<in> cod g"
  by (simp add: compose_welldefined_cod compose_welldefined_dom)

lemma compose_deterministic : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> (x, y) \<in> func (g \<bullet> f) \<Longrightarrow> (x, y') \<in> func (g \<bullet> f) \<Longrightarrow> y = y'"
  by (smt (verit, ccfv_threshold) compose_def valid_map_deterministic relcomp.simps select_convs(2))

lemma compose_total : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> x \<in> dom f \<Longrightarrow> \<exists>y. (x, y) \<in> func (g \<bullet> f)"
  by (metis (no_types, lifting) compose_def fun_app fun_app2 relcomp.simps select_convs(2))

lemma compose_valid : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<bullet> f)"
  by (smt (verit) CollectD Function.dom_def compose_def compose_deterministic compose_welldefined_cod select_convs(1) valid_map_def)

lemma cod_compose [simp] : "dom g = cod f \<Longrightarrow> cod (g \<bullet> f) = cod g"
  by (simp add: compose_def)

lemma dom_compose [simp] : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<bullet> f) = dom f"
  by (smt (verit) Collect_cong Function.dom_def compose_total compose_welldefined_dom mem_Collect_eq)
  
lemma compose_assoc : "valid_map h \<Longrightarrow> valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> dom h = cod g \<Longrightarrow> dom g = cod f \<Longrightarrow> (h \<bullet> g) \<bullet> f = h \<bullet> (g \<bullet> f)"
  by (smt (verit, ccfv_SIG) O_assoc cod_compose cod_compose compose_def compose_def compose_def compose_def dom_compose select_convs(2) select_convs(2))

lemma compose_app [simp] : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> (x, y) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow> (y, z) \<in> func g 
 \<Longrightarrow> (g \<bullet> f) \<cdot> x = z"
  unfolding valid_map_def compose_def dom_def app_def
  apply (simp add: Let_def)
  apply clarsimp
  apply safe
  apply (smt (verit) relcomp.simps the_equality)
  by (meson relcomp.relcompI)

lemma compose_app_assoc : "valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> x \<in> dom f \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<bullet> f) \<cdot> x = g \<cdot> (f \<cdot> x)"
  by (metis compose_app fun_app fun_app2)

(* Properties *)

definition is_surjective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_surjective f \<equiv> \<forall> y . y \<in> cod f \<longrightarrow> (\<exists> x . x \<in> dom f \<and> f \<cdot> x = y)"

definition is_injective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_injective f \<equiv> \<forall> x x' . x \<in> dom f \<longrightarrow> x' \<in> dom f \<longrightarrow> f \<cdot> x = f \<cdot> x' \<longrightarrow> x = x'"

definition is_bijective :: "('x, 'y) Function \<Rightarrow> bool" where
"is_bijective f \<equiv> is_surjective f \<and> is_injective f"

lemma surjection_is_right_cancellative : "valid_map h \<Longrightarrow> valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> is_surjective f \<Longrightarrow> cod f = dom g \<Longrightarrow> cod f = dom h
 \<Longrightarrow> g \<bullet> f = h \<bullet> f \<Longrightarrow> g = h"
  by (metis cod_compose compose_app_assoc fun_ext is_surjective_def)

lemma injection_is_left_cancellative : "valid_map h \<Longrightarrow> valid_map g \<Longrightarrow> valid_map f \<Longrightarrow> is_injective f \<Longrightarrow> cod g = dom f \<Longrightarrow> cod h = dom f 
 \<Longrightarrow> f \<bullet> g = f \<bullet> h \<Longrightarrow> g = h"
  by (smt (verit) compose_app_assoc dom_compose fun_app2 fun_ext is_injective_def)

(* Identity functions *)

definition ident :: "'x set \<Rightarrow> ('x, 'x) Function" where
"ident X \<equiv>  \<lparr> cod = X, func = Id_on X \<rparr>"

lemma ident_valid : "valid_map (ident X)"
  by (simp add: dom_def Id_on_iff ident_def valid_map_def) 

lemma ident_dom [simp] : "dom (ident X) = X" 
  by (simp add: Id_on_iff dom_def ident_def)

lemma ident_cod [simp] : "cod (ident X) = X"
  by (simp add: ident_def)

lemma ident_func [simp] : "func (ident X) = Id_on X"
  by (simp add: ident_def)

lemma ident_app [simp] : "x \<in> X \<Longrightarrow> ident X \<cdot> x = x"
  by (metis Id_onI fun_app_iff ident_def ident_valid select_convs(2)) 

lemma compose_ident_left [simp] : "valid_map f \<Longrightarrow> ident (cod f) \<bullet> f = f"
  by (smt (verit) cod_compose compose_app_assoc compose_valid dom_compose fun_app2 fun_ext ident_app ident_cod ident_dom ident_valid)

lemma compose_ident_right [simp] : "valid_map f \<Longrightarrow> f \<bullet> ident (dom f) = f"
  by (smt (verit, best) cod_compose compose_app_assoc compose_def compose_ident_left compose_valid dom_compose ext_inject fun_ext ident_app ident_def ident_dom ident_valid) 

(* Constant functions *)

definition "Function_const_undefined_arg_not_in_codomain _ \<equiv> undefined"

definition const :: "'x set \<Rightarrow>  'y set  \<Rightarrow> 'y \<Rightarrow>  ('x, 'y) Function" where
"const X Y y \<equiv> 
  if y \<in> Y
  then \<lparr> cod = Y, func = { (x, y) | x. x \<in> X }\<rparr>
  else Function_const_undefined_arg_not_in_codomain y" 

lemma const_dom [simp] : "y \<in> Y \<Longrightarrow> dom (const X Y y) = X"  
  by (simp add: const_def dom_def)

lemma const_cod [simp] : "y \<in> Y \<Longrightarrow> cod (const X Y y) = Y"
  by (simp add: const_def)

lemma const_app [simp] : "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> (const X Y y) \<cdot> x = y"
  by (smt (verit) CollectD Pair_inject const_cod const_def const_dom fun_app select_convs(2) valid_mapI)

lemma const_valid : "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> valid_map (const X Y y)"
  unfolding valid_map_def const_def
  by clarsimp

lemma const_func : "y \<in> Y \<Longrightarrow> func (const X Y y) = {(x, y) | x . x \<in> X }"
  by (simp add: const_def)

(* Lists functor *)

definition lists :: "'x set \<Rightarrow> ('x list) set" where
"lists X \<equiv> { xs . set xs \<subseteq> X }"

definition lists_map :: "('x, 'y) Function \<Rightarrow> ('x list, 'y list) Function" where
"lists_map f \<equiv> 
  \<lparr> cod = lists (cod f), 
    func = { (ts, map (\<lambda> t . f \<cdot> t) ts) | ts . ts \<in> lists (dom f) } \<rparr>"

lemma lists_map_valid : "valid_map f \<Longrightarrow> valid_map (lists_map f)" 
  unfolding lists_map_def lists_def
  apply (intro valid_mapI)
  apply clarsimp
  apply (meson fun_app2 subsetD)
  by force

lemma lists_map_cod : "cod (lists_map f) = lists (cod f)"
  by (simp add: lists_map_def)

lemma lists_map_dom : "dom (lists_map f) = lists (dom f)"
  unfolding lists_map_def app_def dom_def
  by simp

lemma lists_map_ident : "lists_map (ident X) = ident (lists X)"
proof -
  fix X :: "'x set" 
  have "cod (lists_map (ident X)) = lists X"
    by (simp add: lists_map_cod)
  moreover have "dom (lists_map (ident X)) = lists X"
    by (simp add: lists_map_dom)
  moreover have "func (lists_map (ident X)) = { (ts, ts) | ts . ts \<in> lists X }" unfolding
      lists_map_def lists_def  ident_cod ident_dom ident_func Id_on_def
    apply clarsimp
    by (metis (no_types, lifting) ident_app list.map_ident_strong subsetD)
  ultimately show "lists_map (ident X) = ident (lists X)"
    by (smt (verit, best) Collect_cong Function.dom_def Id_onE Id_onI Id_on_def' ident_cod ident_func mem_Collect_eq valid_map_eqI)
qed

lemma lists_map_trans :
  fixes g :: "('y, 'z) Function" and f :: "('x , 'y) Function"
  assumes f_valid : "valid_map f"
  and g_valid : "valid_map g"
  and cod_eq_dom : "cod f = dom g"
shows "lists_map g \<bullet> lists_map f = lists_map (g \<bullet> f)"
proof (rule fun_ext, goal_cases)
  case 1
  then show ?case
    by (simp add: cod_eq_dom compose_valid f_valid g_valid lists_map_cod lists_map_dom lists_map_valid) 
next
  case 2
  then show ?case
    by (simp add: cod_eq_dom compose_valid f_valid g_valid lists_map_valid) 
next
  case 3
  then show ?case
    by (simp add: cod_eq_dom f_valid g_valid lists_map_cod lists_map_dom lists_map_valid) 
next
  case 4
  then show ?case
    by (simp add: cod_eq_dom lists_map_cod lists_map_dom) 
next
  case (5 x)
  then show ?case 
  proof -
    fix xs
    assume "xs \<in> dom (lists_map g \<bullet> lists_map f)"
    have "xs \<in> dom (lists_map f)"
      by (metis \<open>xs \<in> dom (lists_map g \<bullet> lists_map f)\<close> cod_eq_dom dom_compose f_valid g_valid lists_map_cod lists_map_dom lists_map_valid) 
    define "Lf_xs" where "Lf_xs = map (\<lambda> x . f \<cdot> x) xs" 
    moreover have "Lf_xs = (lists_map f) \<cdot> xs" unfolding Lf_xs_def lists_map_def
      by (smt (z3) Collect_cong Pair_inject \<open>xs \<in> dom (lists_map f)\<close> f_valid fun_app lists_map_def lists_map_valid mem_Collect_eq select_convs(2))
    moreover have "Lf_xs \<in> dom (lists_map g)" unfolding Lf_xs_def lists_map_def
      by (metis Lf_xs_def \<open>xs \<in> dom (lists_map f)\<close> calculation(2) cod_eq_dom f_valid fun_app2 lists_map_cod lists_map_def lists_map_dom lists_map_valid)
    define "LgLf_xs" where "LgLf_xs = map (\<lambda> x . g \<cdot> x) Lf_xs" 
    moreover have "LgLf_xs = (lists_map g) \<cdot> Lf_xs" unfolding Lf_xs_def lists_map_def
      by (smt (verit) Collect_cong Lf_xs_def LgLf_xs_def Pair_inject \<open>Lf_xs \<in> dom (lists_map g)\<close> fun_app g_valid lists_map_def lists_map_valid mem_Collect_eq select_convs(2))
    moreover have "LgLf_xs = (lists_map g \<bullet> lists_map f) \<cdot> xs"
      by (metis \<open>Lf_xs \<in> dom (lists_map g)\<close> \<open>xs \<in> dom (lists_map f)\<close> calculation(2) calculation(4) cod_eq_dom compose_app f_valid fun_app g_valid lists_map_cod lists_map_dom lists_map_valid) 
    moreover have "LgLf_xs = map (\<lambda> x . g \<cdot> (f  \<cdot> x)) xs" unfolding LgLf_xs_def Lf_xs_def
      by clarsimp
    moreover have "\<forall> x . x \<in> dom f \<longrightarrow> g \<cdot> (f  \<cdot> x) = (g \<bullet> f)  \<cdot> x"  using compose_app_assoc [where ?g=g and ?f=f]
      using cod_eq_dom f_valid g_valid by presburger
    moreover have "\<forall> x . x \<in> set xs \<longrightarrow> x \<in> dom f"
      using lists_def \<open>xs \<in> dom (lists_map f)\<close> lists_map_dom by fastforce 
    moreover have "LgLf_xs = map (\<lambda> x . (g \<bullet> f)  \<cdot> x) xs" using LgLf_xs_def calculation assms
      by simp 
    moreover have "LgLf_xs = lists_map (g \<bullet> f) \<cdot> xs" using lists_map_def [where ?f="g \<bullet> f"]
      by (smt (verit, del_insts) \<open>xs \<in> dom (lists_map f)\<close> calculation(9) cod_eq_dom compose_valid dom_compose f_valid fun_app_iff g_valid lists_map_dom lists_map_valid mem_Collect_eq select_convs(2))
    ultimately show "(lists_map g \<bullet> lists_map f) \<cdot> xs = lists_map (g \<bullet> f) \<cdot> xs"
      by presburger 
  qed
qed

(* Nonempty lists functor *)

definition ne_lists :: "'x set \<Rightarrow> ('x list) set" where
"ne_lists X \<equiv> { xs . set xs \<subseteq> X \<and> length xs \<noteq> 0 }" 

definition ne_lists_map :: "('x, 'y) Function \<Rightarrow> ('x list, 'y list) Function" where
"ne_lists_map f \<equiv> 
  \<lparr> cod = ne_lists (cod f), 
    func = { (ts, map (\<lambda> t . f \<cdot> t) ts) | ts . ts \<in> ne_lists (dom f) } \<rparr>"

lemma ne_lists_map_valid : "valid_map f \<Longrightarrow> valid_map (ne_lists_map f)" 
  unfolding ne_lists_map_def ne_lists_def
  apply (intro valid_mapI)
  apply clarsimp
  apply (meson fun_app2 subsetD)
  by force


end
