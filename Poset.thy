theory Poset
imports Main

begin

record 'a Poset =
  el :: "'a set"
  le :: "'a  \<Rightarrow>  'a  \<Rightarrow> bool"

definition valid :: "'a Poset   \<Rightarrow> bool" where
  "valid P \<equiv>
    let
      reflexivity = (\<forall>x. x \<in> el P\<longrightarrow> le P x x);
      antisymmetry = (\<forall>x y. x \<in> el P\<longrightarrow> y \<in> el P\<longrightarrow>  le P x y \<longrightarrow> le P y x \<longrightarrow> x = y);
      transitivity = (\<forall>x y z. x \<in> el P\<longrightarrow> y \<in> el P\<longrightarrow> z \<in> el P\<longrightarrow> le P x y \<longrightarrow> le P y z \<longrightarrow> le P x z)
    in
      reflexivity \<and> antisymmetry \<and> transitivity"

record ('a, 'b) PosetMap =
  func ::"('a \<times>'b) set"
  dom :: "'a Poset"
  cod :: "'b Poset"

definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$$" 997) where
"app f a \<equiv> if a \<in> el (dom f) then (THE b. (a, b) \<in> func f) else undefined"

definition valid_map :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"valid_map f \<equiv>
  let
      le_dom = le (dom f);
      le_cod = le (cod f);
      edom = el (dom f);
      ecod = el (cod f);
      welldefined = valid (dom f) \<and> valid (cod f) \<and> (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> edom \<and> b \<in> ecod);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> edom \<longrightarrow> (\<exists>b. (a, b) \<in> func f));
      monotone = (\<forall>a a'. a \<in> edom \<and> a' \<in> edom \<and> le_dom a a' \<longrightarrow> le_cod (f $$ a) (f $$ a'))

  in welldefined \<and> deterministic \<and> total \<and> monotone"

definition compose :: "('b, 'c) PosetMap \<Rightarrow> ('a, 'b) PosetMap \<Rightarrow> ('a, 'c) PosetMap" (infixl "\<cdot>" 55) where
  "compose g f \<equiv>
  if dom g = cod f
  then \<lparr> func = relcomp (func f) (func g), dom = dom f, cod = cod g \<rparr>
  else undefined"

definition ident :: "'a Poset \<Rightarrow> ('a, 'a) PosetMap" where
"ident P \<equiv> \<lparr> func = Id_on (el P), dom = P, cod = P \<rparr>"

definition product :: "'a Poset \<Rightarrow> 'b Poset \<Rightarrow> ('a \<times> 'b) Poset" (infixl "\<times>\<times>" 55) where
"product P Q \<equiv> \<lparr> el = el P \<times> el Q, le = (\<lambda>(a, b) (a', b'). le P a a' \<and> le Q b b') \<rparr>"


definition discrete :: "'a Poset" where
  "discrete \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x = y   \<rparr>"


(* LEMMAS *)

lemma valid_mapI: "valid (dom f) \<Longrightarrow> valid (cod f)  \<Longrightarrow> (\<And>a b. (a, b) \<in> func f \<Longrightarrow>  a \<in> el (dom f) \<and> b \<in> el (cod f)) \<Longrightarrow> 
                   (\<And>a b b'. (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b') \<Longrightarrow> 
                   (\<And>a. a \<in> el (dom f) \<Longrightarrow> (\<exists>b. (a, b) \<in> func f)) \<Longrightarrow>
                   (\<And>a a'. a \<in> el (dom f) \<and> a' \<in> el (dom f) \<and> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a')) 
  \<Longrightarrow> valid_map f "
  by (clarsimp simp: valid_map_def, intro conjI, fastforce+)

lemma product_valid [simp]: "valid P \<Longrightarrow> valid Q \<Longrightarrow> valid (P \<times>\<times> Q)"
  unfolding valid_def product_def
  apply simp
  apply safe
  apply meson
  by meson

lemma pom_eqI: "cod f = cod g \<Longrightarrow> dom f = dom g \<Longrightarrow> func f = func g \<Longrightarrow> (f :: ('a, 'b) PosetMap) = g"
  apply (rule PosetMap.equality, assumption)
    apply (assumption)
   apply (assumption)
  by simp

theorem validI :
  fixes P :: "'A Poset"
  assumes reflexivity : "(\<And>x. x \<in> el P \<Longrightarrow> le P x x)"
  assumes antisymmetry : "(\<And>x y. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow>  le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y)"
  assumes transitivity : "(\<And>x y z. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z)"
    shows "valid P"
  by (smt (verit, best) antisymmetry reflexivity transitivity valid_def)

(*
theorem valid_mapI :
  fixes f :: "('A, 'a) PosetMap"
  defines "le_dom \<equiv> le (dom f)"
  defines "le_cod \<equiv> le (cod f)"
  defines "edom \<equiv> el (dom f)"
  defines "ecod \<equiv> el (cod f)"
  assumes welldefined : "valid (dom f) \<and> valid (cod f) \<and> (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> edom \<and> b \<in> ecod)"
  assumes deterministic : "(\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b')"
  assumes total : "(\<forall>a. a \<in> edom \<longrightarrow> (\<exists>b. (a, b) \<in> func f))"
  assumes monotone : "(\<forall>a a'. a \<in> edom \<and> a' \<in> edom \<and> le_dom a a' \<longrightarrow> le_cod (f $$ a) (f $$ a'))"
  shows "valid_map f"
  by (smt (verit) deterministic ecod_def edom_def le_cod_def le_dom_def monotone total valid_map_def welldefined)
*)


lemma valid_map_welldefined [simp]: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod f)"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_deterministic [simp]: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_total [simp]: "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_monotone [simp]: "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a')"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma fun_app [simp]: "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> (a, f $$ a) \<in> func f"
  by (metis app_def the_equality valid_map_deterministic valid_map_total)

lemma fun_app2 [simp]: "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> f $$ a \<in> el (cod f)"
  by (meson fun_app valid_map_welldefined)

lemma fun_ext [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<forall>a \<in> el (dom f). f $$ a = g $$ a) \<Longrightarrow> f = g"
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp)
   apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  done


lemma dom_compose [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<cdot> f) = dom f"
  unfolding compose_def
  by (simp add: Let_def)

lemma cod_compose [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> cod (g \<cdot> f) = cod g"
  unfolding compose_def
  by (simp add: Let_def)

lemma compose_welldefined [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<cdot> f) \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod g)"
  unfolding compose_def
  by auto

lemma compose_deterministic [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<cdot> f) \<Longrightarrow> (a, b') \<in> func (g \<cdot> f) \<Longrightarrow> b = b'"
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) compose_def relcomp.simps valid_map_deterministic)

lemma compose_total [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func (g \<cdot> f)"
  unfolding compose_def
  by (smt (verit, best) PosetMap.select_convs(1) fun_app fun_app2 relcomp.relcompI)

lemma fun_app_iff: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (f $$ a) = b"
  apply (clarsimp simp: app_def)
  by fastforce


lemma compose_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<cdot> f) $$ a = g $$ (f $$ a)"
  apply (clarsimp simp: app_def, safe; clarsimp?)
   apply (smt (verit, del_insts) PosetMap.select_convs(1) compose_def compose_deterministic fun_app relcomp.relcompI theI valid_map_deterministic)
  by (metis app_def fun_app valid_map_welldefined)


lemma compose_monotone: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> 
    a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod (g \<cdot> f)) ((g \<cdot> f) $$ a) ((g \<cdot> f) $$ a')"
  apply (simp_all add: Let_def)
  by (clarsimp simp: compose_app)

lemma valid_dom[simp]: "valid_map f \<Longrightarrow> valid (dom f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold) 


lemma valid_cod[simp]: "valid_map f \<Longrightarrow> valid (cod f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold) 
 

lemma compose_valid [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<cdot> f)"
  apply (rule valid_mapI; clarsimp?)
  by (metis cod_compose compose_monotone)

lemma comp_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<cdot> f) $$ a = c"
  apply (rule fun_app_iff)
   apply (erule (2) compose_valid)
  by (clarsimp simp: compose_def, erule (1) relcompI)


lemma ident_valid [simp] : "valid P \<Longrightarrow> valid_map (ident P)"
  unfolding valid_map_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  done

lemma ident_app[simp] :
  fixes a :: "'a"
  assumes "a \<in> el P"
  shows "((ident P) $$ a) = a"
  unfolding ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by (simp add: assms)

lemma valid_reflexivity [simp]: "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> le P x x"
  by (simp add: valid_def)

lemma valid_transitivity [simp]: "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> y \<in> el P\<Longrightarrow> z \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z"
  unfolding valid_def
  by meson

lemma valid_antisymmetry [simp]: "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> y \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y"
  unfolding valid_def
  by meson

lemma valid_monotonicity[simp] :
  "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> x = dom f \<Longrightarrow> y = cod f \<Longrightarrow>
    le x a a' \<Longrightarrow> le y (f $$ a) (f $$ a')"
  unfolding valid_map_def
  apply safe
  apply auto
  by meson


lemma valid_map_dom: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f)"
  by simp

lemma ident_right_neutral [simp] : "valid_map f \<Longrightarrow> dom f = x \<Longrightarrow> f \<cdot> (ident x) = f"
  unfolding compose_def ident_def
  apply (simp add: Let_def)
  apply safe
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp?)
  apply (frule (1) valid_map_welldefined)
  apply (erule relcompI[rotated])
  apply (clarsimp)
  done

lemma ident_left_neutral [simp] : "valid_map f \<Longrightarrow> cod f = x \<Longrightarrow> (ident x) \<cdot> f = f"
  unfolding compose_def ident_def
   apply (simp add: Let_def)
  apply safe
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp?)
  apply (frule (1) valid_map_welldefined)
  apply (erule relcompI)
  apply (clarsimp)
  done



lemma discrete_valid : "valid discrete"
  by (smt (verit) Poset.Poset.select_convs(2) discrete_def valid_def)

(* EXAMPLES *)

definition ex_naturals :: "nat Poset" where
  "ex_naturals \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x \<le> y  \<rparr>"

lemma ex_naturals_valid : "valid ex_naturals"
  by (smt (verit) Poset.Poset.select_convs(2) dual_order.refl ex_naturals_def valid_def order_antisym order_trans)


definition ex_divisibility :: "nat Poset" where
  "ex_divisibility \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x dvd y  \<rparr>"

lemma ex_divisibility_valid : "valid ex_divisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(2) dvd_antisym ex_divisibility_def gcd_nat.refl gcd_nat.trans valid_def)





 end