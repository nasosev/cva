theory Poset
imports Main

begin

record 'a Poset =
  el :: "'a set"
  le_rel :: "('a \<times> 'a) set"

abbreviation le :: "'a Poset \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"le P a a' \<equiv>  (a, a') \<in> le_rel P"

definition valid :: "'a Poset   \<Rightarrow> bool" where
  "valid P \<equiv>
    let
      welldefined = (\<forall>x y. le P x y \<longrightarrow> x \<in> el P \<and> y \<in> el P);
      reflexivity = (\<forall>x. x \<in> el P \<longrightarrow> le P x x);
      antisymmetry = (\<forall>x y. x \<in> el P \<longrightarrow> y \<in> el P  \<longrightarrow> le P x y \<longrightarrow> le P y x  \<longrightarrow> x = y);
      transitivity = (\<forall>x y z. x \<in> el P\<longrightarrow> y \<in> el P \<longrightarrow> z \<in> el P\<longrightarrow> le P x y \<longrightarrow> le P y z \<longrightarrow> le P x z)
    in
      welldefined \<and> reflexivity \<and> antisymmetry \<and> transitivity"

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
"product P Q \<equiv> \<lparr> el = el P \<times> el Q, le_rel =
 {(x, y). fst x \<in> el P \<and> snd x \<in> el Q \<and> fst y \<in> el P \<and> snd y \<in> el Q \<and> (fst x, fst y) \<in> le_rel P \<and> (snd x, snd y) \<in> le_rel Q} \<rparr>"

definition discrete :: "'a Poset" where
  "discrete \<equiv> \<lparr>  el = UNIV , le_rel = {x. fst x = snd x} \<rparr>"

(* Warning: this tuple builder syntax gives unexpected result (defines the total relation)
definition discrete_fake :: "bool Poset" where
  "discrete_fake \<equiv> \<lparr>  el = UNIV , le_rel = {(x,x) . True} \<rparr>"

value discrete_fake
 *)

(* LEMMAS *)

lemma valid_mapI: "valid (dom f) \<Longrightarrow> valid (cod f)  \<Longrightarrow> (\<And>a b. (a, b) \<in> func f \<Longrightarrow>  a \<in> el (dom f) \<and> b \<in> el (cod f)) \<Longrightarrow>
                   (\<And>a b b'. (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b') \<Longrightarrow>
                   (\<And>a. a \<in> el (dom f) \<Longrightarrow> (\<exists>b. (a, b) \<in> func f)) \<Longrightarrow>
                   (\<And>a a'. a \<in> el (dom f) \<and> a' \<in> el (dom f) \<and> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a'))
  \<Longrightarrow> valid_map f "
  by (clarsimp simp: valid_map_def, intro conjI, fastforce+)

lemma product_valid : "valid P \<Longrightarrow> valid Q \<Longrightarrow> valid (P \<times>\<times> Q)"
  unfolding valid_def product_def
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD case_prodI fst_conv mem_Collect_eq mem_Sigma_iff prod.collapse snd_conv)

lemma pom_eqI: "cod f = cod g \<Longrightarrow> dom f = dom g \<Longrightarrow> func f = func g \<Longrightarrow> (f :: ('a, 'b) PosetMap) = g"
  by simp

theorem validI :
  fixes P :: "'A Poset"
  assumes welldefined : "(\<And>x y. le P x y \<Longrightarrow> x \<in> el P \<and> y \<in> el P)"
  assumes reflexivity : "(\<And>x. x \<in> el P \<Longrightarrow> le P x x)"
  assumes antisymmetry : "(\<And>x y. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow>  le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y)"
  assumes transitivity : "(\<And>x y z. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z)"
    shows "valid P"
  by (smt (verit, best) antisymmetry reflexivity transitivity valid_def welldefined)

lemma valid_welldefined : "valid P \<Longrightarrow> le P x y \<Longrightarrow> x \<in> el P \<and> y \<in> el P"
  unfolding valid_def
  by meson

lemma valid_reflexivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> le P x x"
  using valid_def by fastforce

lemma valid_transitivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z"
  unfolding valid_def
  by meson

lemma valid_antisymmetry : "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> y \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y"
  unfolding valid_def
  by meson

lemma valid_monotonicity :
  "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> x = dom f \<Longrightarrow> y = cod f \<Longrightarrow>
    le x a a' \<Longrightarrow> le y (f $$ a) (f $$ a')"
  unfolding valid_map_def
  apply safe
  apply auto
  by meson

lemma valid_map_welldefined : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod f)"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_deterministic : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b'"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_total : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func f"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma valid_map_monotone : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a')"
  unfolding valid_map_def
  by (simp add: Let_def)

lemma fun_app : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> (a, f $$ a) \<in> func f"
  by (metis app_def the_equality valid_map_deterministic valid_map_total)

lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> f $$ a \<in> el (cod f)"
  by (meson fun_app valid_map_welldefined)

lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<forall>a \<in> el (dom f). f $$ a = g $$ a) \<Longrightarrow> f = g"
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp)
   apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  done

lemma dom_compose : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<cdot> f) = dom f"
  unfolding compose_def
  by (simp add: Let_def)

lemma cod_compose : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> cod (g \<cdot> f) = cod g"
  unfolding compose_def
  by (simp add: Let_def)

lemma compose_welldefined : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<cdot> f) \<Longrightarrow> a \<in> el (dom f) \<and> b \<in> el (cod g)"
  by (metis PosetMap.select_convs(1) compose_def relcomp.simps valid_map_welldefined)

lemma compose_deterministic : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> (a, b) \<in> func (g \<cdot> f) \<Longrightarrow> (a, b') \<in> func (g \<cdot> f) \<Longrightarrow> b = b'"
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) compose_def relcomp.simps valid_map_deterministic)

lemma compose_total : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> \<exists>b. (a, b) \<in> func (g \<cdot> f)"
  unfolding compose_def
  by (smt (verit, best) PosetMap.select_convs(1) fun_app fun_app2 relcomp.relcompI)

lemma fun_app_iff  : "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> (f $$ a) = b"
  by (meson fun_app valid_map_deterministic valid_map_welldefined)

lemma compose_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<cdot> f) $$ a = g $$ (f $$ a)"
  apply (clarsimp simp: app_def, safe; clarsimp?)
   apply (smt (verit, del_insts) PosetMap.select_convs(1) compose_def compose_deterministic fun_app relcomp.relcompI theI valid_map_deterministic)
  apply (metis app_def fun_app2)
  by (simp add: dom_compose)

lemma compose_monotone: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow>
    a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod (g \<cdot> f)) ((g \<cdot> f) $$ a) ((g \<cdot> f) $$ a')"
  apply (subst (asm) valid_map_def)
  apply (clarsimp simp: Let_unfold)
  by (simp add: cod_compose compose_app fun_app2 valid_mapI valid_map_monotone)

lemma valid_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

lemma valid_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

lemma compose_valid : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<cdot> f)"
  apply (rule valid_mapI; clarsimp?)
       apply (simp add: dom_compose valid_dom)
  apply (simp add: cod_compose valid_cod)
  apply (simp add: cod_compose compose_welldefined dom_compose)
  apply (simp add: compose_deterministic)
   apply (simp add: compose_total dom_compose)
  by (simp add: compose_monotone dom_compose)

lemma comp_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<cdot> f) $$ a = c"
  apply (rule fun_app_iff)
  apply (smt (verit) cod_compose compose_deterministic compose_monotone compose_total compose_welldefined dom_compose valid_cod valid_dom valid_mapI)
  by (simp add: compose_def relcomp.relcompI)

lemma ident_valid  : "valid P \<Longrightarrow> valid_map (ident P)"
  unfolding valid_map_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  done

lemma ident_app [simp] :
  fixes a :: "'a" and P :: "'a Poset"
  assumes "valid P" and "a \<in> el P"
  shows "((ident P) $$ a) = a"
  unfolding ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by (simp add: assms)

lemma valid_map_dom: "valid_map f \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> a \<in> el (dom f)"
  by (meson valid_map_welldefined)

lemma ident_right_neutral [simp] : "valid_map f \<Longrightarrow> dom f = x \<Longrightarrow> f \<cdot> (ident x) = f"
  unfolding compose_def ident_def
  apply (simp add: Let_def)
  apply safe
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp?)
  apply (frule (1) valid_map_welldefined)
  apply (erule relcompI[rotated])
  by blast

lemma ident_left_neutral [simp]  : "valid_map f \<Longrightarrow> cod f = x \<Longrightarrow> (ident x) \<cdot> f = f"
  unfolding compose_def ident_def
   apply (simp add: Let_def)
  apply safe
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp?)
  apply (frule (1) valid_map_welldefined)
  apply (erule relcompI)
  by blast

lemma discrete_valid : "valid discrete"
  by (smt (verit, best) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) UNIV_I discrete_def fst_conv mem_Collect_eq snd_conv validI)

(* EXAMPLES *)

definition ex_naturals :: "nat Poset" where
  "ex_naturals \<equiv> \<lparr>  el = UNIV , le_rel = {(x,y). x \<le> y}  \<rparr>"

lemma ex_naturals_valid : "valid ex_naturals"
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) UNIV_I dual_order.refl ex_naturals_def mem_Collect_eq old.prod.case order_antisym order_trans valid_def)

definition ex_divisibility :: "nat Poset" where
  "ex_divisibility \<equiv> \<lparr>  el = UNIV , le_rel = {(x,y). x dvd y }  \<rparr>"

lemma ex_divisibility_valid : "valid ex_divisibility"
  by (smt (verit, ccfv_threshold) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) UNIV_I case_prod_conv dvd_antisym ex_divisibility_def gcd_nat.refl gcd_nat.trans mem_Collect_eq valid_def)

 end