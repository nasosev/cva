theory Poset
imports Main

begin

record 'a Poset =
  el :: "'a set"
  le_rel :: "('a \<times> 'a) set"

abbreviation le :: "'a Poset \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
"le P a a' \<equiv> 
  if a \<in> el P \<and> a' \<in> el P 
  then (a, a') \<in> le_rel P 
  else undefined"

(*
abbreviation le_P :: "'a \<Rightarrow> 'a Poset \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<sqsubseteq>\<langle>_\<rangle> _") where
"le_P a P a' \<equiv> (a, a') \<in> le_rel P"
*)

definition valid :: "'a Poset \<Rightarrow> bool" where
  "valid P \<equiv>
    let
      welldefined = (\<forall>x y. (x,y) \<in> le_rel P \<longrightarrow> x \<in> el P \<and> y \<in> el P);
      reflexivity = (\<forall>x. x \<in> el P \<longrightarrow> (x,x) \<in> le_rel P);
      antisymmetry = (\<forall>x y. x \<in> el P \<longrightarrow> y \<in> el P  \<longrightarrow>  (x,y) \<in> le_rel P \<longrightarrow> (y,x) \<in> le_rel P  \<longrightarrow> x = y);
      transitivity = (\<forall>x y z. x \<in> el P\<longrightarrow> y \<in> el P \<longrightarrow> z \<in> el P\<longrightarrow>  (x,y) \<in> le_rel P \<longrightarrow> (y,z) \<in> le_rel P\<longrightarrow> (x,z) \<in> le_rel P)
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
      e_dom = el (dom f);
      e_cod = el (cod f);
      welldefined = valid (dom f) \<and> valid (cod f) \<and> (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> e_dom \<and> b \<in> e_cod);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> e_dom \<longrightarrow> (\<exists>b. (a, b) \<in> func f));
      monotone = (\<forall>a a'. a \<in> e_dom \<and> a' \<in> e_dom \<and> le_dom a a' \<longrightarrow> le_cod (f $$ a) (f $$ a'))

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

definition is_inf :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_inf P U i \<equiv>  U \<subseteq> el P \<and> i \<in> el P \<and>  ((\<forall>u\<in>U. le P i u) \<and> (\<forall>z \<in> el P. (\<forall>u\<in>U. le P z u) \<longrightarrow> le P z i))"

definition is_sup :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_sup P U s \<equiv> U \<subseteq> el P \<and> s \<in> el P \<and>  (s \<in> el P \<and> (\<forall>u\<in>U. le P u s) \<and> (\<forall>z \<in> el P. (\<forall>u\<in>U. le P u z) \<longrightarrow> le P s z))"

definition inf :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a option" where
"inf P U \<equiv> if (\<exists>i. i \<in> el P \<and> is_inf P U i) then Some (SOME i. i \<in> el P \<and> is_inf P U i) else None"

definition sup :: "'a Poset \<Rightarrow> 'a set \<Rightarrow> 'a option" where
"sup P U \<equiv> if (\<exists>s. s \<in> el P \<and> is_sup P U s) then Some (SOME s. s \<in> el P \<and> is_sup P U s) else None"

abbreviation is_complete :: "'a Poset \<Rightarrow> bool" where
"is_complete P \<equiv> valid P \<and> (\<forall>U. U \<subseteq> el P \<longrightarrow> (\<exists>i. is_inf P U i))"

abbreviation is_cocomplete :: "'a Poset \<Rightarrow> bool" where
"is_cocomplete P \<equiv> valid P \<and> (\<forall>U. U \<subseteq> el P \<longrightarrow> (\<exists>s. is_sup P U s))"

(* LEMMAS *)

(* Validity *)

lemma valid_mapI: "valid (dom f) \<Longrightarrow> valid (cod f)  \<Longrightarrow> (\<And>a b. (a, b) \<in> func f \<Longrightarrow>  a \<in> el (dom f) \<and> b \<in> el (cod f)) \<Longrightarrow>
                   (\<And>a b b'. (a, b) \<in> func f \<Longrightarrow> (a, b') \<in> func f \<Longrightarrow> b = b') \<Longrightarrow>
                   (\<And>a. a \<in> el (dom f) \<Longrightarrow> (\<exists>b. (a, b) \<in> func f)) \<Longrightarrow>
                   (\<And>a a'. a \<in> el (dom f) \<and> a' \<in> el (dom f) \<and> le (dom f) a a' \<Longrightarrow> le (cod f) (f $$ a) (f $$ a'))
  \<Longrightarrow> valid_map f "
  by (smt (verit) Poset.valid_map_def) 

lemma product_valid : "valid P \<Longrightarrow> valid Q \<Longrightarrow> valid (P \<times>\<times> Q)"
  unfolding valid_def product_def
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD case_prodI fst_conv mem_Collect_eq mem_Sigma_iff prod.collapse snd_conv)

lemma pom_eqI: "cod f = cod g \<Longrightarrow> dom f = dom g \<Longrightarrow> func f = func g \<Longrightarrow> (f :: ('a, 'b) PosetMap) = g"
  by simp

theorem validI :
  fixes P :: "'a Poset"
  assumes welldefined : "(\<And>x y. (x,y) \<in> le_rel P \<Longrightarrow> x \<in> el P \<and> y \<in> el P)"
  assumes reflexivity : "(\<And>x. x \<in> el P \<Longrightarrow> le P x x)"
  assumes antisymmetry : "(\<And>x y. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow>  le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y)"
  assumes transitivity : "(\<And>x y z. x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P \<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z)"
    shows "valid P"
  by (smt (verit, best) antisymmetry reflexivity transitivity valid_def welldefined)

lemma valid_welldefined : "valid P \<Longrightarrow> (x,y) \<in> le_rel P \<Longrightarrow> x \<in> el P \<and> y \<in> el P"
  by (smt (verit) valid_def)

lemma valid_reflexivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> le P x x"
  by (smt (verit) valid_def)

lemma valid_transitivity : "valid P \<Longrightarrow> x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> z \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z"
  by (smt (verit, ccfv_threshold) valid_def)

lemma valid_antisymmetry : "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> y \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y x \<Longrightarrow> x = y"
  by (smt (verit, ccfv_threshold) valid_def)

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
  apply auto
  apply meson
   apply metis
  by metis

lemma fun_app : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> (a, f $$ a) \<in> func f"
  by (metis app_def the_equality valid_map_deterministic valid_map_total)

lemma fun_app2 : "valid_map f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> fa = f $$ a \<Longrightarrow> fa \<in> el (cod f)"
  by (meson fun_app valid_map_welldefined)

lemma fun_ext : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom f = dom g \<Longrightarrow> cod f = cod g \<Longrightarrow> (\<forall>a \<in> el (dom f). f $$ a = g $$ a) \<Longrightarrow> f = g"
  apply (rule pom_eqI; clarsimp?)
  apply (intro set_eqI iffI; clarsimp)
   apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  apply (metis fun_app valid_map_deterministic valid_map_welldefined)
  done

lemma dom_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> dom (g \<cdot> f) = dom f"
  unfolding compose_def
  by (simp add: Let_def)

lemma cod_compose [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> cod (g \<cdot> f) = cod g"
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

lemma valid_dom : "valid_map f \<Longrightarrow> valid (dom f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

lemma valid_cod : "valid_map f \<Longrightarrow> valid (cod f)"
  apply (subst (asm) valid_map_def)
  by (clarsimp simp: Let_unfold)

lemma compose_app: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> dom g = cod f \<Longrightarrow> (g \<cdot> f) $$ a = g $$ (f $$ a)"
  apply (clarsimp simp: app_def, safe; clarsimp?)
   apply (smt (verit, del_insts) PosetMap.select_convs(1) compose_def compose_deterministic fun_app relcomp.relcompI theI valid_map_deterministic)
  by (metis app_def fun_app2)

lemma compose_monotone :
  fixes f :: "('a,'b) PosetMap" and g :: "('b,'c) PosetMap" and a a' :: "'a"
  assumes f_valid : "valid_map f" and g_valid : "valid_map g"
  and a_elem : "a \<in> el (dom f)" and a'_elem : "a' \<in> el (dom f)" 
  and le_aa' : "le (dom f) a a'"
  and dom_cod : "dom g = cod f"
shows "le (cod g) ((g \<cdot> f) $$ a) ((g \<cdot> f) $$ a')"
proof -
  have "le (cod f) (f $$ a) (f $$ a')" using valid_map_monotone
    by (metis a'_elem a_elem f_valid le_aa')   
  moreover have  "le (cod g) (g $$ (f $$ a)) (g $$ (f $$ a'))" using valid_map_monotone
    by (metis a'_elem a_elem calculation dom_cod f_valid fun_app2 g_valid) 
  ultimately show ?thesis using compose_app
    by (metis a'_elem a_elem dom_cod f_valid g_valid)
qed

lemma compose_valid : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<cdot> f)"
  apply (rule valid_mapI; clarsimp?)
       apply (simp add:  valid_dom)
  apply (simp add:  valid_cod)
  apply (simp add:  compose_welldefined )
  apply (simp add: compose_deterministic)
   apply (simp add: compose_total )
  by (simp add: compose_monotone)

lemma comp_app [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> (a, b) \<in> func f \<Longrightarrow> dom g = cod f \<Longrightarrow>
                (b, c) \<in> func g \<Longrightarrow> (g \<cdot> f) $$ a = c"
  apply (rule fun_app_iff)
  using compose_valid apply blast
  by (simp add: compose_def relcomp.relcompI)

lemma ident_valid  : "valid P \<Longrightarrow> valid_map (ident P)"
  unfolding valid_map_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by blast

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


(* Infima & suprema *)

lemma inf_unique : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> i \<in> el P\<Longrightarrow> i' \<in> el P \<Longrightarrow> is_inf P U i \<Longrightarrow> is_inf P U i' \<Longrightarrow> i = i'"
  unfolding is_inf_def
  by (metis valid_antisymmetry)

lemma sup_unique : "valid P  \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> s \<in> el P\<Longrightarrow> s' \<in> el P \<Longrightarrow> is_sup P U s \<Longrightarrow> is_sup P U s' \<Longrightarrow> s = s'"
  unfolding is_sup_def
  by (metis valid_antisymmetry)

lemma inf_is_glb : "valid P  \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> i \<in> el P \<Longrightarrow> is_inf P U i
\<Longrightarrow> \<forall>u\<in>U. le P z u \<Longrightarrow> le P z i"
  by (simp add: is_inf_def)

lemma sup_is_lub : "valid P  \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> z \<in> el P \<Longrightarrow> s \<in> el P \<Longrightarrow> is_sup P U s
\<Longrightarrow> \<forall>u\<in>U. le P u z \<Longrightarrow> le P s z"
  by (simp add: is_sup_def)

lemma inf_smaller : "valid P  \<Longrightarrow> U \<subseteq> el P  \<Longrightarrow> i \<in> el P \<Longrightarrow> is_inf P U i \<Longrightarrow> \<forall> u \<in> U. le P i u"
  unfolding is_inf_def
  by blast


lemma sup_greater : "valid P  \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> s \<in> el P  \<Longrightarrow> is_sup P U s \<Longrightarrow> \<forall> u \<in> U. le P u s"
  unfolding is_sup_def
  by blast

lemma some_inf_is_inf : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> i \<in> el P \<Longrightarrow> inf P U = Some i \<Longrightarrow> is_inf P U i"
  unfolding inf_def
  by (metis (no_types, lifting) option.distinct(1) option.inject someI_ex)

lemma some_sup_is_sup : "valid P\<Longrightarrow> U \<subseteq> el P \<Longrightarrow> sup P U = Some s \<Longrightarrow> is_sup P U s"
  unfolding sup_def
  by (metis (no_types, lifting) Poset.sup_unique option.distinct(1) option.inject some_equality)

lemma complete_inf_not_none : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> is_complete P \<Longrightarrow> inf P U \<noteq> None"
  by (simp add: inf_def is_inf_def)

lemma cocomplete_sup_not_none : "valid P \<Longrightarrow> U \<subseteq> el P \<Longrightarrow> is_cocomplete P \<Longrightarrow> sup P U \<noteq> None"
  by (simp add: is_sup_def sup_def)

lemma complete_equiv_cocomplete : "is_complete P \<longleftrightarrow> is_cocomplete P"
proof
  assume "is_complete P"
  fix U
  define "s" where "s = inf P {a \<in> Poset.el P . (\<forall> u \<in> U . le P u a)}"
  have "s = sup P U" 
    oops

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