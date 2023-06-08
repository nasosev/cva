theory Poset
imports Main

begin
declare [[show_types]]
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

definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$$" 999) where
"app f a \<equiv> if a \<in> el (dom f) then (THE b. (a, b) \<in> func f) else undefined"

definition valid_map :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"valid_map f \<equiv>
  let
      le_dom = le (dom f);
      le_cod = le (cod f);
      dom = el (dom f);
      cod = el (cod f);

      welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom \<and> b \<in> cod);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> dom \<longrightarrow> (\<exists>b. (a, b) \<in> func f));
      monotone = (\<forall>a a'. a \<in> dom \<and> a' \<in> dom \<and> le_dom a a' \<longrightarrow> le_cod (f $$ a) (f $$ a'))

  in welldefined \<and> deterministic \<and> total \<and> monotone"

definition compose :: "('b, 'c) PosetMap \<Rightarrow> ('a, 'b) PosetMap \<Rightarrow> ('a, 'c) PosetMap" (infixl "\<cdot>" 55) where
  "compose g f \<equiv>
  if dom g = cod f
  then \<lparr> func = relcomp (func f) (func g), dom = dom f, cod = cod g \<rparr>
  else undefined"

definition ident :: "'a Poset \<Rightarrow> ('a, 'a) PosetMap" where
"ident P \<equiv> \<lparr> func = Id_on (el P), dom = P, cod = P \<rparr>"

(* LEMMAS *)

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


lemma compose_monotone [simp]: "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> le (dom f) a a' \<Longrightarrow> le (cod (g \<cdot> f)) ((g \<cdot> f) $$ a) ((g \<cdot> f) $$ a')"
  unfolding compose_def valid_map_def
  apply (simp_all add: Let_def)
  apply safe
  sorry


lemma compose_valid [simp] : "valid_map f \<Longrightarrow> valid_map g \<Longrightarrow> dom g = cod f \<Longrightarrow> valid_map (g \<cdot> f)"
  by (smt (verit) cod_compose compose_deterministic compose_monotone compose_total compose_welldefined dom_compose valid_map_def)

lemma ident_valid [simp] : "valid_map (ident P)"
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

lemma ident_right_neutral [simp] : "valid_map f \<Longrightarrow> dom f = x \<Longrightarrow> f \<cdot> (ident x) = f"
  unfolding compose_def ident_def
  apply (simp add: Let_def)
  apply safe
  sorry

lemma ident_left_neutral [simp] : "valid_map f \<Longrightarrow> cod f = x \<Longrightarrow> (ident x) \<cdot> f = f"
  sorry

(* EXAMPLES *)

definition ex_naturals :: "nat Poset" where
  "ex_naturals \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x \<le> y  \<rparr>"

lemma ex_naturals_valid : "valid ex_naturals"
  by (smt (verit) Poset.Poset.select_convs(2) dual_order.refl ex_naturals_def valid_def order_antisym order_trans)


definition ex_divisibility :: "nat Poset" where
  "ex_divisibility \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x dvd y  \<rparr>"

lemma ex_divisibility_valid : "valid ex_divisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(2) dvd_antisym ex_divisibility_def gcd_nat.refl gcd_nat.trans valid_def)

definition ex_discrete :: "'a Poset" where
  "ex_discrete \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x = y   \<rparr>"

lemma ex_discrete_valid : "valid ex_discrete"
  by (smt (verit) Poset.Poset.select_convs(2) ex_discrete_def valid_def)



 end