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


definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$$" 0) where 
"app f a \<equiv> if a \<in> el (dom f) then (THE b. (a, b) \<in> func f) else undefined"

definition validMap :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"validMap f \<equiv> 
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

lemma ident_valid [simp] : "validMap (ident P)"
  unfolding validMap_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  done

lemma ident_app[simp] : 
  fixes a :: "'a"
  assumes "a \<in> el P" 
  shows "((ident P) $$ a) = a"
  unfolding ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  by (simp add: assms)
  

lemma monotonicity[simp] : 
  "validMap f \<Longrightarrow> a \<in> el (dom f) \<Longrightarrow> a' \<in> el (dom f) \<Longrightarrow> x = dom f \<Longrightarrow> y = cod f \<Longrightarrow> 
    le x a a' \<Longrightarrow> le y (f $$ a) (f $$ a')"
  unfolding validMap_def
  apply safe
  apply auto
  by meson


  

lemma reflexivity: "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> le P x x"
  by (simp add: valid_def)
  

lemma transitivity: "valid P \<Longrightarrow> x \<in> el P\<Longrightarrow> y \<in> el P\<Longrightarrow> z \<in> el P\<Longrightarrow> le P x y \<Longrightarrow> le P y z \<Longrightarrow> le P x z"
  unfolding valid_def
  by meson
  

  
  
    
(* EXAMPLES *)



definition exNaturals :: "nat Poset" where
  "exNaturals \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x \<le> y  \<rparr>"



lemma exNaturals_valid : "valid exNaturals"
  by (smt (verit) Poset.Poset.select_convs(2) dual_order.refl exNaturals_def valid_def order_antisym order_trans)


definition exDivisibility :: "nat Poset" where
  "exDivisibility \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x dvd y  \<rparr>"

lemma exDivisibility_valid : "valid exDivisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(2) dvd_antisym exDivisibility_def gcd_nat.refl gcd_nat.trans valid_def)

definition exDiscrete :: "'a Poset" where
  "exDiscrete \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x = y   \<rparr>"

lemma exDiscrete_valid : "valid exDiscrete"
  by (smt (verit) Poset.Poset.select_convs(2) exDiscrete_def valid_def)



 end