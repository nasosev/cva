theory Poset
imports Main 

begin

record 'a Poset = 
  el :: "'a set"
  le :: "'a  \<Rightarrow>  'a  \<Rightarrow> bool" 

definition isValid :: "'a Poset   \<Rightarrow> bool" where
  "isValid p \<equiv>
    let
      reflexivity = (\<forall>x. x \<in> el p \<longrightarrow> le p x x); 
      antisymmetry = (\<forall>x y. x \<in> el p \<longrightarrow> y \<in> el p \<longrightarrow>  le p x y \<longrightarrow> le p y x \<longrightarrow> x = y); 
      transitivity = (\<forall>x y z. x \<in> el p \<longrightarrow> y \<in> el p \<longrightarrow> z \<in> el p \<longrightarrow> le p x y \<longrightarrow> le p y z \<longrightarrow> le p x z)
    in
      reflexivity \<and> antisymmetry \<and> transitivity"

record ('a, 'b) PosetMap =
  func ::"('a \<times>'b) set"
  dom :: "'a Poset"
  cod :: "'b Poset"


definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 0) where 
"app f a \<equiv> if a \<in> el (dom f) then (THE b. (a, b) \<in> func f) else undefined"

definition isValidMap :: "('a, 'b) PosetMap \<Rightarrow> bool" where
"isValidMap f \<equiv> 
  let 
      le_dom = le (dom f);
      le_cod = le (cod f);
      dom = el (dom f);
      cod = el (cod f);

      welldefined = (\<forall>a b. (a, b) \<in> func f \<longrightarrow> a \<in> dom \<and> b \<in> cod);
      deterministic = (\<forall>a b b'. (a, b) \<in> func f \<and> (a, b') \<in> func f \<longrightarrow> b = b');
      total = (\<forall>a. a \<in> dom \<longrightarrow> (\<exists>b. (a, b) \<in> func f));
      monotone = (\<forall>a a'. a \<in> dom \<and> a' \<in> dom \<and> le_dom a a' \<longrightarrow> le_cod (f $ a) (f $ a'))

  in welldefined \<and> deterministic \<and> total \<and> monotone"



definition compose :: "('b, 'c) PosetMap \<Rightarrow> ('a, 'b) PosetMap \<Rightarrow> ('a, 'c) PosetMap" (infixl "\<circ>" 55) where
  "compose g f \<equiv> 
  if dom g = cod f 
  then \<lparr> func = relcomp (func f) (func g), dom = dom f, cod = cod g \<rparr>
  else undefined"

definition ident :: "'a Poset \<Rightarrow> ('a, 'a) PosetMap" where
"ident p \<equiv> \<lparr> func = Id_on (el p), dom = p, cod = p \<rparr>" 




lemma ident_isValid : "isValidMap (ident p)"
  unfolding isValidMap_def  ident_def app_def
  apply ( simp add: Let_unfold Id_on_def )
  done


  

(* 
lemma fun_app [simp]: "a \<in> el (dom f) \<Longrightarrow> (f $$ a) = func f a"
  by (simp add: app_def) *)

  
    
(* EXAMPLES *)



definition exNaturals :: "nat Poset" where
  "exNaturals \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x \<le> y  \<rparr>"



lemma exNaturals_isValid : "isValid exNaturals"
  by (smt (verit) Poset.Poset.select_convs(2) dual_order.refl exNaturals_def isValid_def order_antisym order_trans)


definition exDivisibility :: "nat Poset" where
  "exDivisibility \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x dvd y  \<rparr>"

lemma exDivisibility_isValid : "isValid exDivisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(2) dvd_antisym exDivisibility_def gcd_nat.refl gcd_nat.trans isValid_def)

definition exDiscrete :: "'a Poset" where
  "exDiscrete \<equiv> \<lparr>  el = UNIV , le = \<lambda> x y . x = y   \<rparr>"

lemma exDiscrete_isValid : "isValid exDiscrete"
  by (smt (verit) Poset.Poset.select_convs(2) exDiscrete_def isValid_def)



 end