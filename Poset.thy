theory Poset
imports Main 

begin

record 'a Poset = 
  elements :: "'a set"
  le :: "'a  \<Rightarrow>  'a  \<Rightarrow> bool"

definition isValid :: "'a Poset   \<Rightarrow> bool" where
  "isValid p \<equiv>
    let
      reflexivity = (\<forall>x. x \<in> elements p \<longrightarrow> le p x x); 
      antisymmetry = (\<forall>x y. x \<in> elements p \<longrightarrow> y \<in> elements p \<longrightarrow> le p x y \<longrightarrow> le p y x \<longrightarrow> x = y); 
      transitivity = (\<forall>x y z. x \<in> elements p \<longrightarrow> y \<in> elements p \<longrightarrow> z \<in> elements p \<longrightarrow> le p x y \<longrightarrow> le p y z \<longrightarrow> le p x z)
    in
      reflexivity \<and> antisymmetry \<and> transitivity"

record ('a, 'b) PosetMap =
  func ::"'a \<Rightarrow> 'b" 
  dom :: "'a Poset"
  cod :: "'b Poset"

definition isValidMap :: "('a, 'b) PosetMap \<Rightarrow> bool" where
  "isValidMap f \<equiv> 
    let 
       welldefined = (\<forall>x. x \<in> elements (dom f) \<longrightarrow> func f x \<in> elements (cod f));
       monotonicity = (\<forall>x y. x \<in> elements (dom f) \<longrightarrow> y \<in> elements (dom f) \<longrightarrow> le (dom f) x y \<longrightarrow> le (cod f) (func f x) (func f y))
    in
        welldefined \<and> monotonicity"


definition compose :: "('b, 'c) PosetMap \<Rightarrow> ('a, 'b) PosetMap \<Rightarrow> ('a, 'c) PosetMap" (infixl "\<circ>" 55) where
  "compose g f \<equiv> \<lparr>  func = (func g) o (func f), dom = dom f, cod = cod g \<rparr>" 


definition app :: "('a, 'b) PosetMap \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$$" 0) where
   "app f x \<equiv> if x \<in> elements (dom f) then func f x else undefined"

definition ident :: "'a Poset \<Rightarrow> ('a, 'a) PosetMap" where
  "ident p \<equiv> \<lparr> func = id, dom = p, cod = p \<rparr>"

lemma ident_isValid : "isValidMap (ident p)"
  by (simp add: ident_def isValidMap_def)

    
(* EXAMPLES *)



definition exNaturals :: "nat Poset" where
  "exNaturals \<equiv> \<lparr>  elements = UNIV , le = \<lambda> x y . x \<le> y  \<rparr>"



lemma exNaturals_isValid : "isValid exNaturals"
  by (smt (verit) Poset.Poset.select_convs(2) dual_order.refl exNaturals_def isValid_def order_antisym order_trans)


definition exDivisibility :: "nat Poset" where
  "exDivisibility \<equiv> \<lparr>  elements = UNIV , le = \<lambda> x y . x dvd y  \<rparr>"

lemma exDivisibility_isValid : "isValid exDivisibility"
  by (smt (verit, del_insts) Poset.Poset.select_convs(2) dvd_antisym exDivisibility_def gcd_nat.refl gcd_nat.trans isValid_def)

definition exDiscrete :: "'a Poset" where
  "exDiscrete \<equiv> \<lparr>  elements = UNIV , le = \<lambda> x y . x = y   \<rparr>"

lemma exDiscrete_isValid : "isValid exDiscrete"
  by (smt (verit) Poset.Poset.select_convs(2) exDiscrete_def isValid_def)

end