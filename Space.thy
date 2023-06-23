section \<open> Space.thy \<close>

text \<open>
  Theory      :  Space.thy

  This theory formalizes the notions of topological spaces and inclusions between open sets.
  It introduces the definition of a Space, the notion of validity of a Space and an Inclusion.
  It also defines operations on Inclusions such as composition and identity, and properties 
  of these structures and operations are proven as lemmas.
--------------------------------------------------------------------------------
\<close>

theory Space
imports Main

begin

text \<open> 
Type synonym 'A Open is used to represent a set of 'A elements. 
\<close>
type_synonym 'A Open = "'A set"

text \<open> 
  Record 'A Space encapsulates the structure of a topological space. 
  It includes a set of opens (sets of elements of type 'A) and a universe (set of all elements of type 'A). 
\<close>
record 'A Space =
  opens :: "'A Open set"
  universe :: "'A set"

text \<open> 
  Definition of validity of a topological space. A space is considered valid if it fulfills the axioms 
  of topology which include the presence of the empty set and the universe in the opens, closure under 
  intersection and union. 
\<close>
definition valid :: "'A Space \<Rightarrow> bool" where
  "valid T =
    ({} \<in> opens T \<and> universe T \<in> opens T \<and>
    (\<forall>A. A \<in> opens T \<longrightarrow> A \<subseteq> universe T) \<and>
    (\<forall>A B. A \<in> opens T \<longrightarrow> B \<in> opens T \<longrightarrow> A \<inter> B \<in> opens T) \<and>
    (\<forall>U. U \<subseteq> opens T  \<longrightarrow> (\<Union>U) \<in> opens T))"

text \<open> 
  Record 'A Inclusion represents an inclusion, a structure that maps one open set to another within a space.
\<close>
record 'A Inclusion =
  space :: "'A Space"
  dom :: "'A Open"
  cod :: "'A Open"

text \<open> 
  Definition of validity of an inclusion. An inclusion is valid if it fulfills certain conditions 
  including the validity of the space and the property that the domain is a subset of the codomain. 
\<close>
definition valid_inclusion :: "'A Inclusion \<Rightarrow> bool" where
  "valid_inclusion i \<equiv> valid (space i) \<and>
    (dom i \<subseteq> cod i \<and> dom i \<in> opens (space i) \<and> cod i \<in> opens (space i))"

text \<open> 
  Definition of inclusions of a space. It represents the set of all valid inclusions of a given space. 
\<close>
definition inclusions :: "'A Space \<Rightarrow> 'A Inclusion set" where
  "inclusions T \<equiv> {i. valid_inclusion i \<and> space i = T}"

text \<open> 
  Definition of an identity inclusion for a given open in a space. An identity inclusion is a mapping 
  from an open to itself within the space. 
\<close>
definition ident :: "'A Space \<Rightarrow> 'A Open \<Rightarrow> 'A Inclusion" where
  "ident T A \<equiv> \<lparr> space = T, dom = A, cod = A \<rparr>"

text \<open> 
  Definition of composition of inclusions. The composition of two inclusions results in a new 
  inclusion if they share the same space and the domain of the second inclusion equals the 
  codomain of the first inclusion. If these conditions are not met, the result is undefined.
\<close>
definition compose :: "'A Inclusion \<Rightarrow> 'A Inclusion \<Rightarrow> 'A Inclusion" where
  "compose j i \<equiv>
    if (space j = space i \<and> dom j = cod i)
    then \<lparr> space = space j, dom = dom i, cod = cod j \<rparr>
    else undefined"

text \<open> 
  Definition of inclusion making. This creates an inclusion from two open sets within a space.
\<close>
definition make_inclusion :: "'A Space \<Rightarrow> 'A Open \<Rightarrow> 'A Open \<Rightarrow> 'A Inclusion" where
  "make_inclusion T B A \<equiv> \<lparr> space = T, dom = B, cod = A \<rparr>"

text \<open> 
  The following lemmas correspond to various properties of the structures and operations defined above.
\<close>

text \<open> 
The empty set is always an element of opens of a valid space. 
\<close>
lemma valid_empty : "valid T \<Longrightarrow> {} \<in> opens T"
  by (simp add: valid_def)

text \<open> The universe is always an element of opens of a valid space. \<close>
lemma valid_universe : "valid T \<Longrightarrow> universe T \<in> opens T"
  by (simp add: valid_def)

text \<open> The union of a subset of opens of a valid space is an element of the opens of that space. \<close>
lemma valid_union : "valid T \<Longrightarrow> U \<subseteq> opens T \<Longrightarrow> (\<Union>U) \<in> opens T"
  by (simp add: valid_def)

text \<open> The intersection of two elements of opens of a valid space is an element of the opens of that space. \<close>
lemma valid_inter : "valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> B \<in> opens T \<Longrightarrow> A \<inter> B \<in> opens T"
  by (simp add: valid_def)

text \<open> 
An inclusion is valid if it satisfies the conditions of 'valid\_inclusion'. 
\<close>
lemma valid_inclusionI : "valid (space i) \<Longrightarrow> dom i \<subseteq> cod i \<Longrightarrow> dom i \<in> opens (space i) \<Longrightarrow> cod i \<in> opens (space i) \<Longrightarrow> valid_inclusion i"
  using valid_inclusion_def by blast

text \<open> The identity inclusion of an open in a valid space is a valid inclusion. \<close>
lemma valid_ident : "valid T \<Longrightarrow> A \<in> opens T  \<Longrightarrow> valid_inclusion (ident T A)"
  by (simp add: ident_def valid_inclusion_def)

text \<open> 
The composition of two valid inclusions in the same space where the domain of the second one is 
   the codomain of the first one, is a valid inclusion. 
\<close>
lemma compose_valid : "valid_inclusion i \<Longrightarrow> valid_inclusion j \<Longrightarrow> space j = space i \<Longrightarrow> dom j = cod i \<Longrightarrow> valid_inclusion (compose j i)"
  by (metis (no_types, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) compose_def dual_order.trans valid_inclusion_def)

text \<open> The domain of the composition of two valid inclusions in the same space where the domain of 
   the second one is the codomain of the first one, is the domain of the first inclusion. \<close>
lemma dom_compose [simp] : "valid_inclusion i \<Longrightarrow> valid_inclusion j \<Longrightarrow> space j = space i \<Longrightarrow> dom j = cod i  \<Longrightarrow> dom (compose j i) = dom i"
  by (simp add: compose_def)

text \<open> The codomain of the composition of two valid inclusions in the same space where the domain of 
   the second one is the codomain of the first one, is the codomain of the second inclusion. \<close>
lemma cod_compose [simp] : "valid_inclusion i \<Longrightarrow> valid_inclusion j \<Longrightarrow> space j = space i \<Longrightarrow> dom j = cod i  \<Longrightarrow> cod (compose j i) = cod j"
  by (simp add: compose_def)

text \<open> The composition of an identity inclusion and another inclusion from the same open in the same 
   space is equal to the original inclusion. \<close>
lemma compose_ident_left [simp] : "valid_inclusion i \<Longrightarrow> space i = T \<Longrightarrow> dom i = A \<Longrightarrow> cod i = B \<Longrightarrow> compose (ident T B) i = i"
  by (simp add: compose_def ident_def)

text \<open> The composition of an inclusion and the identity inclusion from the same open in the same 
   space is equal to the original inclusion. \<close>
lemma compose_ident_right [simp] : "valid_inclusion i \<Longrightarrow> space i = T \<Longrightarrow> dom i = A \<Longrightarrow> cod i = B \<Longrightarrow> compose i (ident T A) = i"
  by (simp add: compose_def ident_def)

text \<open> An inclusion from the inclusions of a valid space is a valid inclusion. \<close>
lemma valid_inclusions : "valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> valid_inclusion i"
  using inclusions_def by blast

text \<open> The codomain of an inclusion from the inclusions of a valid space is an element of opens of that space. \<close>
lemma valid_inclusion_cod : "valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> A = cod i \<Longrightarrow> A \<in> opens T"
  by (metis (mono_tags, lifting) inclusions_def mem_Collect_eq valid_inclusion_def)

text \<open> The domain of an inclusion from the inclusions of a valid space is an element of opens of that space. \<close>
lemma valid_inclusion_dom : "valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> B = dom i \<Longrightarrow> B \<in> opens T"
  by (metis (mono_tags, lifting) inclusions_def mem_Collect_eq valid_inclusion_def)

text \<open> An inclusion made from two opens in a valid space that are subsets of each other is a valid inclusion. \<close>
lemma valid_make_inclusion : "valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> B \<in> opens T \<Longrightarrow> B \<subseteq> A \<Longrightarrow> i = make_inclusion T B A \<Longrightarrow> valid_inclusion i"
  by (simp add: make_inclusion_def valid_inclusion_def)

text \<open> An inclusion made from an open to itself in a valid space is the same as the identity inclusion of that open. \<close>
lemma make_inclusion_ident [simp] : "valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> make_inclusion T A A = ident T A"
  by (simp add: ident_def make_inclusion_def)

text \<open> The union of the domain and codomain of an inclusion from the inclusions of a valid space is the codomain. \<close>
lemma inc_cod_sup [simp] : "valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> B = dom i \<Longrightarrow> A = cod i \<Longrightarrow> A \<union> B = A"
  by (meson Un_absorb2 valid_inclusion_def valid_inclusions)

text \<open> The intersection of the domain and codomain of an inclusion from the inclusions of a valid space is the domain. \<close>
lemma inc_dom_inf [simp] : "valid T \<Longrightarrow> i \<in> inclusions T \<Longrightarrow> B = dom i \<Longrightarrow> A = cod i \<Longrightarrow> A \<inter> B = B"
  by (meson Int_absorb1 valid_inclusion_def valid_inclusions)

text \<open> 
  The following are examples of specific spaces and the validation of their properties.
\<close>

text \<open> The Sierpinski space is a valid space. \<close>
definition ex_sierpinski :: "bool Space" where
  "ex_sierpinski = \<lparr> opens = {{}, {False},{False,True}}, universe = {False,True} \<rparr>"

lemma ex_sierpinski_valid : "valid ex_sierpinski"
  unfolding ex_sierpinski_def valid_def by auto

text \<open> The discrete space is a valid space. \<close>
definition ex_discrete :: "'a Space" where
  "ex_discrete = \<lparr> opens = Pow UNIV, universe = UNIV \<rparr>"

lemma ex_discrete_valid : "valid ex_discrete"
  unfolding ex_discrete_def valid_def by auto

end
