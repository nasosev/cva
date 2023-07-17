section \<open> Space.thy \<close>

theory Space
imports Main
begin

(* Space type *)

type_synonym 'A Open = "'A set"

record 'A Space =
  opens :: "'A Open set"
  universe :: "'A set"

definition valid :: "'A Space \<Rightarrow> bool" where
  "valid T \<equiv>
    (\<forall>A. A \<in> opens T \<longrightarrow> A \<subseteq> universe T) \<and>
    ({} \<in> opens T \<and> universe T \<in> opens T \<and>
    (\<forall>A B. A \<in> opens T \<longrightarrow> B \<in> opens T \<longrightarrow> A \<inter> B \<in> opens T) \<and>
    (\<forall>U. U \<subseteq> opens T  \<longrightarrow> \<Union>U \<in> opens T))"

(* Inclusion type *)

record 'A Inclusion =
  dom :: "'A Open"
  cod :: "'A Open"

abbreviation (input) valid_inc :: "'A Inclusion \<Rightarrow> bool" where
  "valid_inc i \<equiv> dom i \<subseteq> cod i"

definition inclusions :: "'A Space \<Rightarrow> 'A Inclusion set" where
  "inclusions T \<equiv> {i. valid_inc i \<and> dom i \<in> opens T \<and> cod i \<in> opens T}"

lemma inclusion_valid : "i \<in> inclusions T \<Longrightarrow> valid_inc i"
  by (simp add: inclusions_def)

lemma inclusion_dom : "i \<in> inclusions T \<Longrightarrow> dom i \<in> opens T"
  by (simp add: inclusions_def)

lemma inclusion_cod : "i \<in> inclusions T \<Longrightarrow> cod i \<in> opens T"
  by (simp add: inclusions_def)

(* There are built-in constructors (Inclusion.make), but the simplifier/SH doesn't seem to like them? *)
abbreviation (input) make_inc :: "'A Open \<Rightarrow> 'A Open \<Rightarrow> 'A Inclusion" where
"make_inc B A \<equiv> \<lparr> dom = B, cod = A \<rparr>"

(* Validity *)

lemma valid_welldefined : "valid T \<Longrightarrow> (A \<in> opens T \<Longrightarrow> A \<subseteq> universe T)"
  using valid_def by blast

lemma valid_empty : "valid T \<Longrightarrow> {} \<in> opens T"
  using valid_def by blast

lemma valid_universe : "valid T \<Longrightarrow> universe T \<in> opens T"
  using valid_def by blast

lemma valid_union : "valid T \<Longrightarrow> U \<subseteq> opens T \<Longrightarrow> \<Union>U \<in> opens T"
  using valid_def by blast

lemma valid_union2 : "valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> B \<in> opens T \<Longrightarrow> A \<union> B \<in> opens T"
  using valid_union [where ?T=T and ?U="{A,B}"]
  by force

lemma valid_inter : "valid T \<Longrightarrow> A \<in> opens T \<Longrightarrow> B \<in> opens T \<Longrightarrow> A \<inter> B \<in> opens T"
  using valid_def by blast

lemma valid_inc_dom : "i \<in> inclusions T \<Longrightarrow> dom i \<in> opens T"
  by (simp add: inclusions_def)

lemma valid_inc_cod: "i \<in> inclusions T \<Longrightarrow> cod i \<in> opens T"
  by (simp add: inclusions_def)

lemma validI [intro]: "(\<And>A. A \<in> opens T \<Longrightarrow> A \<subseteq> universe T) \<Longrightarrow> {} \<in> opens T \<Longrightarrow> universe T \<in> opens T 
\<Longrightarrow> (\<And>U. U \<subseteq> opens T \<Longrightarrow> \<Union>U \<in> opens T) \<Longrightarrow> (\<And>A B. A \<in> opens T \<Longrightarrow> B \<in> opens T \<Longrightarrow> A \<inter> B \<in> opens T) \<Longrightarrow> valid T"
  by (simp add: valid_def)

(* Inclusion composition *)

definition "Space_compose_inclusion_endpoint_mistmatch _ _ \<equiv> undefined"

definition compose_inc :: "'A Inclusion \<Rightarrow> 'A Inclusion \<Rightarrow> 'A Inclusion" (infixl "\<propto>" 55) where
  "compose_inc j i \<equiv>
    if dom j = cod i
    then \<lparr> dom = dom i, cod = cod j \<rparr>
    else Space_compose_inclusion_endpoint_mistmatch j i"

lemma compose_inc_valid : "valid_inc j \<Longrightarrow> valid_inc i \<Longrightarrow> dom j = cod i \<Longrightarrow> valid_inc (j \<propto> i)"
  by (metis Inclusion.select_convs(1) Inclusion.select_convs(2) compose_inc_def dual_order.trans)

lemma dom_compose_inc [simp] : "dom j = cod i \<Longrightarrow> dom (j \<propto> i) = dom i"
  by (simp add: compose_inc_def)

lemma cod_compose_inc [simp] : "dom j = cod i \<Longrightarrow> cod (j \<propto> i) = cod j"
  by (simp add: compose_inc_def)

(* Identity inclusion *)

definition ident :: "'A Open \<Rightarrow> 'A Inclusion" where
  "ident A \<equiv> make_inc A A"

lemma ident_valid : "A \<in> opens T \<Longrightarrow> valid_inc (ident A)"
  by (simp add: ident_def)

lemma valid_ident_inc : "A \<in> opens T \<Longrightarrow> ident A \<in> inclusions T" 
  by (simp add: ident_def inclusions_def)

lemma compose_inc_ident_left [simp] : "ident (cod i) \<propto> i = i"
  by (simp add: compose_inc_def ident_def)

lemma compose_inc_ident_right [simp] : "i \<propto> ident (dom i) = i"
  by (simp add: compose_inc_def ident_def)

(* Properties *)

lemma inc_cod_sup [simp] : "i \<in> inclusions T \<Longrightarrow> dom i \<union> cod i = cod i"
  using inclusions_def by fastforce

lemma inc_dom_inf [simp] : "i \<in> inclusions T \<Longrightarrow> dom i \<inter> cod i = dom i"
  by (simp add: Int_absorb1 Int_commute inclusions_def)

(* Examples *)

definition discrete :: "'a Space" where
  "discrete = \<lparr> opens = Pow UNIV, universe = UNIV \<rparr>"

lemma valid_discrete : "valid discrete"
  by (simp add: discrete_def valid_def) 

definition codiscrete :: "'a Space" where
  "codiscrete = \<lparr> opens = {{}, UNIV}, universe = UNIV \<rparr>"

lemma valid_codiscrete : "valid codiscrete" 
  unfolding codiscrete_def valid_def 
  apply clarsimp
  by blast

definition sierpinski :: "bool Space" where
  "sierpinski = 
    \<lparr> opens = {{}, {False}, UNIV }, 
      universe = UNIV \<rparr>"

lemma valid_sierpinski : "valid sierpinski"  
  unfolding sierpinski_def valid_def 
  apply clarsimp
  by blast

end
