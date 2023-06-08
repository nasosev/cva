theory Space
imports Main

begin

type_synonym 'A Open = "'A set"


record 'A Space =
  opens :: "'A Open set"
  universe :: "'A set"

definition valid :: "'A Space \<Rightarrow> bool" where
  "valid T =
    ({} \<in> opens T \<and> universe T \<in> opens T \<and>
    (\<forall>A. A \<in> opens T \<longrightarrow> A \<subseteq> universe T) \<and>
    (\<forall>A B. A \<in> opens T \<longrightarrow> B \<in> opens T \<longrightarrow> A \<inter> B \<in> opens T) \<and>
    (\<forall>U. U \<subseteq> opens T  \<longrightarrow> (\<Union>U) \<in> opens T))"

record 'A Inclusion =
  space :: "'A Space"
  dom :: "'A Open"
  cod :: "'A Open"

definition valid_inclusion :: "'A Inclusion \<Rightarrow> bool" where
  "valid_inclusion i =
    (dom i \<subseteq> cod i \<and> dom i \<in> opens (space i) \<and> cod i \<in> opens (space i))"

definition inclusions :: "'A Space \<Rightarrow> 'A Inclusion set" where
  "inclusions T = {i. valid_inclusion i \<and> space i = T}"

definition ident :: "'A Space \<Rightarrow> 'A Open \<Rightarrow> 'A Inclusion" where
  "ident T A = \<lparr> space = T, dom = A, cod = A \<rparr>"

definition compose :: "'A Inclusion \<Rightarrow> 'A Inclusion \<Rightarrow> 'A Inclusion" where
  "compose j i \<equiv>
    if (space j = space i \<and> dom j = cod i)
    then \<lparr> space = space j, dom = dom i, cod = cod j \<rparr>
    else undefined"

(* LEMMAS *)

lemma valid_ident [simp] : "valid T \<Longrightarrow> A \<in> opens T  \<Longrightarrow> valid_inclusion (ident T A)"
  by (simp add: ident_def valid_inclusion_def)

lemma compose_valid [simp] : "valid_inclusion i \<Longrightarrow> valid_inclusion j \<Longrightarrow> space j = space i \<Longrightarrow> dom j = cod i \<Longrightarrow> valid_inclusion (compose j i)"
  by (metis (no_types, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) compose_def dual_order.trans valid_inclusion_def)
  

(* EXAMPLES *)

definition ex_sierpinski :: "bool Space" where
  "ex_sierpinski = \<lparr> opens = {{}, {False},{False,True}}, universe = {False,True} \<rparr>"

lemma ex_sierpinski_valid : "valid ex_sierpinski"
  unfolding ex_sierpinski_def valid_def by auto


definition ex_discrete :: "'a Space" where
  "ex_discrete = \<lparr> opens = Pow UNIV, universe = UNIV \<rparr>"

lemma ex_discrete_valid :  "valid (ex_discrete )"
  unfolding ex_discrete_def valid_def by auto

definition ex_codiscrete :: "'a Space" where
  "ex_codiscrete = \<lparr> opens = {{}, UNIV}, universe = UNIV \<rparr>"

lemma ex_codiscrete_valid : "valid ex_codiscrete"
  unfolding ex_codiscrete_def valid_def by auto




end