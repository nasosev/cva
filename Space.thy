theory Space
imports Main

begin

type_synonym 'A Open = "'A set"


record 'A Space = 
  opens :: "'A Open set"
  universe :: "'A set"

definition isValid :: "'A Space \<Rightarrow> bool" where
  "isValid T = 
    ({} \<in> opens T \<and> universe T \<in> opens T \<and>
    (\<forall>A. A \<in> opens T \<longrightarrow> A \<subseteq> universe T) \<and>
    (\<forall>A B. A \<in> opens T \<longrightarrow> B \<in> opens T \<longrightarrow> A \<inter> B \<in> opens T) \<and>
    (\<forall>U. U \<subseteq> opens T  \<longrightarrow> (\<Union>U) \<in> opens T))"

record 'A Inclusion = 
  space :: "'A Space"
  dom :: "'A Open"
  cod :: "'A Open"

definition isValidInclusion :: "'A Inclusion \<Rightarrow> bool" where
  "isValidInclusion i = 
    (dom i \<subseteq> cod i \<and> dom i \<in> opens (space i) \<and> cod i \<in> opens (space i))"

 


definition inclusions :: "'A Space \<Rightarrow> 'A Inclusion set" where
  "inclusions T = {i. isValidInclusion i \<and> space i = T}"
  
definition ident :: "'A Space \<Rightarrow> 'A Open \<Rightarrow> 'A Inclusion" where
  "ident T A = \<lparr> space = T, dom = A, cod = A \<rparr>"

definition compose :: "'A Inclusion \<Rightarrow> 'A Inclusion \<Rightarrow> 'A Inclusion" where
  "compose j i \<equiv> 
    if (space j = space i \<and> dom j = cod i) 
    then \<lparr> space = space j, dom = dom i, cod = cod j \<rparr> 
    else undefined"



(* EXAMPLES *)

definition exSierpinski :: "bool Space" where
  "exSierpinski = \<lparr> opens = {{}, {False},{False,True}}, universe = {False,True} \<rparr>"

lemma "isValid exSierpinski"
  unfolding exSierpinski_def isValid_def by auto


definition exDiscrete :: "'a set \<Rightarrow> 'a Space" where
  "exDiscrete X = \<lparr> opens = Pow X, universe = X \<rparr>"

lemma "isValid (exDiscrete X)"
  unfolding exDiscrete_def isValid_def by auto

definition exCodiscrete :: "'a set \<Rightarrow> 'a Space" where
  "exCodiscrete X = \<lparr> opens = {{}, X}, universe = X \<rparr>"

lemma "isValid (exCodiscrete X)"
  unfolding exCodiscrete_def isValid_def by auto




end