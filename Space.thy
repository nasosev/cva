theory Space
imports Main

begin

type_synonym 't Open = "'t set"


record 't Space = 
  opens :: "'t Open set"
  universe :: "'t set"

definition isValid :: "'t Space \<Rightarrow> bool" where
  "isValid t = 
    ({} \<in> opens t \<and> universe t \<in> opens t \<and>
    (\<forall>a. a \<in> opens t \<longrightarrow> a \<subseteq> universe t) \<and>
    (\<forall>a b. a \<in> opens t \<longrightarrow> b \<in> opens t \<longrightarrow> a \<inter> b \<in> opens t) \<and>
    (\<forall>U. U \<subseteq> opens t  \<longrightarrow> (\<Union>U) \<in> opens t))"

record 't Inclusion = 
  space :: "'t Space"
  dom :: "'t Open"
  cod :: "'t Open"

definition isValidInclusion :: "'t Inclusion \<Rightarrow> bool" where
  "isValidInclusion i = 
    (dom i \<subseteq> cod i \<and> dom i \<in> opens (space i) \<and> cod i \<in> opens (space i))"

 


definition inclusions :: "'t Space \<Rightarrow> 't Inclusion set" where
  "inclusions t = {i. isValidInclusion i \<and> space i = t}"
  
definition ident :: "'t Space \<Rightarrow> 't Open \<Rightarrow> 't Inclusion" where
  "ident t a = \<lparr> space = t, dom = a, cod = a \<rparr>"

definition compose :: "'t Inclusion \<Rightarrow> 't Inclusion \<Rightarrow> 't Inclusion" where
  "compose j i \<equiv> 
    if (space j = space i \<and> dom j = cod i) 
    then \<lparr> space = space j, dom = dom i, cod = cod j \<rparr> 
    else undefined"
end