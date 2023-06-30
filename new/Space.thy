section \<open> Space.thy \<close>

theory Space
imports Main

begin

(* Space type *)

type_synonym 'A Open = "'A set"

record 'A RawSpace =
  raw_opens :: "'A Open set"
  raw_universe :: "'A set"

definition valid :: "'A RawSpace \<Rightarrow> bool" where
  "valid rT =
    ({} \<in> raw_opens rT \<and> raw_universe rT \<in> raw_opens rT \<and>
    (\<forall>A. A \<in> raw_opens rT \<longrightarrow> A \<subseteq> raw_universe rT) \<and>
    (\<forall>A B. A \<in> raw_opens rT \<longrightarrow> B \<in> raw_opens rT \<longrightarrow> A \<inter> B \<in> raw_opens rT) \<and>
    (\<forall>U. U \<subseteq> raw_opens rT  \<longrightarrow> (\<Union>U) \<in> raw_opens rT))"

typedef 'A Space = "{ rT :: 'A RawSpace . valid rT}"
proof
  define "rT" where "rT = \<lparr> raw_opens = {{}}, raw_universe = {} \<rparr>"
  have "valid rT"
    using rT_def valid_def by fastforce
  thus "rT \<in> {rT. valid rT}" by auto
qed

setup_lifting type_definition_Space

lift_definition opens :: "'A Space \<Rightarrow> 'A Open set" is raw_opens done

lift_definition universe :: "'A Space \<Rightarrow> 'A set" is raw_universe done

(* Inclusion type *)

record 'A RawInclusion =
  raw_dom :: "'A Open"
  raw_cod :: "'A Open"

abbreviation valid_inc :: "'A RawInclusion \<Rightarrow> bool" where
  "valid_inc ri \<equiv> raw_dom ri \<subseteq> raw_cod ri"

typedef 'A Inclusion = "{ ri :: 'A RawInclusion . valid_inc ri}"
  by (metis RawInclusion.select_convs(1) RawInclusion.select_convs(2) dual_order.refl mem_Collect_eq)

setup_lifting type_definition_Inclusion

lift_definition dom :: "'A Inclusion \<Rightarrow> 'A Open" is raw_dom done

lift_definition cod :: "'A Inclusion \<Rightarrow> 'A Open" is raw_cod done

abbreviation inclusions :: "'A Space \<Rightarrow> 'A Inclusion set" where
  "inclusions T \<equiv> {i.  dom i \<in> opens T \<and> cod i \<in> opens T}"

(* Validity *)

lemma valid_empty : "{} \<in> opens T"
  apply transfer
  using valid_def by blast

lemma valid_universe : " universe T \<in> opens T"
  apply transfer
  using valid_def by blast

lemma valid_union : "U \<subseteq> opens T \<Longrightarrow> (\<Union>U) \<in> opens T"
  apply transfer
  using valid_def by blast

lemma valid_inter : " A \<in> opens T \<Longrightarrow> B \<in> opens T \<Longrightarrow> A \<inter> B \<in> opens T"
  apply transfer
  using valid_def by blast

(* Identity inclusion *)

definition raw_ident :: "'A Open \<Rightarrow> 'A RawInclusion" where
  "raw_ident A \<equiv> \<lparr> raw_dom = A, raw_cod = A \<rparr>"

lift_definition ident :: "'A Open \<Rightarrow> 'A Inclusion" is raw_ident
  by (simp add: raw_ident_def) 

lemma valid_ident_inc : "A \<in> opens T \<Longrightarrow> ident A \<in> inclusions T" 
  apply transfer
  by (simp add: raw_ident_def)

(* Inclusion composition *)

definition "Space_compose_inclusion_endpoint_mistmatch _ _ \<equiv> undefined"

definition raw_compose_inc :: "'A RawInclusion \<Rightarrow> 'A RawInclusion \<Rightarrow> 'A RawInclusion" where
  "raw_compose_inc j i \<equiv>
    if raw_dom j = raw_cod i
    then \<lparr> raw_dom = raw_cod i, raw_cod = raw_cod j \<rparr>
    else Rep_Inclusion (Space_compose_inclusion_endpoint_mistmatch j i)"

lift_definition compose_inc :: "'A Inclusion \<Rightarrow> 'A Inclusion \<Rightarrow> 'A Inclusion" is raw_compose_inc 

