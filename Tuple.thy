section \<open> Tuple.thy \<close>

theory Tuple
  imports Main Presheaf Prealgebra OVA
begin

type_synonym ('A, 'x) Relation = "('A, 'x set) Valuation"

record ('A, 'x) TupleSystem =
  presheaf :: "('A, 'x) Presheaf"

abbreviation space :: "('A, 'x) TupleSystem \<Rightarrow> 'A Space" where
"space T \<equiv> Presheaf.space (presheaf T)"

abbreviation ob :: "('A,'x) TupleSystem \<Rightarrow> ('A Open, 'x set) Function" where
"ob T \<equiv> Presheaf.ob (presheaf T)"

abbreviation ar :: "('A,'x) TupleSystem \<Rightarrow> ('A Inclusion, ('x, 'x) Function) Function" where
"ar T \<equiv> Presheaf.ar (presheaf T)"

definition valid :: "('A, 'x) TupleSystem \<Rightarrow> bool" where
  "valid T \<equiv>
    let
      welldefined = Presheaf.valid (presheaf T);
      flasque = \<forall>i. i \<in> inclusions (space T) \<longrightarrow> Function.is_surjective (ar T \<cdot> i);
      binary_gluing = (\<forall> A B a b . A \<in> opens (space T) \<longrightarrow> B \<in> opens (space T) 
        \<longrightarrow> a \<in> ob T \<cdot> A
        \<longrightarrow> b \<in> ob T \<cdot> B
        \<longrightarrow> (ar T \<cdot> (make_inc (A \<inter> B) A)) \<cdot> a = (ar T \<cdot> (make_inc (A \<inter> B) B)) \<cdot> b
        \<longrightarrow> (\<exists> c . c \<in> (ob T \<cdot> (A \<union> B)) \<and> (ar T \<cdot> (make_inc A (A \<union> B))) \<cdot> c = a \<and> (ar T \<cdot> (make_inc B (A \<union> B))) \<cdot> c = b))
    in
    welldefined \<and> flasque \<and> binary_gluing"

(* Relational OVA generated from a tuple system *)

definition rel_prealg :: "('A, 'x) TupleSystem \<Rightarrow> ('A, 'x set) Prealgebra" where
  "rel_prealg T \<equiv>
    let
      R0 = \<lparr> Function.cod = UNIV, func = { (A, Poset.powerset (ob T \<cdot> A)) | A . A \<in> opens (space T) } \<rparr>;
      R1 = \<lparr> Function.cod = UNIV, func = { (i, Poset.direct_image (ar T \<cdot> i)) | i . i \<in> inclusions (space T) } \<rparr>
    in
    \<lparr> Prealgebra.space = space T, Prealgebra.ob = R0, Prealgebra.ar = R1 \<rparr>"

definition rel_neutral :: "('A, 'x) TupleSystem \<Rightarrow> ('A, unit, 'x set) PrealgebraMap" where
  "rel_neutral T \<equiv>
    let
      dom = Prealgebra.terminal (space T);
      cod = rel_prealg T;
      nat = \<lparr> Function.cod = UNIV , 
              func = {(A, Poset.const (Prealgebra.ob dom \<cdot> A) (Prealgebra.ob cod \<cdot> A) (ob T \<cdot> A)) | A . A \<in> opens (space T)}  \<rparr>
    in
      \<lparr> dom = dom, cod = cod, nat = nat \<rparr>"

definition rel_semigroup :: "('A, 'x) TupleSystem \<Rightarrow> (('A, 'x) Relation) Semigroup" where
  "rel_semigroup T \<equiv> 
    let
      R = rel_prealg T;
      mult = \<lparr> PosetMap.dom = gc R \<times>\<times> gc R, 
              cod = gc R, 
              func = { (((A,a), (B,b)), (C, c)) | A a B b C c .
                          A \<in> opens (space T)
                        \<and> B \<in> opens (space T)  
                        \<and> C = A \<union> B
                        \<and> a \<in> el (Prealgebra.ob R \<cdot> A)
                        \<and> b \<in> el (Prealgebra.ob R \<cdot> B)
                        \<and> c = { t . t \<in> ob T \<cdot> C
                                        \<and> (ar T \<cdot> (make_inc A C)) \<cdot> t \<in> a     
                                        \<and> (ar T \<cdot> (make_inc B C)) \<cdot> t \<in> b } } \<rparr>
    in
      \<lparr> Semigroup.mult = mult \<rparr>"

(* Validity of prealgebra *)

lemma valid_welldefined :  "valid T \<Longrightarrow> Presheaf.valid (presheaf T)" unfolding valid_def
  by (simp add: Let_def)

lemma valid_flasque : "valid T \<Longrightarrow> i \<in> inclusions (space T) \<Longrightarrow> Function.is_surjective (ar T \<cdot> i)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_binary_gluing : "valid T \<Longrightarrow> A \<in> opens (space T) \<Longrightarrow> B \<in> opens (space T) \<Longrightarrow> a \<in> ob T \<cdot> A \<Longrightarrow> b \<in> ob T \<cdot> B
        \<Longrightarrow> (ar T \<cdot> (make_inc (A \<inter> B) A)) \<cdot> a = (ar T \<cdot> (make_inc (A \<inter> B) B)) \<cdot> b
        \<Longrightarrow> (\<exists> c . c \<in> (ob T \<cdot> (A \<union> B)) \<and> (ar T \<cdot> (make_inc A (A \<union> B))) \<cdot> c = a \<and> (ar T \<cdot> (make_inc B (A \<union> B))) \<cdot> c = b)"
  unfolding valid_def
  by (simp add: Let_def)

lemma validI [intro] :
  fixes T :: "('A, 'x) TupleSystem"
  assumes welldefined : "Presheaf.valid (presheaf T)"
  and flasque : "\<And>i. i \<in> inclusions (space T) \<Longrightarrow> Function.is_surjective (ar T \<cdot> i)"
  and binary_gluing : "\<And> A B a b . A \<in> opens (space T) \<Longrightarrow> B \<in> opens (space T) 
        \<Longrightarrow> a \<in> ob T \<cdot> A
        \<Longrightarrow> b \<in> ob T \<cdot> B
        \<Longrightarrow> (ar T \<cdot> (make_inc (A \<inter> B) A)) \<cdot> a = (ar T \<cdot> (make_inc (A \<inter> B) B)) \<cdot> b
        \<Longrightarrow> (\<exists> c . c \<in> (ob T \<cdot> (A \<union> B)) \<and> (ar T \<cdot> (make_inc A (A \<union> B))) \<cdot> c = a \<and> (ar T \<cdot> (make_inc B (A \<union> B))) \<cdot> c = b)"
shows "valid T"
  unfolding valid_def
  apply (simp add: Let_def)
  by (simp add: assms)

lemma valid_space : "valid T \<Longrightarrow> Space.valid (space T)"
  using Presheaf.valid_space Tuple.valid_welldefined by blast

lemma valid_relation_space : "valid T \<Longrightarrow> Prealgebra.space (rel_prealg T) = space T"
  unfolding rel_prealg_def
  by (meson Prealgebra.Prealgebra.select_convs(1))

lemma relation_ob_valid : "Function.valid_map (Prealgebra.ob (rel_prealg T))"
  unfolding rel_prealg_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ar_valid : "Function.valid_map (Prealgebra.ar (rel_prealg T))"
  unfolding rel_prealg_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ob_value : "A \<in> opens (space T) \<Longrightarrow> (Prealgebra.ob (rel_prealg T)) \<cdot> A = Poset.powerset (ob T \<cdot> A )"
  unfolding rel_prealg_def
  by (simp add: Function.dom_def)

lemma relation_ob_value_valid : "valid T \<Longrightarrow> A \<in> opens (space T) \<Longrightarrow> Poset.valid (Prealgebra.ob (rel_prealg T) \<cdot> A)"
  using relation_ob_value [where ?T=T]
  by (simp add: powerset_valid)

lemma relation_as_value : "A \<in> opens (space T) \<Longrightarrow> a \<subseteq> ob T \<cdot> A \<Longrightarrow> a \<in> el (Prealgebra.ob (rel_prealg T) \<cdot> A)"
  by (simp add: powerset_def relation_ob_value)

lemma relation_ar_value : "i \<in> inclusions (space T) 
\<Longrightarrow> Prealgebra.ar (rel_prealg T) \<cdot> i = Poset.direct_image (ar T \<cdot> i)"
  unfolding rel_prealg_def [where ?T=T]
  by (simp add: Function.dom_def)

lemma relation_ar_value_valid : "valid T \<Longrightarrow> i \<in> inclusions (space T) \<Longrightarrow> Poset.valid_map (Prealgebra.ar (rel_prealg T) \<cdot> i)"
  using Presheaf.valid_ar Tuple.valid_welldefined direct_image_valid relation_ar_value by fastforce

lemma relation_ar_dom : "valid T \<Longrightarrow> i \<in> inclusions (space T)
\<Longrightarrow> PosetMap.dom (Prealgebra.ar (rel_prealg T) \<cdot> i) = Prealgebra.ob (rel_prealg T) \<cdot> Space.cod i"
  by (simp add: Tuple.valid_welldefined direct_image_dom relation_ar_value relation_ob_value)

lemma relation_ar_cod : "valid T \<Longrightarrow> i \<in> inclusions (space T)
\<Longrightarrow> PosetMap.cod (Prealgebra.ar (rel_prealg T) \<cdot> i) = Prealgebra.ob (rel_prealg T) \<cdot> Space.dom i"
  unfolding rel_prealg_def
  by (simp add: Function.fun_app_iff Function.valid_map_def Tuple.valid_welldefined direct_image_cod)

lemma relation_ar_ident :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  defines "R \<equiv> rel_prealg T"
  assumes "valid T"
  assumes "A \<in> opens (space T)"
  shows "Prealgebra.ar R \<cdot> Space.ident A = Poset.ident (Prealgebra.ob R \<cdot> A)"
  using Presheaf.valid_identity R_def Tuple.valid_welldefined assms(2) assms(3) direct_image_ident relation_ar_value relation_ob_value valid_ident_inc by fastforce

lemma relation_ar_trans :
  fixes T :: "('A, 'x) TupleSystem" and i j :: "'A Inclusion"
  defines "R \<equiv> rel_prealg T"
  assumes T_valid: "valid T"
  and i_inc : "i \<in> inclusions (space T)"
  and j_inc :"j \<in> inclusions (space T)"
  and endpoints : "Space.dom j = Space.cod i"
shows "Prealgebra.ar R \<cdot> (j \<propto> i) = Prealgebra.ar R \<cdot> i \<diamondop> Prealgebra.ar R \<cdot> j"
  by (smt (verit, ccfv_threshold) Presheaf.valid_ar Presheaf.valid_cod Presheaf.valid_composition Presheaf.valid_dom R_def T_valid Tuple.valid_welldefined cod_compose_inc compose_inc_valid direct_image_trans dom_compose_inc endpoints i_inc j_inc mem_Collect_eq relation_ar_value)

lemma valid_rel_prealg :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "Prealgebra.valid (rel_prealg T)"
proof (intro Prealgebra.validI, safe, goal_cases)
  case 1
  then show ?case
    by (simp add: Tuple.valid_space assms valid_relation_space) 
next
  case 2
  then show ?case
    by (simp add: relation_ob_valid) 
next
  case 3
  then show ?case
    by (simp add: relation_ar_valid) 
next
  case (4 A)
  then show ?case
    by (simp add: assms relation_ob_value_valid valid_relation_space) 
next
  case (5 i)
  then show ?case
    by (simp add: assms relation_ar_value_valid valid_relation_space) 
next
  case (6 i)
  then show ?case
    by (simp add: assms relation_ar_dom valid_relation_space) 
next
  case (7 i)
  then show ?case
    by (simp add: assms relation_ar_cod valid_relation_space) 
next
  case (8 A)
  then show ?case
    by (simp add: assms relation_ar_ident valid_relation_space) 
next
  case (9 i j)
  then show ?case
    by (simp add: assms relation_ar_trans valid_relation_space) 
qed 

(* Validity of neutral *)

lemma rel_neutral_nat_valid : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> opens (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T"
  shows "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)"
proof -
  define "dom" where "dom = Prealgebra.terminal (space T)"
  define "cod" where "cod = rel_prealg T"
  have "(PrealgebraMap.nat (rel_neutral T)) \<cdot> A = Poset.const ((Prealgebra.ob dom) \<cdot> A) ((Prealgebra.ob cod) \<cdot> A) ((ob T) \<cdot> A)" 
    using rel_neutral_def [where ?T=T]
    by (smt (verit) Function.dom_def Function.fun_app_iff Function.select_convs(1) Function.select_convs(2) Function.valid_map_def PrealgebraMap.select_convs(3) UNIV_I \<open>A \<in> opens (Tuple.space T)\<close> fst_conv local.cod_def local.dom_def mem_Collect_eq snd_conv)
  moreover have "Poset.valid (Prealgebra.ob dom \<cdot> A)"
    by (metis Presheaf.valid_space Tuple.valid_welldefined \<open>A \<in> opens (Tuple.space T)\<close> \<open>Tuple.valid T\<close> discrete_valid local.dom_def terminal_ob)
  moreover have "Poset.valid (Prealgebra.ob cod \<cdot> A)"  using valid_rel_prealg [where ?T=T]
    by (simp add: \<open>A \<in> opens (Tuple.space T)\<close> \<open>Tuple.valid T\<close> local.cod_def relation_ob_value_valid)
  ultimately show "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)" using Poset.const_valid
     cod_def dom_def powerset_def  relation_ob_value
    by (smt (verit) A_open Poset.Poset.select_convs(1) Pow_top T_valid \<epsilon>_def)
qed

lemma rel_neutral_nat_value : "valid T \<Longrightarrow> A \<in> opens (space T) \<Longrightarrow>
 PrealgebraMap.nat (rel_neutral T) \<cdot> A =  Poset.const Poset.discrete (Prealgebra.ob (rel_prealg T) \<cdot> A) (ob T \<cdot> A)"
  unfolding rel_neutral_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app_iff Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.valid_space Tuple.valid_welldefined UNIV_I const_ob fst_conv mem_Collect_eq snd_conv)

lemma rel_neutral_is_element :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" 
  and A_open: "A \<in> opens (space T)" 
  defines "R \<equiv> rel_prealg T"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (rel_neutral T) \<cdot> A) \<star> ()"
shows "\<epsilon>A \<in> el (Prealgebra.ob R \<cdot> A)"
  by (smt (verit, best) A_open Poset.Poset.select_convs(1) Poset.const_app Poset.discrete_def Pow_top R_def T_valid UNIV_I \<epsilon>A_def discrete_valid powerset_def rel_neutral_nat_value relation_ob_value relation_ob_value_valid)

lemma rel_neutral_nat_value_app :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open" and x :: "unit"
  assumes T_valid: "valid T" 
  and A_open: "A \<in> opens (space T)" 
  and x_el : "x \<in> el (Poset.dom (PrealgebraMap.nat (rel_neutral T) \<cdot> A ))"
shows "(PrealgebraMap.nat (rel_neutral T) \<cdot> A) \<star> x =  ob T \<cdot> A"
  by (smt (verit, ccfv_SIG) A_open Poset.Poset.select_convs(1) Poset.const_app Poset.discrete_def Pow_top T_valid UNIV_I discrete_valid powerset_def rel_neutral_nat_value relation_ob_value relation_ob_value_valid)

lemma rel_neutral_dom : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> opens (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T"
  shows "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> A) = Prealgebra.ob (PrealgebraMap.dom \<epsilon>) \<cdot> A"
  by (smt (verit, ccfv_SIG) A_open Poset.Poset.select_convs(1) Poset.const_dom Pow_top PrealgebraMap.select_convs(1) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def powerset_def rel_neutral_def rel_neutral_nat_value relation_ob_value terminal_ob)

lemma rel_neutral_cod : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> opens (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T"
  shows "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> A) = Prealgebra.ob (PrealgebraMap.cod \<epsilon>) \<cdot> A"
  by (smt (verit, ccfv_SIG) A_open Poset.Poset.select_convs(1) Poset.const_cod Poset.discrete_def PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_witness \<epsilon>_def old.unit.exhaust rel_neutral_def rel_neutral_dom rel_neutral_is_element rel_neutral_nat_value rel_neutral_nat_value_app terminal_ob)

lemma rel_neutral_top : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> opens (space T)"
  defines "R \<equiv> rel_prealg T"
    and "RA \<equiv> (PrealgebraMap.nat (rel_neutral T) \<cdot> A) \<star> ()"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (rel_neutral T) \<cdot> A) \<star> ()"
shows "Poset.is_top (Prealgebra.ob R \<cdot> A) \<epsilon>A"
proof (safe, goal_cases)
  case 1
  then show ?case
    using A_open R_def T_valid \<epsilon>A_def rel_neutral_is_element by blast 
next
  case (2 p)
  then show ?case
  proof -
    fix p
    assume "p \<in> el (Prealgebra.ob R \<cdot> A)"
    have "p \<subseteq> ob T \<cdot> A"
      by (smt (verit) A_open Poset.Poset.select_convs(1) PowD R_def T_valid \<open>p \<in> el (Prealgebra.ob R \<cdot> A)\<close> powerset_def relation_ob_value) 
    moreover have "Prealgebra.ob R \<cdot> A = powerset (ob T \<cdot> A)"
      using A_open R_def T_valid relation_ob_value by blast 
    moreover have "\<epsilon>A = ob T \<cdot> A" using \<epsilon>A_def rel_neutral_nat_value_app [where ?T=T and
          ?A=A and ?x="()"]
      by (smt (verit) A_open Poset.Poset.select_convs(1) Poset.const_dom Poset.discrete_def Pow_top R_def T_valid UNIV_witness calculation(2) old.unit.exhaust powerset_def rel_neutral_nat_value)
    moreover have "p \<subseteq> \<epsilon>A" using calculation
      by blast 
    show "Poset.le (Prealgebra.ob R \<cdot> A) p \<epsilon>A" using R_def rel_prealg_def [where ?T=T]
      by (smt (verit, best) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Pow_iff Pow_top \<open>p \<in> el (Prealgebra.ob R \<cdot> A)\<close> calculation(2) calculation(3) case_prodI mem_Collect_eq powerset_def) 
  qed
qed

lemma rel_neutral_stable : 
  fixes T :: "('A, 'x) TupleSystem" and i :: "'A Inclusion"
  assumes T_valid: "valid T" and i_inc: "i \<in> inclusions (space T)"
  defines "R \<equiv> rel_prealg T"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (rel_neutral T) \<cdot> Space.cod i) \<star> ()"
  and "\<epsilon>B \<equiv> (PrealgebraMap.nat (rel_neutral T) \<cdot> Space.dom i) \<star> ()"
shows "(Prealgebra.ar R \<cdot> i) \<star> \<epsilon>A = \<epsilon>B" 
proof -
  define "Ti" where "Ti = ar T \<cdot> i"
  define "Ri" where "Ri = Prealgebra.ar R \<cdot> i"

  have "Function.is_surjective Ti"
    using T_valid i_inc valid_flasque Ti_def by blast  
  moreover have "Ri = direct_image Ti"
    using R_def Ri_def T_valid Ti_def i_inc relation_ar_value by blast
  moreover have "Poset.is_surjective Ri" using Poset.surj_imp_direct_image_surj [where?f=Ti]
    using Presheaf.valid_ar T_valid Ti_def Tuple.valid_welldefined calculation(1) calculation(2) i_inc by blast 
  moreover have "\<epsilon>B \<in> el (Poset.cod Ri)" using \<epsilon>B_def Ri_def R_def rel_prealg_def [where
        ?T=T] rel_neutral_def [where ?T=T]
    by (smt (verit, best) T_valid i_inc mem_Collect_eq rel_neutral_is_element relation_ar_cod)
  moreover have "\<exists> x . x \<in> el (Poset.dom Ri) \<and> Ri \<star> x = \<epsilon>B"
    using calculation(3) calculation(4) is_surjective_def
    by fastforce 
  obtain "x" where "x \<in> el (Poset.dom Ri) \<and> Ri \<star> x = \<epsilon>B"
    using \<open>\<exists>x. x \<in> el (PosetMap.dom Ri) \<and> Ri \<star> x = \<epsilon>B\<close> by blast 
  moreover have "Poset.le (PosetMap.dom Ri) x \<epsilon>A"
    using R_def Ri_def T_valid \<epsilon>A_def calculation(5) i_inc mem_Collect_eq rel_neutral_top relation_ar_dom by fastforce 
  ultimately show ?thesis
    by (smt (verit) Poset.fun_app Poset.valid_map_cod Presheaf.valid_ar R_def Ri_def T_valid Ti_def Tuple.valid_welldefined \<epsilon>A_def \<epsilon>B_def direct_image_mono i_inc mem_Collect_eq rel_neutral_top relation_ar_cod relation_ar_dom relation_ar_value_valid relation_ob_value_valid valid_antisymmetry) 
qed

lemma rel_neutral_natural : 
  fixes T :: "('A, 'x) TupleSystem" and i :: "'A Inclusion"
  assumes T_valid: "valid T" and i_inc: "i \<in> inclusions (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T "
  shows "PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i =
         Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i"
proof (intro Poset.fun_ext,goal_cases)
  case 1
  then show ?case
    by (smt (verit, best) Poset.compose_ident_right PrealgebraMap.select_convs(1) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def const_ar i_inc mem_Collect_eq rel_neutral_def rel_neutral_dom rel_neutral_nat_valid terminal_ob) 
next
  case 2
  then show ?case
    by (smt (verit, ccfv_threshold) Poset.compose_valid Prealgebra.valid_ar Prealgebra.valid_dom PrealgebraMap.select_convs(2) T_valid \<epsilon>_def i_inc mem_Collect_eq rel_neutral_cod rel_neutral_def rel_neutral_nat_valid valid_rel_prealg valid_relation_space) 
next
  case 3
  then show ?case
    by (smt (z3) Poset.compose_ident_right Poset.dom_compose Prealgebra.valid_ar Prealgebra.valid_dom PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def const_ar i_inc mem_Collect_eq rel_neutral_cod rel_neutral_def rel_neutral_dom rel_neutral_nat_valid terminal_ob valid_rel_prealg valid_relation_space) 
next
  case 4
  then show ?case
    by (smt (verit, del_insts) Poset.cod_compose Poset.compose_ident_right Prealgebra.valid_ar Prealgebra.valid_dom PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def const_ar i_inc mem_Collect_eq rel_neutral_cod rel_neutral_def rel_neutral_dom rel_neutral_nat_valid res_cod terminal_ob valid_rel_prealg valid_relation_space) 
next
  case (5 a)
  then show ?case
    by (smt (verit) Poset.Poset.select_convs(1) Poset.compose_app_assoc Poset.compose_ident_right Poset.discrete_def PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_unit \<epsilon>_def const_ar i_inc mem_Collect_eq rel_neutral_cod rel_neutral_def rel_neutral_dom rel_neutral_nat_valid rel_neutral_stable relation_ar_dom relation_ar_value_valid singletonD terminal_ob)   
qed

lemma rel_neutral_valid :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "Prealgebra.valid_map (rel_neutral T)"
proof (intro valid_mapI, safe, goal_cases)
  case 1
  then show ?case
    by (smt (verit, best) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def PrealgebraMap.select_convs(1) Presheaf.valid_space Tuple.valid_welldefined assms rel_neutral_def) 
next
  case 2
  then show ?case
    by (simp add: Prealgebra.const_def rel_neutral_def rel_prealg_def) 
next
  case 3
  then show ?case
    by (smt (verit) Function.dom_def Function.select_convs(1) Function.select_convs(2) Function.valid_map_def PrealgebraMap.select_convs(3) UNIV_I fst_conv mem_Collect_eq rel_neutral_def snd_conv) 
next
  case 4
  then show ?case
    by (smt (verit, ccfv_threshold) PrealgebraMap.select_convs(1) Presheaf.valid_space Tuple.valid_welldefined assms rel_neutral_def terminal_valid) 
next
  case 5
  then show ?case
    by (smt (verit, ccfv_SIG) PrealgebraMap.select_convs(2) assms rel_neutral_def valid_rel_prealg) 
next
  case (6 A)
  then show ?case
    by (smt (verit, best) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def PrealgebraMap.select_convs(1) assms rel_neutral_def rel_neutral_nat_valid) 
next
  case (7 A)
  then show ?case
    by (smt (verit, best) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def PrealgebraMap.select_convs(1) assms rel_neutral_def rel_neutral_dom) 
next
  case (8 A)
  then show ?case
    by (smt (verit) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def PrealgebraMap.select_convs(1) assms rel_neutral_cod rel_neutral_def) 
next
  case (9 i)
  then show ?case using rel_neutral_natural [where ?T=T and ?i=i]
    by (smt (verit) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def PrealgebraMap.select_convs(1) assms mem_Collect_eq rel_neutral_def)
qed

(* Validity of combination *)

lemma rel_semigroup_dom :  
  fixes T :: "('A, 'x) TupleSystem" and R:: "('A, 'x set) Prealgebra"
  assumes T_valid : "valid T"
  defines "R \<equiv> rel_prealg T"
  shows "PosetMap.dom (mult (rel_semigroup T)) = gc R \<times>\<times> gc R"
using rel_semigroup_def [where ?T=T]
  by (smt (verit, best) PosetMap.select_convs(1) R_def Semigroup.select_convs(1))

lemma rel_semigroup_cod :  
  fixes T :: "('A, 'x) TupleSystem" and R:: "('A, 'x set) Prealgebra"
  assumes T_valid : "valid T"
  defines "R \<equiv> rel_prealg T"
  shows "PosetMap.cod (mult (rel_semigroup T)) = gc R"
using rel_semigroup_def [where ?T=T]
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(2) R_def Semigroup.select_convs(1)) 

lemma rel_semigroup_mult_welldefined_dom :  
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x) Relation"
  assumes T_valid : "valid T" and abc_el : "((a,b), c) \<in> PosetMap.func (mult (rel_semigroup T))"
  shows "(a,b) \<in> el (PosetMap.dom (mult (rel_semigroup T)))"
proof -
  define "R" where "R = rel_prealg T"
  have "PosetMap.dom (mult (rel_semigroup T)) = gc R \<times>\<times> gc R"
    using R_def T_valid rel_semigroup_dom by blast 
  moreover have "a \<in> el (gc R)" using rel_semigroup_def [where ?T=T]
    by (smt (verit, best) Pair_inject PosetMap.select_convs(3) R_def Semigroup.select_convs(1) T_valid abc_el local_elem_gc mem_Collect_eq valid_rel_prealg valid_relation_space)
  moreover have "b \<in> el (gc R)" using rel_semigroup_def [where ?T=T]
    by (smt (z3) Pair_inject PosetMap.select_convs(3) R_def Semigroup.select_convs(1) T_valid abc_el local_elem_gc mem_Collect_eq valid_rel_prealg valid_relation_space)
  ultimately show ?thesis using assms
    by (simp add: Poset.product_def)
qed

lemma rel_semigroup_mult_val :  
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "R \<equiv> rel_prealg T"
  defines "dc \<equiv> d a \<union> d b"
  defines "ec \<equiv> { t . t \<in> ob T \<cdot> dc \<and> (ar T \<cdot> (make_inc (d a) dc)) \<cdot> t \<in> e a     
                                         \<and> (ar T \<cdot> (make_inc (d b) dc)) \<cdot> t \<in> e b }"
  defines "c \<equiv> (dc, ec)"
  assumes T_valid : "valid T" and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)"
  shows "mul (rel_semigroup T) a b = c" 
proof -
  have "(a,b) \<in> el (gc R \<times>\<times> gc R)"
    by (simp add: Poset.product_def a_el b_el) 
  moreover have "(a,b) \<in> el (PosetMap.dom (mult (rel_semigroup T)))"
    using R_def T_valid calculation rel_semigroup_dom by fastforce
  moreover have "((a,b),c) \<in> PosetMap.func (mult (rel_semigroup T))" using rel_semigroup_def [where ?T=T]
    apply (simp add: Let_def)
    by (smt (verit) Collect_cong R_def T_valid a_el b_el c_def dc_def ec_def gc_elem_local local_dom prod.collapse valid_rel_prealg valid_relation_space)
  ultimately show ?thesis using rel_semigroup_def [where ?T=T] Poset.app_def [where ?f="mult
 (rel_semigroup T)" and ?a="(a,b)"]
    by (smt (z3) Pair_inject PosetMap.select_convs(3) Semigroup.select_convs(1) mem_Collect_eq the_equality) 
qed

lemma rel_semigroup_mult_tup_proj_el1 : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  defines "i_A \<equiv> make_inc (d a) (d a \<union> d b)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "t \<in> e (join \<star> (a, b)) \<Longrightarrow> (ar T \<cdot> i_A) \<cdot> t \<in> e a"
proof -
  fix t
  assume "t \<in> e (join \<star> (a, b))"
  have "(a,b) \<in> el (Poset.dom join)"
    by (smt (verit) Poset.Poset.select_convs(1) Poset.product_def R_def SigmaI T_valid a_el b_el join_def rel_semigroup_dom)
  moreover have "e (join \<star> (a, b)) = { t . t \<in> ob T \<cdot> (d a \<union> d b) \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> t \<in> e a     
                                         \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> t \<in> e b }" 
    using assms calculation rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
    by simp  
  ultimately show "(ar T \<cdot> i_A) \<cdot> t \<in> e a" using  assms
    using \<open>t \<in> e (join \<star> (a, b))\<close> by blast
qed

lemma rel_semigroup_mult_tup_proj_el2 : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  defines "i_B \<equiv> make_inc (d b) (d a \<union> d b)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "t \<in> e (join \<star> (a, b)) \<Longrightarrow> (ar T \<cdot> i_B) \<cdot> t \<in> e b"
proof -
  fix t
  assume "t \<in> e (join \<star> (a, b))"
  have "(a,b) \<in> el (Poset.dom join)"
    by (smt (verit) Poset.Poset.select_convs(1) Poset.product_def R_def SigmaI T_valid a_el b_el join_def rel_semigroup_dom)
  moreover have "e (join \<star> (a, b)) = { t . t \<in> ob T \<cdot> (d a \<union> d b) \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> t \<in> e a     
                                         \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> t \<in> e b }" 
    using assms calculation rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
    by simp  
  ultimately show "(ar T \<cdot> i_B) \<cdot> t \<in> e b" using  assms
    using \<open>t \<in> e (join \<star> (a, b))\<close> by blast 
qed

lemma rel_semigroup_mult_d [simp] : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "d (join \<star> (a, b)) = d a \<union> d b"
  using rel_semigroup_def [where ?T=T] assms rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
  by simp 

lemma rel_semigroup_mult_e [simp] : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "e (join \<star> (a, b)) = { t . t \<in> ob T \<cdot> (d a \<union> d b) 
                                     \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> t \<in> e a     
                                     \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> t \<in> e b }"
  using rel_semigroup_def [where ?T=T] assms rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
  by simp 

lemma rel_semigroup_mult_local_subset : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "e (join \<star> (a, b)) \<subseteq> ob T \<cdot> (d a \<union> d b)" 
  using rel_semigroup_def [where ?T=T] assms rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
  by simp 

lemma rel_semigroup_mult_local_el : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "e (join \<star> (a, b)) \<in> el (Prealgebra.ob R \<cdot> (d a \<union> d b))"
  using rel_semigroup_def [where ?T=T] assms rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
  by (metis (no_types, lifting) Tuple.valid_space local_dom rel_semigroup_mult_local_subset relation_as_value valid_rel_prealg valid_relation_space valid_union2) 

lemma rel_semigroup_mult_el : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "join \<star> (a, b) \<in> el (gc R)"
proof - 
  define "dc" where "dc = d a \<union> d b"
  define "ec" where "ec = { t . t \<in> ob T \<cdot> dc \<and> (ar T \<cdot> (make_inc (d a) dc)) \<cdot> t \<in> e a     
                                        \<and> (ar T \<cdot> (make_inc (d b) dc)) \<cdot> t \<in> e b }"
  define "c" where "c = (dc, ec)"
  have "(a,b) \<in> el (PosetMap.dom join)" using assms  Poset.product_def
    by (smt (verit) Poset.Poset.select_convs(1) SigmaI rel_semigroup_dom)
  moreover have "join \<star> (a, b) = c" using assms calculation rel_semigroup_def [where ?T=T] Poset.app_def
      [where ?f=join and ?a="(a,b)"] rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
    using c_def dc_def ec_def by fastforce 
  moreover have "ec \<subseteq> ob T \<cdot> dc"
    using ec_def by blast 
  ultimately show ?thesis
    by (metis R_def T_valid Tuple.valid_space a_el b_el c_def dc_def local_dom local_elem_gc relation_as_value valid_rel_prealg valid_relation_space valid_union2)
qed

lemma rel_semigroup_mult_welldefined_cod :  
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x) Relation"
  assumes T_valid : "valid T" and abc_el : "((a,b), c) \<in> PosetMap.func (mult (rel_semigroup T))"
  shows "c \<in> el (PosetMap.cod (mult (rel_semigroup T)))"
proof -
  define "R" where "R = rel_prealg T"
  have "PosetMap.cod (mult (rel_semigroup T)) = gc R" using rel_semigroup_def [where ?T=T]
    by (smt (verit, best) PosetMap.select_convs(2) R_def Semigroup.select_convs(1))
  moreover have "(a,b) \<in> el (PosetMap.dom (mult (rel_semigroup T)))"
    using T_valid abc_el rel_semigroup_mult_welldefined_dom by blast
  moreover have "mul (rel_semigroup T) a b = c" using rel_semigroup_def [where ?T=T] rel_semigroup_mult_val [where ?T=T and ?a=a and ?b=b]
    by (smt (verit) CollectD Collect_cong PosetMap.select_convs(3) Semigroup.select_convs(1) T_valid abc_el fst_conv local_elem_gc snd_conv valid_rel_prealg valid_relation_space)
  moreover have dc : "d c = d a \<union> d b"  using rel_semigroup_def [where ?T=T]
    by (smt (verit) CollectD PosetMap.select_convs(3) Semigroup.select_convs(1) abc_el fst_conv snd_conv)
  moreover have "e c \<subseteq> ob T \<cdot> (d c)" using rel_semigroup_def [where ?T=T] assms calculation
    by (smt (verit, del_insts) CollectD PosetMap.select_convs(3) Semigroup.select_convs(1) fst_conv snd_conv subsetI)
    moreover have da: "d a \<in> opens (space T)"
      by (smt (verit) Poset.Poset.select_convs(1) Poset.product_def T_valid calculation(2) local_dom mem_Sigma_iff rel_semigroup_dom valid_rel_prealg valid_relation_space) 
    moreover have db: "d b \<in> opens (space T)"
      by (smt (verit) Poset.Poset.select_convs(1) Poset.product_def T_valid calculation(2) local_dom mem_Sigma_iff rel_semigroup_dom valid_rel_prealg valid_relation_space) 
  moreover have "d c \<in> opens (space T)" using da db dc Space.valid_union2 [where ?T="space T" and ?A=da and ?B=db]
      valid_space [where ?T=T]
    by (simp add: T_valid valid_union2) 
  moreover have "e c \<in> el (Prealgebra.ob R \<cdot> (d c))" using assms R_def rel_prealg_def [where ?T=T]
      relation_as_value [where ?T=T and ?A="d c" and ?a="e c"]
    using calculation(5) calculation(8) by fastforce 
  ultimately show ?thesis
    by (metis R_def T_valid local_elem_gc prod.collapse valid_rel_prealg valid_relation_space) 
qed

lemma rel_semigroup_mult_deterministic : 
  fixes T :: "('A, 'x) TupleSystem" and a b c c' :: "('A, 'x) Relation"
  assumes T_valid : "valid T" 
  and "((a,b), c) \<in> PosetMap.func (mult (rel_semigroup T))" and "((a,b), c') \<in> PosetMap.func (mult (rel_semigroup T))" 
shows "c = c'"
using rel_semigroup_def [where ?T=T]
  by (smt (z3) CollectD Pair_inject PosetMap.select_convs(3) Semigroup.select_convs(1) assms(2) assms(3))

lemma rel_semigroup_mult_total : 
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x) Relation"
  assumes T_valid : "valid T" 
  and ab_el : "(a,b) \<in> el (PosetMap.dom (mult (rel_semigroup T)))" 
shows "\<exists>c. ((a,b), c) \<in> PosetMap.func (mult (rel_semigroup T))"
proof
  define "dc" where "dc = d a \<union> d b"
  define "ec" where "ec = { t . t \<in> ob T \<cdot> dc \<and> (ar T \<cdot> (make_inc (d a) dc)) \<cdot> t \<in> e a     
                                         \<and> (ar T \<cdot> (make_inc (d b) dc)) \<cdot> t \<in> e b }"
  define "c" where "c = (dc, ec)"
  have "d a \<in> opens (space T)"  using rel_semigroup_def [where ?T=T]
    by (metis (no_types, opaque_lifting) T_valid ab_el local_dom product_el_1 rel_semigroup_dom valid_rel_prealg valid_relation_space) 
  moreover have "d b \<in> opens (space T)" using rel_semigroup_def [where ?T=T]
    by (metis (no_types, opaque_lifting) T_valid ab_el local_dom product_el_2 rel_semigroup_dom valid_rel_prealg valid_relation_space) 
  moreover have "e a \<in> el (Prealgebra.ob (rel_prealg T) \<cdot> (d a))"
    by (metis T_valid ab_el gc_elem_local product_el_1 rel_semigroup_dom valid_rel_prealg)
  moreover have "e b \<in> el (Prealgebra.ob (rel_prealg T) \<cdot> (d b))"
    by (metis T_valid ab_el gc_elem_local product_el_2 rel_semigroup_dom valid_rel_prealg) 
  moreover have "((a,b), c) \<in> PosetMap.func (mult (rel_semigroup T))" using assms calculation rel_semigroup_def [where ?T=T] dc_def
      ec_def c_def 
    apply (simp add :Let_def)
    using prod.exhaust_sel by blast
  ultimately show "((a,b), c) \<in> PosetMap.func (mult (rel_semigroup T))"
    by blast
qed

lemma relation_le_is_subseteq :
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "R \<equiv> rel_prealg T"
  and "i \<equiv> make_inc (d b) (d a)"
  assumes T_valid : "valid T" and "a \<in> el (gc R)" and "b \<in> el (gc R)"
  and "Poset.le (gc R) a b"
shows "(Prealgebra.ar R \<cdot> i) \<star> e a \<subseteq> e b"
proof -          
  define "ea_B" where "ea_B = Prealgebra.ar R \<cdot> i \<star> e a"
  have "d b \<subseteq> d a"
    using R_def T_valid assms(3) assms(4) assms(5) d_antitone valid_rel_prealg
    using assms(6) by blast 
  moreover have "valid_inc i"
    by (simp add: calculation i_def)
  moreover have "Poset.le (Prealgebra.ob R \<cdot> d b) ea_B (e b)"
    using assms gc_le_eq [where ?F=R] ea_B_def i_def
    by blast 
  moreover have "Prealgebra.ob R \<cdot> d b = powerset (ob T \<cdot> d b)"
    by (metis R_def T_valid assms(5) local_dom relation_ob_value valid_rel_prealg valid_relation_space) 
  moreover have "ea_B \<in> el (Prealgebra.ob R \<cdot> d b)" using assms calculation Prealgebra.valid_ar
      [where ?i=i]
    by (smt (verit) Inclusion.select_convs(1) Inclusion.select_convs(2) Prealgebra.image ea_B_def gc_elem_local local_dom mem_Collect_eq valid_rel_prealg)
  moreover have "ea_B \<subseteq> e b" using powerset_le
      [where ?A="ob T \<cdot> d b" and ?a="ea_B" and ?a'="e b"]
    by (metis R_def T_valid assms(5) calculation(3) calculation(4) calculation(5) gc_elem_local valid_rel_prealg) 
  ultimately show ?thesis using relation_ob_value [where ?A="d b" and ?T=T] assms powerset_le
      [where ?A="ob T \<cdot> d b" and ?a="ea_B" and ?a'="e b"]
    using ea_B_def by force
qed

lemma relation_res_tup :
  fixes T :: "('A, 'x) TupleSystem" and ea :: "'x set" and t :: "'x" and A B :: "'A
 Open"
  defines "R \<equiv> rel_prealg T"
  and "i \<equiv> make_inc B A"
  assumes T_valid : "valid T" 
  and A_open : "A \<in> opens (space T)" 
  and B_open : "B \<in> opens (space T)" 
  and a_el : "ea \<in> el (Prealgebra.ob R \<cdot> A)"
  and B_le_A : "B \<subseteq> A"
  and t_el_a : "t \<in> ea"
shows "(ar T \<cdot> i) \<cdot> t \<in> (Prealgebra.ar R \<cdot> i) \<star> ea"
  by (smt (z3) A_open B_le_A B_open CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) Poset.Poset.select_convs(1) Pow_iff Presheaf.valid_welldefined R_def T_valid Tuple.valid_welldefined a_el direct_image_app i_def powerset_def relation_ar_value relation_ob_value t_el_a)

lemma rel_semigroup_mult_monotone : 
  fixes T :: "('A, 'x) TupleSystem" and a b a' b' :: "('A, 'x) Relation"
  defines "join \<equiv> mult (rel_semigroup T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and ab_el : "(a,b) \<in> el (PosetMap.dom join)" 
  and a'b'_el : "(a',b') \<in> el (PosetMap.dom join)" 
  and "Poset.le (PosetMap.dom join) (a,b) (a',b')"
shows "Poset.le (gc R) (join \<star> (a, b)) (join \<star> (a', b'))"
proof (intro gc_leI, goal_cases)
  case 1
  then show ?case
    by (metis R_def T_valid ab_el join_def product_el_1 product_el_2 rel_semigroup_dom rel_semigroup_mult_el) 
next
  case 2
  then show ?case
    by (metis R_def T_valid a'b'_el join_def product_el_1 product_el_2 rel_semigroup_dom rel_semigroup_mult_el) 
next
  case 3
  then show ?case
    by (smt (verit) Poset.Poset.select_convs(2) Poset.product_def Product_Type.Collect_case_prodD T_valid Un_mono a'b'_el ab_el assms(6) d_antitone fst_conv join_def rel_semigroup_dom rel_semigroup_mult_d snd_conv valid_rel_prealg) 
next
  case 4
  then show ?case 
  proof - 
    have "a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)"
      by (metis R_def T_valid a'b'_el ab_el join_def product_el_1 product_el_2 rel_semigroup_dom) 
    moreover have "d a \<union> d b \<in> opens (space T)"
      by (metis T_valid Tuple.valid_space ab_el join_def local_dom product_el_1 product_el_2 rel_semigroup_dom valid_rel_prealg valid_relation_space valid_union2) 
    moreover have "d (mul (rel_semigroup T) a b) = d a \<union> d b" using calculation assms rel_semigroup_mult_d [where ?T=T and ?a=a
          and ?b=b]
      by fastforce 
    moreover have "Prealgebra.ob R \<cdot> d (join \<star> (a, b)) = powerset (ob T \<cdot> (d a \<union> d b))" using
        assms calculation  relation_ob_value [where ?T=T and ?A="d a \<union> d b"]
      by presburger
    define "i" where "i = make_inc (d a' \<union> d b') (d a \<union> d b)"

    moreover have "(Prealgebra.ar R \<cdot> i \<star> e (join \<star> (a, b))) \<subseteq> (e (join \<star> (a', b')))"
    proof
      fix t
      assume "t \<in> Prealgebra.ar R \<cdot> i \<star> e (join \<star> (a, b))"

      define "eab" where "eab = { t . t \<in> ob T \<cdot> (d a \<union> d b) 
                                     \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> t \<in> e a     
                                     \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> t \<in> e b }"

      have "e (join \<star> (a, b)) = eab"
        using R_def T_valid calculation(1) join_def eab_def by fastforce 
      moreover have "d a' \<union> d b' \<in> opens (space T)"
        by (metis Presheaf.valid_space R_def T_valid Tuple.valid_welldefined \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> local_dom valid_rel_prealg valid_relation_space valid_union2)  
      moreover have "d a' \<union> d b' \<subseteq> d a \<union> d b"
        by (metis R_def T_valid \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> a'b'_el ab_el assms(6) d_antitone join_def product_le_1 product_le_2 rel_semigroup_dom sup.mono valid_gc valid_rel_prealg) 
      moreover have "i \<in> inclusions (space T)"
        using \<open>d a \<union> d b \<in> opens (Tuple.space T)\<close> calculation(2) calculation(3) i_def by auto
      moreover have "t \<in> Prealgebra.ar R \<cdot> i \<star> eab"
        using \<open>t \<in> Prealgebra.ar R \<cdot> i \<star> e (join \<star> (a, b))\<close> calculation(1) by auto
      moreover have "\<exists> t' . t' \<in> eab \<and> (ar T \<cdot> i) \<cdot> t' = t" using calculation assms relation_ar_value
          [where ?T=T and ?i=i] fibre_from_image [where ?f="ar T \<cdot> i" and ?a=eab]
        by (smt (verit, del_insts) Inclusion.select_convs(2) Presheaf.valid_ar Presheaf.valid_dom Tuple.valid_welldefined \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> i_def mem_Collect_eq rel_semigroup_mult_local_subset) 
      then obtain "t'" where "t' \<in> eab \<and> (ar T \<cdot> i) \<cdot> t' = t"
        by blast 

      define "t'_A" where "t'_A = (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> t'" 
      define "t'_B" where "t'_B = (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> t'" 

      moreover have t'_A : "t'_A \<in> e a"
        using R_def T_valid \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> \<open>t' \<in> eab \<and> (Tuple.ar T \<cdot> i) \<cdot> t' = t\<close> calculation(1) join_def t'_A_def by auto  
      moreover have "t'_B \<in> e b"
        using R_def T_valid \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> \<open>t' \<in> eab \<and> (Tuple.ar T \<cdot> i) \<cdot> t' = t\<close> calculation(1) join_def t'_B_def by auto 

      moreover have "Poset.le (gc R) a a'"
        by (metis R_def T_valid \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> a'b'_el ab_el assms(6) join_def product_le_1 rel_semigroup_dom valid_gc valid_rel_prealg) 
      moreover have "Poset.le (gc R) b b'"
        by (metis R_def T_valid \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> a'b'_el ab_el assms(6) join_def product_le_2 rel_semigroup_dom valid_gc valid_rel_prealg)

      define "i_A'_A" where "i_A'_A = make_inc (d a') (d a)"
      define "i_B'_B" where "i_B'_B = make_inc (d b') (d b)"

      moreover have "i_A'_A \<in> inclusions (space T)"
        by (metis (no_types, lifting) CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) R_def T_valid \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> calculation(9) d_antitone i_A'_A_def local_dom valid_rel_prealg valid_relation_space) 
      moreover have "i_B'_B \<in> inclusions (space T)"
        by (metis (no_types, lifting) CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) R_def T_valid \<open>Poset.le (gc R) b b'\<close> \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> calculation(10) d_antitone local_dom valid_rel_prealg valid_relation_space)
      
      define "t'_A'" where "t'_A' = (ar T \<cdot> i_A'_A) \<cdot> t'_A"
      define "t'_B'" where "t'_B' = (ar T \<cdot> i_B'_B) \<cdot> t'_B" 

      moreover have "t'_A' \<in> (Prealgebra.ar R \<cdot> i_A'_A) \<star> e a" using assms calculation relation_res_tup
        by (metis (no_types, lifting) \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> d_antitone gc_elem_local i_A'_A_def local_dom t'_A'_def valid_rel_prealg valid_relation_space)

      moreover have "(Prealgebra.ar R \<cdot> i_A'_A) \<star> e a \<subseteq> e a'" using assms calculation
          relation_le_is_subseteq [where ?T=T]
        using \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> i_A'_A_def by presburger 
      
      moreover have "t'_A' \<in> e a'"
        using calculation(13) calculation(14) by blast 

      moreover have "t'_B' \<in> (Prealgebra.ar R \<cdot> i_B'_B) \<star> e b" using assms calculation relation_res_tup
        by (metis (no_types, lifting) \<open>Poset.le (gc R) b b'\<close> \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> d_antitone gc_elem_local local_dom valid_rel_prealg valid_relation_space)

      moreover have "(Prealgebra.ar R \<cdot> i_B'_B) \<star> e b \<subseteq> e b'" using assms calculation
          relation_le_is_subseteq [where ?T=T]
        using \<open>Poset.le (gc R) b b'\<close> \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> by presburger
      
      moreover have "t'_B' \<in> e b'"
        using calculation(16) calculation(17) by blast

      define "j_A'" where "j_A' = make_inc (d a') (d a' \<union> d b')"
      define "j_B'" where "j_B' = make_inc (d b') (d a' \<union> d b')"

      define "s_A'" where "s_A' = (ar T \<cdot> j_A') \<cdot> t"
      define "s_B'" where "s_B' = (ar T \<cdot> j_B') \<cdot> t" 

      moreover have "s_A' = t'_A'" using assms calculation Presheaf.diamond_rule
        by (metis (no_types, lifting) CollectD Tuple.valid_welldefined \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> \<open>d a \<union> d b \<in> opens (Tuple.space T)\<close> \<open>t' \<in> eab \<and> (Tuple.ar T \<cdot> i) \<cdot> t' = t\<close> d_antitone eab_def i_A'_A_def i_def j_A'_def local_dom s_A'_def sup_ge1 t'_A'_def t'_A_def valid_rel_prealg valid_relation_space)
      moreover have "s_B' = t'_B'" using assms calculation Presheaf.diamond_rule
        by (metis (no_types, lifting) CollectD Tuple.valid_welldefined \<open>Poset.le (gc R) b b'\<close> \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> \<open>d a \<union> d b \<in> opens (Tuple.space T)\<close> \<open>t' \<in> eab \<and> (Tuple.ar T \<cdot> i) \<cdot> t' = t\<close> d_antitone eab_def i_def j_B'_def local_dom sup.cobounded2 valid_rel_prealg valid_relation_space)

      define "ea'b'" where "ea'b' = { t . t \<in> ob T \<cdot> (d a' \<union> d b') 
                                     \<and> (ar T \<cdot> (make_inc (d a') (d a' \<union> d b'))) \<cdot> t \<in> e a'     
                                     \<and> (ar T \<cdot> (make_inc (d b') (d a' \<union> d b'))) \<cdot> t \<in> e b' }"

      moreover have "t \<in> ea'b'"
        by (smt (verit, ccfv_SIG) CollectD CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) Presheaf.image T_valid Tuple.valid_welldefined \<open>s_B' = t'_B'\<close> \<open>t' \<in> eab \<and> (Tuple.ar T \<cdot> i) \<cdot> t' = t\<close> \<open>t'_B' \<in> e b'\<close> calculation(15) calculation(19) calculation(4) ea'b'_def eab_def i_def j_A'_def j_B'_def s_A'_def s_B'_def) 

      moreover have "e (join \<star> (a', b')) = ea'b'" using rel_semigroup_mult_e [where ?T=T and ?a=a' and ?b=b' ]
          join_def ea'b'_def assms calculation
        using \<open>a \<in> el (gc R) \<and> b \<in> el (gc R) \<and> a' \<in> el (gc R) \<and> b' \<in> el (gc R)\<close> by presburger 

      ultimately show "t \<in> e (join \<star> (a', b'))"
        by fastforce 
    qed
    ultimately show ?thesis
      by (smt (verit, best) R_def T_valid join_def local_dom powerset_le rel_semigroup_mult_d rel_semigroup_mult_el rel_semigroup_mult_local_subset relation_as_value relation_ob_value subset_trans valid_rel_prealg valid_relation_space) 
  qed
qed

lemma rel_semigroup_mult_assoc: 
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x) Relation"
  defines "S \<equiv> rel_semigroup T"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" 
  and b_el : "b \<in> el (gc R)" 
  and c_el : "c \<in> el (gc R)" 
shows "mul S (mul S a b) c = mul S a (mul S b c)"
proof (standard, goal_cases)
  case 1
  then show ?case using rel_semigroup_mult_d [where ?T=T and ?a="mul S a b" and ?b=c] rel_semigroup_mult_d [where ?T=T and ?a=a and ?b=b]
    by (metis R_def S_def T_valid Un_assoc a_el b_el c_el rel_semigroup_mult_d rel_semigroup_mult_el)
next
  case 2
  then show ?case 
  proof -
    define "lhs" where "lhs = e (mul S (mul S a b) c)"
    define "rhs" where "rhs = e (mul S a (mul S b c))"
    define "U" where "U = d a \<union> d b \<union> d c"
    define "mhs" where "mhs =  { t . t \<in> ob T \<cdot> U
                                     \<and> (ar T \<cdot> (make_inc (d a) U)) \<cdot> t \<in> e a  
                                     \<and> (ar T \<cdot> (make_inc (d b) U)) \<cdot> t \<in> e b  
                                     \<and> (ar T \<cdot> (make_inc (d c) U)) \<cdot> t \<in> e c }"

    have trans: "\<forall> A B t . A \<in> opens (space T) \<longrightarrow> B \<in> opens (space T) \<longrightarrow> B \<subseteq> A \<longrightarrow> A \<subseteq> U \<longrightarrow> t \<in> ob T \<cdot> U 
  \<longrightarrow> (ar T \<cdot> (make_inc B A)) \<cdot> ((ar T \<cdot> (make_inc A  U)) \<cdot> t) = (ar T \<cdot> (make_inc B U)) \<cdot> t"
      by (smt (verit, del_insts) Function.ident_app Presheaf.diamond_rule Presheaf.valid_identity Presheaf.valid_space R_def Space.ident_def T_valid Tuple.valid_welldefined U_def a_el b_el c_el dual_order.refl dual_order.trans local_dom valid_rel_prealg valid_relation_space valid_union2)

    moreover have "lhs = { t . t \<in> ob T \<cdot> U
                                     \<and> (ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t \<in> e (mul S a b)  
                                     \<and> (ar T \<cdot> (make_inc (d c) U)) \<cdot> t \<in> e c }" using rel_semigroup_mult_e [where ?T=T and ?a="mul S a b" and ?b=c]
      by (smt (verit) Collect_cong R_def S_def T_valid U_def a_el b_el c_el lhs_def rel_semigroup_mult_d rel_semigroup_mult_el)

    moreover have "... = { t . t \<in> ob T \<cdot> U
                                     \<and> (ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t \<in> { t . t \<in> ob T \<cdot> (d a \<union> d b) 
                                                                                 \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> t \<in> e a     
                                                                                 \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> t \<in> e b } 
                                     \<and> (ar T \<cdot> (make_inc (d c) U)) \<cdot> t \<in> e c }" 
      using rel_semigroup_mult_e [where ?T=T and ?a=a and ?b=b]
      using R_def S_def T_valid a_el b_el by presburger

     moreover have "... = { t . t \<in> ob T \<cdot> U
                                     \<and> ((ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t) \<in> ob T \<cdot> (d a \<union> d b) 
                                                                                 \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> ((ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t) \<in> e a     
                                                                                 \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> ((ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t) \<in> e b  
                                     \<and> (ar T \<cdot> (make_inc (d c) U)) \<cdot> t \<in> e c }"
       by blast 

     moreover have "... = { t . t \<in> ob T \<cdot> U 
                                     \<and> (ar T \<cdot> (make_inc (d a) (d a \<union> d b))) \<cdot> ((ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t) \<in> e a     
                                     \<and> (ar T \<cdot> (make_inc (d b) (d a \<union> d b))) \<cdot> ((ar T \<cdot> (make_inc (d a \<union> d b) U)) \<cdot> t) \<in> e b  
                                     \<and> (ar T \<cdot> (make_inc (d c) U)) \<cdot> t \<in> e c }" 
       using Presheaf.restricted_element [where ?F="presheaf T" and ?A=U and ?B="d a \<union> d b"]
       by (metis (no_types, lifting) Presheaf.valid_space R_def T_valid Tuple.valid_welldefined U_def a_el b_el c_el local_dom sup.cobounded1 valid_rel_prealg valid_relation_space valid_union2) 


     moreover have "... = mhs" using  assms  mhs_def trans
       by (smt (verit) Collect_cong U_def local_dom rel_semigroup_mult_d rel_semigroup_mult_el sup.cobounded1 sup.cobounded2 valid_rel_prealg valid_relation_space) 

     ultimately have lhs: "lhs = mhs"
       by presburger 

    have "rhs = { t . t \<in> ob T \<cdot> U
                                     \<and> (ar T \<cdot> (make_inc (d a) U)) \<cdot> t \<in> e a     
                                     \<and> (ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t \<in> e (mul S b c)  }" using rel_semigroup_mult_e [where ?T=T and ?a=a and ?b="mul S b c"]
      by (smt (verit, ccfv_SIG) Collect_cong R_def S_def T_valid U_def a_el b_el c_el rel_semigroup_mult_d rel_semigroup_mult_el rhs_def sup_assoc)

    moreover have "... = { t . t \<in> ob T \<cdot> U
                                     \<and> (ar T \<cdot> (make_inc (d a) U)) \<cdot> t \<in> e a     
                                     \<and> (ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t \<in> { t . t \<in> ob T \<cdot> (d b \<union> d c) 
                                     \<and> (ar T \<cdot> (make_inc (d b) (d b \<union> d c))) \<cdot> t \<in> e b     
                                     \<and> (ar T \<cdot> (make_inc (d c) (d b \<union> d c))) \<cdot> t \<in> e c }  }" 
      using rel_semigroup_mult_e [where ?T=T and ?a=b and ?b=c]
      using R_def S_def T_valid b_el c_el by presburger 

    moreover have "... = { t . t \<in> ob T \<cdot> U
                                     \<and> (ar T \<cdot> (make_inc (d a) U)) \<cdot> t \<in> e a     
                                     \<and> (ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t \<in> ob T \<cdot> (d b \<union> d c) 
                                     \<and> ((ar T \<cdot> (make_inc (d b) (d b \<union> d c))) \<cdot> ((ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t)) \<in> e b     
                                     \<and> ((ar T \<cdot> (make_inc (d c) (d b \<union> d c))) \<cdot> ((ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t)) \<in> e c }"
      by blast 

    moreover have "... = { t . t \<in> ob T \<cdot> U   
                                     \<and> (ar T \<cdot> (make_inc (d a) U)) \<cdot> t \<in> e a    
                                     \<and> ((ar T \<cdot> (make_inc (d b) (d b \<union> d c))) \<cdot> ((ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t)) \<in> e b     
                                     \<and> ((ar T \<cdot> (make_inc (d c) (d b \<union> d c))) \<cdot> ((ar T \<cdot> (make_inc (d b \<union> d c) U)) \<cdot> t)) \<in> e c }"
      using Presheaf.restricted_element [where ?F="presheaf T" and ?A=U and ?B="d b \<union> d c"]
      by (metis (no_types, lifting) Presheaf.valid_space R_def T_valid Tuple.valid_welldefined U_def a_el b_el c_el local_dom sup.cobounded2 sup_assoc valid_rel_prealg valid_relation_space valid_union2)

    moreover have "... = mhs"
      by (smt (verit, del_insts) Collect_cong R_def S_def T_valid Tuple.valid_welldefined U_def \<open>{t . t \<in> Tuple.ob T \<cdot> U \<and> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a, cod = d a \<union> d b\<rparr>) \<cdot> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a \<union> d b, cod = U\<rparr>) \<cdot> t \<in> e a \<and> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d b, cod = d a \<union> d b\<rparr>) \<cdot> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a \<union> d b, cod = U\<rparr>) \<cdot> t \<in> e b \<and> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d c, cod = U\<rparr>) \<cdot> t \<in> e c} = mhs\<close> a_el b_el c_el local.trans local_dom rel_semigroup_mult_d rel_semigroup_mult_el sup.cobounded1 sup.cobounded2 sup_assoc valid_rel_prealg valid_relation_space) 

    ultimately have rhs : "rhs = mhs"
      by presburger 
    show ?thesis using lhs rhs
      using lhs_def rhs_def by fastforce
  qed
qed

lemma rel_semigroup_mult_valid :
  fixes T :: "('A, 'x) TupleSystem"
  assumes T_valid : "valid T"
  shows "Poset.valid_map (mult (rel_semigroup T))"
proof (intro Poset.valid_mapI, goal_cases)
  case 1
  then show ?case
    by (simp add: assms product_valid rel_semigroup_dom valid_gc valid_rel_prealg)
next
  case 2
  then show ?case
    by (simp add: assms rel_semigroup_cod valid_gc valid_rel_prealg)
next
  case (3 ab c)
  then show ?case using rel_semigroup_mult_welldefined_dom [where ?T=T] rel_semigroup_mult_welldefined_cod
      [where ?T=T] 
    by (metis assms surj_pair)
next
  case (4 ab c c')
  then show ?case
    by (metis assms prod.collapse rel_semigroup_mult_deterministic)     
next
  case (5 a)
  then show ?case
    by (metis assms prod.collapse rel_semigroup_mult_total) 
next
  case (6 a a')
  then show ?case
    by (metis assms prod.collapse rel_semigroup_cod rel_semigroup_mult_monotone) 
qed
 
lemma rel_semigroup_valid :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "Semigroup.valid (rel_semigroup T)"
proof (intro Semigroup.validI, safe, goal_cases)
  case 1
  then show ?case
    by (simp add: assms rel_semigroup_mult_valid) 
next
  case 2
  then show ?case
    by (simp add: assms rel_semigroup_cod rel_semigroup_dom) 
next
  case (3 A a B b C c)
  then show ?case
    by (simp add: assms rel_semigroup_cod rel_semigroup_mult_assoc) 
qed

theorem rel_semigroup_mult_comm : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "S \<equiv> rel_semigroup T"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" 
  and b_el : "b \<in> el (gc R)" 
shows "mul S a b = mul S b a"
proof (standard, goal_cases)
  case 1
  then show ?case using R_def S_def T_valid a_el b_el
    by (simp add: sup_commute) 
next
  case 2
  then show ?case using rel_semigroup_mult_val [where ?T=T]
    by (metis (no_types, lifting) Collect_cong R_def S_def T_valid a_el b_el sup_commute)
qed

(* Relational OVA *)

abbreviation rel_ova :: "('A, 'x) TupleSystem \<Rightarrow> ('A, 'x set) OVA" where
"rel_ova T \<equiv> \<lparr> prealgebra = rel_prealg T, neutral = rel_neutral T, semigroup = rel_semigroup T \<rparr>"

lemma rel_space : "valid T \<Longrightarrow> space T = OVA.space (rel_ova T)"
  by (simp add: valid_relation_space) 

lemma rel_el_open : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> d a \<in> opens (space T)"
  by (metis OVA.select_convs(3) comp_apply local_dom rel_semigroup_cod valid_rel_prealg valid_relation_space)

lemma rel_el_subset : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> e a \<subseteq> ob T \<cdot> d a"
  by (metis (no_types, lifting) OVA.select_convs(3) comp_apply gc_elem_local powerset_el rel_el_open rel_semigroup_cod relation_ob_value valid_rel_prealg)

lemma rel_subset_el : "valid T \<Longrightarrow> A \<in> opens (space T) \<Longrightarrow> a \<subseteq> ob T \<cdot> A \<Longrightarrow> (A, a) \<in> elems (rel_ova T)"
  by (simp add: local_elem_gc rel_semigroup_cod relation_as_value valid_rel_prealg valid_relation_space) 

lemma rel_comb_el : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> b \<in> elems (rel_ova T) 
   \<Longrightarrow> comb (rel_ova T) a b \<in> elems (rel_ova T)"
  by (simp add: rel_semigroup_cod rel_semigroup_mult_el) 

lemma rel_comb_d : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> b \<in> elems (rel_ova T) 
\<Longrightarrow> d (comb (rel_ova T) a b) = d a \<union> d b"
  by (simp add: rel_semigroup_cod) 

lemma rel_comb_e : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> b \<in> elems (rel_ova T) 
\<Longrightarrow> e (comb (rel_ova T) a b) = { t . t \<in> ob T \<cdot> (d a \<union> d b) 
                              \<and> (ar T \<cdot> make_inc (d a) (d a \<union> d b)) \<cdot> t \<in> e a
                              \<and> (ar T \<cdot> make_inc (d b) (d a \<union> d b)) \<cdot> t \<in> e b }" 
  using rel_semigroup_mult_e [where ?T=T and ?a=a and ?b=b]
  by (simp add: rel_semigroup_cod)

lemma rel_res_el : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> B \<in> Space.opens (space T) \<Longrightarrow> B \<subseteq> d a
  \<Longrightarrow> res (rel_ova T) B a \<in> elems (rel_ova T)"
  by (simp add: Prealgebra.restricted_element local_elem_gc rel_el_open rel_el_subset rel_semigroup_cod relation_as_value res_def valid_rel_prealg valid_relation_space) 

lemma rel_res_d : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> B \<in> Space.opens (space T) \<Longrightarrow> B \<subseteq> d a
  \<Longrightarrow> d (res (rel_ova T) B a) = B"
  by (simp add: valid_relation_space)

lemma rel_res_e : "valid T \<Longrightarrow> a \<in> elems (rel_ova T) \<Longrightarrow> B \<in> Space.opens (space T) \<Longrightarrow> B \<subseteq> d a
  \<Longrightarrow> e (res (rel_ova T) B a) = { (ar T \<cdot> make_inc B (d a)) \<cdot> t | t . t \<in> e a}"
using rel_prealg_def [where ?T=T] direct_image_app [where ?f="ar T \<cdot> make_inc B (d a)" and ?a="e a"]
  by (smt (z3) Inclusion.select_convs(1) Inclusion.select_convs(2) OVA.select_convs(1) Presheaf.valid_ar Presheaf.valid_dom Tuple.valid_welldefined mem_Collect_eq rel_el_open rel_el_subset relation_ar_value res_def snd_conv valid_relation_space)

lemma rel_neut_el : "valid T \<Longrightarrow> A \<in> Space.opens (space T)
  \<Longrightarrow> neut (rel_ova T) A \<in> elems (rel_ova T)"
  by (simp add: local_elem_gc rel_neutral_is_element rel_semigroup_cod valid_rel_prealg valid_relation_space)

lemma rel_neut_d : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow> d (neut (rel_ova T) A) = A"
  by simp 

lemma rel_neut_e : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow> e (neut (rel_ova T) A) = ob T \<cdot> A" 
using rel_neutral_def [where ?T=T] rel_neutral_nat_value_app [where ?T=T and ?A=A]
  by (smt (verit, del_insts) OVA.select_convs(2) PrealgebraMap.select_convs(1) Tuple.valid_space UNIV_unit all_not_in_conv empty_not_UNIV old.unit.exhaust rel_neutral_dom snd_conv terminal_value) 

lemma rel_diamond_rule :
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation" and u :: "'x"
  defines "V \<equiv> rel_ova T"
  and t_tup : "t \<equiv> (ar T \<cdot> make_inc (d a) (d a \<union> d b)) \<cdot> u"
  and s_tup : "s \<equiv> (ar T \<cdot> make_inc (d b) (d a \<union> d b)) \<cdot> u"
  assumes T_valid : "valid T"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  and u_tup : "u \<in> ob T \<cdot> (d a \<union> d b)"
shows "(ar T \<cdot> make_inc (d a \<inter> d b) (d a)) \<cdot> t = (ar T \<cdot> make_inc (d a \<inter> d b) (d b)) \<cdot> s"
  by (metis Presheaf.diamond_rule Space.valid_def T_valid Tuple.valid_space Tuple.valid_welldefined V_def a_el b_el inf_sup_ord(1) inf_sup_ord(2) inf_sup_ord(3) inf_sup_ord(4) rel_el_open s_tup t_tup u_tup valid_union2)

lemma rel_neutral_law_left : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open" and a :: "('A, 'x) Relation"
  defines "V \<equiv> rel_ova T"
  assumes T_valid : "valid T"
  and A_open : "A \<in> opens (space T)"
  and a_el : "a \<in> elems V"
shows "comb V (neut V (d a)) a = a"
proof -
  define "ea" where "ea = { t . t \<in> ob T \<cdot> d a \<and> (ar T \<cdot> (make_inc (d a) (d a))) \<cdot> t \<in> e (neut V (d a))    
                                         \<and> (ar T \<cdot> (make_inc (d a) (d a))) \<cdot> t \<in> e a }"
  have "e (comb V (neut V (d a)) a) = { t . t \<in> ob T \<cdot> d a \<and> t \<in> e (neut V (d a)) \<and> t \<in> e a }" 
    using rel_semigroup_mult_e [where ?T=T and ?a="neut V (d a)" and ?b=a] Presheaf.valid_identity
      [where ?F="presheaf T"] Function.ident_app
    by (smt (verit) Collect_cong OVA.select_convs(3) Space.ident_def T_valid Tuple.valid_welldefined Un_absorb V_def a_el comp_apply fst_conv rel_el_open rel_neut_el rel_semigroup_cod)
  moreover have "... = { t . t \<in> ob T \<cdot> d a \<and> t \<in> e a }" using calculation
      rel_neutral_nat_value_app [where ?T=T and ?A="d a"]
    by (metis (no_types, lifting) T_valid V_def a_el rel_el_open rel_neut_e)
  moreover have "... = e a" 
    using calculation relation_ob_value [where ?T=T and ?A="d a"] powerset_el [where ?A="ob T \<cdot> A" and ?a="e a"] assms
    by (smt (verit) Collect_cong Collect_mem_eq rel_el_subset subsetD)
  ultimately have e: "e (comb V (neut V (d a)) a) = e a"
    by presburger 
  have "a = (d a, e a)"  
    by simp 
  moreover have "comb V (neut V (d a)) a \<in> elems V"
    using T_valid V_def a_el rel_comb_el rel_el_open rel_neut_el by blast
  moreover have "(comb V (neut V (d a)) a)  = (d a, e a)" using gc_elD [where ?a="(comb V (neut V (d
        a)) a)"]  e calculation
    by (smt (z3) OVA.select_convs(3) T_valid V_def a_el comp_def eq_fst_iff rel_el_open rel_neut_el rel_semigroup_cod rel_semigroup_mult_d sup.idem)
  ultimately show ?thesis
    by presburger
qed

lemma comb_law_left : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x) Relation"
  defines "V \<equiv> rel_ova T"
  assumes T_valid : "valid T"
  and a_el : "a \<in> elems V"
  and b_el : "b \<in> elems V"
shows "res (rel_ova T) (d a) (comb (rel_ova T) a b) = comb (rel_ova T) a (res (rel_ova T) (d a \<inter> d b) b)"
proof (standard, goal_cases)
  case 1
  then show ?case
  proof -
    have "d (comb (rel_ova T) a b) = d a \<union> d b"
      using T_valid V_def a_el b_el rel_semigroup_cod by fastforce 
    moreover have "d (res (rel_ova T) (d a) (comb (rel_ova T) a b)) = d a" using d_res [where ?V=V and ?B="d a"]
      by (metis T_valid V_def a_el b_el calculation rel_comb_el rel_el_open rel_res_d sup.cobounded1)
    moreover have "d (res (rel_ova T) (d a \<inter> d b) b) = d a \<inter> d b"
      by (metis Int_lower2 T_valid Tuple.valid_space V_def a_el b_el rel_el_open rel_res_d valid_inter)
    moreover have "(res (rel_ova T) (d a \<inter> d b) b) \<in> elems V"
      by (metis Int_lower2 T_valid Tuple.valid_space V_def a_el b_el rel_el_open rel_res_el valid_inter) 
    moreover have "d (comb (rel_ova T) a (res (rel_ova T) (d a \<inter> d b) b)) = d a"
      by (metis Int_Un_eq(3) T_valid V_def a_el calculation(3) calculation(4) rel_comb_d) 
    ultimately show ?thesis
      by blast
  qed
  next
  case 2
  then show ?case 
  proof -
    define "i_A" where "i_A = make_inc (d a) (d a \<union> d b)"
    define "i_B" where "i_B = make_inc (d b) (d a \<union> d b)"
    define "i_AB_B" where "i_AB_B = make_inc (d a \<inter> d b) (d b)"
    define "i_AB_A" where "i_AB_A = make_inc (d a \<inter> d b) (d a)"

    define "lhs" where "lhs = e (res V (d a) (comb V a b)) "
    define "rhs" where "rhs = e (comb V a (res V (d a \<inter> d b) b))"

    have "e (comb V a b) = { t . t \<in> ob T \<cdot> (d a \<union> d b) 
                                      \<and> (ar T \<cdot> i_A) \<cdot> t \<in> e a     
                                      \<and> (ar T \<cdot> i_B) \<cdot> t \<in> e b }" 
        using  i_A_def i_B_def assms rel_comb_e [where ?T=T and ?a=a and ?b=b] by presburger

    moreover have "lhs = (Prealgebra.ar (rel_prealg T) \<cdot> i_A) \<star> { t . t \<in> ob T \<cdot> (d a \<union> d b) 
                                      \<and> (ar T \<cdot> i_A) \<cdot> t \<in> e a     
                                      \<and> (ar T \<cdot> i_B) \<cdot> t \<in> e b }"
      using i_A_def i_B_def assms  lhs_def calculation
      by (smt (verit, ccfv_threshold) OVA.select_convs(1) rel_comb_d rel_comb_el rel_el_open res_def snd_conv sup_ge1 valid_relation_space)

    moreover have l1: "... = { (ar T \<cdot> i_A) \<cdot> t | t . t \<in> ob T \<cdot> (d a \<union> d b) 
                                      \<and> (ar T \<cdot> i_A) \<cdot> t \<in> e a     
                                      \<and> (ar T \<cdot> i_B) \<cdot> t \<in> e b }"
      using assms i_A_def i_B_def rel_prealg_def [where ?T=T] direct_image_app [where ?f="ar T \<cdot>
          i_A"] calculation
      by (smt (z3) Collect_cong Inclusion.select_convs(1) Inclusion.select_convs(2) Presheaf.valid_ar Presheaf.valid_dom Tuple.valid_welldefined mem_Collect_eq rel_comb_d rel_comb_el rel_el_open rel_el_subset relation_ar_value sup_ge1) 

    ultimately have lhs2 : "lhs = { t | t s u . t \<in> e a \<and> s \<in> e b
                                     \<and> u \<in> ob T \<cdot> (d a \<union> d b) 
                                     \<and> s = (ar T \<cdot> i_B) \<cdot> u 
                                     \<and> t = (ar T \<cdot> i_A) \<cdot> u }"
      by blast 

      have r1: "e (res (rel_ova T) (d a \<inter> d b) b) = (Prealgebra.ar (rel_prealg T) \<cdot> i_AB_B) \<star> e b"
        using i_AB_B_def Int_lower2 OVA.select_convs(1) V_def res_def snd_eqD
      by (metis T_valid Tuple.valid_space a_el b_el rel_el_open valid_inter valid_relation_space)

    moreover have r2: "... = { (ar T \<cdot> i_AB_B) \<cdot> t | t . t \<in> e b }" 
        using rel_prealg_def [where ?T=T] direct_image_app [where ?f="ar T \<cdot> i_AB_B" and ?a="e b"] calculation
        by (smt (verit, del_insts) Inclusion.select_convs(1) Inclusion.select_convs(2) Int_lower2 Presheaf.valid_ar Presheaf.valid_dom T_valid Tuple.valid_space Tuple.valid_welldefined V_def a_el b_el i_AB_B_def mem_Collect_eq rel_el_open rel_el_subset relation_ar_value valid_inter)

    moreover have r3: "rhs =  { t . t \<in> ob T \<cdot> d a 
                                      \<and> (ar T \<cdot> (Space.ident (d a))) \<cdot> t \<in> e a     
                                      \<and> (ar T \<cdot> i_AB_A) \<cdot> t \<in> e (res (rel_ova T) (d a \<inter> d b) b) }"
      using  rel_comb_e [where ?T=T and ?a=a and ?b="res (rel_ova T) (d a \<inter> d b) b"] assms rhs_def
      by (smt (verit) Collect_cong Int_Un_eq(3) Int_lower2 Space.ident_def Tuple.valid_space fst_conv i_AB_A_def rel_el_open rel_res_el rel_space res_def valid_inter)

    moreover have r4: "... = { t . t \<in> ob T \<cdot> d a \<and> t \<in> e a \<and> (ar T \<cdot> i_AB_A) \<cdot> t \<in> e (res (rel_ova T) (d a \<inter> d b) b) }"
      by (metis (no_types, lifting) Function.ident_app Presheaf.valid_identity T_valid Tuple.valid_welldefined V_def a_el rel_el_open)

    moreover have r5: "... = { t . t \<in> e a \<and> (ar T \<cdot> i_AB_A) \<cdot> t \<in> e (res (rel_ova T) (d a \<inter> d b) b) }"
      by (metis (no_types, lifting) T_valid V_def a_el rel_el_subset subsetD)

    moreover have r6: "... = { t . t \<in> e a \<and> (ar T \<cdot> i_AB_A) \<cdot> t \<in> { (ar T \<cdot> i_AB_B) \<cdot> t | t .
        t \<in> e b } }" using r1 r2 by presburger 

    moreover have r7: "... = { t | t s . t \<in> e a \<and> s \<in> e b
                                       \<and> (ar T \<cdot> i_AB_A) \<cdot> t = (ar T \<cdot> i_AB_B) \<cdot> s }"
      by blast
    ultimately have rhs2: "rhs = { t | t s . t \<in> e a \<and> s \<in> e b
                                       \<and> (ar T \<cdot> i_AB_A) \<cdot> t = (ar T \<cdot> i_AB_B) \<cdot> s }"
        by presburger 

      moreover have "{ t | t s . t \<in> e a \<and> s \<in> e b \<and> (ar T \<cdot> i_AB_A) \<cdot> t = (ar T \<cdot> i_AB_B) \<cdot> s } 
                          \<subseteq> { t | u t s . u \<in> ob T \<cdot> (d a \<union> d b) 
                                     \<and> t \<in> e a \<and> s \<in> e b
                                     \<and> s = (ar T \<cdot> i_B) \<cdot> u 
                                     \<and> t = (ar T \<cdot> i_A) \<cdot> u }" 
        using valid_binary_gluing [where ?T=T and ?A="d a" and ?B="d b"] assms
          calculation i_AB_A_def i_AB_B_def i_A_def i_B_def
        by (smt (verit) Collect_mono_iff rel_el_open rel_el_subset subset_iff) 

      moreover have "rhs \<subseteq> lhs" using rhs2 lhs2
        using calculation(2) by force 

      moreover have "lhs \<subseteq> rhs" using rhs2 lhs2 calculation assms rel_diamond_rule [where ?T=T]
        by (smt (verit) Collect_mono_iff i_AB_A_def i_AB_B_def i_A_def i_B_def) 

      ultimately show ?thesis
        by (metis V_def lhs_def rhs_def subset_antisym)
    qed
  qed

(* [Theorem 2 (1/4), CVA] *)
theorem rel_ova_valid :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "OVA.valid (rel_ova T)"
proof (intro OVA.validI, goal_cases)
  case 1
  then show ?case
    by (smt (verit, best) OVA.select_convs(1) OVA.select_convs(2) OVA.select_convs(3) Prealgebra.valid_map_cod PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) assms comp_apply rel_neutral_def rel_semigroup_cod rel_neutral_valid rel_semigroup_valid valid_relation_space) 
next
  case 2
  then show ?case
    by (simp add: assms rel_semigroup_cod) 
next
  case 3
  then show ?case using rel_neutral_law_left [where ?T=T]
    by (simp add: assms valid_relation_space)
next
  case 4
  then show ?case using rel_neutral_law_left [where ?T=T] rel_semigroup_mult_comm [where ?T=T]
    by (smt (z3) OVA.select_convs(2) OVA.select_convs(3) assms comp_apply local_dom local_elem_gc rel_neutral_is_element rel_semigroup_cod valid_rel_prealg valid_relation_space) 
next
  case 5
  then show ?case using comb_law_left [where ?T=T]
    using assms by blast
next
  case 6
  then show ?case using comb_law_left [where ?T=T] rel_semigroup_mult_comm [where ?T=T]
    by (smt (verit, del_insts) Int_commute OVA.select_convs(3) Tuple.valid_space assms comp_apply inf_le1 rel_el_open rel_res_el rel_semigroup_cod valid_inter)
qed

(* [Theorem 2 (2/4), CVA] *)
theorem rel_ova_commutative :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "is_commutative (rel_ova T)"
  by (simp add: assms is_commutative_def rel_semigroup_cod rel_semigroup_mult_comm)

(* [Theorem 2 (3/4), CVA] *)
theorem rel_ova_strongly_neutral :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "is_strongly_neutral (rel_ova T)"
  unfolding is_strongly_neutral_def
proof safe
  fix A B
  assume "A \<in> opens (OVA.space (rel_ova T))"
  assume "B \<in> opens (OVA.space (rel_ova T))"

  define "lhs" where "lhs = comb (rel_ova T) (neut (rel_ova T) A) (neut (rel_ova T) B)"
  define "rhs" where "rhs = neut (rel_ova T) (A \<union> B)"

  have "rhs = (A \<union> B, ob T \<cdot> (A \<union> B))"
    by (metis OVA.select_convs(1) Tuple.valid_space \<open>A \<in> opens (OVA.space (rel_ova T))\<close> \<open>B \<in> opens (OVA.space (rel_ova T))\<close> rhs_def assms rel_neut_e snd_conv valid_relation_space valid_union2) 
  moreover have "\<forall> t .  t \<in> ob T \<cdot> (A \<union> B)  \<longrightarrow> (ar T \<cdot> make_inc A (A \<union> B)) \<cdot> t \<in> ob T \<cdot> A"
    by (metis OVA.select_convs(1) Presheaf.restricted_element Tuple.valid_space Tuple.valid_welldefined Un_upper1 \<open>A \<in> opens (OVA.space (rel_ova T))\<close> \<open>B \<in> opens (OVA.space (rel_ova T))\<close> assms valid_relation_space valid_union2)
  moreover have "\<forall> t .  t \<in> ob T \<cdot> (A \<union> B)  \<longrightarrow> (ar T \<cdot> make_inc B (A \<union> B)) \<cdot> t \<in> ob T \<cdot> B"
    by (metis OVA.select_convs(1) Presheaf.restricted_element Tuple.valid_space Tuple.valid_welldefined Un_upper2 \<open>A \<in> opens (OVA.space (rel_ova T))\<close> \<open>B \<in> opens (OVA.space (rel_ova T))\<close> assms valid_relation_space valid_union2)
  moreover have "lhs = (A \<union> B, { t . t \<in> ob T \<cdot> (A \<union> B)
                              \<and> (ar T \<cdot> make_inc A (A \<union> B) ) \<cdot> t \<in> ob T \<cdot> A
                              \<and> (ar T \<cdot> make_inc B (A \<union> B) ) \<cdot> t \<in> ob T \<cdot> B })"  using lhs_def
    rel_comb_e [where ?T=T] rel_neut_e [where ?T=T]
    by (smt (verit, best) Collect_cong \<open>A \<in> opens (OVA.space (rel_ova T))\<close> \<open>B \<in> opens (OVA.space (rel_ova T))\<close> assms prod.collapse prod.inject rel_comb_d rel_neut_el rel_space) 
  moreover have "... = (A \<union> B, ob T \<cdot> (A \<union> B))"
    using calculation(2) calculation(3) by auto
  ultimately have "lhs = rhs"
    by fastforce 
  thus "comb (rel_ova T) (neut (rel_ova T) A) (neut (rel_ova T) B) = neut (rel_ova T) (A \<union> B)"
    using lhs_def rhs_def by force
qed    

lemma rel_idempotent : 
  fixes T :: "('A, 'x) TupleSystem" and B :: "'A Open" and a :: "('A, 'x) Relation"
  defines "R \<equiv> rel_ova T"
  assumes T_valid : "valid T"
  assumes B_elem : "B \<in> Space.opens (OVA.space R)"
  and B_le_A :  "B \<subseteq> d a"
  and a_el : "a \<in> OVA.elems R"
  shows "OVA.comb R a (OVA.res R B a) = a"
proof -
  define "a_B" where "a_B = OVA.res R B a"
  define "a'" where "a' = OVA.comb R a a_B"
  have "comb R a a_B = mul (rel_semigroup T) a a_B"
    using R_def by auto 
  moreover have "a \<in> el (gc (rel_prealg T))"
    using R_def T_valid a_el rel_semigroup_cod by fastforce 
  moreover have "a_B \<in> el (gc (rel_prealg T))"
    by (metis B_elem B_le_A OVA.select_convs(3) R_def T_valid a_B_def a_el comp_apply rel_ova_valid rel_semigroup_cod res_elem) 
  moreover have "a' = mul (rel_semigroup T) a a_B"
    using a'_def calculation(1) by blast 
  moreover have "d a \<union> d a_B = d a"
    using B_elem B_le_A a_B_def a_el by auto 
  moreover have "e a' = {t |t.
     t \<in> Tuple.ob T \<cdot> (d a) \<and>
     (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a, cod = d a\<rparr>) \<cdot> t \<in> e a \<and> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a_B, cod = d a\<rparr>) \<cdot> t \<in> e a_B}"
    using  a'_def  rel_semigroup_mult_e [where ?T=T and ?a=a and ?b=a_B] T_valid calculation(1) calculation(2) calculation(3) calculation(5) by presburger 
  moreover have "... = {t |t.
     t \<in> Tuple.ob T \<cdot> (d a) \<and> t \<in> e a \<and> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a_B, cod = d a\<rparr>) \<cdot> t \<in> e
    a_B}"
    by (metis (no_types, lifting) Function.ident_app Presheaf.valid_identity Space.ident_def T_valid Tuple.valid_welldefined calculation(2) local_dom valid_rel_prealg valid_relation_space)
  moreover have "... =  {t |t. t \<in> e a \<and> (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a_B, cod = d a\<rparr>) \<cdot> t \<in> e a_B}"
    using R_def T_valid a_el rel_el_subset by blast 
  moreover have "\<forall> t. t \<in> e a \<longrightarrow>  (Tuple.ar T \<cdot> \<lparr>Inclusion.dom = d a_B, cod = d a\<rparr>) \<cdot> t \<in> e a_B"
    using a_B_def R_def
    by (metis (no_types, lifting) B_elem B_le_A OVA.select_convs(1) T_valid a_el calculation(2) d_res gc_elem_local local_dom relation_res_tup res_def snd_conv valid_rel_prealg valid_relation_space) 
  ultimately have "e a' = e a"
    by force
  thus ?thesis
    by (metis OVA.select_convs(3) R_def T_valid \<open>a \<in> el (gc (rel_prealg T))\<close> \<open>a_B \<in> el (gc (rel_prealg T))\<close> \<open>d a \<union> d a_B = d a\<close> a'_def a_B_def prod.collapse rel_semigroup_mult_d)
qed

lemma rel_idempotent_left : 
  fixes T :: "('A, 'x) TupleSystem" and B :: "'A Open" and a :: "('A, 'x) Relation"
  defines "R \<equiv> rel_ova T"
  assumes T_valid : "valid T"
  assumes B_elem : "B \<in> Space.opens (OVA.space R)"
  and B_le_A :  "B \<subseteq> d a"
  and a_el : "a \<in> OVA.elems R"
  shows "OVA.comb R (OVA.res R B a) a = a"
  by (metis B_elem B_le_A OVA.select_convs(1) OVA.select_convs(3) R_def T_valid a_el rel_idempotent rel_ova_valid rel_res_el rel_semigroup_mult_comm rel_space valid_gc_poset)

(* [Theorem 2 (4/4), CVA] *)
theorem rel_ova_tuple_system :
  fixes T :: "('A, 'x) TupleSystem"
  defines "R \<equiv> rel_ova T"
  defines "flasque \<equiv> \<forall>i. i \<in> inclusions (OVA.space R) \<longrightarrow> Poset.is_surjective (Prealgebra.ar (prealgebra R) \<cdot> i)"
  defines "binary_gluing \<equiv> \<forall> a b . a \<in> OVA.elems R \<longrightarrow> b \<in> OVA.elems R
        \<longrightarrow> OVA.res R (d a \<inter> d b) a = OVA.res R (d a \<inter> d b) b
        \<longrightarrow> (\<exists> c . c \<in> OVA.elems R \<and> d c = d a \<union> d b \<and> OVA.res R (d a) c = a \<and> OVA.res R (d b) c = b)"
  assumes "valid T"
  shows "flasque \<and> binary_gluing"
proof (safe, goal_cases)
  case 1
  then show ?case 
    unfolding flasque_def
using surj_imp_direct_image_surj Presheaf.valid_ar R_def Tuple.valid_welldefined assms(4) relation_ar_value valid_flasque valid_relation_space by fastforce
next
  case 2
  then show ?case              
    unfolding binary_gluing_def
    by (metis (no_types, lifting) Int_lower2 OVA.select_convs(1) R_def Tuple.valid_space assms(4) comb_is_element comb_law_left inf_le1 rel_el_open rel_idempotent rel_idempotent_left rel_ova_valid valid_comb_law_right valid_domain_law valid_inter valid_relation_space)    fix a b
qed

(* Lists (L) and non-empty lists (L_+) functors *)

definition lists :: "('A, 'x) TupleSystem \<Rightarrow> ('A, 'x list) TupleSystem" where
"lists T = 
  \<lparr> presheaf = \<lparr> 
    Presheaf.space = space T, 
    Presheaf.ob = \<lparr> Function.cod = UNIV, func = { (A, Function.lists (ob T \<cdot> A)) | A . A \<in> opens (space T) } \<rparr>,
     ar = \<lparr> Function.cod = UNIV, func = { (i, Function.lists_map (ar T \<cdot> i)) | i . i \<in> inclusions (space T) }  \<rparr> \<rparr> \<rparr>"

lemma lists_space: "Tuple.space (Tuple.lists T) = space T"
  by (simp add: Tuple.lists_def)

lemma lists_ob_value : "A \<in> opens (space T) \<Longrightarrow> (Presheaf.ob (presheaf (lists T))) \<cdot> A = Function.lists (ob T \<cdot> A)"
  unfolding lists_def
  by (simp add: Function.fun_app_iff Function.valid_map_def)

lemma lists_ar_value : "i \<in> inclusions (space T) \<Longrightarrow> (Presheaf.ar (presheaf (lists T))) \<cdot> i = Function.lists_map (ar T \<cdot> i)"
  unfolding lists_def
  by (simp add: Function.dom_def)

lemma lists_ar_value_valid : "valid T \<Longrightarrow> i \<in> inclusions (space T) \<Longrightarrow> Function.valid_map ((Presheaf.ar (presheaf (lists T))) \<cdot> i)"
  unfolding lists_def
  by (smt (verit) Function.fun_app_iff Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.Presheaf.select_convs(3) Presheaf.valid_ar Tuple.valid_welldefined TupleSystem.select_convs(1) UNIV_I fst_conv lists_map_valid mem_Collect_eq snd_conv) 

lemma lists_ar_dom : "valid T \<Longrightarrow> i \<in> inclusions (space T)
\<Longrightarrow> Function.dom (Presheaf.ar (presheaf (lists T)) \<cdot> i) = Presheaf.ob (presheaf (lists T)) \<cdot> Space.cod i"
  unfolding lists_def
  by (simp add: Function.fun_app_iff Function.valid_map_def Tuple.valid_welldefined lists_map_dom)

lemma lists_ar_cod : "valid T \<Longrightarrow> i \<in> inclusions (space T)
\<Longrightarrow> Function.cod (Presheaf.ar (presheaf (lists T)) \<cdot> i) = Presheaf.ob (presheaf (lists T)) \<cdot> Space.dom i"
  unfolding lists_def
  by (simp add: Function.fun_app_iff Function.valid_map_def Tuple.valid_welldefined lists_map_def)

lemma lists_ar_ident :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  defines "L \<equiv> presheaf (lists T)"
  assumes T_valid : "valid T"
  assumes A_open : "A \<in> opens (space T)"
  shows "Presheaf.ar L \<cdot> Space.ident A = Function.ident (Presheaf.ob L \<cdot> A)"
  using A_open L_def Presheaf.valid_identity T_valid Tuple.valid_welldefined lists_ar_value lists_map_ident lists_ob_value valid_ident_inc by fastforce

lemma lists_ar_trans :
  fixes T :: "('A, 'x) TupleSystem" and i j :: "'A Inclusion"
  defines "L \<equiv> presheaf (lists T)"
  assumes T_valid: "valid T"
  and i_inc : "i \<in> inclusions (space T)"
  and j_inc :"j \<in> inclusions (space T)"
  and endpoints : "Space.dom j = Space.cod i"
shows "Presheaf.ar L \<cdot> (j \<propto> i) = Presheaf.ar L \<cdot> i \<bullet> Presheaf.ar L \<cdot> j"
  by (smt (verit, del_insts) L_def Presheaf.valid_ar Presheaf.valid_cod Presheaf.valid_composition Presheaf.valid_dom T_valid Tuple.valid_welldefined cod_compose_inc compose_inc_valid dom_compose_inc endpoints i_inc j_inc lists_ar_value lists_map_trans mem_Collect_eq)

lemma valid_presheaf_lists : 
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "Presheaf.valid (presheaf (lists T))"
proof (intro Presheaf.validI, goal_cases)
  case 1
  then show ?case 
  unfolding lists_def
  by (simp add: Tuple.valid_space assms)
next
  case 2
  then show ?case 
  unfolding lists_def
  by fastforce
next
  case 3
  then show ?case
  unfolding lists_def
  by fastforce
next
  case (4 i)
  then show ?case
    unfolding lists_def
    apply clarsimp
    by (smt (verit) CollectD CollectI Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_mapI UNIV_I assms fst_conv lists_ar_value lists_ar_value_valid snd_conv)
next
  case (5 i)
  then show ?case 
    unfolding lists_def
    apply clarsimp
    by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.valid_dom Tuple.valid_welldefined UNIV_I assms fst_conv lists_map_dom mem_Collect_eq snd_conv)
next
  case (6 i)
  then show ?case 
    unfolding lists_def
    apply clarsimp
    by (simp add: Function.dom_def Tuple.valid_welldefined assms lists_map_cod)
next
  case (7 A)
  then show ?case
    using assms lists_ar_ident [where ?T=T and ?A=A] lists_space [where ?T=T]
    by simp
next
  case (8 i j)
  then show ?case 
    using assms lists_ar_trans [where ?T=T and ?i=i and ?j=j] lists_space [where ?T=T]
    by simp
qed

lemma valid_lists : 
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "valid (lists T)"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (simp add: assms valid_presheaf_lists) 
next
  case (2 i)
  then show ?case sorry
next
  case (3 A B a b)
  then show ?case sorry
qed     

end
