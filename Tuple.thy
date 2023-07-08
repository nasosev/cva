theory Tuple
  imports Main Presheaf Prealgebra OVA
begin

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
      flasque = \<forall>i. i \<in> Space.inclusions (space T) \<longrightarrow> Function.is_surjective (ar T \<cdot> i);
      binary_gluing = (\<forall> A B a b i_A j_A i_B j_B . A \<in> Space.opens (space T) \<longrightarrow> B \<in> Space.opens (space T) 
        \<longrightarrow> a \<in> ob T \<cdot> A
        \<longrightarrow> b \<in> ob T \<cdot> B
        \<longrightarrow> i_A = Space.make_inc (A \<inter> B) A
        \<longrightarrow> j_A = Space.make_inc A (A \<union> B)
        \<longrightarrow> i_B = Space.make_inc (A \<inter> B) B
        \<longrightarrow> j_B = Space.make_inc B (A \<union> B)
        \<longrightarrow> (ar T \<cdot> i_A) \<cdot> a = (ar T \<cdot> i_B) \<cdot> b
        \<longrightarrow> (\<exists> c . c \<in> (ob T \<cdot> (A \<union> B)) \<and> (ar T \<cdot> j_A) \<cdot> c = a \<and> (ar T \<cdot> j_B) \<cdot> c = b))
    in
    welldefined \<and> flasque \<and> binary_gluing"

(* Relational OVA generated from a tuple system *)

definition rel_prealg :: "('A, 'x) TupleSystem \<Rightarrow> ('A, 'x set) Prealgebra" where
  "rel_prealg T \<equiv>
    let
      R0 = \<lparr> Function.cod = UNIV, func = { (A, Poset.powerset (ob T \<cdot> A)) | A . A \<in> Space.opens (space T) } \<rparr>;
      R1 = \<lparr> Function.cod = UNIV, func = { (i, Poset.direct_image (ar T \<cdot> i)) | i . i \<in> Space.inclusions (space T) } \<rparr>
    in
    \<lparr> Prealgebra.space = space T, Prealgebra.ob = R0, Prealgebra.ar = R1 \<rparr>"

definition rel_neutral :: "('A, 'x) TupleSystem \<Rightarrow> ('A, unit, 'x set) PrealgebraMap" where
  "rel_neutral T \<equiv>
    let
      dom = Prealgebra.terminal (space T);
      cod = rel_prealg T;
      nat = \<lparr> 
              Function.cod = UNIV , 
              func = {(A, Poset.const (Prealgebra.ob dom \<cdot> A) (Prealgebra.ob cod \<cdot> A)  (ob T \<cdot> A)) | A . A \<in> Space.opens (space T)} 
            \<rparr>
    in
      \<lparr> dom = dom, cod = cod, nat = nat \<rparr>"

definition rel_comb :: "('A, 'x) TupleSystem \<Rightarrow> (('A, 'x set) Valuation) Semigroup" where
  "rel_comb T \<equiv> 
    let
      R = rel_prealg T;
      mult = \<lparr> 
              PosetMap.dom = gc R \<times>\<times> gc R, 
              cod = gc R, 
              func = { (((A,a), (B,b)), (C, c)) | A a B b C c .
                          A \<in> Space.opens (space T)
                        \<and> B \<in> Space.opens (space T)  
                        \<and> C = A \<union> B
                        \<and> a \<in> el (Prealgebra.ob R \<cdot> A)
                        \<and> b \<in> el (Prealgebra.ob R \<cdot> B)
                        \<and> c = { t | t . t \<in> ob T \<cdot> C
                                        \<and> (ar T \<cdot> (Space.make_inc A C)) \<cdot> t \<in> a     
                                        \<and> (ar T \<cdot> (Space.make_inc B C)) \<cdot> t \<in> b    }
                       }
             \<rparr>
    in
      \<lparr> Semigroup.mult = mult \<rparr>"

definition rel_alg :: "('A, 'x) TupleSystem \<Rightarrow> ('A, 'x set) OVA" where
"rel_alg T \<equiv>
  let
    R = rel_prealg T

  in
  undefined"

(* Validity of prealgebra *)

lemma valid_welldefined :  "valid T \<Longrightarrow> Presheaf.valid (presheaf T)" unfolding valid_def
  by (simp add: Let_def)

lemma valid_flasque : "valid T \<Longrightarrow> i \<in> Space.inclusions (space T) \<Longrightarrow> Function.is_surjective (ar T \<cdot> i)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_binary_gluing : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow> B \<in> Space.opens (space T) \<Longrightarrow> a \<in> ob T \<cdot> A
        \<Longrightarrow> b \<in> ob T \<cdot> B
         \<Longrightarrow> i_A = Space.make_inc (A \<inter> B) A
           \<Longrightarrow> j_A = Space.make_inc A (A \<union> B)
         \<Longrightarrow> i_B = Space.make_inc (A \<inter> B) B
           \<Longrightarrow> j_B = Space.make_inc B (A \<union> B)
            \<Longrightarrow> (ar T \<cdot> i_A) \<cdot> a = (ar T \<cdot> i_B) \<cdot> b
            \<Longrightarrow> (\<exists> c . c \<in> (ob T \<cdot> (A \<union> B)) \<and> (ar T \<cdot> j_A) \<cdot> c = a \<and> (ar T \<cdot> j_B) \<cdot> c = b)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_space : "valid T \<Longrightarrow> Space.valid (space T)"
  using Presheaf.valid_space Tuple.valid_welldefined by blast

lemma valid_relation_space : "valid T \<Longrightarrow> Prealgebra.space (rel_prealg T) = space T"
  unfolding rel_prealg_def
  by (meson Prealgebra.Prealgebra.select_convs(1))

lemma relation_ob_valid : "valid T \<Longrightarrow> Function.valid_map (Prealgebra.ob (rel_prealg T))"
  unfolding rel_prealg_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ar_valid : "valid T \<Longrightarrow> Function.valid_map (Prealgebra.ar (rel_prealg T))"
  unfolding rel_prealg_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ob_value : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow> (Prealgebra.ob (rel_prealg T)) \<cdot> A = Poset.powerset (ob T \<cdot> A )"
  unfolding rel_prealg_def
  by (simp add: Function.dom_def)

lemma relation_ob_value_valid : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow> Poset.valid (Prealgebra.ob (rel_prealg T) \<cdot> A)"
  using relation_ob_value [where ?T=T]
  by (simp add: powerset_valid)

lemma relation_as_value : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow> a \<subseteq> (ob T \<cdot> A) \<Longrightarrow> a \<in> el (Prealgebra.ob (rel_prealg T) \<cdot> A)"
  by (simp add: powerset_def relation_ob_value)

lemma relation_ar_value : "valid T \<Longrightarrow> i \<in> Space.inclusions (space T) 
\<Longrightarrow> Prealgebra.ar (rel_prealg T) \<cdot> i = Poset.direct_image (ar T \<cdot> i)"
  unfolding rel_prealg_def [where ?T=T]
  by (simp add: Function.dom_def)

lemma relation_ar_value_valid : "valid T \<Longrightarrow> i \<in> Space.inclusions (space T) \<Longrightarrow> Poset.valid_map (Prealgebra.ar (rel_prealg T) \<cdot> i)"
  using Presheaf.valid_ar Tuple.valid_welldefined direct_image_valid relation_ar_value by fastforce

lemma relation_ar_dom : "valid T \<Longrightarrow> i \<in> Space.inclusions (space T)
\<Longrightarrow> PosetMap.dom (Prealgebra.ar (rel_prealg T) \<cdot> i) = Prealgebra.ob (rel_prealg T) \<cdot> Space.cod i"
  unfolding rel_prealg_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.valid_dom Tuple.valid_welldefined UNIV_I direct_image_dom fst_conv mem_Collect_eq snd_conv)

lemma relation_ar_cod : "valid T \<Longrightarrow> i \<in> Space.inclusions (space T)
\<Longrightarrow> PosetMap.cod (Prealgebra.ar (rel_prealg T) \<cdot> i) = Prealgebra.ob (rel_prealg T) \<cdot> Space.dom i"
  unfolding rel_prealg_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.valid_welldefined Tuple.valid_welldefined UNIV_I direct_image_cod fst_conv mem_Collect_eq snd_conv)

lemma relation_ar_ident :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  defines "R \<equiv> rel_prealg T"
  assumes "valid T"
  assumes "A \<in> Space.opens (space T)"
  shows "Prealgebra.ar R \<cdot> Space.ident A = Poset.ident (Prealgebra.ob R \<cdot> A)"
  using Presheaf.valid_identity R_def Tuple.valid_welldefined assms(2) assms(3) direct_image_ident relation_ar_value relation_ob_value valid_ident_inc by fastforce

lemma relation_ar_trans :
  fixes T :: "('A, 'x) TupleSystem" and i j :: "'A Inclusion"
  defines "R \<equiv> rel_prealg T"
  assumes T_valid: "valid T"
  and i_inc : "i \<in> Space.inclusions (space T)"
  and j_inc :"j \<in> Space.inclusions (space T)"
  and endpoints : "Space.dom j = Space.cod i"
shows "Prealgebra.ar R \<cdot> (j \<propto> i) = Prealgebra.ar R \<cdot> i \<diamondop> Prealgebra.ar R \<cdot> j"
  by (smt (verit, ccfv_threshold) Presheaf.valid_ar Presheaf.valid_cod Presheaf.valid_composition Presheaf.valid_dom R_def T_valid Tuple.valid_welldefined cod_compose_inc compose_inc_valid direct_image_trans dom_compose_inc endpoints i_inc j_inc mem_Collect_eq relation_ar_value)

lemma valid_rel_prealg :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  defines "R \<equiv> rel_prealg T"
  shows "Prealgebra.valid R"
proof (intro Prealgebra.validI, standard+, goal_cases)
  case 1
  then show ?case
    using Presheaf.valid_space R_def Tuple.valid_welldefined assms(1) valid_relation_space by auto 
next
  case 2
  then show ?case
    by (simp add: R_def assms(1) relation_ar_cod relation_ar_dom relation_ar_valid relation_ar_value_valid relation_ob_valid relation_ob_value_valid valid_relation_space) 
next
  case 3
  then show ?case
    by (simp add: R_def assms(1) relation_ar_ident valid_relation_space) 
next
  case 4
  then show ?case
    using R_def assms(1) relation_ar_trans valid_relation_space by fastforce 
qed

(* Validity of neutral *)

lemma rel_neutral_nat_valid : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> Space.opens (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T"
  shows "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)"
proof -
  define "dom" where "dom = Prealgebra.terminal (space T)"
  define "cod" where "cod = rel_prealg T"
  have "(PrealgebraMap.nat (rel_neutral T)) \<cdot> A = Poset.const ((Prealgebra.ob dom) \<cdot> A) ((Prealgebra.ob cod) \<cdot> A) ((ob T) \<cdot> A)" 
    using rel_neutral_def [where ?T=T]
    by (smt (verit) Function.dom_def Function.fun_app_iff Function.select_convs(1) Function.select_convs(2) Function.valid_map_def PrealgebraMap.select_convs(3) UNIV_I \<open>A \<in> Space.opens (Tuple.space T)\<close> fst_conv local.cod_def local.dom_def mem_Collect_eq snd_conv)
  moreover have "Poset.valid (Prealgebra.ob dom \<cdot> A)"
    by (metis Presheaf.valid_space Tuple.valid_welldefined \<open>A \<in> Space.opens (Tuple.space T)\<close> \<open>Tuple.valid T\<close> discrete_valid local.dom_def terminal_ob)
  moreover have "Poset.valid (Prealgebra.ob cod \<cdot> A)"  using valid_rel_prealg [where ?T=T]
    by (simp add: \<open>A \<in> Space.opens (Tuple.space T)\<close> \<open>Tuple.valid T\<close> local.cod_def relation_ob_value_valid)
  ultimately show "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)" using Poset.const_valid
     cod_def dom_def powerset_def  relation_ob_value
    by (smt (verit) A_open Poset.Poset.select_convs(1) Pow_top T_valid \<epsilon>_def)
qed

lemma rel_neutral_nat_value : "valid T \<Longrightarrow> A \<in> Space.opens (space T) \<Longrightarrow>
 PrealgebraMap.nat (rel_neutral T) \<cdot> A =  Poset.const Poset.discrete (Prealgebra.ob (rel_prealg T) \<cdot> A) (ob T \<cdot> A)"
  unfolding rel_neutral_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app_iff Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.valid_space Tuple.valid_welldefined UNIV_I const_ob fst_conv mem_Collect_eq snd_conv)

lemma rel_neutral_is_element :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" 
  and A_open: "A \<in> Space.opens (space T)" 
  defines "R \<equiv> rel_prealg T"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (rel_neutral T) \<cdot> A) \<star> ()"
shows "\<epsilon>A \<in> el (Prealgebra.ob R \<cdot> A)"
  by (smt (verit, best) A_open Poset.Poset.select_convs(1) Poset.const_app Poset.discrete_def Pow_top R_def T_valid UNIV_I \<epsilon>A_def discrete_valid powerset_def rel_neutral_nat_value relation_ob_value relation_ob_value_valid)

lemma rel_neutral_nat_value_app :
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open" and x :: "unit"
  assumes T_valid: "valid T" 
  and A_open: "A \<in> Space.opens (space T)" 
  and x_el : "x \<in> el (Poset.dom (PrealgebraMap.nat (rel_neutral T) \<cdot> A ))"
shows "(PrealgebraMap.nat (rel_neutral T) \<cdot> A) \<star> x =  ob T \<cdot> A"
  by (smt (verit, ccfv_SIG) A_open Poset.Poset.select_convs(1) Poset.const_app Poset.discrete_def Pow_top T_valid UNIV_I discrete_valid powerset_def rel_neutral_nat_value relation_ob_value relation_ob_value_valid)

lemma rel_neutral_dom : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> Space.opens (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T"
  shows "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> A) = Prealgebra.ob (PrealgebraMap.dom \<epsilon>) \<cdot> A"
  by (smt (verit, ccfv_SIG) A_open Poset.Poset.select_convs(1) Poset.const_dom Pow_top PrealgebraMap.select_convs(1) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def powerset_def rel_neutral_def rel_neutral_nat_value relation_ob_value terminal_ob)

lemma rel_neutral_cod : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> Space.opens (space T)"
  defines "\<epsilon> \<equiv> rel_neutral T"
  shows "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> A) = Prealgebra.ob (PrealgebraMap.cod \<epsilon>) \<cdot> A"
  by (smt (verit, ccfv_SIG) A_open Poset.Poset.select_convs(1) Poset.const_cod Poset.discrete_def PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_witness \<epsilon>_def old.unit.exhaust rel_neutral_def rel_neutral_dom rel_neutral_is_element rel_neutral_nat_value rel_neutral_nat_value_app terminal_ob)

lemma rel_neutral_top : 
  fixes T :: "('A, 'x) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> Space.opens (space T)"
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
  assumes T_valid: "valid T" and i_inc: "i \<in> Space.inclusions (space T)"
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
    using calculation(3) calculation(4) by blast 
  obtain "x" where "x \<in> el (Poset.dom Ri) \<and> Ri \<star> x = \<epsilon>B"
    using \<open>\<exists>x. x \<in> el (PosetMap.dom Ri) \<and> Ri \<star> x = \<epsilon>B\<close> by blast 
  moreover have "Poset.le (PosetMap.dom Ri) x \<epsilon>A"
    using R_def Ri_def T_valid \<epsilon>A_def calculation(5) i_inc mem_Collect_eq rel_neutral_top relation_ar_dom by fastforce 
  ultimately show ?thesis
    by (smt (verit) Poset.fun_app Poset.valid_map_cod Presheaf.valid_ar R_def Ri_def T_valid Ti_def Tuple.valid_welldefined \<epsilon>A_def \<epsilon>B_def direct_image_mono i_inc mem_Collect_eq rel_neutral_top relation_ar_cod relation_ar_dom relation_ar_value_valid relation_ob_value_valid valid_antisymmetry) 
qed

lemma rel_neutral_natural : 
  fixes T :: "('A, 'x) TupleSystem" and i :: "'A Inclusion"
  assumes T_valid: "valid T" and i_inc: "i \<in> Space.inclusions (space T)"
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

lemma valid_rel_neutral :
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

lemma rel_comb_dom :  
  fixes T :: "('A, 'x) TupleSystem" and R:: "('A, 'x set) Prealgebra"
  assumes T_valid : "valid T"
  defines "R \<equiv> rel_prealg T"
  shows "PosetMap.dom (mult (rel_comb T)) = gc R \<times>\<times> gc R"
using rel_comb_def [where ?T=T]
  by (smt (verit, best) PosetMap.select_convs(1) R_def Semigroup.select_convs(1))

lemma rel_comb_cod :  
  fixes T :: "('A, 'x) TupleSystem" and R:: "('A, 'x set) Prealgebra"
  assumes T_valid : "valid T"
  defines "R \<equiv> rel_prealg T"
  shows "PosetMap.cod (mult (rel_comb T)) = gc R"
using rel_comb_def [where ?T=T]
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(2) R_def Semigroup.select_convs(1)) 

lemma rel_comb_mult_welldefined_dom :  
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x set) Valuation"
  assumes T_valid : "valid T" and abc_el : "((a,b), c) \<in> PosetMap.func (mult (rel_comb T))"
  shows "(a,b) \<in> el (PosetMap.dom (mult (rel_comb T)))"
proof -
  define "R" where "R = rel_prealg T"
  have "PosetMap.dom (mult (rel_comb T)) = gc R \<times>\<times> gc R"
    using R_def T_valid rel_comb_dom by blast 
  moreover have "a \<in> el (gc R)" using rel_comb_def [where ?T=T]
    by (smt (verit, best) Pair_inject PosetMap.select_convs(3) R_def Semigroup.select_convs(1) T_valid abc_el local_elem_gc mem_Collect_eq valid_rel_prealg valid_relation_space)
  moreover have "b \<in> el (gc R)" using rel_comb_def [where ?T=T]
    by (smt (z3) Pair_inject PosetMap.select_convs(3) R_def Semigroup.select_convs(1) T_valid abc_el local_elem_gc mem_Collect_eq valid_rel_prealg valid_relation_space)
  ultimately show ?thesis using assms
    by (simp add: Poset.product_def)
qed

lemma rel_comb_mult_val :  
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x set) Valuation"
  defines "R \<equiv> rel_prealg T"
  defines "dc \<equiv> d a \<union> d b"
  defines "ec \<equiv>  { t | t . t \<in> ob T \<cdot> dc \<and> (ar T \<cdot> (Space.make_inc (d a) dc)) \<cdot> t \<in> e a     
                                         \<and> (ar T \<cdot> (Space.make_inc (d b) dc)) \<cdot> t \<in> e b }"
  defines "c \<equiv> (dc, ec)"
  assumes T_valid : "valid T" and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)"
  shows "mul (rel_comb T) a b = c" 
proof -
  have "(a,b) \<in> el (gc R \<times>\<times> gc R)"
    by (simp add: Poset.product_def a_el b_el) 
  moreover have "(a,b) \<in> el (PosetMap.dom (mult (rel_comb T)))"
    using R_def T_valid calculation rel_comb_dom by fastforce
  moreover have "((a,b),c) \<in> PosetMap.func (mult (rel_comb T))" using rel_comb_def [where ?T=T]
    apply (simp add: Let_def)
    by (smt (verit) Collect_cong R_def T_valid a_el b_el c_def dc_def ec_def gc_elem_local local_dom prod.collapse valid_rel_prealg valid_relation_space)
  ultimately show ?thesis using rel_comb_def [where ?T=T] Poset.app_def [where ?f="mult
 (rel_comb T)" and ?a="(a,b)"]
    by (smt (z3) Pair_inject PosetMap.select_convs(3) Semigroup.select_convs(1) mem_Collect_eq the_equality) 
qed

lemma rel_comb_mult_dom : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x set) Valuation"
  defines "join \<equiv> mult (rel_comb T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "d (join \<star> (a, b)) = d a \<union> d b"
  using rel_comb_def [where ?T=T] assms rel_comb_mult_val [where ?T=T and ?a=a and ?b=b]
  by simp 

lemma rel_comb_mult_local_subset : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x set) Valuation"
  defines "join \<equiv> mult (rel_comb T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "e (join \<star> (a, b)) \<subseteq> ob T \<cdot> (d a \<union> d b)" 
  using rel_comb_def [where ?T=T] assms rel_comb_mult_val [where ?T=T and ?a=a and ?b=b]
  by simp 

lemma rel_comb_mult_local_el : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x set) Valuation"
  defines "join \<equiv> mult (rel_comb T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "e (join \<star> (a, b)) \<in> el (Prealgebra.ob R \<cdot> (d a \<union> d b))"
  using rel_comb_def [where ?T=T] assms rel_comb_mult_val [where ?T=T and ?a=a and ?b=b]
  by (metis (no_types, lifting) Tuple.valid_space local_dom rel_comb_mult_local_subset relation_as_value valid_rel_prealg valid_relation_space valid_union2) 

lemma rel_comb_mult_el : 
  fixes T :: "('A, 'x) TupleSystem" and a b :: "('A, 'x set) Valuation"
  defines "join \<equiv> mult (rel_comb T)"
  and "R \<equiv> rel_prealg T"
  assumes T_valid : "valid T" 
  and a_el : "a \<in> el (gc R)" and b_el : "b \<in> el (gc R)" 
shows "join \<star> (a, b) \<in> el (gc R)"
proof - 
  define "dc" where "dc = d a \<union> d b"
  define "ec" where "ec = { t | t . t \<in> ob T \<cdot> dc \<and> (ar T \<cdot> (Space.make_inc (d a) dc)) \<cdot> t \<in> e a     
                                        \<and> (ar T \<cdot> (Space.make_inc (d b) dc)) \<cdot> t \<in> e b }"
  define "c" where "c = (dc, ec)"
  have "(a,b) \<in> el (PosetMap.dom join)" using assms  Poset.product_def
    by (smt (verit) Poset.Poset.select_convs(1) SigmaI rel_comb_dom)
  moreover have "join \<star> (a, b) = c" using assms calculation rel_comb_def [where ?T=T] Poset.app_def
      [where ?f=join and ?a="(a,b)"] rel_comb_mult_val [where ?T=T and ?a=a and ?b=b]
    using c_def dc_def ec_def by fastforce 
  moreover have "ec \<subseteq> ob T \<cdot> dc"
    using ec_def by blast 
  ultimately show ?thesis
    by (metis R_def T_valid Tuple.valid_space a_el b_el c_def dc_def local_dom local_elem_gc relation_as_value valid_rel_prealg valid_relation_space valid_union2)
qed


lemma rel_comb_mult_welldefined_cod :  
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x set) Valuation"
  assumes T_valid : "valid T" and abc_el : "((a,b), c) \<in> PosetMap.func (mult (rel_comb T))"
  shows "c \<in> el (PosetMap.cod (mult (rel_comb T)))"
proof -
  define "R" where "R = rel_prealg T"
  have "PosetMap.cod (mult (rel_comb T)) = gc R" using rel_comb_def [where ?T=T]
    by (smt (verit, best) PosetMap.select_convs(2) R_def Semigroup.select_convs(1))
  moreover have "(a,b) \<in> el (PosetMap.dom (mult (rel_comb T)))"
    using T_valid abc_el rel_comb_mult_welldefined_dom by blast
  moreover have "mul (rel_comb T) a b = c" using rel_comb_def [where ?T=T] rel_comb_mult_val [where ?T=T and ?a=a and ?b=b]
    by (smt (verit) CollectD Collect_cong PosetMap.select_convs(3) Semigroup.select_convs(1) T_valid abc_el fst_conv local_elem_gc snd_conv valid_rel_prealg valid_relation_space)
  moreover have dc : "d c = d a \<union> d b"  using rel_comb_def [where ?T=T]
    by (smt (verit) CollectD PosetMap.select_convs(3) Semigroup.select_convs(1) abc_el fst_conv snd_conv)
  moreover have "e c \<subseteq> ob T \<cdot> (d c)" using rel_comb_def [where ?T=T] assms calculation
    by (smt (verit, del_insts) CollectD PosetMap.select_convs(3) Semigroup.select_convs(1) fst_conv snd_conv subsetI)
    moreover have da: "d a \<in> Space.opens (space T)"
      by (smt (verit) Poset.Poset.select_convs(1) Poset.product_def T_valid calculation(2) local_dom mem_Sigma_iff rel_comb_dom valid_rel_prealg valid_relation_space) 
    moreover have db: "d b \<in> Space.opens (space T)"
      by (smt (verit) Poset.Poset.select_convs(1) Poset.product_def T_valid calculation(2) local_dom mem_Sigma_iff rel_comb_dom valid_rel_prealg valid_relation_space) 
  moreover have "d c \<in> Space.opens (space T)" using da db dc Space.valid_union2 [where ?T="space T" and ?A=da and ?B=db]
      valid_space [where ?T=T]
    by (simp add: T_valid valid_union2) 
  moreover have "e c \<in> el (Prealgebra.ob R \<cdot> (d c))" using assms R_def rel_prealg_def [where ?T=T]
      relation_as_value [where ?T=T and ?A="d c" and ?a="e c"]
    using calculation(5) calculation(8) by fastforce 
  ultimately show ?thesis
    by (metis R_def T_valid local_elem_gc prod.collapse valid_rel_prealg valid_relation_space) 
qed

lemma rel_comb_mult_deterministic : 
  fixes T :: "('A, 'x) TupleSystem" and a b c c' :: "('A, 'x set) Valuation"
  assumes T_valid : "valid T" 
  and "((a,b), c) \<in> PosetMap.func (mult (rel_comb T))" and "((a,b), c') \<in> PosetMap.func (mult (rel_comb T))" 
shows "c = c'"
using rel_comb_def [where ?T=T]
  by (smt (z3) CollectD Pair_inject PosetMap.select_convs(3) Semigroup.select_convs(1) assms(2) assms(3))

lemma rel_comb_mult_total : 
  fixes T :: "('A, 'x) TupleSystem" and a b c :: "('A, 'x set) Valuation"
  assumes T_valid : "valid T" 
  and ab_el : "(a,b) \<in> el (PosetMap.dom (mult (rel_comb T)))" 
shows "\<exists>c. ((a,b), c) \<in> PosetMap.func (mult (rel_comb T))"
proof -
  define "dc" where "dc = d a \<union> d b"
  define "ec" where "ec = { t | t . t \<in> ob T \<cdot> dc \<and> (ar T \<cdot> (Space.make_inc (d a) dc)) \<cdot> t \<in> e a     
                                         \<and> (ar T \<cdot> (Space.make_inc (d b) dc)) \<cdot> t \<in> e b }"
  define "c" where "c = (dc, ec)"
  have "d a \<in> Space.opens (space T)"  using rel_comb_def [where ?T=T]
    by (metis (no_types, opaque_lifting) T_valid ab_el local_dom product_el_1 rel_comb_dom valid_rel_prealg valid_relation_space) 
  moreover have "d b \<in> Space.opens (space T)" using rel_comb_def [where ?T=T]
    by (metis (no_types, opaque_lifting) T_valid ab_el local_dom product_el_2 rel_comb_dom valid_rel_prealg valid_relation_space) 
  moreover have "e a \<in> el (Prealgebra.ob (rel_prealg T) \<cdot> (d a))"
    by (metis T_valid ab_el gc_elem_local product_el_1 rel_comb_dom valid_rel_prealg)
  moreover have "e b \<in> el (Prealgebra.ob (rel_prealg T) \<cdot> (d b))"
    by (metis T_valid ab_el gc_elem_local product_el_2 rel_comb_dom valid_rel_prealg) 
  moreover have "((a,b), c) \<in> PosetMap.func (mult (rel_comb T))" using assms calculation rel_comb_def [where ?T=T] dc_def
      ec_def c_def 
    apply (simp add :Let_def)
    using prod.exhaust_sel by blast
  ultimately show ?thesis
    by blast
qed

(* Todo: trim this *)
lemma rel_comb_mult_monotone : 
  fixes T :: "('A, 'x) TupleSystem" and a b a' b' :: "('A, 'x set) Valuation"
  defines "join \<equiv> mult (rel_comb T)"
  assumes T_valid : "valid T" 
  and ab_el : "(a,b) \<in> el (PosetMap.dom join)" 
  and a'b'_el : "(a',b') \<in> el (PosetMap.dom join)" 
  and "Poset.le (PosetMap.dom join) (a,b) (a',b')"
shows "Poset.le (PosetMap.cod join) (join \<star> (a, b)) (join \<star> (a', b'))"
proof -
  define "PP" where "PP = PosetMap.dom join"
  define "P" where "P = PosetMap.cod join"
  define "ab" where "ab = join \<star> (a, b)"
  define "a'b'" where "a'b' = join \<star> (a', b')"
  have "Poset.le P a a'" using rel_comb_def [where ?T=T]
    by (metis (no_types, lifting) P_def T_valid a'b'_el ab_el assms(5) join_def product_el_1 product_le_1 rel_comb_cod rel_comb_dom valid_gc valid_rel_prealg)
  moreover have "Poset.le P b b'" using rel_comb_def [where ?T=T]
    by (metis (no_types, lifting) T_valid a'b'_el ab_el assms(5) P_def join_def product_el_2 product_le_2 rel_comb_cod rel_comb_dom valid_gc valid_rel_prealg)      
  moreover have "a \<in> el P"
    by (metis P_def T_valid ab_el join_def product_el_1 rel_comb_cod rel_comb_dom) 
  moreover have "a' \<in> el P"
    by (metis P_def T_valid a'b'_el join_def product_el_1 rel_comb_cod rel_comb_dom)
  moreover have "d a' \<subseteq> d a"
    by (metis P_def T_valid calculation(1) calculation(3) calculation(4) d_antitone join_def rel_comb_cod valid_rel_prealg) 
  moreover have "b \<in> el P"
    by (metis P_def T_valid ab_el join_def product_el_2 rel_comb_cod rel_comb_dom) 
  moreover have "b' \<in> el P"
    by (metis P_def T_valid a'b'_el join_def product_el_2 rel_comb_cod rel_comb_dom) 
  moreover have "d b' \<subseteq> d b"
    by (metis P_def T_valid calculation(2) calculation(6) calculation(7) d_antitone join_def rel_comb_cod valid_rel_prealg) 
  moreover have "d b' \<subseteq> d b"
    using calculation(8) by force
  moreover have "(a,b) \<in> el PP"
    using PP_def ab_el by blast 
  moreover have "(a',b') \<in> el PP"
    using PP_def a'b'_el by blast 
  moreover have "ab \<in> el P" using ab_def join_def rel_comb_def [where ?T=T]
    by (metis (no_types, lifting) P_def T_valid calculation(3) calculation(6) rel_comb_cod rel_comb_mult_el)
  moreover have "a'b' \<in> el P" using ab_def join_def rel_comb_def [where ?T=T]
    by (metis (no_types, lifting) P_def T_valid a'b'_def calculation(4) calculation(7) rel_comb_cod rel_comb_mult_el)
  moreover have "d a'b' \<subseteq> d ab"
    by (metis P_def T_valid Un_mono a'b'_def ab_def calculation(3) calculation(4) calculation(5) calculation(6) calculation(7) calculation(8) join_def rel_comb_cod rel_comb_mult_dom) 
  define "i" where "i = Space.make (d a'b') (d ab)"
  
  moreover have "(Prealgebra.ar (rel_prealg T) \<cdot> i) \<star> (e ab) \<subseteq> e a'b'" using assms calculation rel_comb_def [where ?T=T]
    
  
  ultimately show ?thesis
  
  
lemma rel_comb_mult_valid :
  fixes T :: "('A, 'x) TupleSystem"
  assumes T_valid : "valid T"
  shows "Poset.valid_map (mult (rel_comb T))"
proof (intro Poset.valid_mapI, goal_cases)
  case 1
  then show ?case
    by (simp add: assms product_valid rel_comb_dom valid_gc valid_rel_prealg)
next
  case 2
  then show ?case
    by (simp add: assms rel_comb_cod valid_gc valid_rel_prealg)
next
  case (3 ab c)
  then show ?case using rel_comb_mult_welldefined_dom [where ?T=T] rel_comb_mult_welldefined_cod
      [where ?T=T] 
    by (metis assms surj_pair)
next
  case (4 ab c c')
  then show ?case
    by (metis assms prod.collapse rel_comb_mult_deterministic)     
next
  case (5 a)
  then show ?case
    by (metis assms prod.collapse rel_comb_mult_total) 
next
  case (6 a a')
  then show ?case sorry
qed

lemma valid_rel_comb :
  fixes T :: "('A, 'x) TupleSystem"
  assumes "valid T"
  shows "Semigroup.valid (rel_comb T)"
proof (intro Semigroup.validI, safe, goal_cases)
  case 1
  then show ?case sorry
next
  case 2
  then show ?case sorry
next
  case (3 a b a b a b)
  then show ?case sorry
qed
  oops

end
