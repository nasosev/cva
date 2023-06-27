theory Tuple
  imports Main Presheaf Prealgebra OVA
begin

(* We define a tuple system as Pos-valued presheaf for convenience, but we will ignore its poset
structure *)
type_synonym ('A, 'a) TupleSystem = "('A, 'a) Presheaf"

definition valid :: "('A, 'a) TupleSystem \<Rightarrow> bool" where
  "valid T \<equiv>
    let
      S = Presheaf.space T;
      T0 = Presheaf.ob T;
      T1 = Presheaf.ar T;

      welldefined = Presheaf.valid T;
      flasque = (\<forall>i. i \<in> Space.inclusions S \<longrightarrow> Function.is_surjective (T1 \<cdot>\<cdot> i));
      binary_gluing = (\<forall> A B a b i_A j_A i_B j_B . A \<in> Space.opens S \<longrightarrow> B \<in> Space.opens S \<longrightarrow> a \<in> (T0 \<cdot>\<cdot> A)
        \<longrightarrow> b \<in> (T0 \<cdot>\<cdot> B)
         \<longrightarrow> i_A = Space.make_inclusion S (A \<inter> B) A
           \<longrightarrow> j_A = Space.make_inclusion S A (A \<union> B)
         \<longrightarrow> i_B = Space.make_inclusion S (A \<inter> B) B
           \<longrightarrow> j_B = Space.make_inclusion S B (A \<union> B)
            \<longrightarrow> (T1 \<cdot>\<cdot> i_A) \<cdot>\<cdot> a = (T1 \<cdot>\<cdot> i_B) \<cdot>\<cdot> b
            \<longrightarrow> (\<exists> c . c \<in> (T0 \<cdot>\<cdot> (A \<union> B)) \<and> (T1 \<cdot>\<cdot> j_A) \<cdot>\<cdot> c = a \<and> (T1 \<cdot>\<cdot> j_B) \<cdot>\<cdot> c = b))
    in
    welldefined \<and> flasque \<and> binary_gluing"

definition relation_prealgebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) Prealgebra" where
  "relation_prealgebra T \<equiv>
    let
      S = Presheaf.space T;
      T0 = Presheaf.ob T;
      T1 = Presheaf.ar T;
      R0 = \<lparr> Function.cod = UNIV, func = {(A, Poset.powerset (T0 \<cdot>\<cdot> A)) | A . A \<in> Space.opens S} \<rparr>;
      R1 = \<lparr> Function.cod = UNIV, func = {(i, Poset.direct_image (T1 \<cdot>\<cdot> i)) | i . i \<in> Space.inclusions S} \<rparr>
    in
    \<lparr>Prealgebra.space = S, ob = R0, ar = R1\<rparr>"

definition relation_neutral :: "('A, 'a) TupleSystem \<Rightarrow> ('A, unit, 'a set) PrealgebraMap" where
  "relation_neutral T \<equiv>
    let
      map_space = Presheaf.space T;
      dom = Prealgebra.terminal map_space;
      cod = relation_prealgebra T;
      nat = \<lparr> Function.cod = UNIV , 
              func = {(A, Poset.const (Prealgebra.ob dom \<cdot>\<cdot> A) (Prealgebra.ob cod \<cdot>\<cdot> A)  (Presheaf.ob T \<cdot>\<cdot> A)) 
            | A . A \<in> Space.opens map_space}  \<rparr>
    in
      \<lparr> PrealgebraMap.map_space = map_space, nat = nat, dom = dom, cod = cod \<rparr>"

definition relation_algebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) OVA" where
"relation_algebra T \<equiv>
  let
    \<Psi> = relation_prealgebra T

  in
  undefined"

abbreviation (input) space :: "('A,'a) TupleSystem \<Rightarrow> 'A Space" where
"space T \<equiv> Presheaf.space T"

text \<open> ----------------- LEMMAS ----------------- \<close>

lemma valid_welldefined :  "valid T \<Longrightarrow> Presheaf.valid T" unfolding valid_def
  by (simp add: Let_def)

lemma valid_flasque : "valid T \<Longrightarrow> i \<in> Space.inclusions (Presheaf.space T) \<Longrightarrow> Function.is_surjective (Presheaf.ar T \<cdot>\<cdot> i)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_binary_gluing : "valid T \<Longrightarrow>  A \<in> Space.opens (Presheaf.space T) \<Longrightarrow> B \<in> Space.opens (Presheaf.space T) \<Longrightarrow> a \<in> Presheaf.ob T \<cdot>\<cdot> A
        \<Longrightarrow> b \<in> Presheaf.ob T \<cdot>\<cdot> B
         \<Longrightarrow> i_A = Space.make_inclusion (Presheaf.space T) (A \<inter> B) A
           \<Longrightarrow> j_A = Space.make_inclusion (Presheaf.space T) A (A \<union> B)
         \<Longrightarrow> i_B = Space.make_inclusion (Presheaf.space T) (A \<inter> B) B
           \<Longrightarrow> j_B = Space.make_inclusion (Presheaf.space T) B (A \<union> B)
            \<Longrightarrow> (Presheaf.ar T \<cdot>\<cdot> i_A) \<cdot>\<cdot> a = (Presheaf.ar T \<cdot>\<cdot> i_B) \<cdot>\<cdot> b
            \<Longrightarrow> (\<exists> c . c \<in> (Presheaf.ob T \<cdot>\<cdot> (A \<union> B)) \<and> (Presheaf.ar T \<cdot>\<cdot> j_A) \<cdot>\<cdot> c = a \<and> (Presheaf.ar T \<cdot>\<cdot> j_B) \<cdot>\<cdot> c = b)"
  unfolding valid_def
  by (simp add: Let_def)

lemma relation_space_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> Prealgebra.space R = Presheaf.space T"
  unfolding relation_prealgebra_def
  by (meson Prealgebra.Prealgebra.select_convs(1))

lemma relation_ob_valid : "valid T \<Longrightarrow> R0 = Prealgebra.ob (relation_prealgebra T) \<Longrightarrow> Function.valid_map R0"
  unfolding relation_prealgebra_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ar_valid : "valid T \<Longrightarrow> R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow> Function.valid_map R1"
  unfolding relation_prealgebra_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ob_value : "valid T \<Longrightarrow> R0 = Prealgebra.ob (relation_prealgebra T) \<Longrightarrow>
 (\<And> A . A \<in> Space.opens (Presheaf.space T) \<Longrightarrow> X = (Presheaf.ob T) \<cdot>\<cdot> A \<Longrightarrow> R0 \<cdot>\<cdot> A = Poset.powerset X)"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I fst_conv mem_Collect_eq snd_conv)

lemma relation_ob_value_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
 (\<And> A .A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> Poset.valid (R0 \<cdot>\<cdot> A))"
  using relation_ob_value [where ?T=T]
  by (metis powerset_valid relation_space_valid)

lemma relation_ar_value : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow>
 (\<And> i.  i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> X = (Presheaf.ob T) \<cdot>\<cdot> (Space.cod i) \<Longrightarrow> Y = (Presheaf.ob T) \<cdot>\<cdot> (Space.dom i)
\<Longrightarrow> f= Presheaf.ar T \<cdot>\<cdot> i \<Longrightarrow> R1 \<cdot>\<cdot> i = Poset.direct_image f)"
  unfolding relation_prealgebra_def [where ?T=T]
  by (smt (verit) Function.fun_app Function.select_convs(2) Function.valid_map_def Prealgebra.Prealgebra.select_convs(3) \<open>relation_prealgebra T \<equiv> let S = Presheaf.space T; T0 = Presheaf.ob T; T1 = Presheaf.ar T; R0 = \<lparr>Function.cod = UNIV, func = {(A, powerset (T0 \<cdot>\<cdot> A)) |A. A \<in> Space.opens S}\<rparr>; R1 = \<lparr>Function.cod = UNIV, func = {(i, direct_image (T1 \<cdot>\<cdot> i)) |i. i \<in> Space.inclusions S}\<rparr> in \<lparr>Prealgebra.space = S, ob = R0, ar = R1\<rparr>\<close> mem_Collect_eq relation_ar_valid relation_space_valid) 

lemma relation_ar_value_valid : "valid T \<Longrightarrow>  R = relation_prealgebra T \<Longrightarrow>  R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow>
  (\<And> i . i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> Poset.valid_map (R1 \<cdot>\<cdot> i))"
  by (metis Presheaf.valid_ar Tuple.valid_welldefined direct_image_valid relation_ar_value relation_space_valid)

lemma relation_ar_dom : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
R1 = Prealgebra.ar R \<Longrightarrow> i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.dom (R1 \<cdot>\<cdot> i) = R0 \<cdot>\<cdot> Inclusion.cod i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.dom_proj Tuple.valid_welldefined UNIV_I direct_image_dom fst_conv inclusions_def mem_Collect_eq snd_conv valid_inclusion_def)


lemma relation_ar_cod : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
R1 = Prealgebra.ar R \<Longrightarrow> i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.cod (R1 \<cdot>\<cdot> i) = R0 \<cdot>\<cdot> Inclusion.dom i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Pair_inject Presheaf.cod_proj Tuple.valid_welldefined UNIV_I direct_image_cod inclusions_def mem_Collect_eq valid_inclusion_def)

lemma relation_ar_ident :
  fixes T :: "('A,'a) TupleSystem" and A :: "'A Open"
  defines "R \<equiv> relation_prealgebra T"
assumes "valid T"
  assumes "A \<in> Space.opens (Prealgebra.space R)"
  shows "(ar R) \<cdot>\<cdot> Space.ident (Prealgebra.space R) A = Poset.ident ((ob R) \<cdot>\<cdot> A)"
proof -
  define "i" where "i = Space.ident (Prealgebra.space R) A"
  define "f" where "f = Presheaf.ar T"
  define "Rf" where "Rf = (ar R) \<cdot>\<cdot> i"
  moreover have c: "Space.cod i = A"
    by (simp add: Space.ident_def i_def)
  moreover have "Space.dom i = A"
    by (simp add: Space.ident_def i_def)
  moreover have "\<forall> u . u \<in> Presheaf.ob T \<cdot>\<cdot> A \<longrightarrow> (f \<cdot>\<cdot> i) \<cdot>\<cdot> u = u"
    by (metis Function.ident_app Presheaf.ident_app R_def Tuple.valid_welldefined assms(2) assms(3) f_def i_def relation_space_valid) 
  moreover have "(Prealgebra.ob R) \<cdot>\<cdot> A = powerset ((Presheaf.ob T) \<cdot>\<cdot> A)" using  relation_prealgebra_def
      [where ?T=T]
    using R_def assms(2) assms(3) relation_ob_value relation_space_valid by fastforce 
  moreover have "i \<in> Space.inclusions (Prealgebra.space R)" using R_def relation_space_valid [where
        ?T=T and ?R=R] Space.valid_ident_inclusion  [where ?T="(Presheaf.space T)" and ?A=A]
    using Presheaf.valid_space Tuple.valid_welldefined assms(2) assms(3) i_def by auto  
  moreover have "Poset.dom ((ar R) \<cdot>\<cdot> i) = (ob R) \<cdot>\<cdot> (Inclusion.cod i)"
    using  assms(3)
    using R_def assms(2) calculation(6) relation_ar_dom by blast
  moreover have "Rf = Poset.direct_image (f \<cdot>\<cdot> i)" using Rf_def  relation_prealgebra_def [where ?T=T]
    using R_def assms(2) calculation(6) f_def relation_ar_value by blast
    
  moreover have "Poset.dom Rf = (ob R) \<cdot>\<cdot> A"
    using Rf_def c calculation(7) by blast  
  moreover have "Poset.cod Rf = (ob R) \<cdot>\<cdot> A"
    using R_def Rf_def assms(2) calculation(3) calculation(6) relation_ar_cod by blast  
  moreover have "(Presheaf.ar T) \<cdot>\<cdot> i = Function.ident ((Presheaf.ob T) \<cdot>\<cdot> A)"
    by (metis Presheaf.valid_identity R_def Tuple.valid_welldefined assms(2) assms(3) i_def relation_space_valid) 
    moreover have "(ar R) \<cdot>\<cdot> i = Poset.ident ((ob R) \<cdot>\<cdot> A)"
      by (metis Rf_def calculation(11) calculation(5) calculation(8) direct_image_ident f_def) 
    ultimately show ?thesis using R_def  relation_prealgebra_def [where ?T=T] i_def
      by metis
  qed

lemma relation_ar_trans :
  fixes T :: "('A,'a) TupleSystem" and i j :: "'A Inclusion"
  defines "R \<equiv> relation_prealgebra T"
  assumes T_valid: "Presheaf.valid T"
  and i_inc : "i \<in> Space.inclusions (Prealgebra.space R)"
  and j_inc :"j \<in> Space.inclusions (Prealgebra.space R)"
  and endpoints : "Inclusion.dom j = Inclusion.cod i"
shows "ar R \<cdot>\<cdot> Space.compose j i = ar R \<cdot>\<cdot> i \<odot> ar R \<cdot>\<cdot> j"
proof -
  define "f" where "f = Presheaf.ar T"
  have "ar R \<cdot>\<cdot> i = direct_image (f \<cdot>\<cdot> i)" 
  moreover have "ar R \<cdot>\<cdot> j = direct_image (f j) (el (ob T \<cdot>\<cdot> Inclusion.cod j)) (el (ob T \<cdot>\<cdot> Inclusion.dom j))"
    using R_def T_valid f_def j_inc relation_ar_value by blast
  define "ji" where "ji = (Space.compose j i)"
    moreover have "ar R \<cdot>\<cdot> ji = direct_image (f ji) (el (ob T \<cdot>\<cdot> Inclusion.cod ji)) (el (ob T \<cdot>\<cdot>
      Inclusion.dom ji))"
      by (smt (z3) Inclusion.select_convs(1) R_def Space.compose_def Space.compose_valid T_valid endpoints f_def i_inc inclusions_def j_inc ji_def mem_Collect_eq relation_ar_value)
    moreover have "\<forall> x . x \<in> el (ob T \<cdot>\<cdot> (Inclusion.cod j)) \<longrightarrow> f ji x = (f i o f j) x"
      by (smt (verit, ccfv_SIG) R_def T_valid Tuple.valid_welldefined cod_proj comp_apply compose_app dom_proj endpoints f_def i_inc j_inc ji_def relation_space_valid valid_ar valid_composition)
    moreover have "ar R \<cdot>\<cdot> Space.compose j i = ar R \<cdot>\<cdot> i \<odot> ar R \<cdot>\<cdot> j"
      by (smt (verit) Prealgebra.valid_welldefined R_def Space.cod_compose Space.dom_compose T_valid Tuple.valid_welldefined \<open>ar R \<cdot>\<cdot> j = direct_image (f j) (el (ob T \<cdot>\<cdot> Inclusion.cod j)) (el (ob T \<cdot>\<cdot> Inclusion.dom j))\<close> calculation(1) calculation(3) compose_app direct_image_trans_weak endpoints f_def i_inc image inclusions_def j_inc ji_def mem_Collect_eq relation_space_valid valid_composition)
    ultimately show ?thesis
      by meson
  qed

lemma valid_relation_prealgebra :
  fixes T :: "('A,'a) TupleSystem"
  assumes "valid T"
  defines "R \<equiv> relation_prealgebra T"
  shows "Prealgebra.valid R"
proof (rule Prealgebra.validI, auto)
  show "Space.valid (Prealgebra.space R)"
    by (metis Presheaf.valid_space R_def Tuple.valid_welldefined assms(1) relation_space_valid) 
  show "Function.valid_map (ob R)"
    using R_def assms(1) relation_ob_valid by auto
  show "Function.valid_map (ar R)"
    using R_def assms(1) relation_ar_valid by auto
  show "\<And>A. A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> Poset.valid (ob R \<cdot>\<cdot> A)"
    by (metis R_def assms(1) relation_ob_value_valid relation_space_valid)
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> Poset.valid_map (ar R \<cdot>\<cdot> i)"
    by (metis R_def assms(1) relation_ar_value_valid relation_space_valid)
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.dom (ar R \<cdot>\<cdot> i) = ob R \<cdot>\<cdot> Inclusion.cod
 i"
    using R_def assms(1) relation_ar_dom by blast
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.cod (ar R \<cdot>\<cdot> i) = ob R \<cdot>\<cdot> Inclusion.dom
 i"
    using R_def assms(1) relation_ar_cod by blast
  show "\<And>A. A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> ar R \<cdot>\<cdot> Space.ident (Prealgebra.space R) A =
 Poset.ident (ob R \<cdot>\<cdot> A)"
    using R_def assms(1) relation_ar_ident by blast
  show "\<And>i j. j \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow>
           i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow>
           Inclusion.dom j = Inclusion.cod i \<Longrightarrow> ar R \<cdot>\<cdot> Space.compose j i = ar R \<cdot>\<cdot> i \<odot> ar R \<cdot>\<cdot> j"
    by (simp add: R_def assms(1) relation_ar_trans)
qed

lemma relation_neutral_nat_valid : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A)"
proof-
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "dom" where "dom = Prealgebra.terminal (map_space \<epsilon>)"
  define "cod" where "cod = relation_prealgebra T"

  have "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A = Poset.const (Prealgebra.ob dom \<cdot>\<cdot> A) (Prealgebra.ob cod \<cdot>\<cdot> A) (el (ob
 T \<cdot>\<cdot> A))" using relation_neutral_def [where ?T=T]
    by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Pair_inject PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) UNIV_I \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>\<epsilon> = relation_neutral T\<close> local.cod_def local.dom_def mem_Collect_eq)
  moreover have "Poset.valid (Prealgebra.ob dom \<cdot>\<cdot> A)"
    by (simp add: \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> discrete_valid local.dom_def terminal_def)
  moreover have "Poset.valid (Prealgebra.ob cod \<cdot>\<cdot> A)"  using valid_relation_prealgebra [where ?T=T]
    by (metis (no_types, lifting) PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> local.cod_def relation_neutral_def relation_space_valid valid_ob)
  show "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A)" using Poset.const_valid [where ?P="Prealgebra.ob
 dom \<cdot>\<cdot> A" and ?Q="Prealgebra.ob cod \<cdot>\<cdot> A" and ?q="el (ob
 T \<cdot>\<cdot> A)"]
    by (metis (no_types, lifting) Poset.Poset.simps(1) Pow_top PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Poset.valid (ob cod \<cdot>\<cdot> A)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation(1) calculation(2) local.cod_def powerset_def relation_neutral_def relation_ob_value)
qed

lemma relation_neutral_nat_value : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> \<epsilon>A = el (ob T \<cdot>\<cdot> A) \<Longrightarrow>
 PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A =  Poset.const Poset.discrete (ob R \<cdot>\<cdot> A) \<epsilon>A"
  unfolding relation_neutral_def
  apply (simp_all add : Let_def)
  by (simp add: Function.dom_def Function.valid_map_def terminal_def)

lemma relation_neutral_nat_value_app : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> \<epsilon>A = el (ob T \<cdot>\<cdot> A) \<Longrightarrow> domain = Poset.dom ( PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A ) \<Longrightarrow>
 x \<in> el domain \<Longrightarrow> (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) \<cdot> x =  \<epsilon>A"
  using relation_neutral_nat_value [where ?T = T and ?A = A]
proof -
  define "one" where "one = PrealgebraMap.dom \<epsilon>"
    fix T \<epsilon> A x domain R \<epsilon>A
    assume "valid T"
    assume "\<epsilon> = relation_neutral T"
    assume "A \<in> Space.opens (map_space \<epsilon>)"
    assume "R = relation_prealgebra T"
    assume "\<epsilon>A = el (ob T \<cdot>\<cdot> A)"
    assume "domain = Poset.dom ( PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A )"
    assume "x \<in> el domain"
    have "x = ()"
      by simp 
    moreover have "\<epsilon>A \<in> el (ob R \<cdot>\<cdot> A)"
      by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>R = relation_prealgebra T\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> \<open>\<epsilon>A = el (ob T \<cdot>\<cdot> A)\<close> powerset_def relation_neutral_def relation_ob_value)  
    moreover have "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A = Poset.const Poset.discrete (ob R \<cdot>\<cdot> A) \<epsilon>A"
      using \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>R = relation_prealgebra T\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> \<open>\<epsilon>A = el (ob T \<cdot>\<cdot> A)\<close> relation_neutral_nat_value by blast 
                                                                      
    ultimately show "(PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) \<cdot> x =  \<epsilon>A" using Poset.const_app [where
 ?P="Poset.discrete" and ?Q="(ob R \<cdot>\<cdot> A)" and ?q=\<epsilon>A and ?p=x]
      by (metis (no_types, lifting) Poset.Poset.select_convs(1) PrealgebraMap.select_convs(1) UNIV_I \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>R = relation_prealgebra T\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> discrete_def discrete_valid relation_neutral_def relation_ob_value_valid relation_space_valid) 
  qed

lemma relation_neutral_dom : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = ob (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> A"
proof -
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "R" where "R = relation_prealgebra T"
  have "dom \<epsilon> = Prealgebra.terminal (space T)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(3) \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_def)
  moreover have "ob (dom \<epsilon>) \<cdot>\<cdot> A = Poset.discrete"
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(2) PrealgebraMap.select_convs(1) UNIV_I \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation const_app relation_neutral_def terminal_def)
  moreover have "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A = Poset.const discrete (ob R \<cdot>\<cdot> A) (el (ob T \<cdot>\<cdot> A))"
    using R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_nat_value by blast
  moreover have "el (ob T \<cdot>\<cdot> A) \<in> el (ob R \<cdot>\<cdot> A)"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top PrealgebraMap.select_convs(1) R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> powerset_def relation_neutral_def relation_ob_value)
  moreover have "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = Poset.discrete" using calculation
      Poset.const_def [where ?q="el (ob T \<cdot>\<cdot> A)" and ?Q="(ob R \<cdot>\<cdot> A) " and ?P="Poset.discrete"]
    by (smt (verit, ccfv_SIG) PosetMap.select_convs(2))
    ultimately show "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = ob
 (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> A"
      by presburger
  qed

lemma relation_neutral_cod : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = ob (PrealgebraMap.cod \<epsilon>) \<cdot>\<cdot> A"
proof -
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "R" where "R = relation_prealgebra T"
  have "cod \<epsilon> = R"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(4) R_def \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_def) 
  moreover have "ob (cod \<epsilon>) \<cdot>\<cdot> A = ob R \<cdot>\<cdot> A"
    using calculation by fastforce
  moreover have "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A = Poset.const discrete (ob R \<cdot>\<cdot> A) (el (ob T \<cdot>\<cdot> A))"
    using R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_nat_value by blast
  moreover have "el (ob T \<cdot>\<cdot> A) \<in> el (ob R \<cdot>\<cdot> A)"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top PrealgebraMap.select_convs(1) R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> powerset_def relation_neutral_def relation_ob_value)
  moreover have "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) =  ob R \<cdot>\<cdot> A"
    by (simp add: Poset.const_def calculation(3) calculation(4)) 
    ultimately show "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = ob (PrealgebraMap.cod \<epsilon>) \<cdot>\<cdot> A"
      by meson 
  qed

lemma relation_neutral_stable : 
  fixes T :: "('A, 'a) Prealgebra" and i :: "'A Inclusion"
  assumes T_valid: "valid T" and i_inc: "i \<in> Space.inclusions (space T)"
  defines "R \<equiv> relation_prealgebra T"
  and "\<epsilon> \<equiv> (relation_neutral T)"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (relation_neutral T) \<cdot>\<cdot> Space.cod i) \<cdot> ()"
  and "\<epsilon>B \<equiv> ((PrealgebraMap.nat (relation_neutral T)) \<cdot>\<cdot> Space.cod i) \<cdot> ()"
shows "(ar R \<cdot>\<cdot> i) \<cdot> \<epsilon>A = \<epsilon>B"
proof -
  have "\<exists> x . (ar R \<cdot>\<cdot> i) \<cdot> \<epsilon>A = \<epsilon>B" using valid_flasque [where ?T=T and ?i=i] 


lemma relation_neutral_natural : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> 
i \<in> Space.inclusions (map_space \<epsilon>) \<Longrightarrow>
         PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.dom i \<odot> ar (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> i =
         ar (PrealgebraMap.cod \<epsilon>) \<cdot>\<cdot> i \<odot> PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.cod i"
proof -
  fix T i \<epsilon>
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "i \<in> Space.inclusions (map_space \<epsilon>)"
  define "R" where "R = relation_prealgebra T"


  show "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.dom i \<odot> ar (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> i =
         ar (PrealgebraMap.cod \<epsilon>) \<cdot>\<cdot> i \<odot> PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.cod i"
  proof -
    define "one" where "one = PrealgebraMap.dom \<epsilon>"
    fix x
    assume "x \<in> el (ob one \<cdot>\<cdot> (Space.cod i))"
    have "x = ()"
      by simp 
    moreover have "ar (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> i \<cdot> x = ()"
      by simp 
    moreover have "Inclusion.dom i \<in> Space.opens (map_space \<epsilon>)"
      using \<open>i \<in> Space.inclusions (map_space \<epsilon>)\<close> inclusions_def valid_inclusion_def by force 
    moreover have " el (ob T \<cdot>\<cdot> (Space.dom i)) \<in> el (ob R \<cdot>\<cdot> (Space.dom i))"
      by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top PrealgebraMap.select_convs(1) R_def \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation(3) powerset_def relation_neutral_def relation_ob_value) 
    moreover have "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.dom i \<cdot> x = el (ob T \<cdot>\<cdot> (Space.dom i))" using
        relation_neutral_nat_value_app [where ?T=T and ?A="Inclusion.dom i"]  calculation
      by (metis (no_types, lifting) Prealgebra.valid_welldefined PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(3) Tuple.valid_welldefined UNIV_unit UNIV_witness \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_def relation_neutral_dom singletonD terminal_value)
    moreover have "PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.cod i \<cdot> x = el (ob T \<cdot>\<cdot> (Space.cod i))"
      by (metis (no_types, lifting) Prealgebra.valid_welldefined PrealgebraMap.select_convs(1) Tuple.valid_welldefined \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> \<open>i \<in> Space.inclusions (map_space \<epsilon>)\<close> \<open>x \<in> el (ob one \<cdot>\<cdot> Inclusion.cod i)\<close> one_def relation_neutral_def relation_neutral_dom relation_neutral_nat_value_app valid_inclusion_cod) 
    moreover have "(ar R \<cdot>\<cdot> i) \<cdot>  el (ob T \<cdot>\<cdot> (Space.cod i)) =  el (ob T \<cdot>\<cdot>
 (Space.dom i))" using relation_prealgebra_def [where ?T=T] R_def direct_image_def [where ?f="
 ((\<cdot>) (ar T \<cdot>\<cdot> i))" and ?X="el (ob T \<cdot>\<cdot> (Space.dom i))" and ?Y="el (ob T \<cdot>\<cdot> (Space.dom i))"]
      oops


lemma valid_relation_neutral :
  fixes T :: "('A,'a) TupleSystem"
  assumes "valid T"
  defines "\<epsilon> \<equiv> relation_neutral T"
  shows "Prealgebra.valid_map \<epsilon>"
proof (rule valid_mapI, auto)
  show "Space.valid (map_space \<epsilon>)" unfolding relation_neutral_def
    by (smt (verit, best) Prealgebra.valid_space PrealgebraMap.select_convs(1) Tuple.valid_welldefined \<epsilon>_def assms(1) relation_neutral_def)
  show "Function.valid_map (PrealgebraMap.nat \<epsilon>)"
    by (smt (verit) Function.dom_def Function.select_convs(1) Function.select_convs(2) Function.valid_map_def PrealgebraMap.select_convs(2) UNIV_I \<epsilon>_def fst_conv mem_Collect_eq relation_neutral_def snd_conv)
  show "Prealgebra.valid (PrealgebraMap.dom \<epsilon>)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(3) \<epsilon>_def \<open>Space.valid (map_space \<epsilon>)\<close> relation_neutral_def terminal_valid)
  show "Prealgebra.valid (PrealgebraMap.cod \<epsilon>)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(4) \<epsilon>_def assms(1) relation_neutral_def valid_relation_prealgebra)
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A)" using
      Poset.const_valid
    using \<epsilon>_def assms(1) relation_neutral_nat_valid by blast
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = ob
 (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> A"
    using \<epsilon>_def assms(1) relation_neutral_dom by blast
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> A) = ob
 (PrealgebraMap.cod \<epsilon>) \<cdot>\<cdot> A"
    using \<epsilon>_def assms(1) relation_neutral_cod by blast 
  show "\<And>i. i \<in> Space.inclusions (map_space \<epsilon>) \<Longrightarrow>
         PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.dom i \<odot> ar (PrealgebraMap.dom \<epsilon>) \<cdot>\<cdot> i =
         ar (PrealgebraMap.cod \<epsilon>) \<cdot>\<cdot> i \<odot> PrealgebraMap.nat \<epsilon> \<cdot>\<cdot> Inclusion.cod i"
    oops
end
