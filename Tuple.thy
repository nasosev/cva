theory Tuple
  imports Main Presheaf Prealgebra OVA
begin


(* TODO Change this to datatype to prevent accidentally using the wrong valid method *)
type_synonym ('A, 'a) TupleSystem = "('A, 'a) Presheaf"


abbreviation (input) space :: "('A,'a) TupleSystem \<Rightarrow> 'A Space" where
"space T \<equiv> Presheaf.space T"

definition valid :: "('A, 'a) TupleSystem \<Rightarrow> bool" where
  "valid T \<equiv>
    let
      S = space T;
      T0 = Presheaf.ob T;
      T1 = Presheaf.ar T;

      welldefined = Presheaf.valid T;
      flasque = (\<forall>i. i \<in> Space.inclusions S \<longrightarrow> Function.is_surjective (T1 \<cdot> i));
      binary_gluing = (\<forall> A B a b i_A j_A i_B j_B . A \<in> Space.opens S \<longrightarrow> B \<in> Space.opens S \<longrightarrow> a \<in> (T0 \<cdot> A)
        \<longrightarrow> b \<in> (T0 \<cdot> B)
         \<longrightarrow> i_A = Space.make_inclusion S (A \<inter> B) A
           \<longrightarrow> j_A = Space.make_inclusion S A (A \<union> B)
         \<longrightarrow> i_B = Space.make_inclusion S (A \<inter> B) B
           \<longrightarrow> j_B = Space.make_inclusion S B (A \<union> B)
            \<longrightarrow> (T1 \<cdot> i_A) \<cdot> a = (T1 \<cdot> i_B) \<cdot> b
            \<longrightarrow> (\<exists> c . c \<in> (T0 \<cdot> (A \<union> B)) \<and> (T1 \<cdot> j_A) \<cdot> c = a \<and> (T1 \<cdot> j_B) \<cdot> c = b))
    in
    welldefined \<and> flasque \<and> binary_gluing"

definition relation_prealgebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) Prealgebra" where
  "relation_prealgebra T \<equiv>
    let
      S = space T;
      T0 = Presheaf.ob T;
      T1 = Presheaf.ar T;
      R0 = \<lparr> Function.cod = UNIV, func = {(A, Poset.powerset (T0 \<cdot> A)) | A . A \<in> Space.opens S} \<rparr>;
      R1 = \<lparr> Function.cod = UNIV, func = {(i, Poset.direct_image (T1 \<cdot> i)) | i . i \<in> Space.inclusions S} \<rparr>
    in
    \<lparr>Prealgebra.space = S, ob = R0, ar = R1\<rparr>"

definition relation_neutral :: "('A, 'a) TupleSystem \<Rightarrow> ('A, unit, 'a set) PrealgebraMap" where
  "relation_neutral T \<equiv>
    let
      map_space = space T;
      dom = Prealgebra.terminal map_space;
      cod = relation_prealgebra T;
      nat = \<lparr> 
              Function.cod = UNIV , 
              func = {(A, Poset.const (Prealgebra.ob dom \<cdot> A) (Prealgebra.ob cod \<cdot> A)  (Presheaf.ob T \<cdot> A)) | A . A \<in> Space.opens map_space} 
            \<rparr>
    in
      \<lparr> PrealgebraMap.map_space = map_space, nat = nat, dom = dom, cod = cod \<rparr>"

definition relation_comb :: "('A, 'a) TupleSystem \<Rightarrow> (('A, 'a set) Valuation) Semigroup" where
  "relation_comb T \<equiv> 
    let
      poset = gc (relation_prealgebra T);
      mult = \<lparr> 
              PosetMap.dom = undefined, 
              cod = undefined, 
              func = undefined 
             \<rparr>
    in
      \<lparr> Semigroup.poset = poset, Semigroup.mult = mult \<rparr>"

definition relation_algebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) OVA" where
"relation_algebra T \<equiv>
  let
    \<Psi> = relation_prealgebra T

  in
  undefined"
text \<open> ----------------- LEMMAS ----------------- \<close>

lemma valid_welldefined :  "valid T \<Longrightarrow> Presheaf.valid T" unfolding valid_def
  by (simp add: Let_def)

lemma valid_flasque : "valid T \<Longrightarrow> i \<in> Space.inclusions (Presheaf.space T) \<Longrightarrow> Function.is_surjective (Presheaf.ar T \<cdot> i)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_binary_gluing : "valid T \<Longrightarrow>  A \<in> Space.opens (Presheaf.space T) \<Longrightarrow> B \<in> Space.opens (Presheaf.space T) \<Longrightarrow> a \<in> Presheaf.ob T \<cdot> A
        \<Longrightarrow> b \<in> Presheaf.ob T \<cdot> B
         \<Longrightarrow> i_A = Space.make_inclusion (Presheaf.space T) (A \<inter> B) A
           \<Longrightarrow> j_A = Space.make_inclusion (Presheaf.space T) A (A \<union> B)
         \<Longrightarrow> i_B = Space.make_inclusion (Presheaf.space T) (A \<inter> B) B
           \<Longrightarrow> j_B = Space.make_inclusion (Presheaf.space T) B (A \<union> B)
            \<Longrightarrow> (Presheaf.ar T \<cdot> i_A) \<cdot> a = (Presheaf.ar T \<cdot> i_B) \<cdot> b
            \<Longrightarrow> (\<exists> c . c \<in> (Presheaf.ob T \<cdot> (A \<union> B)) \<and> (Presheaf.ar T \<cdot> j_A) \<cdot> c = a \<and> (Presheaf.ar T \<cdot> j_B) \<cdot> c = b)"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_relation_space : "valid T \<Longrightarrow> Prealgebra.space (relation_prealgebra T) = Presheaf.space T"
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
 (\<And> A . A \<in> Space.opens (Presheaf.space T) \<Longrightarrow> X = (Presheaf.ob T) \<cdot> A \<Longrightarrow> R0 \<cdot> A = Poset.powerset X)"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I fst_conv mem_Collect_eq snd_conv)

lemma relation_ob_value_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
 (\<And> A .A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> Poset.valid (R0 \<cdot> A))"
  using relation_ob_value [where ?T=T]
  by (metis powerset_valid valid_relation_space)

lemma relation_ar_value : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow>
 (\<And> i.  i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> X = (Presheaf.ob T) \<cdot> (Space.cod i) \<Longrightarrow> Y = (Presheaf.ob T) \<cdot> (Space.dom i)
\<Longrightarrow> f= Presheaf.ar T \<cdot> i \<Longrightarrow> R1 \<cdot> i = Poset.direct_image f)"
  unfolding relation_prealgebra_def [where ?T=T]
  by (smt (verit) Function.fun_app Function.select_convs(2) Function.valid_map_def Prealgebra.Prealgebra.select_convs(3) \<open>relation_prealgebra T \<equiv> let S = Presheaf.space T; T0 = Presheaf.ob T; T1 = Presheaf.ar T; R0 = \<lparr>Function.cod = UNIV, func = {(A, powerset (T0 \<cdot> A)) |A. A \<in> Space.opens S}\<rparr>; R1 = \<lparr>Function.cod = UNIV, func = {(i, direct_image (T1 \<cdot> i)) |i. i \<in> Space.inclusions S}\<rparr> in \<lparr>Prealgebra.space = S, ob = R0, ar = R1\<rparr>\<close> mem_Collect_eq relation_ar_valid valid_relation_space) 

lemma relation_ar_value_valid : "valid T \<Longrightarrow>  R = relation_prealgebra T \<Longrightarrow>  R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow>
  (\<And> i . i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> Poset.valid_map (R1 \<cdot> i))"
  by (metis Presheaf.valid_ar Tuple.valid_welldefined direct_image_valid relation_ar_value valid_relation_space)

lemma relation_ar_dom : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
R1 = Prealgebra.ar R \<Longrightarrow> i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.dom (R1 \<cdot> i) = R0 \<cdot> Space.cod i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Presheaf.res_dom Tuple.valid_welldefined UNIV_I direct_image_dom fst_conv inclusions_def mem_Collect_eq snd_conv valid_inclusion_def)

lemma relation_ar_cod : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
R1 = Prealgebra.ar R \<Longrightarrow> i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.cod (R1 \<cdot> i) = R0 \<cdot> Space.dom i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Pair_inject Presheaf.res_cod Tuple.valid_welldefined UNIV_I direct_image_cod inclusions_def mem_Collect_eq valid_inclusion_def)

lemma relation_ar_ident :
  fixes T :: "('A,'a) TupleSystem" and A :: "'A Open"
  defines "R \<equiv> relation_prealgebra T"
assumes "valid T"
  assumes "A \<in> Space.opens (Prealgebra.space R)"
  shows "(ar R) \<cdot> Space.ident (Prealgebra.space R) A = Poset.ident ((ob R) \<cdot> A)"
proof -
  define "i" where "i = Space.ident (Prealgebra.space R) A"
  define "f" where "f = Presheaf.ar T"
  define "Rf" where "Rf = (ar R) \<cdot> i"
  moreover have c: "Space.cod i = A"
    by (simp add: Space.ident_def i_def)
  moreover have "Space.dom i = A"
    by (simp add: Space.ident_def i_def)
  moreover have "\<forall> u . u \<in> Presheaf.ob T \<cdot> A \<longrightarrow> (f \<cdot> i) \<cdot> u = u"
    by (metis Function.ident_app Presheaf.ident_app R_def Tuple.valid_welldefined assms(2) assms(3) f_def i_def valid_relation_space) 
  moreover have "(Prealgebra.ob R) \<cdot> A = powerset ((Presheaf.ob T) \<cdot> A)" using  relation_prealgebra_def
      [where ?T=T]
    using R_def assms(2) assms(3) relation_ob_value valid_relation_space by fastforce 
  moreover have "i \<in> Space.inclusions (Prealgebra.space R)" using R_def valid_relation_space [where
        ?T=T] Space.valid_ident_inclusion  [where ?T="(Presheaf.space T)" and ?A=A]
    using Presheaf.valid_space Tuple.valid_welldefined assms(2) assms(3) i_def by auto
  moreover have "Poset.dom ((ar R) \<cdot> i) = (ob R) \<cdot> (Space.cod i)"
    using  assms(3)
    using R_def assms(2) calculation(6) relation_ar_dom by blast
  moreover have "Rf = Poset.direct_image (f \<cdot> i)" using Rf_def  relation_prealgebra_def [where ?T=T]
    using R_def assms(2) calculation(6) f_def relation_ar_value by blast
    
  moreover have "Poset.dom Rf = (ob R) \<cdot> A"
    using Rf_def c calculation(7) by blast  
  moreover have "Poset.cod Rf = (ob R) \<cdot> A"
    using R_def Rf_def assms(2) calculation(3) calculation(6) relation_ar_cod by blast  
  moreover have "(Presheaf.ar T) \<cdot> i = Function.ident ((Presheaf.ob T) \<cdot> A)"
    by (metis Presheaf.valid_identity R_def Tuple.valid_welldefined assms(2) assms(3) i_def valid_relation_space) 
    moreover have "(ar R) \<cdot> i = Poset.ident ((ob R) \<cdot> A)"
      by (metis Rf_def calculation(11) calculation(5) calculation(8) direct_image_ident f_def) 
    ultimately show ?thesis using R_def  relation_prealgebra_def [where ?T=T] i_def
      by metis
  qed

lemma relation_ar_trans :
  fixes T :: "('A,'a) TupleSystem" and i j :: "'A Inclusion"
  defines "R \<equiv> relation_prealgebra T"
  assumes T_valid: "valid T"
  and i_inc : "i \<in> Space.inclusions (Prealgebra.space R)"
  and j_inc :"j \<in> Space.inclusions (Prealgebra.space R)"
  and endpoints : "Space.dom j = Space.cod i"
shows "ar R \<cdot> Space.compose j i = ar R \<cdot> i \<diamondop> ar R \<cdot> j"
proof -
  define "f" where "f = Presheaf.ar T"
  have "i \<in> Space.inclusions (space T)" using valid_relation_space [where ?T=T] R_def i_inc T_valid
    by simp
  moreover have "ar R \<cdot> i = direct_image (f \<cdot> i)" using R_def relation_prealgebra_def [where ?T=T] f_def
      Function.app_def
    using T_valid i_inc relation_ar_value by blast
  moreover have "ar R \<cdot> j = direct_image (f \<cdot> j)" 
    using R_def T_valid f_def j_inc relation_ar_value by blast
  define "ji" where "ji = (Space.compose j i)"
    moreover have "ar R \<cdot> ji = direct_image (f \<cdot> ji)"
      by (smt (z3) Space.select_convs(1) R_def Space.compose_def Space.compose_valid T_valid endpoints f_def i_inc inclusions_def j_inc ji_def mem_Collect_eq relation_ar_value)
    moreover have "\<forall> x . x \<in> Presheaf.ob T \<cdot> (Space.cod j) \<longrightarrow> (f \<cdot> ji) \<cdot> x = (f \<cdot> i \<bullet> f \<cdot> j) \<cdot> x"
      by (metis Presheaf.valid_composition R_def T_valid Tuple.valid_welldefined calculation(1) endpoints f_def j_inc ji_def valid_relation_space)
      
    moreover have "ar R \<cdot> Space.compose j i = ar R \<cdot> i \<diamondop> ar R \<cdot> j"
      by (metis Presheaf.res_cod Presheaf.res_dom Presheaf.valid_ar Presheaf.valid_composition R_def T_valid Tuple.valid_welldefined \<open>Prealgebra.ar R \<cdot> j = direct_image (f \<cdot> j)\<close> calculation(1) calculation(2) calculation(4) direct_image_trans endpoints f_def j_inc ji_def valid_relation_space) 
    ultimately show ?thesis
      by meson
  qed

lemma valid_relation_prealgebra :
  fixes T :: "('A,'a) TupleSystem"
  assumes "valid T"
  defines "R \<equiv> relation_prealgebra T"
  shows "Prealgebra.valid R"
proof (intro Prealgebra.validI, auto)
  show "Space.valid (Prealgebra.space R)"
    by (metis Presheaf.valid_space R_def Tuple.valid_welldefined assms(1) valid_relation_space) 
  show "Function.valid_map (ob R)"
    using R_def assms(1) relation_ob_valid by auto
  show "Function.valid_map (ar R)"
    using R_def assms(1) relation_ar_valid by auto
  show "\<And>A. A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> Poset.valid (ob R \<cdot> A)"
    by (metis R_def assms(1) relation_ob_value_valid valid_relation_space)
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> Poset.valid_map (ar R \<cdot> i)"
    by (metis R_def assms(1) relation_ar_value_valid valid_relation_space)
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.dom (ar R \<cdot> i) = ob R \<cdot> Space.cod
 i"
    using R_def assms(1) relation_ar_dom by blast
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.cod (ar R \<cdot> i) = ob R \<cdot> Space.dom
 i"
    using R_def assms(1) relation_ar_cod by blast
  show "\<And>A. A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> ar R \<cdot> Space.ident (Prealgebra.space R) A =
 Poset.ident (ob R \<cdot> A)"
    using R_def assms(1) relation_ar_ident by blast
  show "\<And>i j. j \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow>
           i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow>
           Space.dom j = Space.cod i \<Longrightarrow> ar R \<cdot> Space.compose j i = ar R \<cdot> i \<diamondop> ar R \<cdot> j"
    by (simp add: R_def assms(1) relation_ar_trans)
qed

lemma valid_relation_neutral_space : "valid T \<Longrightarrow> map_space (relation_neutral T) = space T"
  by (smt (verit, best) PrealgebraMap.select_convs(1) relation_neutral_def) 

lemma relation_neutral_nat_valid : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)"
proof-
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "dom" where "dom = Prealgebra.terminal (map_space \<epsilon>)"
  define "cod" where "cod = relation_prealgebra T"

  have "PrealgebraMap.nat \<epsilon> \<cdot> A = Poset.const (Prealgebra.ob dom \<cdot> A) (Prealgebra.ob cod \<cdot> A) (Presheaf.ob
 T \<cdot> A)" using relation_neutral_def [where ?T=T]
    by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) UNIV_I \<open>A \<in> Space.opens (PrealgebraMap.map_space \<epsilon>)\<close> \<open>\<epsilon> = relation_neutral T\<close> fst_conv local.cod_def local.dom_def mem_Collect_eq snd_conv) 
  moreover have "Poset.valid (Prealgebra.ob dom \<cdot> A)"
    by (simp add: \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> discrete_valid local.dom_def terminal_def)
  moreover have "Poset.valid (Prealgebra.ob cod \<cdot> A)"  using valid_relation_prealgebra [where ?T=T]
    by (metis (no_types, lifting) PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> local.cod_def relation_neutral_def valid_relation_space valid_ob)
  show "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)" using Poset.const_valid 
    by (metis (no_types, lifting) Poset.Poset.simps(1) Pow_top PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Poset.valid (ob cod \<cdot> A)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation(1) calculation(2) local.cod_def powerset_def relation_neutral_def relation_ob_value)
qed

lemma relation_neutral_nat_value : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> \<epsilon>A = Presheaf.ob T \<cdot> A \<Longrightarrow>
 PrealgebraMap.nat \<epsilon> \<cdot> A =  Poset.const Poset.discrete (ob R \<cdot> A) \<epsilon>A"
  unfolding relation_neutral_def
  apply (simp_all add : Let_def)
  by (simp add: Function.dom_def Function.valid_map_def terminal_def)

lemma relation_neutral_is_element :
  fixes T :: "('A, 'a) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" 
  and A_open: "A \<in> Space.opens (space T)" 
  defines "R \<equiv> relation_prealgebra T"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (relation_neutral T) \<cdot> A) \<star> ()"
shows "\<epsilon>A \<in> el (ob R \<cdot> A)"
proof -
  have "A \<in> Space.opens (map_space ((relation_neutral T)))"
    by (simp add: A_open T_valid valid_relation_neutral_space) 
  moreover have "A \<in> Space.opens (Prealgebra.space R)"
    by (simp add: A_open R_def T_valid valid_relation_space) 
  moreover have "Poset.cod (nat (relation_neutral T) \<cdot> A) = ob R \<cdot> A" 
    using relation_neutral_def [where ?T=T] Poset.const_def              
    by (smt (verit) A_open Poset.Poset.select_convs(1) Poset.const_cod Pow_top PrealgebraMap.select_convs(1) R_def T_valid powerset_def relation_neutral_nat_value relation_ob_value)
  moreover have "Poset.dom (nat (relation_neutral T) \<cdot> A) = Poset.discrete" using relation_neutral_def [where
      ?T=T] Poset.const_def
    by (smt (verit, best) A_open Poset.Poset.select_convs(1) Poset.const_dom Pow_top PrealgebraMap.select_convs(1) T_valid powerset_def relation_neutral_nat_value relation_ob_value) 
  moreover have "() \<in> el (Poset.dom (nat (relation_neutral T) \<cdot> A) )" using relation_neutral_def [where
      ?T=T]
    by (metis (mono_tags, lifting) Poset.Poset.select_convs(1) UNIV_witness calculation(4) discrete_def old.unit.exhaust)
  ultimately show ?thesis unfolding R_def \<epsilon>A_def relation_neutral_nat_value [where ?T=T]
    by (metis Poset.fun_app2 T_valid relation_neutral_nat_valid) 
qed
    
lemma relation_neutral_nat_value_app :
  fixes T :: "('A, 'a) TupleSystem" and A :: "'A Open" and x :: "unit"
  assumes T_valid: "valid T" 
  and A_open: "A \<in> Space.opens (space T)" 
  and "x \<in> el (Poset.dom (PrealgebraMap.nat (relation_neutral T) \<cdot> A ))"
  defines "R \<equiv> relation_prealgebra T"
  and "\<epsilon>A \<equiv> Presheaf.ob T \<cdot> A"
shows "(PrealgebraMap.nat (relation_neutral T) \<cdot> A) \<star> x =  \<epsilon>A"
proof - 
    have "x = ()"
      by simp 
    moreover have "Space.opens (map_space  (relation_neutral T)) = Space.opens (space T)"
      by (metis (mono_tags, lifting) PrealgebraMap.select_convs(1) relation_neutral_def)
    moreover have "\<epsilon>A \<in> el (ob R \<cdot> A)" using \<epsilon>A_def R_def relation_prealgebra_def [where ?T=T]
        relation_neutral_def [where ?T=T]
      by (metis (no_types, lifting) A_open Poset.Poset.select_convs(1) Pow_top T_valid powerset_def relation_ob_value) 
    moreover have "PrealgebraMap.nat (relation_neutral T) \<cdot> A = Poset.const Poset.discrete (ob R \<cdot>
      A) \<epsilon>A"
      using A_open R_def T_valid \<epsilon>A_def calculation(2) relation_neutral_nat_value by blast 
    ultimately show "(PrealgebraMap.nat (relation_neutral T) \<cdot> A) \<star> x =  \<epsilon>A" using Poset.const_app [where
 ?P="Poset.discrete" and ?Q="(ob R \<cdot> A)" and ?q=\<epsilon>A and ?p=x]
      by (metis A_open Poset.const_dom R_def T_valid assms(3) discrete_valid relation_ob_value_valid valid_relation_space) 
  qed

lemma relation_neutral_dom : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> A) = ob (PrealgebraMap.dom \<epsilon>) \<cdot> A"
proof -
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "R" where "R = relation_prealgebra T"
  have "dom \<epsilon> = Prealgebra.terminal (space T)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(3) \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_def)
  moreover have "ob (dom \<epsilon>) \<cdot> A = Poset.discrete"
    by (metis (no_types, lifting) Function.const_app Prealgebra.Prealgebra.select_convs(2) PrealgebraMap.select_convs(1) UNIV_I \<open>A \<in> Space.opens (PrealgebraMap.map_space \<epsilon>)\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation relation_neutral_def terminal_def) 
  moreover have "PrealgebraMap.nat \<epsilon> \<cdot> A = Poset.const discrete (ob R \<cdot> A) (Presheaf.ob T \<cdot> A)"
    using R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_nat_value by blast
  moreover have "Presheaf.ob T \<cdot> A \<in> el (ob R \<cdot> A)"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top PrealgebraMap.select_convs(1) R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> powerset_def relation_neutral_def relation_ob_value)
  moreover have "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> A) = Poset.discrete"
    by (simp add: Poset.const_def calculation(3) calculation(4))  
    ultimately show "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> A) = ob
 (PrealgebraMap.dom \<epsilon>) \<cdot> A"
      by presburger
  qed

lemma relation_neutral_cod : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>)
\<Longrightarrow> PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> A) = ob (PrealgebraMap.cod \<epsilon>) \<cdot> A"
proof -
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "R" where "R = relation_prealgebra T"
  have "cod \<epsilon> = R"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(4) R_def \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_def) 
  moreover have "ob (cod \<epsilon>) \<cdot> A = ob R \<cdot> A"
    using calculation by fastforce
  moreover have "PrealgebraMap.nat \<epsilon> \<cdot> A = Poset.const discrete (ob R \<cdot> A) (Presheaf.ob T \<cdot> A)"
    using R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_nat_value by blast
  moreover have "(Presheaf.ob T \<cdot> A) \<in> el (ob R \<cdot> A)"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top PrealgebraMap.select_convs(1) R_def \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> powerset_def relation_neutral_def relation_ob_value)
  moreover have "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> A) =  ob R \<cdot> A"
    by (simp add: Poset.const_def calculation(3) calculation(4)) 
    ultimately show "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> A) = ob (PrealgebraMap.cod \<epsilon>) \<cdot> A"
      by meson 
  qed

lemma relation_neutral_top : 
  fixes T :: "('A, 'a) TupleSystem" and A :: "'A Open"
  assumes T_valid: "valid T" and A_open: "A \<in> Space.opens (space T)"
  defines "R \<equiv> relation_prealgebra T"
    and "RA \<equiv> (PrealgebraMap.nat (relation_neutral T) \<cdot> A) \<star> ()"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (relation_neutral T) \<cdot> A) \<star> ()"
shows "Poset.is_top (ob R \<cdot> A) \<epsilon>A"
proof safe
  show "\<epsilon>A \<in> el (Prealgebra.ob R \<cdot> A)" using \<epsilon>A_def R_def R_def relation_prealgebra_def [where ?T=T]
      relation_neutral_nat_value_app [where ?T=T]
    using A_open T_valid relation_neutral_is_element by blast
next
  fix p
  assume "p \<in> el (Prealgebra.ob R \<cdot> A)"
  have "p \<subseteq> Presheaf.ob T \<cdot> A"
    by (metis (no_types, lifting) A_open Poset.Poset.select_convs(1) PowD R_def T_valid \<open>p \<in> el (Prealgebra.ob R \<cdot> A)\<close> powerset_def relation_ob_value) 
  moreover have "Prealgebra.ob R \<cdot> A = powerset (Presheaf.ob T \<cdot> A)"
    using A_open R_def T_valid relation_ob_value by blast 
  moreover have "\<epsilon>A = Presheaf.ob T \<cdot> A" using \<epsilon>A_def relation_neutral_nat_value_app [where ?T=T and
        ?A=A and ?x="()"]
    by (metis (mono_tags, lifting) A_open Poset.Poset.select_convs(1) Poset.const_dom Pow_top R_def T_valid UNIV_witness calculation(2) discrete_def old.unit.exhaust powerset_def relation_neutral_nat_value valid_relation_neutral_space) 
  moreover have "p \<subseteq> \<epsilon>A" using calculation
    by blast 
  show "le (Prealgebra.ob R \<cdot> A) p \<epsilon>A" using R_def relation_prealgebra_def [where ?T=T]
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) Pow_iff calculation(1) calculation(2) calculation(3) case_prodI equalityE mem_Collect_eq powerset_def)
qed

lemma relation_neutral_stable : 
  fixes T :: "('A, 'a) TupleSystem" and i :: "'A Inclusion"
  assumes T_valid: "valid T" and i_inc: "i \<in> Space.inclusions (space T)"
  defines "R \<equiv> relation_prealgebra T"
  and "\<epsilon>A \<equiv> (PrealgebraMap.nat (relation_neutral T) \<cdot> Space.cod i) \<star> ()"
  and "\<epsilon>B \<equiv> (PrealgebraMap.nat (relation_neutral T) \<cdot> Space.dom i) \<star> ()"
shows "(ar R \<cdot> i) \<star> \<epsilon>A = \<epsilon>B"
proof -
  define "Ti" where "Ti = Presheaf.ar T \<cdot> i"
  define "Ri" where "Ri = ar R \<cdot> i"

  have "Function.is_surjective Ti"
    using T_valid i_inc valid_flasque Ti_def by blast  
  moreover have "Ri = direct_image Ti"
    by (metis R_def T_valid Ti_def i_inc relation_ar_value valid_relation_space Ri_def) 
  moreover have "Poset.is_surjective Ri" using Poset.surj_imp_direct_image_surj [where
        ?f=Ti]
    by (metis Presheaf.valid_ar T_valid Ti_def Tuple.valid_welldefined calculation(1) calculation(2) i_inc) 
  moreover have "\<epsilon>B \<in> el (Poset.cod Ri)" using \<epsilon>B_def Ri_def R_def relation_prealgebra_def [where
        ?T=T] relation_neutral_def [where ?T=T]
    by (metis (mono_tags, lifting) Poset.fun_app2 PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(3) PrealgebraMap.select_convs(4) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_unit UNIV_witness i_inc old.unit.exhaust relation_ar_cod relation_neutral_cod relation_neutral_dom relation_neutral_nat_valid valid_relation_space terminal_value valid_inclusion_dom)
  moreover have "\<exists> x . x \<in> el (Poset.dom Ri) \<and> Ri \<star> x = \<epsilon>B"
    using calculation(3) calculation(4) by blast 
  obtain "x" where "x \<in> el (Poset.dom Ri) \<and> Ri \<star> x = \<epsilon>B"
    using \<open>\<exists>x. x \<in> el (PosetMap.dom Ri) \<and> Ri \<star> x = \<epsilon>B\<close> by blast 
  moreover have "le (PosetMap.dom Ri) x \<epsilon>A"
    by (metis Presheaf.valid_space R_def Ri_def T_valid Tuple.valid_welldefined assms(4) calculation(5) i_inc relation_ar_dom relation_neutral_top valid_inclusion_cod valid_relation_space) 
  ultimately show ?thesis
    by (smt (verit) Poset.valid_cod Poset.valid_def Prealgebra.res_cod Prealgebra.image Prealgebra.valid_dom Presheaf.valid_ar Presheaf.valid_space R_def Ri_def T_valid Ti_def Tuple.valid_welldefined \<epsilon>A_def \<epsilon>B_def direct_image_mono direct_image_valid i_inc relation_neutral_top valid_inclusion_cod valid_inclusion_dom valid_relation_prealgebra valid_relation_space)
qed

lemma relation_neutral_natural : 
  fixes T :: "('A, 'a) TupleSystem" and i :: "'A Inclusion"
  assumes T_valid: "valid T" and i_inc: "i \<in> Space.inclusions (space T)"
  defines "\<epsilon> \<equiv> relation_neutral T "
  shows "PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> ar (PrealgebraMap.dom \<epsilon>) \<cdot> i =
         ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i"
proof (rule Poset.fun_ext)
  show "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>)
 \<cdot> i)" 
  proof -
    have "Poset.valid_map (Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i)"
      by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.valid_ar PrealgebraMap.select_convs(3) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_def terminal_def terminal_valid) 
    moreover have "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i)"
      by (metis Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_nat_valid valid_inclusion_dom valid_relation_neutral_space)  
    ultimately show "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar
 (PrealgebraMap.dom \<epsilon>) \<cdot> i)"
      by (metis (no_types, lifting) Poset.compose_valid Prealgebra.Prealgebra.select_convs(1) Prealgebra.res_cod PrealgebraMap.select_convs(3) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_def relation_neutral_dom terminal_def terminal_valid valid_inclusion_dom valid_relation_neutral_space)
  qed
next
  show "Poset.valid_map (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot>
 Space.cod i)" 
  proof -
    have "Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i)"
      by (metis Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_nat_valid valid_inclusion_cod valid_relation_neutral_space) 
    moreover have "Poset.valid_map (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i)"
      by (metis (no_types, lifting) Prealgebra.valid_ar PrealgebraMap.select_convs(4) T_valid \<epsilon>_def i_inc relation_neutral_def valid_relation_prealgebra valid_relation_space) 
    show "Poset.valid_map (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot>
 Space.cod i)"
      by (metis (no_types, lifting) Poset.compose_valid Prealgebra.valid_dom PrealgebraMap.select_convs(4) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def \<open>Poset.valid_map (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i)\<close> calculation i_inc relation_neutral_cod relation_neutral_def valid_inclusion_cod valid_relation_neutral_space valid_relation_prealgebra valid_relation_space) 
  qed
next 
  show "PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i) =
    PosetMap.dom (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i)"
    by (metis (no_types, lifting) Poset.dom_compose Prealgebra.Prealgebra.select_convs(1) Prealgebra.res_cod Prealgebra.valid_ar Prealgebra.valid_dom PrealgebraMap.select_convs(3) PrealgebraMap.select_convs(4) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_cod relation_neutral_def relation_neutral_dom relation_neutral_nat_valid terminal_def terminal_valid valid_inclusion_cod valid_inclusion_dom valid_relation_neutral_space valid_relation_prealgebra valid_relation_space) 
next 
  show "PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i) =
    PosetMap.cod (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i)"
    by (metis (no_types, lifting) Poset.compose_def PosetMap.select_convs(2) Prealgebra.Prealgebra.select_convs(1) Prealgebra.res_cod Prealgebra.valid_dom PrealgebraMap.select_convs(3) PrealgebraMap.select_convs(4) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_cod relation_neutral_def relation_neutral_dom terminal_def terminal_valid valid_inclusion_cod valid_inclusion_dom valid_relation_neutral_space valid_relation_prealgebra valid_relation_space)
next 
  show "\<And>a. a \<in> el (PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i)) \<Longrightarrow>
         (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i) \<star> a =
         (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i) \<star> a " 
  proof -
    fix a
    assume "a \<in> el (PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar
 (PrealgebraMap.dom \<epsilon>) \<cdot> i))"

    define "\<epsilon>A" where "\<epsilon>A \<equiv> (PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i) \<star> ()"
  define "\<epsilon>B" where "\<epsilon>B \<equiv> (PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i) \<star> ()"
    have "\<And> x .x \<in> el (ob (PrealgebraMap.dom \<epsilon>) \<cdot> (Space.cod i)) \<Longrightarrow> x = ()"
      by simp 
    moreover have "ar (PrealgebraMap.dom \<epsilon>) \<cdot> i \<star> () = ()"
      by simp 
    moreover have "Space.dom i \<in> Space.opens (map_space \<epsilon>)"
      by (metis Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc valid_inclusion_dom valid_relation_neutral_space) 
    moreover have " Presheaf.ob T \<cdot> (Space.dom i) \<in> el (ob (relation_prealgebra T) \<cdot> (Space.dom i))"
      by (metis (no_types, lifting) Poset.Poset.select_convs(1) Pow_top T_valid \<epsilon>_def calculation(3) powerset_def relation_ob_value valid_relation_neutral_space)
    moreover have "\<epsilon>B = Presheaf.ob T \<cdot> (Space.dom i)" using
        relation_neutral_nat_value_app [where ?T=T and ?A="Space.dom i"]  calculation \<epsilon>B_def
      by (metis (no_types, lifting) PrealgebraMap.select_convs(3) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_I UNIV_unit \<epsilon>_def relation_neutral_def relation_neutral_dom terminal_value valid_relation_neutral_space) 
    moreover have "\<epsilon>A = Presheaf.ob T \<cdot> (Space.cod i)" using \<epsilon>A_def
      by (metis (mono_tags, lifting) PrealgebraMap.select_convs(3) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_unit UNIV_witness \<epsilon>_def i_inc old.unit.exhaust relation_neutral_def relation_neutral_dom relation_neutral_nat_value_app terminal_value valid_inclusion_cod valid_relation_neutral_space)
    moreover have "(ar (relation_prealgebra T) \<cdot> i) \<star>  Presheaf.ob T \<cdot> (Space.cod i) = Presheaf.ob T \<cdot> (Space.dom i)"
      using relation_prealgebra_def [where ?T=T]  direct_image_def [where ?f="
  (Presheaf.ar T \<cdot> i)" ]
      by (metis (no_types, lifting) T_valid \<epsilon>A_def \<epsilon>B_def \<epsilon>_def calculation(5) calculation(6) i_inc relation_neutral_stable) 
    moreover have "(Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i) \<star> a
= \<epsilon>B"
      by (smt (verit) Poset.compose_app_assoc PrealgebraMap.select_convs(3) PrealgebraMap.select_convs(4) Presheaf.valid_space T_valid Tuple.valid_welldefined UNIV_I UNIV_unit \<epsilon>A_def \<epsilon>_def calculation(5) calculation(6) calculation(7) i_inc old.unit.exhaust relation_ar_dom relation_ar_value_valid relation_neutral_cod relation_neutral_def relation_neutral_dom relation_neutral_nat_valid terminal_value valid_inclusion_cod valid_relation_neutral_space valid_relation_space)
    moreover have "(Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i) \<star>
 a = ()"
      by auto 
moreover have "(PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i) \<star> () = \<epsilon>B"
  by (simp add: \<epsilon>B_def) 
 define "g" where "g = PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i" 
  define "f" where "f = Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i"
   moreover have "Poset.valid_map g"
    using T_valid \<epsilon>_def calculation(3) relation_neutral_nat_valid g_def by blast 
  moreover have "Poset.valid_map f"
    by (metis (no_types, lifting) f_def Prealgebra.Prealgebra.select_convs(1) Prealgebra.valid_ar PrealgebraMap.select_convs(3) Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_def terminal_def terminal_valid)  
  moreover have "PrealgebraMap.dom \<epsilon> = Prealgebra.terminal (space T)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(3) \<epsilon>_def relation_neutral_def)   
  moreover have "Poset.cod f = Poset.discrete"     using calculation terminal_def [where ?T="space
 T"]
    by (metis Poset.const_dom Prealgebra.Prealgebra.select_convs(1) Prealgebra.valid_cod Presheaf.valid_space T_valid Tuple.valid_welldefined \<epsilon>_def i_inc relation_neutral_dom relation_neutral_nat_value terminal_valid)
  moreover have "Poset.dom g = Poset.cod f" using g_def f_def \<epsilon>_def relation_neutral_def [where
        ?T=T]
    by (metis (no_types, lifting) Poset.const_dom T_valid calculation(14) calculation(3) calculation(4) relation_neutral_nat_value)
  moreover have "a = ()"
    by simp  
  moreover have "a \<in> el (Poset.dom f)"
    using \<open>a \<in> el (PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> Inclusion.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i))\<close> calculation(10) calculation(11) calculation(12) calculation(15) g_def by fastforce 
  moreover have "(g \<diamondop> f) \<star> a =  g \<star> (f \<star> a)"
using calculation compose_app_assoc [where ?f="Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i" and ?g="PrealgebraMap.nat
 \<epsilon> \<cdot> Space.dom i" and ?a=a]
  using g_def by fastforce  
    ultimately show "(PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> Prealgebra.ar (PrealgebraMap.dom \<epsilon>) \<cdot> i) \<star> a =
         (Prealgebra.ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i) \<star> a"
      by (metis \<epsilon>B_def g_def)  
  qed
qed

lemma valid_relation_neutral :
  fixes T :: "('A,'a) TupleSystem"
  assumes "valid T"
  defines "\<epsilon> \<equiv> relation_neutral T"
  shows "Prealgebra.valid_map \<epsilon>"
proof (intro valid_mapI, auto)
  show "Space.valid (map_space \<epsilon>)" unfolding relation_neutral_def
    by (metis (no_types, lifting) Prealgebra.valid_space PrealgebraMap.select_convs(1) \<epsilon>_def assms(1) relation_neutral_def valid_relation_space valid_relation_prealgebra) 
  show "Function.valid_map (PrealgebraMap.nat \<epsilon>)"
    by (smt (verit) Function.dom_def Function.select_convs(1) Function.select_convs(2) Function.valid_map_def PrealgebraMap.select_convs(2) UNIV_I \<epsilon>_def fst_conv mem_Collect_eq relation_neutral_def snd_conv)
  show "Prealgebra.valid (PrealgebraMap.dom \<epsilon>)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(3) \<epsilon>_def \<open>Space.valid (map_space \<epsilon>)\<close> relation_neutral_def terminal_valid)
  show "Prealgebra.valid (PrealgebraMap.cod \<epsilon>)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(4) \<epsilon>_def assms(1) relation_neutral_def valid_relation_prealgebra)
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> Poset.valid_map (PrealgebraMap.nat \<epsilon> \<cdot> A)" using
      Poset.const_valid
    using \<epsilon>_def assms(1) relation_neutral_nat_valid by blast
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> PosetMap.dom (PrealgebraMap.nat \<epsilon> \<cdot> A) = ob
 (PrealgebraMap.dom \<epsilon>) \<cdot> A"
    using \<epsilon>_def assms(1) relation_neutral_dom by blast
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> PosetMap.cod (PrealgebraMap.nat \<epsilon> \<cdot> A) = ob
 (PrealgebraMap.cod \<epsilon>) \<cdot> A"
    using \<epsilon>_def assms(1) relation_neutral_cod by blast 
  show "\<And>i. i \<in> Space.inclusions (map_space \<epsilon>) \<Longrightarrow>
         PrealgebraMap.nat \<epsilon> \<cdot> Space.dom i \<diamondop> ar (PrealgebraMap.dom \<epsilon>) \<cdot> i =
         ar (PrealgebraMap.cod \<epsilon>) \<cdot> i \<diamondop> PrealgebraMap.nat \<epsilon> \<cdot> Space.cod i"
    by (simp add: \<epsilon>_def assms(1) relation_neutral_natural valid_relation_neutral_space)
qed
end
