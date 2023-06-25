theory Tuple
  imports Main Prealgebra OVA
begin

(* We define a tuple system as Pos-valued presheaf for convenience, but we will ignore its poset
structure *)
type_synonym ('A, 'a) TupleSystem = "('A, 'a) Prealgebra"

definition valid :: "('A, 'a) TupleSystem \<Rightarrow> bool" where
  "valid T \<equiv>
    let
      S = Prealgebra.space T;
      T0 = Prealgebra.ob T;
      T1 = Prealgebra.ar T;

      welldefined = Prealgebra.valid T;
      flasque = (\<forall>i. i \<in> Space.inclusions S \<longrightarrow> Poset.is_surjective (T1 $ i));
      binary_gluing = (\<forall> A B a b i_A j_A i_B j_B . A \<in> Space.opens S \<longrightarrow> B \<in> Space.opens S \<longrightarrow> a \<in> Poset.el (T0 $ A)
        \<longrightarrow> b \<in> Poset.el (T0 $ B)
         \<longrightarrow> i_A = Space.make_inclusion S (A \<inter> B) A
           \<longrightarrow> j_A = Space.make_inclusion S A (A \<union> B)
         \<longrightarrow> i_B = Space.make_inclusion S (A \<inter> B) B
           \<longrightarrow> j_B = Space.make_inclusion S B (A \<union> B)
            \<longrightarrow> (T1 $ i_A) $$ a = (T1 $ i_B) $$ b
            \<longrightarrow> (\<exists> c . c \<in> Poset.el (T0 $ (A \<union> B)) \<and> (T1 $ j_A) $$ c = a \<and> (T1 $ j_B) $$ c = b))
    in
    welldefined \<and> flasque \<and> binary_gluing"

definition relation_prealgebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) Prealgebra" where
  "relation_prealgebra T \<equiv>
    let
      S = Prealgebra.space T;
      T0 = Prealgebra.ob T;
      T1 = Prealgebra.ar T;
      f  = \<lambda> i u. (T1 $ i) $$ u;
      R0 = \<lparr> func = {(A, Poset.powerset (Poset.el (T0 $ A))) | A . A \<in> Space.opens S} , cod = UNIV \<rparr>;
      R1 = \<lparr> func = {(i, Poset.direct_image (f i) (Poset.el (T0 $ (Space.cod i))) (Poset.el (T0 $ (Space.dom i)))
            ) | i . i \<in> Space.inclusions S} , cod = UNIV \<rparr>
    in
    \<lparr>Prealgebra.space = S, ob = R0, ar = R1\<rparr>"

definition relation_neutral :: "('A, 'a) TupleSystem \<Rightarrow> ('A, unit, 'a set) PrealgebraMap" where
  "relation_neutral T \<equiv> 
    let
      map_space = Prealgebra.space T;
      dom = Prealgebra.terminal map_space;
      cod = relation_prealgebra T;
      nat = \<lparr> func = {(A, 
                          Poset.const (Prealgebra.ob dom $ A) (Prealgebra.ob cod $ A) (el (ob T $ A))
                      ) | A . A \<in> Space.opens map_space} , cod = UNIV \<rparr>
    in 
      \<lparr> PrealgebraMap.map_space = map_space, nat = nat, dom = dom, cod = cod \<rparr>"

definition relation_algebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) OVA" where
"relation_algebra T \<equiv> 
  let 
    \<Psi> = relation_prealgebra T
    
  in
  undefined"

abbreviation (input) space :: "('A,'a) TupleSystem \<Rightarrow> 'A Space" where
"space T \<equiv> Prealgebra.space T"

text \<open> ----------------- LEMMAS ----------------- \<close>

lemma valid_welldefined :  "valid T \<Longrightarrow> Prealgebra.valid T" unfolding valid_def
  by (simp add: Let_def)

lemma valid_flasque : "valid T \<Longrightarrow> (\<forall>i. i \<in> Space.inclusions (Prealgebra.space T) \<longrightarrow> Poset.is_surjective (Prealgebra.ar T $ i))"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_binary_gluing : "valid T \<Longrightarrow> (\<forall> A B a b i_A j_A i_B j_B . A \<in> Space.opens (Prealgebra.space T) \<longrightarrow> B \<in> Space.opens (Prealgebra.space T) \<longrightarrow> a \<in> Poset.el (Prealgebra.ob T $ A)
        \<longrightarrow> b \<in> Poset.el (Prealgebra.ob T $ B)
         \<longrightarrow> i_A = Space.make_inclusion (Prealgebra.space T) (A \<inter> B) A
           \<longrightarrow> j_A = Space.make_inclusion (Prealgebra.space T) A (A \<union> B)
         \<longrightarrow> i_B = Space.make_inclusion (Prealgebra.space T) (A \<inter> B) B
           \<longrightarrow> j_B = Space.make_inclusion (Prealgebra.space T) B (A \<union> B)
            \<longrightarrow> (Prealgebra.ar T $ i_A) $$ a = (Prealgebra.ar T $ i_B) $$ b
            \<longrightarrow> (\<exists> c . c \<in> Poset.el (Prealgebra.ob T $ (A \<union> B)) \<and> (Prealgebra.ar T $ j_A) $$ c = a \<and> (Prealgebra.ar T $ j_B) $$ c = b))"
  unfolding valid_def
  by (simp add: Let_def)

lemma relation_space_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> Prealgebra.space R = Prealgebra.space T"
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
 (\<forall> A . A \<in> Space.opens (Prealgebra.space T) \<longrightarrow> X = Poset.el ((ob T) $ A) \<longrightarrow> R0 $ A = Poset.powerset X)"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I fst_conv mem_Collect_eq snd_conv)

lemma relation_ob_value_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
 (\<forall> A . A \<in> Space.opens (Prealgebra.space R) \<longrightarrow> Poset.valid (R0 $ A))"
  using relation_ob_value [where ?T=T]
  by (metis powerset_valid relation_space_valid)

lemma relation_ar_value : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow>
 (\<forall> i . i \<in> Space.inclusions (Prealgebra.space R) \<longrightarrow> X = Poset.el ((ob T) $ (Space.cod i)) \<longrightarrow> Y = Poset.el ((ob T) $ (Space.dom i)) 
\<longrightarrow> f=(($$) (ar T $ i)) \<longrightarrow> R1 $ i = Poset.direct_image f X Y)"
  unfolding relation_prealgebra_def [where ?T=T]
  by (smt (verit) Function.fun_app Function.select_convs(1) Function.valid_map_def Prealgebra.Prealgebra.select_convs(1) Prealgebra.Prealgebra.select_convs(3) \<open>relation_prealgebra T \<equiv> let S = Prealgebra.space T; T0 = ob T; T1 = ar T; f = \<lambda>i. ($$) (T1 $ i); R0 = \<lparr>Function.func = {(A, powerset (el (T0 $ A))) |A. A \<in> Space.opens S}, cod = UNIV\<rparr>; R1 = \<lparr>Function.func = {(i, direct_image (f i) (el (T0 $ Inclusion.cod i)) (el (T0 $ Inclusion.dom i))) | i. i \<in> Space.inclusions S}, cod = UNIV\<rparr> in \<lparr>Prealgebra.space = S, ob = R0, ar = R1\<rparr>\<close> mem_Collect_eq relation_ar_valid)

lemma relation_ar_value_valid : "valid T \<Longrightarrow>  R = relation_prealgebra T \<Longrightarrow>  R1 = Prealgebra.ar (relation_prealgebra T) \<Longrightarrow>
  (\<forall> i . i \<in> Space.inclusions (Prealgebra.space R) \<longrightarrow> Poset.valid_map (R1 $ i))"
using relation_ar_value [where ?T=T]
  by (metis Tuple.valid_welldefined direct_image_valid image relation_space_valid) 

lemma relation_ar_dom : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
R1 = Prealgebra.ar R \<Longrightarrow> i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.dom (R1 $ i) = R0 $ Inclusion.cod i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I direct_image_dom fst_conv inclusions_def mem_Collect_eq snd_conv valid_inclusion_def)

lemma relation_ar_cod : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Prealgebra.ob R \<Longrightarrow>
R1 = Prealgebra.ar R \<Longrightarrow> i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.cod (R1 $ i) = R0 $ Inclusion.dom i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I direct_image_cod fst_conv inclusions_def mem_Collect_eq snd_conv valid_inclusion_def)

lemma relation_ar_ident : 
  fixes T :: "('A,'a) Prealgebra" and A :: "'A Open"
  defines "R \<equiv> relation_prealgebra T"
assumes "valid T"
  assumes "A \<in> Space.opens (Prealgebra.space R)"
  shows "(ar R) $ Space.ident (Prealgebra.space R) A = Poset.ident ((ob R) $ A)"
proof -
  define "i" where "i = Space.ident (Prealgebra.space R) A"
  define "f" where "f = (\<lambda> i u. ((ar T) $ i) $$ u)"
  define "Rf" where "Rf = (ar R) $ i"
  moreover have c: "Space.cod i = A"
    by (simp add: Space.ident_def i_def) 
  moreover have "Space.dom i = A"
    by (simp add: Space.ident_def i_def) 
  moreover have "\<forall> u . u \<in> el ((ob T) $ A) \<longrightarrow> f i u = u"
    by (metis Poset.ident_app R_def Tuple.valid_welldefined assms(2) assms(3) f_def i_def relation_space_valid valid_gc_1 valid_ob) 
  moreover have "(ob R) $ A = powerset (Poset.el ((ob T) $ A))" using  relation_prealgebra_def
      [where ?T=T]
    by (smt (verit) Function.fun_app Function.select_convs(1) Function.valid_map_def Prealgebra.Prealgebra.select_convs(1) Prealgebra.Prealgebra.select_convs(2) R_def assms(2) assms(3) mem_Collect_eq relation_ob_valid) 
  moreover have "i \<in> Space.inclusions (Prealgebra.space R)" using R_def relation_space_valid [where
        ?T=T and ?R=R] Space.valid_ident_inclusion  [where ?T="(Prealgebra.space T)" and ?A=A] i_def
    using Prealgebra.valid_space Tuple.valid_welldefined assms(3) assms(2) by auto 
  moreover have "Poset.dom ((ar R) $ i) = (ob R) $ (Inclusion.cod i)"
    using  assms(3)
    using R_def assms(2) calculation(6) relation_ar_dom by blast 
  moreover have "Rf = Poset.direct_image (f i) (Poset.el (ob T $ (Space.cod i))) (Poset.el (ob T $
 (Space.dom i)))" using Rf_def  relation_prealgebra_def [where ?T=T]
    using R_def \<open>f \<equiv> \<lambda>i. ($$) (ar T $ i)\<close> assms(2) calculation(6) relation_ar_value by blast 
  moreover have "Poset.dom Rf = (ob R) $ A" using  relation_prealgebra_def [where ?T=T] 
      and Poset.direct_image_dom [where ?f="\<lambda>i. ($$) ((ar T) $ i)"]
    using Rf_def c calculation(6)
    using calculation(7) by fastforce 
  moreover have "Poset.cod Rf = (ob R) $ A" using  relation_prealgebra_def [where ?T=T] 
      and Poset.direct_image_cod [where ?f="\<lambda>i. ($$) ((ar T) $ i)"]
    by (simp add: calculation(3) calculation(5) calculation(8) direct_image_cod) 
  moreover have "(ar T) $ i = Poset.ident ((ob T) $ A)"
    by (metis R_def Tuple.valid_welldefined assms(2) assms(3) i_def relation_space_valid valid_identity) 
    moreover have "(ar R) $ i = Poset.ident ((ob R) $ A)"
      using Rf_def c calculation(3) calculation(4) calculation(5) calculation(8) direct_image_ident by force  
    ultimately show ?thesis using R_def  relation_prealgebra_def [where ?T=T] i_def
      by metis 
  qed

lemma relation_ar_trans : 
  fixes T :: "('A,'a) Prealgebra" and i j :: "'A Inclusion"
  defines "R \<equiv> relation_prealgebra T"
  assumes T_valid: "valid T"
  and i_inc : "i \<in> Space.inclusions (Prealgebra.space R)" 
  and j_inc :"j \<in> Space.inclusions (Prealgebra.space R)"
  and endpoints : "Inclusion.dom j = Inclusion.cod i"
shows "ar R $ Space.compose j i = ar R $ i \<cdot> ar R $ j"
proof -
  define "f" where "f = (\<lambda>i. ($$) (ar T $ i))"
  have "ar R $ i = direct_image (f i) (el (ob T $ Inclusion.cod i)) (el (ob T $ Inclusion.dom i))"
    using R_def T_valid f_def i_inc relation_ar_value by blast 
  moreover have "ar R $ j = direct_image (f j) (el (ob T $ Inclusion.cod j)) (el (ob T $ Inclusion.dom j))"
    using R_def T_valid f_def j_inc relation_ar_value by blast
  define "ji" where "ji = (Space.compose j i)"
    moreover have "ar R $ ji = direct_image (f ji) (el (ob T $ Inclusion.cod ji)) (el (ob T $
      Inclusion.dom ji))"
      by (smt (z3) Inclusion.select_convs(1) R_def Space.compose_def Space.compose_valid T_valid endpoints f_def i_inc inclusions_def j_inc ji_def mem_Collect_eq relation_ar_value) 
    moreover have "\<forall> x . x \<in> el (ob T $ (Inclusion.cod j)) \<longrightarrow> f ji x = (f i o f j) x"
      by (smt (verit, ccfv_SIG) R_def T_valid Tuple.valid_welldefined cod_proj comp_apply compose_app dom_proj endpoints f_def i_inc j_inc ji_def relation_space_valid valid_ar valid_composition) 
    moreover have "ar R $ Space.compose j i = ar R $ i \<cdot> ar R $ j"
      by (smt (verit) Prealgebra.valid_welldefined R_def Space.cod_compose Space.dom_compose T_valid Tuple.valid_welldefined \<open>ar R $ j = direct_image (f j) (el (ob T $ Inclusion.cod j)) (el (ob T $ Inclusion.dom j))\<close> calculation(1) calculation(3) compose_app direct_image_trans_weak endpoints f_def i_inc image inclusions_def j_inc ji_def mem_Collect_eq relation_space_valid valid_composition) 
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
    by (metis Prealgebra.valid_space R_def Tuple.valid_welldefined assms(1) relation_space_valid) 
  show "Function.valid_map (ob R)"
    using R_def assms(1) relation_ob_valid by auto
  show "Function.valid_map (ar R)"
    using R_def assms(1) relation_ar_valid by auto 
  show "\<And>A. A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> Poset.valid (ob R $ A)"
    by (metis R_def assms(1) relation_ob_value_valid relation_space_valid) 
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> Poset.valid_map (ar R $ i)"
    by (metis R_def assms(1) relation_ar_value_valid relation_space_valid) 
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.dom (ar R $ i) = ob R $ Inclusion.cod
 i"
    using R_def assms(1) relation_ar_dom by blast 
  show "\<And>i. i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow> PosetMap.cod (ar R $ i) = ob R $ Inclusion.dom
 i"
    using R_def assms(1) relation_ar_cod by blast 
  show "\<And>A. A \<in> Space.opens (Prealgebra.space R) \<Longrightarrow> ar R $ Space.ident (Prealgebra.space R) A =
 Poset.ident (ob R $ A)"
    using R_def assms(1) relation_ar_ident by blast 
  show "\<And>i j. j \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow>
           i \<in> Space.inclusions (Prealgebra.space R) \<Longrightarrow>
           Inclusion.dom j = Inclusion.cod i \<Longrightarrow> ar R $ Space.compose j i = ar R $ i \<cdot> ar R $ j"
    by (simp add: R_def assms(1) relation_ar_trans) 
qed

lemma relation_neutral_nat_valid : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>) 
\<Longrightarrow> Poset.valid_map (PrealgebraMap.nat \<epsilon> $ A)" 
proof-
  fix T \<epsilon> A 
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)"
  define "dom" where "dom = Prealgebra.terminal (map_space \<epsilon>)"
  define "cod" where "cod = relation_prealgebra T"

  have "PrealgebraMap.nat \<epsilon> $ A = Poset.const (Prealgebra.ob dom $ A) (Prealgebra.ob cod $ A) (el (ob
 T $ A))" using relation_neutral_def [where ?T=T]
    by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def Pair_inject PrealgebraMap.select_convs(1) PrealgebraMap.select_convs(2) UNIV_I \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>\<epsilon> = relation_neutral T\<close> local.cod_def local.dom_def mem_Collect_eq) 
  moreover have "Poset.valid (Prealgebra.ob dom $ A)"
    by (simp add: \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> discrete_valid local.dom_def terminal_def) 
  moreover have "Poset.valid (Prealgebra.ob cod $ A)"  using valid_relation_prealgebra [where ?T=T]
    by (metis (no_types, lifting) PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> local.cod_def relation_neutral_def relation_space_valid valid_ob) 
  show "Poset.valid_map (PrealgebraMap.nat \<epsilon> $ A)" using Poset.const_valid [where ?P="Prealgebra.ob
 dom $ A" and ?Q="Prealgebra.ob cod $ A" and ?q="el (ob
 T $ A)"]
    by (metis (no_types, lifting) Poset.Poset.simps(1) Pow_top PrealgebraMap.select_convs(1) \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>Poset.valid (ob cod $ A)\<close> \<open>Tuple.valid T\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation(1) calculation(2) local.cod_def powerset_def relation_neutral_def relation_ob_value) 
qed

lemma relation_neutral_nat_value : "valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>) 
\<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> \<epsilon>A = el (ob T $ A) \<Longrightarrow>
 PrealgebraMap.nat \<epsilon> $ A =  Poset.const Poset.discrete (ob R $ A) \<epsilon>A" 
  unfolding relation_neutral_def
  apply (simp_all add : Let_def)
  by (simp add: Function.dom_def Function.valid_map_def terminal_def)
  
lemma relation_neutral_dom : "\<And>A. valid T \<Longrightarrow> \<epsilon> = relation_neutral T \<Longrightarrow> A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> PosetMap.dom (PrealgebraMap.nat \<epsilon> $ A) = ob
 (PrealgebraMap.dom \<epsilon>) $ A" 
proof -
  fix T \<epsilon> A
  assume "valid T"
  assume "\<epsilon> = relation_neutral T"
  assume "A \<in> Space.opens (map_space \<epsilon>)" 

  have "dom \<epsilon> = Prealgebra.terminal (space T)"
    by (metis (no_types, lifting) PrealgebraMap.select_convs(3) \<open>\<epsilon> = relation_neutral T\<close> relation_neutral_def) 
  moreover have "ob (dom \<epsilon>) $ A = Poset.discrete"
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(2) PrealgebraMap.select_convs(1) UNIV_I \<open>A \<in> Space.opens (map_space \<epsilon>)\<close> \<open>\<epsilon> = relation_neutral T\<close> calculation const_app relation_neutral_def terminal_def) 
  moreover have "PosetMap.dom (PrealgebraMap.nat \<epsilon> $ A) = Poset.discrete" using relation_neutral_def
      [where ?T=T]  
    apply (simp add: Let_def) 
    
  ultimately show "PosetMap.dom (PrealgebraMap.nat \<epsilon> $ A) = ob
 (PrealgebraMap.dom \<epsilon>) $ A"  

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
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> Poset.valid_map (PrealgebraMap.nat \<epsilon> $ A)" using
      Poset.const_valid
    using \<epsilon>_def assms(1) relation_neutral_nat_valid by blast 
  show "\<And>A. A \<in> Space.opens (map_space \<epsilon>) \<Longrightarrow> PosetMap.dom (PrealgebraMap.nat \<epsilon> $ A) = ob
 (PrealgebraMap.dom \<epsilon>) $ A" using relation_neutral_def [where ?T=T] 
    
end
