theory Tuple
  imports Main Presheaf OVA
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

definition relation_prealgebra :: "('A, 'a) TupleSystem \<Rightarrow> ('A, 'a set) Presheaf" where
  "relation_prealgebra T \<equiv>
    let
      S = Presheaf.space T;
      T0 = Presheaf.ob T;
      T1 = Presheaf.ar T;
      f  = \<lambda> i u. (T1 $ i) $$ u;
      R0 = \<lparr> func = {(A, Poset.powerset (Poset.el (T0 $ A))) | A . A \<in> Space.opens S} , cod = UNIV \<rparr>;
      R1 = \<lparr> func = {(i, Poset.direct_image (f i) (Poset.el (T0 $ (Space.cod i))) (Poset.el (T0 $ (Space.dom i)))
            ) | i . i \<in> Space.inclusions S} , cod = UNIV \<rparr>
    in
    \<lparr>Presheaf.space = S, ob = R0, ar = R1\<rparr>"

text \<open> ----------------- LEMMAS ----------------- \<close>

lemma valid_welldefined :  "valid T \<Longrightarrow> Presheaf.valid T" unfolding valid_def
  by (simp add: Let_def)

lemma valid_flasque : "valid T \<Longrightarrow> (\<forall>i. i \<in> Space.inclusions (Presheaf.space T) \<longrightarrow> Poset.is_surjective (Presheaf.ar T $ i))"
  unfolding valid_def
  by (simp add: Let_def)

lemma valid_binary_gluing : "valid T \<Longrightarrow> (\<forall> A B a b i_A j_A i_B j_B . A \<in> Space.opens (Presheaf.space T) \<longrightarrow> B \<in> Space.opens (Presheaf.space T) \<longrightarrow> a \<in> Poset.el (Presheaf.ob T $ A)
        \<longrightarrow> b \<in> Poset.el (Presheaf.ob T $ B)
         \<longrightarrow> i_A = Space.make_inclusion (Presheaf.space T) (A \<inter> B) A
           \<longrightarrow> j_A = Space.make_inclusion (Presheaf.space T) A (A \<union> B)
         \<longrightarrow> i_B = Space.make_inclusion (Presheaf.space T) (A \<inter> B) B
           \<longrightarrow> j_B = Space.make_inclusion (Presheaf.space T) B (A \<union> B)
            \<longrightarrow> (Presheaf.ar T $ i_A) $$ a = (Presheaf.ar T $ i_B) $$ b
            \<longrightarrow> (\<exists> c . c \<in> Poset.el (Presheaf.ob T $ (A \<union> B)) \<and> (Presheaf.ar T $ j_A) $$ c = a \<and> (Presheaf.ar T $ j_B) $$ c = b))"
  unfolding valid_def
  by (simp add: Let_def)

lemma relation_space_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> Presheaf.space R = Presheaf.space T"
  unfolding relation_prealgebra_def
  by (meson Presheaf.Presheaf.select_convs(1))

lemma relation_ob_valid : "valid T \<Longrightarrow> R0 = Presheaf.ob (relation_prealgebra T) \<Longrightarrow> Function.valid_map R0"
  unfolding relation_prealgebra_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ar_valid : "valid T \<Longrightarrow> R1 = Presheaf.ar (relation_prealgebra T) \<Longrightarrow> Function.valid_map R1"
  unfolding relation_prealgebra_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)

lemma relation_ob_value : "valid T \<Longrightarrow> R0 = Presheaf.ob (relation_prealgebra T) \<Longrightarrow>
 (\<forall> A . A \<in> Space.opens (Presheaf.space T) \<longrightarrow> X = Poset.el ((ob T) $ A) \<longrightarrow> R0 $ A = Poset.powerset X)"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I fst_conv mem_Collect_eq snd_conv)

lemma relation_ob_value_valid : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Presheaf.ob R \<Longrightarrow>
 (\<forall> A . A \<in> Space.opens (Presheaf.space R) \<longrightarrow> Poset.valid (R0 $ A))"
  using relation_ob_value [where ?T=T]
  by (metis powerset_valid relation_space_valid)

lemma relation_ar_value : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow> R1 = Presheaf.ar (relation_prealgebra T) \<Longrightarrow>
 (\<forall> i . i \<in> Space.inclusions (Presheaf.space R) \<longrightarrow> X = Poset.el ((ob T) $ (Space.cod i)) \<longrightarrow> Y = Poset.el ((ob T) $ (Space.dom i)) 
\<longrightarrow> f=(($$) (ar T $ i)) \<longrightarrow> R1 $ i = Poset.direct_image f X Y)"
  unfolding relation_prealgebra_def [where ?T=T]
  by (smt (verit) Function.fun_app Function.select_convs(1) Function.valid_map_def Presheaf.Presheaf.select_convs(1) Presheaf.Presheaf.select_convs(3) \<open>relation_prealgebra T \<equiv> let S = Presheaf.space T; T0 = ob T; T1 = ar T; f = \<lambda>i. ($$) (T1 $ i); R0 = \<lparr>Function.func = {(A, powerset (el (T0 $ A))) |A. A \<in> Space.opens S}, cod = UNIV\<rparr>; R1 = \<lparr>Function.func = {(i, direct_image (f i) (el (T0 $ Inclusion.cod i)) (el (T0 $ Inclusion.dom i))) | i. i \<in> Space.inclusions S}, cod = UNIV\<rparr> in \<lparr>Presheaf.space = S, ob = R0, ar = R1\<rparr>\<close> mem_Collect_eq relation_ar_valid)

lemma relation_ar_value_valid : "valid T \<Longrightarrow>  R = relation_prealgebra T \<Longrightarrow>  R1 = Presheaf.ar (relation_prealgebra T) \<Longrightarrow>
  (\<forall> i . i \<in> Space.inclusions (Presheaf.space R) \<longrightarrow> Poset.valid_map (R1 $ i))"
using relation_ar_value [where ?T=T]
  by (metis Tuple.valid_welldefined direct_image_valid image relation_space_valid) 

lemma relation_ar_dom : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Presheaf.ob R \<Longrightarrow>
R1 = Presheaf.ar R \<Longrightarrow> i \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow> PosetMap.dom (R1 $ i) = R0 $ Inclusion.cod i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I direct_image_dom fst_conv inclusions_def mem_Collect_eq snd_conv valid_inclusion_def)

lemma relation_ar_cod : "valid T \<Longrightarrow> R = relation_prealgebra T \<Longrightarrow>  R0 = Presheaf.ob R \<Longrightarrow>
R1 = Presheaf.ar R \<Longrightarrow> i \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow> PosetMap.cod (R1 $ i) = R0 $ Inclusion.dom i"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I direct_image_cod fst_conv inclusions_def mem_Collect_eq snd_conv valid_inclusion_def)

lemma relation_ar_ident : 
  fixes T :: "('A,'a) Presheaf" and A :: "'A Open"
  defines "R \<equiv> relation_prealgebra T"
assumes "valid T"
  assumes "A \<in> Space.opens (Presheaf.space R)"
  shows "(ar R) $ Space.ident (Presheaf.space R) A = Poset.ident ((ob R) $ A)"
proof -
  define "i" where "i = Space.ident (Presheaf.space R) A"
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
    by (smt (verit) Function.fun_app Function.select_convs(1) Function.valid_map_def Presheaf.Presheaf.select_convs(1) Presheaf.Presheaf.select_convs(2) R_def assms(2) assms(3) mem_Collect_eq relation_ob_valid) 
  moreover have "i \<in> Space.inclusions (Presheaf.space R)" using R_def relation_space_valid [where
        ?T=T and ?R=R] Space.valid_ident_inclusion  [where ?T="(Presheaf.space T)" and ?A=A] i_def
    using Presheaf.valid_space Tuple.valid_welldefined assms(3) assms(2) by auto 
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
  fixes T :: "('A,'a) Presheaf" and i j :: "'A Inclusion"
  defines "R \<equiv> relation_prealgebra T"
  assumes T_valid: "valid T"
  and i_inc : "i \<in> Space.inclusions (Presheaf.space R)" 
  and j_inc :"j \<in> Space.inclusions (Presheaf.space R)"
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
      by (smt (verit) Presheaf.valid_welldefined R_def Space.cod_compose Space.dom_compose T_valid Tuple.valid_welldefined \<open>ar R $ j = direct_image (f j) (el (ob T $ Inclusion.cod j)) (el (ob T $ Inclusion.dom j))\<close> calculation(1) calculation(3) compose_app direct_image_trans_weak endpoints f_def i_inc image inclusions_def j_inc ji_def mem_Collect_eq relation_space_valid valid_composition) 
    ultimately show ?thesis
      by meson
  qed

lemma valid_relation_prealgebra :
  fixes T :: "('A,'a) TupleSystem"
  assumes "valid T"
  defines "R \<equiv> relation_prealgebra T"
  shows "Presheaf.valid R"
proof (rule Presheaf.validI, auto)
  show "Space.valid (Presheaf.space R)"
    by (metis Presheaf.valid_space R_def Tuple.valid_welldefined assms(1) relation_space_valid) 
  show "Function.valid_map (ob R)"
    using R_def assms(1) relation_ob_valid by auto
  show "Function.valid_map (ar R)"
    using R_def assms(1) relation_ar_valid by auto 
  show "\<And>A. A \<in> Space.opens (Presheaf.space R) \<Longrightarrow> Poset.valid (ob R $ A)"
    by (metis R_def assms(1) relation_ob_value_valid relation_space_valid) 
  show "\<And>i. i \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow> Poset.valid_map (ar R $ i)"
    by (metis R_def assms(1) relation_ar_value_valid relation_space_valid) 
  show "\<And>i. i \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow> PosetMap.dom (ar R $ i) = ob R $ Inclusion.cod
 i"
    using R_def assms(1) relation_ar_dom by blast 
  show "\<And>i. i \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow> PosetMap.cod (ar R $ i) = ob R $ Inclusion.dom
 i"
    using R_def assms(1) relation_ar_cod by blast 
  show "\<And>A. A \<in> Space.opens (Presheaf.space R) \<Longrightarrow> ar R $ Space.ident (Presheaf.space R) A =
 Poset.ident (ob R $ A)"
    using R_def assms(1) relation_ar_ident by blast 
  show "\<And>i j. j \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow>
           i \<in> Space.inclusions (Presheaf.space R) \<Longrightarrow>
           Inclusion.dom j = Inclusion.cod i \<Longrightarrow> ar R $ Space.compose j i = ar R $ i \<cdot> ar R $ j"
    by (simp add: R_def assms(1) relation_ar_trans) 
qed

end
