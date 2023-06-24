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
      R1 = \<lparr> func = {(i, Poset.direct_image (f i) (R0 $ (Space.cod i)) (R0 $ (Space.dom i))
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

lemma relation_ob_value_valid : "valid T \<Longrightarrow> R0 = Presheaf.ob (relation_prealgebra T) \<Longrightarrow>
 (\<forall> A . A \<in> Space.opens (Presheaf.space T) \<longrightarrow> Poset.valid (R0 $ A))"
  unfolding relation_prealgebra_def
  apply (simp_all add : Let_def)
  by (smt (verit) Function.dom_def Function.fun_app Function.select_convs(1) Function.select_convs(2) Function.valid_map_def UNIV_I fst_conv mem_Collect_eq powerset_valid snd_conv)

lemma relation_ar_value_valid : "valid T \<Longrightarrow> R1 = Presheaf.ar (relation_prealgebra T) \<Longrightarrow>
  (\<forall> i . i \<in> Space.inclusions (Presheaf.space T) \<longrightarrow> Poset.valid_map (R1 $ i))"
proof auto
  fix i
  assume "valid T"
  assume R1: "R1 = ar (relation_prealgebra T)"
  assume "i \<in> Space.inclusions (Presheaf.space T)"

  define "X" where "X = Poset.el (Presheaf.ob T $ (Space.cod i))"
  define "Y" where "Y = Poset.el (Presheaf.ob T $ (Space.dom i))"
  define "P" where "P = Poset.powerset X" 
  define "Q" where "Q = Poset.powerset Y"

  have "Poset.valid_map (ar T $ i)"
    using Tuple.valid_welldefined \<open>Tuple.valid T\<close> \<open>i \<in> Space.inclusions (Presheaf.space T)\<close> valid_ar by blast 
  moreover have "Poset.valid P"
    by (simp add: P_def powerset_valid) 
  moreover have "Poset.valid Q"
    by (simp add: Q_def powerset_valid) 
  moreover have "R1 $ i = direct_image (($$) (ar T $ i)) P Q" using R1 relation_prealgebra_def [where ?T=T]
    by (smt (verit) Function.fun_app Function.select_convs(1) Function.valid_map_def P_def Presheaf.Presheaf.select_convs(2) Presheaf.Presheaf.select_convs(3) Q_def X_def Y_def \<open>Tuple.valid T\<close> \<open>i \<in> Space.inclusions (Presheaf.space T)\<close> inclusions_def mem_Collect_eq relation_ar_valid relation_ob_valid valid_inclusion_def) 
  ultimately show "Poset.valid_map (ar (relation_prealgebra T) $ i)" using relation_prealgebra_def 
    apply (simp add: Let_def)
    using Poset.direct_image_valid  [where ?f="(($$) (ar T $ i))" 
        and ?A="Poset.el (Presheaf.ob T $ (Space.cod i))" and ?B="Poset.el (Presheaf.ob T $ (Space.dom i))"]
    by (simp add: P_def Q_def R1 Tuple.valid_welldefined X_def Y_def \<open>Tuple.valid T\<close> \<open>i \<in> Space.inclusions (Presheaf.space T)\<close> image) 
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
    oops

(*Poset.powerset_valid  [where ?A="el (ob T $ A)"] *)

next




end
