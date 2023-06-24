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
      R0 = \<lparr> func = {(A, Poset.powerset (Poset.el (T0 $ A))) | A . A \<in> Space.opens S} , cod = UNIV \<rparr>;
      R1 = \<lparr> func = {(i,
        \<lparr> PosetMap.func = {(U,{(T1 $ i) $$ u | u . u \<in> U }) | U . U \<in> Poset.el (R0 $ (Space.cod i))}, dom = R0 $ (Space.cod i), cod = R0 $ (Space.dom i) \<rparr>
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

lemma valid_relation_prealgebra :
  fixes T :: "('A,'a) TupleSystem"
  assumes "valid T"
  defines "R \<equiv> relation_prealgebra T"
  shows "Presheaf.valid R"
  unfolding Presheaf.valid_def Let_def R_def 
proof auto
  have "Presheaf.space R = Presheaf.space T" using R_def valid_def [where ?T=T]
      relation_prealgebra_def [where ?T=T]
    by (metis (no_types, lifting) Presheaf.Presheaf.select_convs(1))
  show "Space.valid (Presheaf.space (relation_prealgebra T))"
    using Presheaf.valid_space R_def Tuple.valid_welldefined \<open>Presheaf.space R = Presheaf.space T\<close> assms(1) by blast 
next
  show "Function.valid_map (ob (relation_prealgebra T))" unfolding relation_prealgebra_def
    apply (simp_all add : Let_def)
    by (simp add: Function.dom_def Function.valid_map_def)
next 
  show "Function.valid_map (ar (relation_prealgebra T))"  unfolding relation_prealgebra_def
    apply (simp_all add : Let_def)
    oops
next




end
