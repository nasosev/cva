section \<open> CVA.thy \<close>

theory CVA
  imports Main OVA
begin

(* CVA type (concurrent valuation algebra) *)
record ('A, 'a) CVA =
  seq_algebra :: "('A, 'a) OVA"
  par_algebra :: "('A, 'a) OVA"

abbreviation poset :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) Poset" where
"poset V \<equiv> OVA.poset (seq_algebra V)"

abbreviation prealgebra :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Prealgebra" where
"prealgebra V \<equiv> OVA.prealgebra (seq_algebra V)"

abbreviation ob :: "('A, 'a) CVA \<Rightarrow> ('A Open, 'a Poset) Function" where
"ob V \<equiv> OVA.ob (seq_algebra V)"

abbreviation ar :: "('A, 'a) CVA \<Rightarrow> ('A Inclusion, ('a, 'a) PosetMap) Function" where
"ar V \<equiv> OVA.ar (seq_algebra V)"

abbreviation elems :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> OVA.elems (seq_algebra V)"

abbreviation (input) space :: "('A,'a) CVA \<Rightarrow> 'A Space" where
"space V \<equiv> OVA.space (seq_algebra V)"

abbreviation par :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"par V \<equiv> OVA.comb (par_algebra V)"

abbreviation seq :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"seq V \<equiv> OVA.comb (seq_algebra V)"

abbreviation le :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"le V \<equiv> OVA.le (seq_algebra V)"

abbreviation local_le :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V \<equiv> OVA.local_le (seq_algebra V)"

abbreviation neut_par :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_par V \<equiv> OVA.neut (par_algebra V)"

abbreviation neut_seq :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_seq V \<equiv> OVA.neut (seq_algebra V)"

abbreviation res :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"res V \<equiv> OVA.res (seq_algebra V)"

abbreviation ext :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"ext V \<equiv> OVA.ext (seq_algebra V)"

definition valid :: "('A, 'a) CVA \<Rightarrow> bool" where
  "valid V \<equiv>
    let
        seq = OVA.comb (seq_algebra V);
        par = OVA.comb (par_algebra V);
        le = OVA.le (seq_algebra V);
        \<epsilon> = OVA.neut (seq_algebra V);
        \<delta> = OVA.neut (par_algebra V);


        welldefined = OVA.valid (seq_algebra V)
                      \<and> OVA.valid (par_algebra V)
                      \<and> (OVA.prealgebra (seq_algebra V) = OVA.prealgebra (par_algebra V));

        commutativity = is_commutative (par_algebra V);

        weak_exchange = \<forall> a b c d. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> c \<in> elems V \<longrightarrow> d \<in> elems V \<longrightarrow>
                         le (seq (par a b) (par c d)) (par (seq a c) (seq b d));

        neutral_law_par = (\<forall>A . A \<in> opens (space V) \<longrightarrow> le (seq (\<delta> A) (\<delta> A)) (\<delta> A));

        neutral_law_seq = (\<forall>A . A \<in> opens (space V) \<longrightarrow> le (\<epsilon> A) (par (\<epsilon> A) (\<epsilon> A)))
    in
      welldefined \<and> commutativity \<and> weak_exchange \<and> neutral_law_par \<and> neutral_law_seq"

abbreviation hoare :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"hoare V p a q \<equiv> le V (seq V p a) q" 

abbreviation rg :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"rg V p r a g q \<equiv> hoare V p (par V r a) q \<and> le V a g" 

(* C.f. Def 7.2 2. Hoare, CAR Tony, et al. "Concurrent kleene algebra." CONCUR 2009-Concurrency Theory: 20th International Conference, CONCUR 2009, Bologna, Italy, September 1-4, 2009. Proceedings 20. Springer Berlin Heidelberg, 2009. *)
(* i \<Zsemi> i = i \<and> i \<parallel> i = i \<and> i \<parallel> (a \<Zsemi> b) \<preceq> (i \<parallel> a) \<Zsemi> (i \<parallel> b) *)
(* for recursion, we should also assume neut_skip \<le> i *)
definition invariant :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"invariant V i \<equiv> 
  le V (neut_seq V (d i)) i 
  \<and> seq V i i = i 
  \<and> par V i i = i 
  \<and> (\<forall> a b . a \<in> elems V \<and> b \<in> elems V \<longrightarrow> le V (par V i (seq V a b)) (seq V (par V i a) (par V i b)))"

definition meet :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"meet V a b = Poset.meet (poset V) a b"

definition join :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"join V a b = Poset.join (poset V) a b"

definition inf :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"inf V U = Poset.inf (poset V) U"

definition sup :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"sup V U = Poset.sup (poset V) U"

(* Properties *)

definition is_complete :: "('A,'a) CVA \<Rightarrow> bool" where
"is_complete V \<equiv> Poset.is_complete (OVA.poset (seq_algebra V))"

lemma cocomplete : "is_complete V \<Longrightarrow> is_cocomplete (poset V)"
  using CVA.is_complete_def complete_equiv_cocomplete by blast 

(* Usually 'continuous' means preservation of directed suprema only, so the below defn. is stronger *)
definition is_continuous :: "('A,'a) CVA \<Rightarrow> bool" where
"is_continuous V \<equiv> is_complete V \<and> (\<forall> a U . U \<subseteq> elems V \<longrightarrow> U \<noteq> {} \<longrightarrow> a \<in> elems V \<longrightarrow>
  par V a (sup V U) = sup V {par V a u | u . u \<in> U} \<and>
  seq V a (sup V U) = sup V {seq V a u | u . u \<in> U} \<and>
  seq V (sup V U) a = sup V {seq V u a | u . u \<in> U})"

(* Constants *)

definition bot :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation" where
"bot V = Poset.bot (poset V)"

definition top :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation" where
"top V = Poset.top (poset V)"

lemma complete_bot_el : "is_complete V \<Longrightarrow> bot V \<in> elems V"
  by (simp add: CVA.bot_def CVA.is_complete_def bot_as_inf inf_el)

lemma complete_top_el : "is_complete V \<Longrightarrow> top V \<in> elems V"
  by (metis CVA.top_def Poset.top_def cocomplete dual_order.refl sup_el) 

(* Validity *)

lemma valid_welldefined: "valid V \<Longrightarrow> OVA.valid (seq_algebra V) \<and> OVA.valid (par_algebra V) \<and> (OVA.prealgebra (seq_algebra V) = OVA.prealgebra (par_algebra V))"
  unfolding valid_def
  by metis

lemma valid_par_commutativity: "valid V \<Longrightarrow> is_commutative (par_algebra V)"
  unfolding valid_def
  by metis

lemma valid_elems :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "elems V = OVA.elems (par_algebra V)"
  by (metis CVA.valid_welldefined assms valid_gc_poset)

lemma valid_le :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "le V = OVA.le (par_algebra V)"
  by (metis (no_types, opaque_lifting) CVA.valid_welldefined assms valid_gc_poset)

lemma local_le :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "local_le V = OVA.local_le (par_algebra V)"
  unfolding OVA.local_le_def
  by (simp add: CVA.valid_welldefined assms)

lemma valid_weak_exchange: "valid V \<Longrightarrow> a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> a3 \<in> elems V \<Longrightarrow> a4 \<in> elems V \<Longrightarrow>
                        le V (seq V (par V a1 a2) (par V a3 a4)) (par V (seq V a1 a3) (seq V a2 a4))"
  unfolding valid_def
  by (metis OVA.valid_welldefined)

lemma valid_neutral_law_par: "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> \<delta>A = neut_par V A
  \<Longrightarrow> le V (seq V \<delta>A \<delta>A) \<delta>A"
  unfolding valid_def
  by (metis valid_gc_poset) 

lemma valid_neutral_law_seq: "valid V \<Longrightarrow>  A \<in> opens (space V) \<Longrightarrow> \<epsilon>A = neut_seq V A
  \<Longrightarrow> le V \<epsilon>A (par V \<epsilon>A \<epsilon>A)"
  unfolding valid_def
  by (metis valid_gc_poset)

lemma valid_res: "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> elems V \<Longrightarrow> res V A a = OVA.res (par_algebra V) A a"
  unfolding valid_def
  by (metis res_def valid_gc_poset)

lemma valid_ext: 
  fixes V :: "('A, 'a) CVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and A_open : "A \<in> opens (space V)" 
  and b_elem : "b \<in> elems V" 
  and B_leq_A : "d b \<subseteq> A"
  shows "ext V A b = OVA.ext (par_algebra V) A b"
  by (smt (verit, best) A_open B_leq_A CVA.valid_welldefined OVA.le_eq_local_le V_valid b_elem d_elem_is_open d_ext ext_elem galois_closure_extensive galois_insertion local_le valid_antisymmetry valid_elems valid_poset valid_res valid_semigroup)

lemma valid_le_reflexive: 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V"
  shows "le V a a"
  by (metis CVA.valid_welldefined V_valid a_elem valid_poset valid_reflexivity valid_semigroup)

lemma valid_le_antisymmetric: 
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and "le V a b" and "le V b a" 
  shows "a = b"
  by (metis CVA.valid_welldefined V_valid a_elem assms(4) assms(5) b_elem valid_antisymmetry valid_poset valid_semigroup) 

lemma valid_le_transitive: 
  fixes V :: "('A, 'a) CVA" and a b c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V" and c_elem : "c \<in> elems V"
  and "le V a b" and "le V b c" 
  shows "le V a c"
  by (smt (verit) CVA.valid_welldefined V_valid a_elem assms(5) assms(6) b_elem c_elem valid_poset valid_semigroup valid_transitivity) 

lemma valid_par_comm : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> par V a b = par V b a"
  using is_commutative_def valid_par_commutativity
  by (metis CVA.valid_welldefined valid_gc_poset) 

lemma valid_seq_elem: 
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  shows "seq V a b \<in> elems V"
  by (metis CVA.valid_welldefined V_valid a_elem b_elem comb_is_element) 

lemma valid_par_elem: 
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  shows "par V a b \<in> elems V"
  by (metis CVA.valid_welldefined V_valid a_elem b_elem comb_is_element valid_gc_poset) 

lemma valid_seq_assoc: 
  fixes V :: "('A, 'a) CVA" and a b c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V" and c_elem : "c \<in> elems V"
  shows "le V (seq V a (seq V b c)) (seq V (seq V a b) c)"
  by (metis CVA.valid_welldefined V_valid a_elem b_elem c_elem valid_comb_associative valid_le_reflexive valid_seq_elem)

lemma valid_par_assoc: 
  fixes V :: "('A, 'a) CVA" and a b c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V" and c_elem : "c \<in> elems V"
  shows "le V (par V a (par V b c)) (par V (par V a b) c)"
  by (metis CVA.valid_welldefined V_valid a_elem b_elem c_elem valid_comb_associative valid_elems valid_le_reflexive valid_par_elem)

lemma valid_seq_mono: 
  fixes V :: "('A, 'a) CVA" and a a' b b' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and a'_elem : "a' \<in> elems V" and b_elem : "b \<in> elems V" and b'_elem : "b' \<in> elems V" 
  and a_le_a' : "le V a a'" and b_le_b' : "le V b b'"
  shows "le V (seq V a b) (seq V a' b')"
  by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid a'_elem a_elem a_le_a' b'_elem b_elem b_le_b' valid_monotone valid_semigroup)

lemma valid_par_mono: 
  fixes V :: "('A, 'a) CVA" and a a' b b' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and a_elem : "a \<in> elems V" and a'_elem : "a' \<in> elems V" and b_elem : "b \<in> elems V" and b'_elem : "b' \<in> elems V" 
  and a_le_a' : "le V a a'" and b_le_b' : "le V b b'"
  shows "le V (par V a b) (par V a' b')"
  by (smt (verit, del_insts) CVA.valid_welldefined V_valid a'_elem a_elem a_le_a' b'_elem b_elem b_le_b' valid_gc_poset valid_monotone valid_semigroup) 

lemma valid_neut_seq_elem:
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)" 
  shows "neut_seq V A \<in> elems V"
  by (meson A_open CVA.valid_welldefined V_valid neutral_is_element)

lemma valid_neut_par_elem: 
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)" 
  shows "neut_par V A \<in> elems V"
  by (metis A_open CVA.valid_welldefined V_valid neutral_is_element valid_elems)

lemma ext_seq: 
  fixes V :: "('A, 'a) CVA" and b :: "('A, 'a) Valuation" and A :: "'A Open"
  assumes V_valid : "valid V" 
  and a_elem : "b \<in> elems V" and A_open : "A \<in> opens (space V)" and B_le_A : "d b \<subseteq> A"
shows "seq V (neut_seq V A) b = ext V A b"
  by (smt (verit, del_insts) A_open B_le_A CVA.valid_welldefined V_valid a_elem d_ext d_neut ext_elem ext_functorial_id ova_comb_local sup.orderE valid_neut_seq_elem valid_neutral_law_left)

lemma ext_symmetric_seq:
  fixes V :: "('A, 'a) CVA" and b :: "('A, 'a) Valuation" and A :: "'A Open"
  assumes V_valid : "valid V" 
  and a_elem : "b \<in> elems V" and A_open : "A \<in> opens (space V)" and B_le_A : "d b \<subseteq> A"
shows "seq V b (neut_seq V A) = ext V A b"
  by (smt (verit, del_insts) A_open B_le_A CVA.valid_welldefined V_valid a_elem d_ext ext_elem ext_functorial_id fst_conv ova_comb_local subset_Un_eq valid_neut_seq_elem valid_neutral_law_right)

lemma ext_par: 
  fixes V :: "('A, 'a) CVA" and b :: "('A, 'a) Valuation" and A :: "'A Open"
  assumes V_valid : "valid V" 
  and a_elem : "b \<in> elems V" and A_open : "A \<in> opens (space V)" and B_le_A : "d b \<subseteq> A"
shows "par V (neut_par V A) b = ext V A b"
  by (smt (verit, del_insts) A_open B_le_A CVA.valid_welldefined V_valid a_elem d_ext ext_elem ext_functorial_id fst_conv ova_comb_local sup.orderE valid_elems valid_ext valid_neut_par_elem valid_neutral_law_left)

lemma ext_symmetric_par:
  fixes V :: "('A, 'a) CVA" and b :: "('A, 'a) Valuation" and A :: "'A Open"
  assumes V_valid : "valid V" 
  and a_elem : "b \<in> elems V" and A_open : "A \<in> opens (space V)" and B_le_A : "d b \<subseteq> A"
shows "par V b (neut_par V A) = ext V A b "
  by (smt (verit, del_insts) A_open B_le_A CVA.valid_welldefined V_valid a_elem d_ext ext_elem ext_functorial_id fst_conv ova_comb_local subset_Un_eq valid_elems valid_ext valid_neut_par_elem valid_neutral_law_right)

(* Lattice and quantale *) 

lemma seq_bot1 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (seq V a (bot V)) (seq V a b)"
  by (smt (verit, best) CVA.bot_def V_complete V_valid a_el b_el bot_min cocomplete complete_bot_el valid_le_reflexive valid_seq_mono) 

lemma seq_bot2 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (seq V (bot V) b) (seq V a b)"
  by (smt (verit, best) CVA.bot_def V_complete V_valid a_el b_el bot_min cocomplete complete_bot_el valid_le_reflexive valid_seq_mono) 

lemma par_bot1 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (par V a (bot V)) (par V a b)"
  by (smt (verit, best) CVA.bot_def V_complete V_valid a_el b_el bot_min cocomplete complete_bot_el valid_le_reflexive valid_par_mono) 

lemma par_bot2 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (par V (bot V) b) (par V a b)"
  by (smt (verit, best) CVA.bot_def V_complete V_valid a_el b_el bot_min cocomplete complete_bot_el valid_le_reflexive valid_par_mono) 

lemma seq_top1 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (seq V a b) (seq V a (top V)) "
  by (smt (verit, best) CVA.top_def V_complete V_valid a_el b_el top_max cocomplete complete_top_el valid_le_reflexive valid_seq_mono) 

lemma seq_top2 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (seq V a b) (seq V (top V) b)"
  by (smt (verit, best) CVA.top_def V_complete V_valid a_el b_el top_max cocomplete complete_top_el valid_le_reflexive valid_seq_mono) 

lemma par_top1 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (par V a b) (par V a (top V))"
  by (smt (verit, best) CVA.top_def V_complete V_valid a_el b_el top_max cocomplete complete_top_el valid_le_reflexive valid_par_mono) 

lemma par_top2 :
  fixes V :: "('A, 'a) CVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V (par V a b) (par V (top V) b)"
  by (smt (verit, best) CVA.top_def V_complete V_valid a_el b_el top_max cocomplete complete_top_el valid_le_reflexive valid_par_mono) 

(* Continuity *)

lemma continuous_complete : "is_continuous V \<Longrightarrow> is_complete V"
  using is_continuous_def by blast 

lemma continuous_cocomplete : "is_continuous V \<Longrightarrow> is_cocomplete (poset V)"
  using cocomplete continuous_complete by blast

lemma continuous_seq_dist :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_continuous V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "seq V a (sup V U) = sup V {seq V a u | u . u \<in> U}" using is_continuous_def [where ?V=V]
  using assms(2) assms(3) assms(4) assms(5) by blast

lemma continuous_seq_dist_symmetric :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_continuous V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "seq V (sup V U) a = sup V {seq V u a | u . u \<in> U}" using is_continuous_def [where ?V=V]
  using assms(2) assms(3) assms(4) assms(5) by blast

lemma continuous_par_dist :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_continuous V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "par V a (sup V U) = sup V {par V a u | u . u \<in> U}" using is_continuous_def [where ?V=V]
  using assms(2) assms(3) assms(4) assms(5) by blast

lemma continuous_par_dist_symmetric :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_continuous V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "par V (sup V U) a = sup V {par V u a | u . u \<in> U}" 
proof -
  have "par V (sup V U) a = par V a (sup V U)"
    by (metis (no_types, opaque_lifting) CVA.is_complete_def CVA.sup_def assms(1) assms(2) assms(3) assms(4) complete_equiv_cocomplete is_cocomplete_def is_continuous_def valid_par_comm)
  moreover have "{par V u a | u . u \<in> U} = {par V a u | u . u \<in> U}"
    using assms(1) assms(3) assms(4) valid_par_comm by blast
  ultimately show ?thesis
    by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) assms(5) continuous_par_dist) 
qed

lemma binary_continuous :
  fixes V :: "('A, 'a) CVA" and a b b' :: "('A, 'a) Valuation"
  assumes "valid V" and "is_continuous V"
  and "a \<in> elems V" and "b \<in> elems V" and "b' \<in> elems V" 
shows "par V a (join V b b') = join V (par V a b) (par V a b')
\<and> seq V a (join V b b') = join V (seq V a b) (seq V a b')
\<and> seq V (join V b b') a = join V (seq V b a) (seq V b' a)"
proof -
  define "U" where "U = {b, b'}" 
  moreover have "U \<noteq> {}" using U_def try
    by simp
  moreover have "U \<subseteq> elems V"
    using U_def assms(5) assms(4) by blast
  have "join V b b' = sup V U" unfolding U_def sup_def Poset.sup_def join_def Poset.join_def
    by force 
  moreover have "{par V a b, par V a b'} = {par V a u | u . u \<in> U}" using U_def 
    by blast
  moreover have "{seq V a b, seq V a b'} = {seq V a u | u . u \<in> U}" using U_def 
    by blast
  moreover have "{seq V b a, seq V b' a} = {seq V u a | u . u \<in> U}" using U_def 
    by blast
  moreover have "join V (par V a b) (par V a b') = sup V {par V a u | u . u \<in> U}"
    by (simp add: CVA.join_def CVA.sup_def Poset.join_def calculation(4))
  moreover have "join V (seq V a b) (seq V a b') = sup V {seq V a u | u . u \<in> U}"
    by (simp add: CVA.join_def CVA.sup_def Poset.join_def calculation(5))
  moreover have "join V (seq V b a) (seq V b' a) = sup V {seq V u a | u . u \<in> U}"
    by (simp add: CVA.join_def CVA.sup_def Poset.join_def calculation(6))
  ultimately show ?thesis using is_continuous_def [where ?V=V ]  \<open>U \<subseteq> CVA.elems V\<close> assms(2) assms(3)
    by presburger 
qed

lemma inf_elem : "is_complete V \<Longrightarrow> U \<subseteq> elems V \<Longrightarrow> inf V U \<in> elems V"
  by (simp add: CVA.inf_def CVA.is_complete_def inf_el) 

lemma sup_elem : "is_complete V \<Longrightarrow> U \<subseteq> elems V \<Longrightarrow> sup V U \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.sup_def complete_equiv_cocomplete sup_el)

lemma meet_elem : "is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> meet V a b \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.meet_def meet_el)

lemma join_elem : "is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> join V a b \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.join_def complete_equiv_cocomplete join_el)

lemma top_elem : "is_complete V \<Longrightarrow> top V \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.top_def Poset.top_def complete_equiv_cocomplete sup_el)

lemma bot_elem : "is_complete V \<Longrightarrow> bot V \<in> elems V"
  by (metis CVA.bot_def CVA.sup_def Poset.bot_def empty_subsetI sup_elem)

(* Iteration 

Todo: implement other properties https://en.wikipedia.org/wiki/Kleene_algebra#Properties
*)

definition par_iter_map :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> (('A, 'a) Valuation, ('A, 'a) Valuation) PosetMap" where
"par_iter_map V x \<equiv> \<lparr> PosetMap.dom = poset V, cod = poset V, 
                   func = { (a, join V (neut_par V (d x)) (par V x a)) | a. a \<in> elems V} \<rparr>"

definition seq_iter_map :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> (('A, 'a) Valuation, ('A, 'a) Valuation) PosetMap" where
"seq_iter_map V x \<equiv> \<lparr> PosetMap.dom = poset V, cod = poset V, 
                   func = { (a, join V (neut_seq V (d x)) (seq V x a) ) | a. a \<in> elems V} \<rparr>"

lemma dom_cod_par_iter_map : "Poset.dom (par_iter_map V a) = Poset.cod (par_iter_map V a)"
  by (simp add: par_iter_map_def) 

lemma dom_cod_seq_iter_map : "Poset.dom (seq_iter_map V a) = Poset.cod (seq_iter_map V a)"
  by (simp add: seq_iter_map_def) 

lemma valid_par_iter_map : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V" and a_elem : "x \<in> elems V"
  shows "Poset.valid_map (par_iter_map V x)"
proof (rule Poset.valid_mapI, goal_cases)
  case 1
  then show ?case
    by (metis (mono_tags, lifting) CVA.valid_welldefined PosetMap.select_convs(1) V_valid par_iter_map_def valid_poset valid_semigroup) 
next
  case 2
  then show ?case
    by (metis (mono_tags, lifting) CVA.valid_welldefined PosetMap.select_convs(2) V_valid par_iter_map_def valid_poset valid_semigroup) 
next
  case (3 a b)
  then show ?case 
  proof -
    have "PosetMap.dom (par_iter_map V a) = poset V \<and> PosetMap.cod (par_iter_map V a) = poset V"
      by (simp add: par_iter_map_def) 
    moreover have "a \<in> elems V"
      by (smt (verit) "3" PosetMap.select_convs(3) fst_conv mem_Collect_eq par_iter_map_def) 
    moreover have "b = join V (neut_par V (d x)) (par V x a)"
      by (smt (verit, best) "3" PosetMap.select_convs(3) fst_conv mem_Collect_eq par_iter_map_def snd_eqD) 
    moreover have "b \<in> elems V" using join_el [where ?P="poset V"]
      by (metis CVA.valid_welldefined V_complete V_valid a_elem calculation(2) calculation(3) d_elem_is_open join_elem valid_neut_par_elem valid_par_elem) 
    ultimately show ?thesis
      by (simp add: par_iter_map_def) 
  qed
next
  case (4 a b b')
  then show ?case
    by (smt (verit) Pair_inject PosetMap.simps(3) mem_Collect_eq par_iter_map_def) 
next
  case (5 a)
  then show ?case
    by (smt (verit, ccfv_threshold) PosetMap.select_convs(1) PosetMap.select_convs(3) mem_Collect_eq par_iter_map_def) 
next
  case (6 a a')
  then show ?case  
  proof -
    have "a \<in> elems V \<and> a' \<in> elems V"
      by (metis (mono_tags, lifting) "6"(1) "6"(2) PosetMap.select_convs(1) par_iter_map_def) 
    moreover have "le V a a'"
      by (smt (verit, del_insts) "6"(3) PosetMap.select_convs(1) par_iter_map_def)
    moreover have "el (PosetMap.dom (par_iter_map V x)) = elems V \<and> el (PosetMap.cod (par_iter_map V x)) = elems V"
      by (simp add: par_iter_map_def) 
    moreover have a_el : "a \<in> el (PosetMap.dom (par_iter_map V x)) "
      using "6"(1) by auto                 
    moreover have a'_el : "a' \<in> el (PosetMap.dom (par_iter_map V x)) "
      by (simp add: "6"(2))
    moreover have "par_iter_map V x \<star> a = join V (neut_par V (d x)) (par V x a)" 
      using Poset.fun_app3 [where ?f="par_iter_map V x" and ?a=a] par_iter_map_def [where ?V=V and ?x=x] a_el
      by (smt (z3) PosetMap.select_convs(3) calculation(3) mem_Collect_eq prod.inject the1_equality)
    moreover have "par_iter_map V x \<star> a' = join V (neut_par V (d x)) (par V x a')" 
      using Poset.fun_app3 [where ?f="par_iter_map V x" and ?a=a'] par_iter_map_def [where ?V=V and ?x=x] a'_el
      by (smt (z3) PosetMap.select_convs(3) calculation(3) mem_Collect_eq prod.inject the1_equality) 
    moreover have "le V (par V x a) (par V x a')"
      using V_valid a_elem calculation(1) calculation(2) valid_le_reflexive valid_par_mono by blast 
    moreover have "le V (join V (neut_par V (d x)) (par V x a)) (join V (neut_par V (d x)) (par V x a'))" using join_mono [where ?P="poset V"]
      by (smt (z3) CVA.join_def CVA.valid_welldefined V_complete V_valid a_elem calculation(1) calculation(1) calculation(8) cocomplete d_elem_is_open join_elem valid_le_reflexive valid_neut_par_elem valid_par_elem)
    ultimately show "Poset.le (PosetMap.cod (par_iter_map V x)) (par_iter_map V x \<star> a) (par_iter_map V x \<star> a')"
      by (smt (verit, best) PosetMap.select_convs(2) par_iter_map_def)
  qed
qed

lemma valid_seq_iter_map : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V" and a_elem : "x \<in> elems V"
  shows "Poset.valid_map (seq_iter_map V x)"
proof (rule Poset.valid_mapI, goal_cases)
  case 1
  then show ?case
    by (simp add: CVA.valid_welldefined OVA.valid_welldefined Semigroup.valid_welldefined V_valid seq_iter_map_def valid_map_welldefined_cod)
next
  case 2
  then show ?case
    by (metis (no_types, lifting) PosetMap.select_convs(2) V_complete cocomplete is_cocomplete_def seq_iter_map_def)
next
  case (3 a b)
  then show ?case 
  proof -
    have "PosetMap.dom (seq_iter_map V a) = poset V \<and> PosetMap.cod (seq_iter_map V a) = poset V"
      by (simp add: seq_iter_map_def)
    moreover have "a \<in> elems V"
      by (smt (verit) "3" PosetMap.select_convs(3) fst_conv mem_Collect_eq seq_iter_map_def)
    moreover have "b = join V (neut_seq V (d x)) (seq V x a)"
      by (smt (verit, del_insts) "3" PosetMap.select_convs(3) fst_conv mem_Collect_eq seq_iter_map_def snd_eqD)
    moreover have "b \<in> elems V" using join_el [where ?P="poset V"]
      by (metis CVA.join_def CVA.valid_welldefined V_complete V_valid a_elem calculation(2) calculation(3) cocomplete d_elem_is_open valid_neut_seq_elem valid_seq_elem)
    ultimately show ?thesis
      by (simp add: seq_iter_map_def) 
  qed
next
  case (4 a b b')
  then show ?case
    by (smt (verit, del_insts) Pair_inject PosetMap.simps(3) mem_Collect_eq seq_iter_map_def) 
next
  case (5 a)
  then show ?case
    by (smt (verit, best) PosetMap.select_convs(1) PosetMap.select_convs(3) mem_Collect_eq seq_iter_map_def) 
next
  case (6 a a')
  then show ?case  
  proof -
    have "a \<in> elems V \<and> a' \<in> elems V"
      by (metis (mono_tags, lifting) "6"(1) "6"(2) PosetMap.select_convs(1) seq_iter_map_def)
    moreover have "le V a a'"
      by (smt (verit, del_insts) "6"(2) "6"(3) PosetMap.select_convs(1) calculation seq_iter_map_def)
    moreover have "el (PosetMap.dom (seq_iter_map V x)) = elems V \<and> el (PosetMap.cod (seq_iter_map V x)) = elems V"
      by (simp add: seq_iter_map_def) 
    moreover have a_el : "a \<in> el (PosetMap.dom (seq_iter_map V x)) "
      using "6"(1) by auto                 
    moreover have a'_el : "a' \<in> el (PosetMap.dom (seq_iter_map V x)) "
      by (simp add: "6"(2))
    moreover have "seq_iter_map V x \<star> a = join V (neut_seq V (d x)) (seq V x a)" 
      using Poset.fun_app3 [where ?f="seq_iter_map V x" and ?a=a] seq_iter_map_def [where ?V=V and ?x=x] a_el calculation assms
      by (smt (z3) PosetMap.select_convs(3) mem_Collect_eq prod.inject the1_equality) 
    moreover have "seq_iter_map V x \<star> a' = join V (neut_seq V (d x)) (seq V x a')" 
      using Poset.fun_app3 [where ?f="seq_iter_map V x" and ?a=a'] seq_iter_map_def [where ?V=V and ?x=x] a'_el calculation assms
      by (smt (z3) PosetMap.select_convs(3) mem_Collect_eq prod.inject the1_equality) 
    moreover have "le V (seq V x a) (seq V x a')"
      using V_valid a_elem calculation(1) calculation(2) valid_le_reflexive valid_seq_mono
      by blast 
    moreover have "le V (join V (neut_seq V (d x)) (seq V x a)) (join V (neut_seq V (d x)) (seq V x a'))" using join_mono [where ?P="poset V"]
      by (smt (z3) CVA.join_def CVA.valid_welldefined V_complete V_valid a_elem calculation(1) calculation(8) cocomplete d_elem_is_open join_elem valid_le_reflexive valid_neut_seq_elem valid_seq_elem)
    ultimately show "Poset.le (PosetMap.cod (seq_iter_map V x)) (seq_iter_map V x \<star> a) (seq_iter_map V x \<star> a')"
      by (smt (verit, best) PosetMap.select_convs(2) seq_iter_map_def)
  qed
qed

definition finite_par_iter :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"finite_par_iter V a = lfp (par_iter_map V a)"

definition infinite_par_iter :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"infinite_par_iter V a = gfp (par_iter_map V a)"

definition finite_seq_iter :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"finite_seq_iter V a = lfp (seq_iter_map V a)"
                               
definition infinite_seq_iter :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"infinite_seq_iter V a = gfp (seq_iter_map V a)"

lemma "finite_par_iter_el" : "valid V \<Longrightarrow> is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> finite_par_iter V a \<in> elems V"
  by (smt (verit, ccfv_SIG) CVA.is_complete_def PosetMap.select_convs(1) PosetMap.select_convs(2) finite_par_iter_def lfp_is_el par_iter_map_def valid_par_iter_map) 

lemma "infinite_par_iter" : "valid V \<Longrightarrow> is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> infinite_par_iter V a \<in> elems V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) PosetMap.select_convs(2) cocomplete gfp_is_el infinite_par_iter_def par_iter_map_def valid_par_iter_map) 

lemma "finite_seq_iter_el" : "valid V \<Longrightarrow> is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> finite_seq_iter V a \<in> elems V"
  by (smt (verit, ccfv_SIG) CVA.is_complete_def PosetMap.select_convs(1) PosetMap.select_convs(2) finite_seq_iter_def lfp_is_el seq_iter_map_def valid_seq_iter_map) 

lemma "infinite_seq_iter" : "valid V \<Longrightarrow> is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> infinite_seq_iter V a \<in> elems V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) PosetMap.select_convs(2) cocomplete gfp_is_el infinite_seq_iter_def seq_iter_map_def valid_seq_iter_map) 

lemma skip_le_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V"
shows "le V (neut_seq V (d a)) (finite_seq_iter V a)"
proof -
  define "a_star" where "a_star = finite_seq_iter V a" 
  have "join V (neut_seq V (d a)) (seq V a a_star) = a_star" using lfp_unfold [where ?P="poset V" and ?f="seq_iter_map V a"]
    CVA.is_complete_def Poset.fun_app Poset.valid_map_deterministic V_complete V_valid a_star_def a_el finite_seq_iter_def lfp_is_el  seq_iter_map_def valid_seq_iter_map
    by (smt (z3) PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) fst_conv mem_Collect_eq)
  moreover have "le V (neut_seq V (d a)) (join V (neut_seq V (d a)) (seq V a a_star))"
    by (metis CVA.join_def CVA.valid_welldefined V_complete V_valid a_star_def a_el cocomplete d_elem_is_open finite_seq_iter_el join_greater1 valid_neut_seq_elem valid_seq_elem) 
 ultimately show ?thesis
    using a_star_def by force
qed

lemma id_le_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and a_el : "a \<in> elems V"
shows "le V a (finite_seq_iter V a)"
proof -
  define "a_star" where "a_star = finite_seq_iter V a" 
  moreover have "a_star \<in> elems V" 
    using V_complete V_valid assms(3) calculation finite_seq_iter_el by blast
  have "join V (neut_seq V (d a)) (seq V a a_star) = a_star" using lfp_unfold [where ?P="poset V" and ?f="seq_iter_map V a"]
    CVA.is_complete_def Poset.fun_app Poset.valid_map_deterministic V_complete V_valid a_star_def a_el finite_seq_iter_def lfp_is_el  seq_iter_map_def valid_seq_iter_map
    by (smt (z3) PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) fst_conv mem_Collect_eq)
  moreover have "le V (seq V a a_star) (join V (neut_seq V (d a)) (seq V a a_star))" 
    using a_star_def join_greater2 [where ?P="poset V" and ?a="neut_seq V (d a)"]
    by (metis (no_types, lifting) CVA.is_complete_def CVA.join_def CVA.valid_welldefined PosetMap.select_convs(1) PosetMap.select_convs(2) V_complete V_valid assms(3) cocomplete d_elem_is_open finite_seq_iter_def lfp_is_el seq_iter_map_def valid_neut_seq_elem valid_seq_elem valid_seq_iter_map)
  moreover have "le V (neut_seq V (d a)) a_star"
     using V_complete V_valid a_star_def a_el skip_le_finite_seq_iter by blast 
  moreover have "le V (seq V a (neut_seq V (d a))) (seq V a a_star)"
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_complete V_valid \<open>a_star \<in> CVA.elems V\<close> a_el calculation(4) cocomplete d_elem_is_open is_cocomplete_def valid_monotone valid_neut_seq_elem valid_reflexivity valid_semigroup) 
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid \<open>a_star \<in> CVA.elems V\<close> a_el valid_le_transitive valid_neutral_law_right valid_seq_elem) 
qed

lemma id_le_seq_iter : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V" 
shows "le V a (finite_seq_iter V a)"
  using V_cont V_valid a_el continuous_complete id_le_finite_seq_iter by blast

lemma kleene_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V"
shows "finite_seq_iter V a = sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<in> UNIV}"
proof - 
  define "f_a" where "f_a = seq_iter_map V a"
  have "finite_seq_iter V a = lfp f_a"
    by (simp add: finite_seq_iter_def f_a_def) 
  moreover have "Poset.valid_map f_a"
    using V_cont V_valid a_el f_a_def is_continuous_def valid_seq_iter_map by blast 
  moreover have "(\<And>A. A \<subseteq> elems V \<Longrightarrow> A \<noteq> {} \<Longrightarrow> f_a \<star> Poset.sup (poset V) A = Poset.sup (poset V) {f_a \<star> a |a. a \<in> A})" 
  proof -
    fix A
    assume "A \<subseteq> elems V"
    assume "A \<noteq> {}"
    define "sup_A" where "sup_A = Poset.sup (CVA.poset V) A"
    have "sup_A \<in> elems V"
      using V_cont \<open>A \<subseteq> CVA.elems V\<close> cocomplete is_continuous_def sup_A_def sup_el by blast 
    moreover have "Poset.valid_map f_a \<and> el (PosetMap.dom f_a) = elems V" 
    using V_cont V_valid a_el f_a_def is_continuous_def valid_seq_iter_map
    by (smt (verit, best) PosetMap.select_convs(1) seq_iter_map_def) 
    moreover have "f_a \<star> sup_A \<in> elems V"  using fun_app2 [where ?f=f_a and ?a=sup_A]
      by (smt (verit, ccfv_SIG) PosetMap.select_convs(2) calculation(1) calculation(2) f_a_def seq_iter_map_def) 
    moreover have "f_a \<star> sup_A = join V (neut_seq V (d a)) (seq V a sup_A)" 
      using fun_app3 [where ?f=f_a and ?a=sup_A] sup_A_def f_a_def seq_iter_map_def [where ?V=V and ?x=a]
      by (smt (verit, ccfv_SIG) Poset.fun_app_iff PosetMap.select_convs(3) calculation(1) calculation(2) mem_Collect_eq) 
    moreover have "\<And> u. u \<in> A \<Longrightarrow> f_a \<star> u = join V (neut_seq V (d a)) (seq V a u)" 
      using fun_app3 [where ?f=f_a] sup_A_def f_a_def seq_iter_map_def [where ?V=V and ?x=a]
      using \<open>A \<subseteq> CVA.elems V\<close> by auto 
    moreover have " {f_a \<star> a |a. a \<in> A} = {join V (neut_seq V (d a)) (seq V a u) | u . u \<in> A}"
      using calculation(5) by force 
    moreover have "Poset.sup (poset V) {f_a \<star> a |a. a \<in> A} = sup V {join V (neut_seq V (d a)) (seq V a u) | u . u \<in> A}"
      using sup_def calculation
      by metis
    moreover have 1: "{seq V a u | u . u \<in> A} \<noteq> {}" 
      using \<open>A \<noteq> {}\<close> by blast
    moreover have 2: "{seq V a u |u. u \<in> A} \<subseteq> elems V"
      by (smt (verit) V_valid \<open>A \<subseteq> CVA.elems V\<close> a_el mem_Collect_eq subset_iff valid_seq_elem)
    moreover have 3: " neut_seq V (d a) \<in> elems V"
      by (meson CVA.valid_welldefined V_valid a_el d_elem_is_open valid_neut_seq_elem) 
    moreover have 4: "is_cocomplete (poset V)" using cocomplete [where ?V=V] V_cont is_continuous_def [where ?V=V]
      by blast
    moreover have 5: "{Poset.join (CVA.poset V) (neut_seq V (d a)) u |u. u \<in> {seq V a u |u. u \<in> A}} = {Poset.join (CVA.poset V) (neut_seq V (d a)) (seq V a u) | u . u \<in> A}"
      by blast
    moreover have "join V (neut_seq V (d a)) (sup V {seq V a u | u . u \<in> A}) = sup V {join V (neut_seq V (d a)) (seq V a u) | u . u \<in> A}" 
      unfolding join_def sup_def
      using 5 4 2 1 3 sup_dist_join1 [where ?P="poset V" and ?a="neut_seq V (d a)" and ?U="{seq V a u | u . u \<in> A}"] by simp
    moreover have "join V (neut_seq V (d a)) (sup V {seq V a u | u . u \<in> A}) \<in> elems V"
      by (metis (no_types, lifting) "2" "3" "4" CVA.join_def CVA.sup_def join_el sup_el)
    moreover have "sup V {join V (neut_seq V (d a)) (seq V a u) | u . u \<in> A} \<in> elems V"
      using calculation(13) calculation(14) by presburger 
    moreover have "f_a \<star> Poset.sup (poset V) A = join V (neut_seq V (d a)) (seq V a (Poset.sup (poset V) A))"
      using calculation(4) sup_A_def by blast 
    moreover have "seq V a (sup V A) = sup V {seq V a u | u . u \<in> A}" using V_cont is_continuous_def [where ?V=V]
      using \<open>A \<noteq> {}\<close> \<open>A \<subseteq> CVA.elems V\<close> a_el by blast
    ultimately show "f_a \<star> Poset.sup (poset V) A = Poset.sup (poset V) {f_a \<star> a |a. a \<in> A}" unfolding f_a_def seq_iter_map_def
      by (simp add: CVA.sup_def)
  qed
  moreover have "Poset.is_complete (CVA.poset V)" using V_cont is_continuous_def [where ?V=V]
    using CVA.is_complete_def by auto
  moreover have "Poset.valid_map f_a \<and> PosetMap.dom f_a = CVA.poset V \<and> PosetMap.cod f_a = CVA.poset V"
    by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) PosetMap.select_convs(2) calculation(2) f_a_def seq_iter_map_def) 
  ultimately show ?thesis using kleene_lfp [where ?P="poset V" and ?f=f_a] unfolding f_a_def finite_seq_iter_def sup_def bot_def
    by fastforce
qed

lemma iter_seq_el: 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V" 
shows "iter (seq_iter_map V a) n \<star> bot V \<in> elems V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) V_cont V_valid a_el complete_bot_el continuous_complete dom_cod_seq_iter_map iter_el seq_iter_map_def valid_seq_iter_map)

lemma iter_seq_zero : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V" 
shows "iter (seq_iter_map V a) 0 \<star> bot V = bot V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) V_cont V_valid a_el complete_bot_el continuous_complete iter_zero_app seq_iter_map_def valid_seq_iter_map)

lemma iter_seq_induction : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V" 
shows "iter (seq_iter_map V a) (Suc n) \<star> bot V = join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) n \<star> bot V)))"
proof -
  have "Poset.valid_map (seq_iter_map V a)"
    using V_cont V_valid a_el continuous_complete valid_seq_iter_map by blast
  moreover have "Poset.valid_map (iter (seq_iter_map V a) n)"
    by (simp add: calculation dom_cod_seq_iter_map iter_valid)
  moreover have "(iter (seq_iter_map V a) n \<star> bot V) \<in> elems V"
    by (metis (no_types, lifting) PosetMap.select_convs(1) V_cont calculation(1) complete_bot_el continuous_complete dom_cod_seq_iter_map iter_el seq_iter_map_def)
  moreover have "iter (seq_iter_map V a) (Suc n) \<star> bot V = seq_iter_map V a \<star> ((iter (seq_iter_map V a) n \<star> bot V))"
    using compose_app_assoc [where ?f="seq_iter_map V a" and ?g="iter (seq_iter_map V a) n" and ?a="bot V"]
    by (metis (no_types, lifting) Poset.compose_app_assoc Poset.iter.simps(2) PosetMap.select_convs(1) V_cont calculation(1) calculation(2) cod_iter complete_bot_el continuous_complete dom_cod_seq_iter_map dom_iter seq_iter_map_def)
  moreover have "... = join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) n \<star> bot V)))"
    using seq_iter_map_def [where ?V=V and ?x=a] Poset.fun_app3
    by (smt (z3) Poset.fun_app PosetMap.select_convs(1) PosetMap.select_convs(3) calculation(1) calculation(3) mem_Collect_eq old.prod.inject)
  ultimately show ?thesis
    by presburger 
qed

primrec fiter_seq :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> nat \<Rightarrow> ('A, 'a) Valuation" where
  "fiter_seq V a 0 = neut_seq V (d a)" 
| "fiter_seq V a (Suc n) = seq V a (fiter_seq V a n)"


lemma fiter_seq_elem :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V"
shows "fiter_seq V a n \<in> elems V"
proof (induct_tac n, goal_cases)
  case 1
  then show ?case
    by (metis CVA.valid_welldefined V_valid a_el d_elem_is_open fiter_seq.simps(1) valid_neut_seq_elem) 
next
  case (2 n)
  then show ?case
    by (metis V_valid a_el fiter_seq.simps(2) valid_seq_elem) 
qed

lemma seq_bot :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V"
shows "le V (seq V a (bot V)) a"
  by (metis CVA.valid_welldefined V_cont V_valid a_el continuous_complete d_elem_is_open seq_bot1 valid_neut_seq_elem valid_neutral_law_right) 

(*
lemma fiter_seq_is_finite_seq_iter1 :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and m :: "nat"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V"
shows "le V (sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<le> m}) (sup V {fiter_seq V a n | n . n \<le> m})"
proof (induct_tac m, goal_cases)
  case 1
  then show ?case 
  proof -
    have "sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<le> 0} = bot V"
      using sup_singleton V_cont V_valid a_el iter_seq_zero le_zero_eq singleton_conv
      by (smt (verit, ccfv_SIG) CVA.sup_def Collect_cong continuous_cocomplete iter_seq_el) 
    
    thus ?thesis 
next
  case (2 n)
  then show ?case sorry
qed
*)

(*
lemma fiter_seq_is_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V"
shows "finite_seq_iter V a = sup V {fiter_seq V a n | n . n \<in> UNIV}"
proof -
  have "sup V {fiter_seq V a n | n . n \<in> UNIV} \<in> elems V"
    by (smt (verit, del_insts) Collect_mem_eq Collect_mono_iff V_cont V_valid a_el continuous_complete fiter_seq_elem sup_elem)
  moreover have "sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<in> UNIV} = finite_seq_iter V a"
    using V_cont V_valid a_el kleene_finite_seq_iter by fastforce 
  moreover have "le V (sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<in> UNIV}) (sup V {fiter_seq V a n | n . n \<in> UNIV})" 
  proof -
    have "\<And> n . le V ((iter (seq_iter_map V a) n) \<star> bot V) (sup V {fiter_seq V a n | n . n \<in> UNIV})"
    proof (induct_tac n, goal_cases)
      case (1 n)
      then show ?case
        by (metis (no_types, lifting) CVA.bot_def V_cont V_valid a_el bot_min calculation(1) continuous_cocomplete iter_seq_zero) 
    next
      case (2 n m)
      then show ?case 
      proof -
        have "le V (iter (seq_iter_map V a) m \<star> bot V) (sup V {fiter_seq V a n |n. n \<in> UNIV})"
          using "2" by blast 
        moreover have "\<exists> b . b \<in> {fiter_seq V a n |n. n \<in> UNIV} \<and> le V (iter (seq_iter_map V a) m \<star> bot V) b" 
    qed
    thus ?thesis using sup_is_lub [where ?P="poset V"]
      by (smt (verit) CVA.sup_def V_cont V_valid a_el calculation(1) continuous_cocomplete iter_seq_el mem_Collect_eq subsetI) 
  qed
  moreover have "le V (sup V {fiter_seq V a n | n . n \<in> UNIV}) (sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<in> UNIV})" 
    sorry
  ultimately show ?thesis
    using V_cont V_valid a_el continuous_complete finite_seq_iter_el valid_le_antisymmetric
    by (metis (no_types, lifting))
qed
*)

lemma seq_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V"
shows "seq V (finite_seq_iter V a) (finite_seq_iter V a) = finite_seq_iter V a"
  oops

lemma ka_finite_seq_iter : "todo" oops (* "(a + b)\<^emph> = a\<^emph> \<sqdot> (b \<sqdot> a\<^emph>)\<^emph>" *)

(* b + x \<sqdot> a \<le> x \<Rightarrow> b \<sqdot> a\<^emph> \<le> x *)
lemma star_induction_left :
  fixes V :: "('A, 'a) CVA" and a b x :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" and x_el : "x \<in> elems V"
  and lhs : "le V (join V b (seq V x a)) x"
shows "le V (seq V b (finite_seq_iter V a)) x" using kleene_finite_seq_iter [where ?V=V and ?a=a] 
  oops

(*b + a \<sqdot> x \<le> x \<Rightarrow> a\<^emph> \<sqdot> b \<le> x *) 
lemma star_induction_right :
  fixes V :: "('A, 'a) CVA" and a b x :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" and x_el : "x \<in> elems V"
  and lhs : "le V (join V b (seq V a x)) x"
shows "le V (seq V (finite_seq_iter V a) b) x"  oops


(* Paper results *)

(* [Proposition 1 (1/3), TMCVA] *)
proposition epsilon_le_delta [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V \<epsilon>A \<delta>A"
  by (smt (verit, best) A_open CVA.valid_welldefined V_valid \<delta>A_def \<epsilon>A_def fst_conv neutral_is_element valid_elems valid_neutral_law_left valid_neutral_law_right valid_weak_exchange)

lemma epsilon_par_epsilon_le_epsilon :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V (par V \<epsilon>A \<epsilon>A) \<epsilon>A"
  by (smt (z3) A_open CVA.valid_welldefined V_valid \<epsilon>A_def comb_is_element fst_conv neutral_is_element valid_domain_law valid_elems valid_neutral_law_left valid_neutral_law_right valid_weak_exchange) 

lemma delta_le_delta_seq_delta :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V \<delta>A (seq V \<delta>A \<delta>A)"
  by (smt (z3) A_open CVA.valid_welldefined V_valid \<delta>A_def comb_is_element d_neut neutral_is_element valid_domain_law valid_elems valid_neutral_law_left valid_neutral_law_right valid_weak_exchange)

(* [Proposition 1 (2/3), TMCVA] *)
proposition delta_seq_delta_eq_delta [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A"
  shows "seq V \<delta>A \<delta>A = \<delta>A"
proof -
  have "le V \<delta>A (seq V \<delta>A \<delta>A)" using assms delta_le_delta_seq_delta
    by blast
  moreover have "le V (seq V \<delta>A \<delta>A) \<delta>A" using assms valid_neutral_law_par [where ?V=V and ?A=A]
    by blast
  ultimately show ?thesis using valid_le_antisymmetric
    using A_open V_valid \<delta>A_def valid_neut_par_elem valid_seq_elem by blast
qed

(* [Proposition 1 (3/3), TMCVA] *)
proposition epsilon_par_epsilon_eq_epsilon [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<epsilon>A \<equiv> neut_seq V A"
  shows "par V \<epsilon>A \<epsilon>A = \<epsilon>A"
proof -
  have "le V (par V \<epsilon>A \<epsilon>A) \<epsilon>A" using assms epsilon_par_epsilon_le_epsilon
    by blast
  moreover have "le V \<epsilon>A (par V \<epsilon>A \<epsilon>A)" using assms valid_neutral_law_seq [where ?V=V and ?A=A]
    by blast
  ultimately show ?thesis
    using A_open V_valid \<epsilon>A_def valid_le_antisymmetric valid_neut_seq_elem valid_par_elem by blast
qed

lemma neutral_collapse_strongly_neutral :
  fixes V :: "('A, 'a) CVA"
  assumes V_valid : "valid V"
  and neutral_collapse : "neut_par V = neut_seq V"
shows "is_strongly_neutral (par_algebra V) = is_strongly_neutral (seq_algebra V)"
  by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid fst_conv is_strongly_neutral_def neutral_collapse neutral_is_element valid_ext) 

(* [Proposition 2, TMCVA] *)
proposition comparitor :
  fixes V :: "('A, 'a) CVA" and a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and neutral_collapse : "neut_par V = neut_seq V"
shows "le V (seq V a b) (par V a b)"
proof -
  define "U" where "U = d a \<union> d b"
  define "e" where "e = neut_seq V U"
  have "e = neut_par V U"
    by (metis e_def neutral_collapse)
  moreover have "ext V U a = par V e a" using valid_ext [where ?V=V and ?A=U and ?b=a] ext_def [where ?V="par_algebra V" and ?A=U]
    by (metis CVA.valid_welldefined Prealgebra.valid_space U_def V_valid a_elem b_elem calculation d_elem_is_open sup_ge1 valid_elems valid_prealgebra valid_union2)
  moreover have "ext V U b = par V b e" using valid_ext [where ?V=V and ?A=U and ?b=b] ext_def [where ?V="par_algebra V" and ?A=U]
    by (metis CVA.valid_welldefined Prealgebra.valid_space U_def V_valid a_elem b_elem calculation(1) d_elem_is_open neutral_is_element sup_ge2 valid_elems valid_par_comm valid_prealgebra valid_union2)
  moreover have "ext V U a = seq V a e" using ext_def [where ?V="seq_algebra V" and ?A=U]
    by (smt (verit) CVA.valid_welldefined U_def V_valid a_elem b_elem calculation(1) d_elem_is_open e_def fst_conv ova_comb_local subset_Un_eq sup_ge1 valid_domain_law valid_elems valid_neut_par_elem valid_neutral_law_right valid_par_comm valid_seq_elem)
  moreover have "ext V U b = seq V e b" using ext_def [where ?V="seq_algebra V" and ?A=U]
    by (metis CVA.valid_welldefined OVA.valid_welldefined Prealgebra.valid_space U_def V_valid a_elem b_elem d_elem_is_open e_def sup_ge2 valid_union2)
  moreover have "seq V a b = seq V (ext V U a) (ext V U b)"
    by (metis CVA.valid_welldefined U_def V_valid a_elem b_elem ova_comb_local)
  moreover have " ... = seq V (par V e a) (par V b e)"
    using calculation(2) calculation(3) by presburger 
  moreover have "le V (seq V (par V e a) (par V b e)) (par V (seq V a e) (seq V e b))"
    by (smt (verit) CVA.valid_welldefined U_def V_valid a_elem b_elem calculation(1) calculation(4) d_elem_is_open neutral_is_element valid_domain_law valid_elems valid_par_comm valid_seq_elem valid_weak_exchange)
  moreover have "par V (seq V a e) (seq V e b) = par V (ext V U a) (ext V U b)"
    using calculation(4) calculation(5) by presburger 
  moreover have "... = par V a b"
    by (metis (no_types, lifting) CVA.valid_welldefined U_def Un_upper1 Un_upper2 V_valid a_elem b_elem d_elem_is_open ova_comb_local valid_domain_law valid_ext valid_gc_poset valid_seq_elem)
  ultimately show ?thesis
    by metis
qed

(* Hoare logic rules: https://en.wikipedia.org/wiki/Hoare_logic#Rules 

Ref. [CKA] : Hoare, CAR Tony, et al. "Concurrent kleene algebra." CONCUR 2009-Concurrency Theory: 20th International Conference, CONCUR 2009, Bologna, Italy, September 1-4, 2009. Proceedings 20. Springer Berlin Heidelberg, 2009.
*)
proposition hoare_domain_rule :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V"
  and "hoare V p a q"
shows "d q \<subseteq> d a \<union> d p"
  by (metis CVA.valid_welldefined OVA.valid_le V_valid assms(2) assms(3) assms(4) assms(5) comb_is_element d_comb sup_commute)

proposition hoare_ext_rule1 :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation" and U :: "'A Open"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V" 
  and "hoare V p a q" 
  and "U \<in> opens (space V)" and "d p \<union> d a \<union> d q \<subseteq> U"
shows "hoare V (ext V U p) a (ext V U q)" 
proof -
  have "le V (seq V p a) q"
    using assms(5) by blast 
  moreover have "le V (ext V U (seq V p a)) (ext V U q)" using ext_monotone' [where ?V="seq_algebra V" and ?A=U]
    by (metis (no_types, opaque_lifting) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(6) assms(7) calculation comb_is_element le_sup_iff valid_domain_law)
  moreover have "ext V U (seq V p a) = seq V (ext V U p) (ext V U a)"
    by (meson CVA.valid_welldefined V_valid assms(2) assms(3) assms(6) assms(7) ext_comm' sup.bounded_iff)
  moreover have "... = seq V (ext V U p) a" using ova_comb_local [where ?V="seq_algebra V"]
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid assms(2) assms(3) assms(6) assms(7) d_ext equalityE ext_elem ext_functorial_id inf_sup_aci(6) le_sup_iff subset_antisym)
  moreover have "le V (seq V (ext V U p) a) (ext V U q)"
    using calculation(2) calculation(3) calculation(4) by force
  ultimately show ?thesis
    by simp
qed    

proposition hoare_ext_rule2 :
  fixes V :: "('A, 'a) CVA" and p b q :: "('A,'a) Valuation" and A :: "'A Open"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "b \<in> elems V" and "q \<in> elems V" 
  and "hoare V p b q" 
  and "A \<in> opens (space V)" and "d b \<subseteq> A"
shows "hoare V p (ext V A b) q" 
proof -
  have "le V (ext V A b) b"
    by (meson CVA.valid_welldefined V_valid assms(3) assms(6) assms(7) ext_le_id) 
  moreover have "le V (seq V p (ext V A b)) (seq V p b)"
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid assms(2) assms(3) assms(6) assms(7) calculation ext_elem valid_comb_monotone valid_le_reflexive) 
  ultimately show ?thesis
    by (smt (verit, best) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) comb_is_element ext_elem valid_poset valid_semigroup valid_transitivity)
qed

proposition hoare_res_rule1 :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation" and P Q :: "'A Open"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V" 
  and "hoare V (res V P p) a q" 
  and "P \<in> opens (space V)" and "P \<subseteq> d p"
  and "Q \<in> opens (space V)" and "Q \<subseteq> d q"
shows "hoare V p a (res V Q q)"
  by (smt (verit, del_insts) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) comb_is_element id_le_res res_elem valid_comb_monotone valid_le_reflexive valid_poset valid_semigroup valid_transitivity)

proposition hoare_res_rule2 :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation" and B :: "'A Open"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V" 
  and "hoare V p (res V B a) q" 
  and "B \<in> opens (space V)" and "B \<subseteq> d a"
shows "hoare V p a q"
  by (smt (verit, ccfv_SIG) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) comb_is_element id_le_res res_elem valid_le_reflexive valid_le_transitive valid_monotone valid_semigroup)

proposition hoare_res_rule3 :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V"
   and "d p \<subseteq> d q"
  and "hoare V p a q" 
shows "hoare V p (res V (d p \<inter> d a) a) (res V (d p) q)" 
proof -
  have "le V (seq V p a) q"
    using assms(6) by force 
  then have "le V (res V (d p) (seq V p a)) (res V (d p) q)"
    by (smt (verit, del_insts) CVA.valid_welldefined OVA.valid_le V_valid assms(2) assms(3) assms(4) assms(5) d_elem_is_open d_res id_le_res res_elem res_monotone' valid_le_transitive valid_seq_elem)
  moreover have "res V (d p) (seq V p a) = seq V p (res V (d p \<inter> d a) a)"
    by (meson CVA.valid_welldefined V_valid assms(2) assms(3) valid_comb_law_left)
  moreover have "le V (seq V p (res V (d p \<inter> d a) a)) (res V (d p) q)"
    using calculation(1) calculation(2) by auto
  ultimately show ?thesis
    by meson
qed

proposition hoare_res_rule4 :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V"
   and "d a \<subseteq> d q"
  and "hoare V p a q" 
shows "hoare V (res V (d p \<inter> d a) p) a (res V (d a) q)" 
proof -
  have "le V (seq V p a) q"
    using assms(6) by force 
  then have "le V (res V (d a) (seq V p a)) (res V (d a) q)"
    by (smt (verit, del_insts) CVA.valid_welldefined OVA.valid_le V_valid assms(2) assms(3) assms(4) assms(5) d_elem_is_open d_res id_le_res res_elem res_monotone' valid_le_transitive valid_seq_elem)
  moreover have "res V (d a) (seq V p a) = seq V (res V (d p \<inter> d a) p) a"
    by (meson CVA.valid_welldefined V_valid assms(2) assms(3) valid_comb_law_right)
  moreover have "le V (seq V (res V (d p \<inter> d a) p) a) (res V (d a) q)"
    using calculation(1) calculation(2) by auto
  ultimately show ?thesis
    by meson
qed

proposition hoare_res_rule5 :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "a \<in> elems V" and "q \<in> elems V"
   and "d p \<inter> d a \<subseteq> d q"
  and "hoare V p a q" 
shows "hoare V (res V (d p \<inter> d a) p) (res V (d p \<inter> d a) a) (res V (d p \<inter> d a) q)" 
proof -
  define "U" where "U = d p \<inter> d a" 
  have "U \<in> opens (space V) \<and> U \<subseteq> d q \<and> U \<subseteq> d (seq V p a)"
    by (smt (verit, best) CVA.valid_welldefined OVA.valid_le Prealgebra.valid_space U_def V_valid assms(2) assms(3) assms(4) assms(5) assms(6) d_elem_is_open order.trans valid_inter valid_prealgebra valid_seq_elem)
  moreover have "le V (seq V p a) q"
     using assms(6) by force
  moreover have "le V (res V U (seq V p a)) (res V U q)" using U_def
    by (metis CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) calculation(1) calculation(2) res_monotone' valid_seq_elem) 
  moreover have "res V U (seq V p a) = seq V (res V U p) (res V U a)"
    by (metis CVA.valid_welldefined U_def V_valid assms(2) assms(3) res_comm)
  moreover have "le V (seq V (res V U p) (res V U a)) (res V U q)"
    using calculation(3) calculation(4) by auto
  ultimately show ?thesis
    using U_def by fastforce
qed


(* [CKA, Lemma 5.2.1] *)
proposition hoare_neut_seq_rule :
  fixes V :: "('A, 'a) CVA" and p q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "q \<in> elems V"
  shows "hoare V p (neut_seq V (d p)) q = le V p q"
  by (metis CVA.valid_welldefined V_valid assms(2) valid_neutral_law_right) 

(* [CKA, Lemma 5.2.1] (special form) *)
proposition hoare_neut_seq_rule' :
  fixes V :: "('A, 'a) CVA" and p:: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V"
  shows "hoare V p (neut_seq V (d p)) p"
  using V_valid assms(2) hoare_neut_seq_rule valid_le_reflexive by blast

(* [CKA, Lemma 5.2.2] *)
proposition hoare_antitony_rule :
  fixes V :: "('A, 'a) CVA" and a b:: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and  "a \<in> elems V" and "b \<in> elems V"
  and "d b \<subseteq> d a"
  shows "(\<forall> p \<in> elems V . \<forall>  q \<in> elems V . hoare V p b q \<longrightarrow> hoare V p a q) = le V a b"
proof (rule iffI[rotated], goal_cases)
  case 1
  then show ?case 
by (smt (verit) V_valid assms(2) assms(3) valid_le_reflexive valid_le_transitive valid_seq_elem valid_seq_mono)
next
  case 2
  then show ?case
  proof -
    have "\<forall> p \<in> elems V . \<forall>  q \<in> elems V . hoare V p b q \<longrightarrow> hoare V p a q"
      using "2" by blast 
    then have "hoare V (neut_seq V (d b)) b b \<longrightarrow> hoare V (neut_seq V (d b)) a b"
      by (metis CVA.valid_welldefined V_valid assms(3) d_elem_is_open valid_neut_seq_elem) 
    then have "hoare V (neut_seq V (d b)) a b"
      by (metis CVA.valid_welldefined V_valid assms(3) valid_le_reflexive valid_neutral_law_left) 
    moreover have "le V (neut_seq V (d a)) (neut_seq V (d b))" 
      using neut_le_neut [where ?V="seq_algebra V" and ?B="d b" and ?A="d a"]
      by (meson CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) d_elem_is_open)
    moreover have "hoare V (neut_seq V (d a)) a b"
      by (smt (verit, del_insts) "2" CVA.valid_welldefined V_valid assms(2) assms(3) calculation(2) d_elem_is_open valid_le_reflexive valid_neut_seq_elem valid_neutral_law_left valid_seq_mono)
    ultimately show ?thesis
      by (metis CVA.valid_welldefined V_valid assms(2) valid_neutral_law_left)
    qed
  qed

(* [CKA, Lemma 5.2.3] *)
proposition hoare_extensionality_rule :
  fixes V :: "('A, 'a) CVA" and a b:: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and  "a \<in> elems V" and "b \<in> elems V"
  and "d a = d b"
  shows "(\<forall> p \<in> elems V . \<forall>  q \<in> elems V . hoare V p a q = hoare V p b q) = (a = b)"
  by (smt (verit) V_valid assms(2) assms(3) assms(4) hoare_antitony_rule set_eq_subset valid_le_antisymmetric)

(* [CKA, Lemma 5.2.4] *)
proposition hoare_sequential_rule :
  fixes V :: "('A, 'a) CVA" and p r a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "r \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
shows "(\<exists> q \<in> elems V . hoare V p a q \<and> hoare V q b r) = hoare V p (seq V a b) r"
proof (rule iffI, goal_cases)
  case 1
  then show ?case
    by (smt (verit) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) comb_is_element hoare_neut_seq_rule hoare_neut_seq_rule' valid_comb_associative valid_comb_monotone valid_poset valid_semigroup valid_transitivity)
next
  case 2
  then show ?case
    by (metis CVA.valid_welldefined V_valid assms(2) assms(4) assms(5) valid_comb_associative valid_le_reflexive valid_seq_elem) 
qed

(* [CKA, Lemma 5.2.4] (special form) *)
proposition hoare_sequential_rule' :
  fixes V :: "('A, 'a) CVA" and p q r a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "q \<in> elems V" and "r \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
  and "hoare V p a q" and "hoare V q b r"
shows "hoare V p (seq V a b) r"
  using V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) hoare_sequential_rule by blast

(* [CKA, Lemma 5.2.5] *)
proposition hoare_weakening_rule :
  fixes V :: "('A, 'a) CVA" and p p' q q' a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "p' \<in> elems V" and "q \<in> elems V" and "q' \<in> elems V" and "a \<in> elems V"
  and "le V p' p" and "le V q q'" and "hoare V p a q"
shows "hoare V p' a q'"
  by (smt (verit) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) comb_is_element valid_gc_poset valid_monotone valid_poset valid_reflexivity valid_semigroup valid_transitivity)  

(* [CKA, Lemma 5.2.6] *)
proposition hoare_failure_rule :
  fixes V :: "('A, 'a) CVA" and p q :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_quantalic : "is_continuous V"
  and seq_right_strict : "\<forall> a \<in> elems V . seq V a (bot V) = bot V"
  and "p \<in> elems V" and "q \<in> elems V"
shows "hoare V p (bot V) q"
  by (metis CVA.bot_def V_quantalic assms(4) assms(5) bot_min cocomplete continuous_complete seq_right_strict) 

(* [CKA, Lemma 5.2.7] *)
proposition hoare_choice_rule :
  fixes V :: "('A, 'a) CVA" and p q a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and "p \<in> elems V" and "q \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
shows "hoare V p (join V a b) q = (hoare V p a q \<and> hoare V p b q)" 
proof (rule iffI, goal_cases)
  case 1
  then show ?case 
  proof -
    have "le V (seq V p (join V a b)) q"
      using "1" by blast 
    moreover have "seq V p (join V a b) = join V (seq V p a) (seq V p b)"
      using V_cont V_valid assms(3) assms(5) assms(6) binary_continuous by blast 
    moreover have "seq V p a \<in> elems V \<and> seq V p b \<in> elems V"
      using V_valid assms(3) assms(5) assms(6) valid_seq_elem by blast
    moreover have "le V (seq V p a) (seq V p (join V a b)) \<and> le V (seq V p b) (seq V p (join V a b))" 
      using join_greater [where ?P="poset V" and ?a="seq V p a" and ?b="seq V p b"]
      by (metis (no_types, opaque_lifting) CVA.join_def V_cont calculation(2) calculation(3) cocomplete is_continuous_def) 
    moreover have "le V (seq V p a) q \<and> le V (seq V p b) q"
      by (smt (verit, best) "1" V_cont V_valid assms(4) calculation(2) calculation(3) calculation(4) is_continuous_def join_elem valid_le_transitive)
    ultimately show ?thesis
      by force
  qed
next
  case 2
  then show ?case
    by (smt (z3) CVA.join_def V_cont V_valid assms(3) assms(4) assms(5) assms(6) binary_continuous cocomplete is_continuous_def join_property valid_seq_elem)
qed

(* [CKA, Lemma 5.2.8] *)
proposition hoare_iteration_rule : 
  fixes V :: "('A, 'a) CVA" and p a:: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and p_el : "p \<in> elems V" and a_el : "a \<in> elems V"
  and dp_le_da : "d p \<subseteq> d a"
shows "hoare V p a p = hoare V p (finite_seq_iter V a) p"
proof (rule iffI, goal_cases)
  define "U" where "U = {((iter (seq_iter_map V a) n) \<star> (bot V)) | n . n \<in> UNIV} "
  define "pU" where "pU = {seq V p ((iter (seq_iter_map V a) n) \<star> (bot V)) | n . n \<in> UNIV}"
  case 1
  then show ?case 
  proof -
    assume "le V (seq V p a) p"
  have "finite_seq_iter V a = sup V U" using kleene_finite_seq_iter [where ?V=V and ?a=a] U_def
    using V_cont V_valid a_el by blast
  moreover have "Poset.valid_map (seq_iter_map V a)" using valid_seq_iter_map [where ?V=V and ?x=a] using V_valid V_cont
    using a_el continuous_complete by blast
  moreover have "\<And> n . ((iter (seq_iter_map V a) n) \<star> (bot V)) \<in> elems V" using iter_el
    by (metis (no_types, lifting) PosetMap.select_convs(1) PosetMap.select_convs(2) V_cont calculation(2) complete_bot_el continuous_complete seq_iter_map_def)
  moreover have "\<And> n . seq V p ((iter (seq_iter_map V a) n) \<star> (bot V)) \<in> elems V"
    using V_valid calculation(3) p_el valid_seq_elem by blast   

  moreover have "\<And> n . le V (seq V p ((iter (seq_iter_map V a) n) \<star> (bot V))) p" 
  proof -
    fix n
    show "le V (seq V p ((iter (seq_iter_map V a) n) \<star> (bot V))) p"
    proof (induct_tac n, goal_cases)
      case 1
      then show ?case
        by (smt (verit, best) V_cont V_valid \<open>hoare V p a p\<close> a_el calculation(3) continuous_complete iter_seq_zero p_el seq_bot1 valid_le_transitive valid_seq_elem) 
    next
      case (2 n)
      then show ?case 
      proof -
        assume "hoare V p (iter (seq_iter_map V a) n \<star> bot V) p"
        then have "le V (seq V p (iter (seq_iter_map V a) n \<star> bot V)) p"
          by meson 
        moreover have "Poset.valid_map (seq_iter_map V a)"
          by (simp add: \<open>Poset.valid_map (seq_iter_map V a)\<close>)
        moreover have "Poset.valid_map (iter (seq_iter_map V a) n)"
          by (metis (no_types, lifting) PosetMap.simps(1) PosetMap.simps(2) calculation(2) iter_valid seq_iter_map_def)
        moreover have "(iter (seq_iter_map V a) n \<star> bot V) \<in> elems V"
          using \<open>\<And>n. iter (seq_iter_map V a) n \<star> CVA.bot V \<in> CVA.elems V\<close> by blast
        moreover have "iter (seq_iter_map V a) (Suc n) \<star> bot V  = join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) n \<star> bot V)))"
          using V_cont V_valid a_el iter_seq_induction by blast
        moreover have "seq V p (neut_seq V (d a)) = ext V (d a) p" using ext_symmetric_seq
          by (metis CVA.valid_welldefined V_valid a_el d_elem_is_open dp_le_da p_el)         
        moreover have "le V ( ext V (d a) p) p" using ext_le_id
          by (metis CVA.valid_welldefined V_valid a_el d_elem_is_open dp_le_da p_el)
        moreover have 0: "hoare V p (neut_seq V (d a)) p"
          using calculation(6) calculation(7) by presburger
        moreover have 1: "hoare V p (seq V a ((iter (seq_iter_map V a) n \<star> bot V))) p"
          using "1" "2" V_valid a_el calculation(4) hoare_sequential_rule' p_el by blast
        moreover have "le V (seq V p (join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) n \<star> bot V))))) p " 
          using 0 1 hoare_choice_rule [where ?V=V and ?p=p and ?q=p and ?a="neut_seq V (d a)" and ?b="seq V a ((iter (seq_iter_map V a) n \<star> bot V))"]
          by (smt (verit, best) CVA.valid_welldefined V_cont V_valid a_el calculation(4) d_elem_is_open p_el valid_neut_seq_elem valid_seq_elem)
        ultimately show "hoare V p (iter (seq_iter_map V a) (Suc n) \<star> bot V) p"
          by presburger 
    qed
  qed
  qed
  moreover have "pU \<subseteq> elems V"
    using pU_def calculation(4) by fastforce 
  moreover have "le V (sup V pU) p" 
    using sup_is_lub [where ?P="poset V" and ?z=p and ?U=pU] pU_def
    by (smt (z3) CVA.sup_def V_cont calculation(5) calculation(6) cocomplete continuous_complete mem_Collect_eq p_el)
  moreover have "U \<noteq> {}"
    using U_def by blast
  moreover have 0 : "pU = {seq V p u |u. u \<in> U}" unfolding U_def pU_def 
    by blast
  moreover have 00: "sup V pU = sup V {seq V p u |u. u \<in> U}"
    using "0" by auto
  moreover have "seq V p (sup V U) = sup V pU " 
    using U_def pU_def 00 V_cont continuous_complete [where ?V=V] is_continuous_def [where ?V=V]
    by (smt (z3) Collect_cong calculation(3) calculation(8) mem_Collect_eq p_el subsetI)
  moreover have "sup V { seq V p ((iter (seq_iter_map V a) n) \<star> (bot V)) | n . n \<in> UNIV} = seq V p (finite_seq_iter V a)" 
    using calculation(1) calculation(11) pU_def by presburger
  ultimately show "le V (seq V p (finite_seq_iter V a)) p"
    by force 
qed
next
  case 2
  then show ?case
    by (smt (verit) V_cont V_valid p_el a_el finite_seq_iter_el hoare_weakening_rule hoare_neut_seq_rule hoare_neut_seq_rule' id_le_finite_seq_iter is_continuous_def valid_seq_elem valid_seq_mono) 
qed

(* [CKA, Lemma 5.3] *)
proposition hoare_premise_rule :
  fixes V :: "('A, 'a) CVA" and a b c:: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "a \<in> elems V" and "b \<in> elems V" and "c \<in> elems V"
  and "d a \<union> d b \<subseteq> d c"
shows "(\<forall> p \<in> elems V . \<forall>  q \<in> elems V . \<forall>  r \<in> elems V . (hoare V p a q \<and> hoare V q b r \<longrightarrow> hoare V p c r)) = le V c (seq V a b)"
proof (rule iffI, goal_cases)
  case 1
  then show ?case 
  proof -
    have "\<forall>p\<in>elems V. \<forall>q\<in>elems V. \<forall>r\<in>elems V. hoare V p a q \<and> hoare V q b r \<longrightarrow> hoare V p c r"
      using "1" by fastforce 
    then have "\<forall>p\<in>elems V. \<forall>r\<in>elems V. hoare V p (seq V a b) r \<longrightarrow> hoare V p c r"
      using V_valid assms(2) assms(3) hoare_sequential_rule by blast
    then have "le V c (seq V a b)" 
      using hoare_antitony_rule [where ?V=V and ?b="seq V a b" and ?a=c] assms
      by (smt (z3) CVA.valid_welldefined d_elem_is_open d_neut dual_order.refl neutral_is_element valid_domain_law valid_neutral_law_right valid_seq_elem)
    thus ?thesis
      by force 
  qed
next
  case 2
  then show ?case
  proof - 
    have "le V c (seq V a b) \<and> seq V a b \<in> elems V"
      using "2" V_valid assms(2) assms(3) valid_seq_elem by blast
    then have "\<forall>p\<in>elems V. \<forall>r\<in>elems V. hoare V p (seq V a b) r \<longrightarrow> hoare V p c r" 
      using hoare_antitony_rule [where ?V=V and ?b="seq V a b" and ?a=c]
      using CVA.valid_welldefined V_valid assms(4) by blast
    then have "\<forall>p\<in>elems V. \<forall>q\<in>elems V. \<forall>r\<in>elems V. hoare V p a q \<and> hoare V q b r \<longrightarrow> hoare V p c r" 
      using hoare_sequential_rule [where ?V=V and ?a=a and ?b=b]
      using V_valid assms(2) assms(3) by blast
    thus ?thesis
      by force
  qed
qed

(* [Proposition 3, TMCVA], [CKA, Lemma 5.4.1] *)
proposition hoare_concurrency_rule :
  fixes V :: "('A, 'a) CVA" and p p' a a' q q' :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "p' \<in> elems V" and "a \<in> elems V" and "a' \<in> elems V" and "q \<in> elems V" and "q' \<in> elems V"
  and "hoare V p a q" and "hoare V p' a' q'"
  shows "hoare V (par V p p') (par V a a') (par V q q')"
proof -
  define "gl" (infixl \<open>\<preceq>\<close> 54) where "a \<preceq> b = le V a b" for a b
  define "sc" (infixl \<open>\<Zsemi>\<close> 55) where "a \<Zsemi> b = seq V a b" for a b
  define "pc" (infixl \<open>\<parallel>\<close> 55) where "a \<parallel> b = par V a b" for a b

  have "p \<Zsemi> a \<preceq> q"
    using assms(8) gl_def sc_def
    by simp 
  moreover have "p' \<Zsemi> a' \<preceq> q'"
    using assms(9) gl_def sc_def by simp 
  moreover have ab: "(p \<parallel> p') \<Zsemi> (a \<parallel> a') \<preceq> (p \<Zsemi> a) \<parallel> (p' \<Zsemi> a')" 
    using V_valid assms(2) assms(3) assms(4) assms(5) gl_def pc_def sc_def valid_weak_exchange
    by (metis (no_types, lifting)) 
  moreover have els:  "(p \<parallel> p') \<Zsemi> (a \<parallel> a') \<in> elems V \<and>
    (p \<Zsemi> a) \<parallel> (p' \<Zsemi> a') \<in> elems V \<and>
    q \<parallel> q' \<in> elems V"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) pc_def sc_def valid_par_elem valid_seq_elem) 
  moreover have bc: "(p \<Zsemi> a) \<parallel> (p' \<Zsemi> a') \<preceq> q \<parallel> q'"
    by (smt (verit, ccfv_threshold) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) gl_def pc_def sc_def valid_par_mono valid_seq_elem)
  moreover have "p \<parallel> p' \<Zsemi> (a \<parallel> a') \<in> CVA.elems V \<and>
    p \<Zsemi> a \<parallel> (p' \<Zsemi> a') \<in> CVA.elems V \<and>
    q \<parallel> q' \<in> CVA.elems V \<and>
    CVA.le V (p \<parallel> p' \<Zsemi> (a \<parallel> a')) (p \<Zsemi> a \<parallel> (p' \<Zsemi> a')) \<and> CVA.le V (p \<Zsemi> a \<parallel> (p' \<Zsemi> a')) (q \<parallel> q')"
    using ab bc els gl_def by blast 
  moreover have "(p \<parallel> p' \<Zsemi> (a \<parallel> a')) \<preceq> (q \<parallel> q')"
    using V_valid calculation(6) valid_le_transitive gl_def by blast
  ultimately show ?thesis
    by (simp add: \<open>(\<preceq>) \<equiv> CVA.le V\<close> pc_def sc_def)
qed

(* See https://en.wikipedia.org/wiki/Separation_logic#Reasoning_about_programs:_triples_and_proof_rules 
 where there is an additional condition mod(a) \<inter> fv(f) = \<emptyset> *)
(* [CKA, Lemma 5.4.2] *)
proposition hoare_frame_rule :
  fixes V :: "('A, 'a) CVA" and p f a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "f \<in> elems V" and "a \<in> elems V" and "q \<in> elems V" 
  and "hoare V p a q" 
  and frame : "res V (d f) a = neut_seq V (d f)"  (* c.f. mod(a) \<inter> fv(f) = \<emptyset> *)
  and idempotence : "par V (res V (d f) a) a = a" (* c.f. idempotence in valuation algebras *)
shows "hoare V (par V f p) a (par V f q)" 
proof - 
  have "seq V (par V f p) a = seq V (par V f p) (par V (res V (d f) a) a)"
    using idempotence by auto
  moreover have "le V (...) (par V (seq V f (res V (d f) a)) (seq V p a))" 
    using valid_weak_exchange [where ?V=V and ?a1.0=f and ?a2.0=p and ?a3.0="res V (d f) a" and ?a4.0=a]
    by (metis CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) d_elem_is_open frame valid_neut_seq_elem)
  moreover have "par V (seq V f (res V (d f) a)) (seq V p a) = par V f (seq V p a)"
    by (metis CVA.valid_welldefined V_valid assms(3) frame valid_neutral_law_right) 
  moreover have "le V (...) (par V f q)"
    by (smt (verit, del_insts) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) valid_le_reflexive valid_par_mono valid_seq_elem) 
  ultimately show ?thesis
    by (smt (z3) V_valid assms(2) assms(3) assms(4) assms(5) valid_le_transitive valid_par_elem valid_seq_elem)
qed

(* Rely-guarantee CVAs

[RGR] 1. van Staden, Stephan. "On rely-guarantee reasoning." Mathematics of Program Construction: 12th International Conference, MPC 2015, Königswinter, Germany, June 29--July 1, 2015. Proceedings 12. Springer International Publishing, 2015.
[CKA] 2. Hoare, CAR Tony, et al. "Concurrent kleene algebra." CONCUR 2009-Concurrency Theory: 20th International Conference, CONCUR 2009, Bologna, Italy, September 1-4, 2009. Proceedings 20. Springer Berlin Heidelberg, 2009.
[CKA11] 3. Hoare, Tony, et al. "Concurrent Kleene algebra and its foundations." The Journal of Logic and Algebraic Programming 80.6 (2011): 266-296. 

*)

(* Invariants 

See Thms 6.4, 6.5, Lem. 6.6 of [CKA].
*)

lemma inv_dist_le : "valid V \<Longrightarrow> i \<in> elems V \<Longrightarrow> invariant V i \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow>  le V (par V i (seq V a b)) (seq V (par V i a) (par V i b))"
  using invariant_def by blast 

lemma inv_dist : "valid V \<Longrightarrow> i \<in> elems V \<Longrightarrow> invariant V i \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> par V i (seq V a b) = seq V (par V i a) (par V i b)"
  by (smt (verit) inv_dist_le invariant_def valid_le_antisymmetric valid_par_elem valid_seq_elem valid_weak_exchange)

lemma inv_neut_seq : "valid V \<Longrightarrow> i \<in> elems V \<Longrightarrow> invariant V i \<Longrightarrow> le V (neut_seq V (d i)) i"
  using invariant_def by blast 

lemma inv_idem_par : "valid V \<Longrightarrow> i \<in> elems V \<Longrightarrow> invariant V i \<Longrightarrow> par V i i = i"
  using invariant_def by blast 

lemma inv_idem_seq : "valid V \<Longrightarrow> i \<in> elems V \<Longrightarrow> invariant V i \<Longrightarrow> seq V i i = i"
  using invariant_def by blast 

lemma inv_par_neut_seq_le_id : "valid V \<Longrightarrow> i \<in> elems V \<Longrightarrow> invariant V i \<Longrightarrow> le V (par V (neut_seq V (d i)) i) i"
  by (smt (verit) CVA.valid_welldefined d_elem_is_open invariant_def neutral_is_element valid_par_mono)

lemma inv_id_le_seq1 :
  fixes V :: "('A, 'a) CVA" and i a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i"and a_el : "a \<in> elems V" 
  and di_eq_da : "d i = d a"
shows "le V a (seq V a i)"
proof - 
  have "a = seq V a (neut_seq V (d a))"
    by (metis CVA.valid_welldefined V_valid a_el valid_neutral_law_right) 
  moreover have "le V (neut_seq V (d a)) i"
    by (smt (verit, best) di_eq_da inv_i invariant_def) 
  ultimately show ?thesis
    by (smt (verit, best) CVA.valid_welldefined V_valid a_el d_elem_is_open i_el valid_le_reflexive valid_neut_seq_elem valid_seq_mono) 
qed

lemma inv_id_le_seq2 :
  fixes V :: "('A, 'a) CVA" and r a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i" and a_el : "a \<in> elems V" 
  and di_eq_da : "d i = d a"
shows "le V a (seq V i a)"
proof - 
  have "a = seq V (neut_seq V (d a)) a"
    by (metis CVA.valid_welldefined V_valid a_el valid_neutral_law_left)
  moreover have "le V (neut_seq V (d a)) i"
    by (smt (verit, best) di_eq_da inv_i invariant_def) 
  ultimately show ?thesis
    by (smt (verit, best) CVA.valid_welldefined V_valid a_el d_elem_is_open i_el valid_le_reflexive valid_neut_seq_elem valid_seq_mono) 
qed

lemma inv_dist_par1 :
  fixes V :: "('A, 'a) CVA" and i a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and i_el : "r \<in> elems V" and inv_i : "invariant V r" and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" 
  and di_eq_da_eq_db : "d i = d a \<and> d i = d b"
shows "le V (seq V r (par V a b)) (par V (seq V r a) (seq V r b))"
  by (smt (verit) V_valid a_el b_el inv_i invariant_def i_el valid_weak_exchange) 

lemma inv_dist_par2 :
  fixes V :: "('A, 'a) CVA" and i a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and i_el : "r \<in> elems V" and inv_i : "invariant V r" and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" 
  and di_eq_da_eq_db : "d i = d a \<and> d i = d b"
shows "le V (seq V (par V a b) r) (par V (seq V a r) (seq V b r))"
  by (smt (verit) V_valid a_el b_el inv_i invariant_def i_el valid_weak_exchange)

lemma inv_iter :
  fixes V :: "('A, 'a) CVA" and i:: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i" 
shows "invariant V (finite_seq_iter V i)" 
  oops

lemma inv_iter_le :
  fixes V :: "('A, 'a) CVA" and a i :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i"  and a_el : "a \<in> elems V"
  and a_le_i : "le V a i"
shows "le V (finite_seq_iter V a) i" 
proof -
  define "U" where "U = {iter (seq_iter_map V a) n \<star> CVA.bot V |n. n \<in> UNIV}"
  then have "finite_seq_iter V a = sup V U"
    using V_cont V_valid a_el kleene_finite_seq_iter by blast
  moreover have "\<And> n . le V ( (iter (seq_iter_map V a) n) \<star> (bot V)) i" 
    proof (induct_tac n, goal_cases)
      case (1 n)
      then show ?case
        by (metis CVA.bot_def V_cont V_valid a_el bot_min cocomplete continuous_complete i_el iter_seq_zero) 
    next
      case (2 n m)
      then show ?case 
      proof -
        have "iter (seq_iter_map V a) (Suc m) \<star> bot V = join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) m \<star> bot V)))" 
          using iter_seq_induction [where ?V=V and ?n=m and ?a=a] V_cont V_valid a_el by fastforce 
        moreover have "d i \<subseteq> d a"
          using CVA.valid_welldefined V_valid a_el a_le_i i_el by blast
        moreover have "le V (neut_seq V (d a)) (neut_seq V (d i))" using neut_le_neut 
          by (metis CVA.valid_welldefined V_valid a_el d_elem_is_open i_el calculation(2))
        moreover have "le V (neut_seq V (d a)) i"
          by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid a_el calculation(3) d_elem_is_open i_el inv_i inv_neut_seq valid_le_transitive valid_neut_seq_elem)
        moreover have "le V ((iter (seq_iter_map V a) m \<star> bot V)) i"
          using "2" by blast
        moreover have "le V (seq V a ((iter (seq_iter_map V a) m \<star> bot V))) (seq V a i)" using valid_seq_mono iter_seq_el
          using "2" V_cont V_valid a_el i_el valid_le_reflexive by blast
        moreover have "le V (seq V a i) i"
          by (smt (verit, del_insts) V_valid a_el a_le_i i_el inv_i inv_idem_seq valid_le_reflexive valid_seq_mono)
        moreover have "le V (seq V a ((iter (seq_iter_map V a) m \<star> bot V))) i"
          by (smt (verit, ccfv_threshold) V_cont V_valid a_el calculation(7) calculation(6) i_el iter_seq_el valid_le_transitive valid_seq_elem) 
        moreover have "le V (join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) m \<star> bot V)))) i"
          by (smt (verit, del_insts) CVA.join_def CVA.valid_welldefined V_cont V_valid a_el calculation(4) calculation(8) cocomplete continuous_complete d_elem_is_open i_el iter_seq_el join_property neutral_is_element valid_seq_elem)
        ultimately show ?thesis
          by presburger 
      qed
    qed
    moreover have "U \<subseteq> CVA.elems V " using U_def
      by (smt (verit) PosetMap.select_convs(1) PosetMap.select_convs(2) V_cont V_valid a_el complete_bot_el continuous_complete iter_el mem_Collect_eq seq_iter_map_def subsetI valid_seq_iter_map) 
    moreover have "le V (sup V U) i"
      unfolding sup_def
      using sup_is_lub [where ?P="poset V" and ?U="U" and ?z=i] U_def
      using V_cont calculation(2) calculation(3) cocomplete continuous_complete i_el by blast
    ultimately show ?thesis
      by presburger 
  qed

lemma inv_par_le_par_iter :
  fixes V :: "('A, 'a) CVA" and a a' i i' :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i"  and a_el : "a \<in> elems V"
  and i'_el : "i' \<in> elems V" and inv_i' : "invariant V i'"  and a'_el : "a' \<in> elems V"
  and a_le_i : "le V a i" and a'_le_i' : "le V a' i'"
shows "le V (par V a a') (par V (finite_seq_iter V i) (finite_seq_iter V i'))" 
proof -
  have "le V a (finite_seq_iter V i)"
    by (smt (verit, del_insts) V_cont V_valid a_el a_le_i continuous_complete finite_seq_iter_el i_el id_le_seq_iter valid_le_transitive)
  moreover have "le V a' (finite_seq_iter V i')"
    by (smt (verit, del_insts) V_cont V_valid a'_el a'_le_i' continuous_complete finite_seq_iter_el i'_el id_le_seq_iter valid_le_transitive)
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) V_cont V_valid a'_el a_el continuous_complete finite_seq_iter_el i'_el i_el valid_par_mono)
qed

lemma inv_par_iter_par1 :
  fixes V :: "('A, 'a) CVA" and a i :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i"  and a_el : "a \<in> elems V"
  and a_le_i : "le V a i"
shows "par V r (finite_seq_iter V a) = par V (finite_seq_iter V (par V r a)) r" 
  oops

(* Rely-guarantee logic rules *)

proposition rg_hoare_rule :
  fixes V :: "('A, 'a) CVA" and p a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_complete : "is_complete V"
  and p_el : "p \<in> elems V" and a_el : "a \<in> elems V" and q_el : "q \<in> elems V"
shows "rg V p (neut_par V (d a)) a (top V) q = hoare V p a q"
proof (rule iffI, goal_cases)
  case 1
  then show ?case
    by (metis CVA.valid_welldefined V_valid a_el valid_elems valid_neutral_law_left) 
next
  case 2
  then show ?case
    by (smt (z3) CVA.top_def CVA.valid_welldefined V_complete V_valid a_el cocomplete top_max valid_gc_poset valid_neutral_law_left) 
qed

(* [CKA, Thm 8.4] *)
(* Note in a CKA parallel restricted to invariants corresponds to supremum in the
 lattice of invariants, since the natural order defined a \<le> b \<longleftrightarrow> a \<parallel> b = b coincides with the ambient
order (and the meet of both orders coincide). This is not the case here. *)
proposition rg_concurrency_rule :
  fixes V :: "('A, 'a) CVA" and r1 p1 a1 q1 g1 r2 p2 b2 q2 g3 :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and V_complete : "is_complete V"
  and "r1 \<in> elems V" and "p1 \<in> elems V" and "a1 \<in> elems V" and "q1 \<in> elems V" and "g1 \<in> elems V"
  and "r2 \<in> elems V" and "p2 \<in> elems V" and "a2 \<in> elems V" and "q2 \<in> elems V" and "g2 \<in> elems V" 
  and rg1 : "rg V p1 r1 a1 g1 q1" and rg2 : "rg V p2 r2 a2 g2 q2"
  and inv_r1 : "invariant V r1" and inv_g1 : "invariant V g1" and inv_r2 : "invariant V r2" and inv_g2 : "invariant V g2"
  and g1_le_r2 : "le V g1 r2" and g2_le_r1 : "le V g2 r1"
shows "rg V (meet V p1 p2) (meet V r1 r2) (par V a1 a2) (par V g1 g2) (meet V q1 q2)"
proof -
  have "le V (par V a1 a2) (par V g1 g2)"
    using V_valid assms(12) assms(5) assms(7) assms(10) rg1 rg2 valid_par_mono by blast 
  moreover have guar: "le V a2 r1 \<and> le V a1 r2"
    using V_valid assms(12) assms(3) assms(5) assms(8) assms(7) assms(10) g1_le_r2 g2_le_r1 rg1 rg2 valid_le_transitive by blast  
  moreover have "le V (seq V p1 (par V r1 a1)) q1 \<and> le V (seq V p2 (par V r2 a2)) q2"
    using rg1 rg2 by fastforce
  moreover have "le V (seq V p1 (par V (par V r1 r1) a1)) q1 \<and> le V (seq V p2 (par V (par V r2 r2) a2)) q2"
    by (smt (verit, best) calculation(3) comp_apply inv_r1 inv_r2 invariant_def)
  moreover have "le V (seq V p1 (par V r1 (par V a1 r1))) q1 \<and> le V (seq V p2 (par V r2 (par V r2 a2))) q2"
    by (smt (verit) CVA.valid_welldefined V_valid assms(3) assms(5) assms(8) assms(10) calculation(4) valid_comb_associative valid_elems valid_par_comm)
  moreover have "le V (par V a1 a2) (par V a1 r1) \<and> le V (par V a1 a2) (par V r2 a2)" 
    using assms guar valid_elems [where ?V=V] valid_le_reflexive [where ?V=V]  valid_par_mono [where ?V=V] 
    by blast 
  moreover have "le V (par V r1 (par V a1 a2)) (par V r1 (par V a1 r1))" 
    using assms valid_elems [where ?V=V] valid_le_reflexive [where ?V=V] valid_par_mono [where ?V=V] valid_par_elem [where ?V=V]
    using guar by auto
   moreover have "le V (par V r2 (par V a1 a2)) (par V r2 (par V r2 a2))" 
    using assms valid_elems [where ?V=V] valid_le_reflexive [where ?V=V] valid_par_mono [where ?V=V] valid_par_elem [where ?V=V]
    using guar by auto
  moreover have "le V (seq V p1 (par V r1 (par V a1 a2))) (seq V p1 (par V r1 (par V a1 r1)))" 
    using assms valid_elems [where ?V=V] valid_le_reflexive [where ?V=V] valid_par_mono [where ?V=V] valid_par_elem [where ?V=V]
valid_seq_mono [where ?V=V] valid_seq_elem [where ?V=V]
    using guar by auto
  moreover have "le V (seq V p2 (par V r2 (par V a1 a2))) (seq V p2 (par V r2 (par V r2 a2)))" 
    using assms valid_elems [where ?V=V] valid_le_reflexive [where ?V=V] valid_par_mono [where ?V=V] valid_par_elem [where ?V=V]
valid_seq_mono [where ?V=V] valid_seq_elem [where ?V=V]
    using guar by auto

  moreover have checkpoint: "le V (seq V p1 (par V r1 (par V a1 a2))) q1 \<and> le V (seq V p2 (par V r2 (par V a1 a2))) q2" 
    using calculation valid_le_transitive [where ?V=V]
    by (smt (verit) V_valid assms(11) assms(6) assms(3) assms(4) assms(5) assms(10) assms(8) assms(9) valid_par_elem valid_seq_elem)

  moreover have meet_p1p2 : "le V (meet V p1 p2) p1 \<and> le V (meet V p1 p2) p2"
    using V_complete meet_smaller1 [where ?P="poset V" and ?a=p1 and ?b=p2] meet_smaller2 [where ?P="poset V" and ?a=p1 and ?b=p2] assms
    by (metis CVA.is_complete_def CVA.meet_def)

  moreover have meet_r1r2 : "le V (meet V r1 r2) r1 \<and> le V (meet V r1 r2) r2"
    using V_complete meet_smaller1 [where ?P="poset V" and ?a=r1 and ?b=r2] meet_smaller2 [where ?P="poset V" and ?a=r1 and ?b=r2] assms
    by (metis CVA.is_complete_def CVA.meet_def)

  moreover have meet_elems : "meet V p1 p2 \<in> elems V \<and> meet V r1 r2 \<in> elems V \<and> meet V q1 q2 \<in> elems V"
    by (metis CVA.is_complete_def CVA.meet_def V_complete assms(11) assms(3) assms(4) assms(6) assms(8) assms(9) meet_el)

  moreover have "le V (par V (meet V r1 r2) (par V a1 a2)) ((par V r1 (par V a1 a2)))"
    by (smt (verit) CVA.valid_welldefined V_valid assms(10) assms(3) assms(5) calculation(13) calculation(14) comb_is_element valid_elems valid_le_reflexive valid_par_mono) 

  moreover have 0: "le V (seq V p1 (par V (meet V r1 r2) (par V a1 a2))) (seq V p1 (par V r1 (par V a1 a2)))"
    by (smt (verit) CVA.valid_welldefined V_valid assms(10) assms(3) assms(4) assms(5) calculation(14) calculation(15) valid_le_reflexive valid_monotone valid_par_elem valid_semigroup) 

  moreover have 00: "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2))) (seq V p1 (par V (meet V r1 r2) (par V a1 a2)))"
    by (smt (verit) V_valid assms(10) assms(4) assms(5) meet_elems meet_p1p2 valid_le_reflexive valid_par_elem valid_seq_mono) 

  moreover have 000: "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2)))  (seq V p1 (par V r1 (par V a1 a2)))" using  meet_p1p2 meet_r1r2 meet_elems checkpoint 00 0 
valid_le_transitive [where ?V=V and ?a="(seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2)))" 
and ?b="(seq V p1 (par V (meet V r1 r2) (par V a1 a2)))" and ?c="(seq V p1 (par V r1 (par V a1 a2)))"]
    by (smt (verit, best) V_valid assms(10) assms(3) assms(4) assms(5) valid_par_elem valid_seq_elem)

 moreover have 0000: "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2))) q1" using  checkpoint 000 00 0
   by (smt (verit, ccfv_threshold) V_valid assms(10) assms(3) assms(4) assms(5) assms(6) meet_elems valid_le_transitive valid_par_elem valid_seq_elem) 

  moreover have "le V (par V (meet V r1 r2) (par V a1 a2)) ((par V r2 (par V a1 a2)))"
    by (smt (verit, del_insts) V_valid assms(10) assms(5) assms(8) meet_elems meet_r1r2 valid_le_reflexive valid_par_elem valid_par_mono)

  moreover have 1: "le V (seq V p2 (par V (meet V r1 r2) (par V a1 a2))) (seq V p2 (par V r2 (par V a1 a2)))"
    by (smt (verit, ccfv_threshold) V_valid assms(10) assms(5) assms(8) assms(9) calculation(20) meet_elems valid_elems valid_le_reflexive valid_par_elem valid_seq_mono)

  moreover have 11: "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2))) (seq V p2 (par V (meet V r1 r2) (par V a1 a2)))"
    by (smt (verit) V_valid assms(10) assms(5) assms(9) meet_elems meet_p1p2 valid_le_reflexive valid_par_elem valid_seq_mono)

  moreover have 111: "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2)))  (seq V p2 (par V r2 (par V a1 a2)))"
    by (smt (verit, del_insts) V_valid assms(10) assms(5) assms(8) assms(9) calculation(20) meet_elems meet_p1p2 valid_par_elem valid_seq_mono)  

 moreover have 1111: "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2))) q2" using  checkpoint 111 11 1
   by (smt (verit, ccfv_threshold) V_valid assms(10) assms(11) assms(5) assms(8) assms(9) hoare_weakening_rule meet_elems meet_p1p2 valid_par_elem valid_seq_elem) 

  moreover have "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2))) (meet V q1 q2)" using meet_property 1111 0000
    by (smt (verit, ccfv_SIG) CVA.is_complete_def CVA.meet_def V_complete V_valid assms(10) assms(11) assms(5) assms(6) meet_elems valid_par_elem valid_seq_elem) 

  ultimately show ?thesis
    by force 
qed

(* [CKA, Thm 8.5] *)
proposition rg_sequential_rule :
  fixes V :: "('A, 'a) CVA" and r1 p1 a1 q1 g1 r2 p2 b2 q2 g3 :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and V_complete : "is_complete V"
  and "r1 \<in> elems V" and "p \<in> elems V" and "a1 \<in> elems V" and "p' \<in> elems V" and "g1 \<in> elems V"
  and "r2 \<in> elems V"  and "a2 \<in> elems V" and "p'' \<in> elems V" and "g2 \<in> elems V" 
  and rg1 : "rg V p r1 a1 g1 p'" and rg2 : "rg V p' r2 a2 g2 p''"
  and inv_r1 : "invariant V r1" and inv_g1 : "invariant V g1" and inv_r2 : "invariant V r2" and inv_g2 : "invariant V g2"
  and "invariant V (meet V r1 r2)"
shows "rg V p (meet V r1 r2) (seq V a1 a2) (seq V g1 g2) p''"
proof -
  have "le V (seq V a1 a2) (seq V g1 g2)"
    using V_valid assms(11) assms(5) assms(7) assms(9) rg1 rg2 valid_seq_mono by blast 
  moreover have 0: "le V (par V (meet V r1 r2) (seq V a1 a2)) (seq V (par V (meet V r1 r2) a1) (par V (meet V r1 r2) a2))"
    using assms(18) assms(5) assms(9) invariant_def by blast
  
  moreover have "le V (par V (meet V r1 r2) a1) (par V r1 a1)"
    by (smt (verit) CVA.is_complete_def CVA.meet_def V_complete V_valid assms(3) assms(5) assms(8) cocomplete is_cocomplete_def meet_el meet_smaller1 valid_par_mono valid_reflexivity) 
  moreover have 1: "le V (seq V (par V (meet V r1 r2) a1) (par V (meet V r1 r2) a2)) (seq V (par V r1 a1) (par V (meet V r1 r2) a2))"
    by (smt (verit) V_complete V_valid assms(3) assms(5) assms(8) assms(9) calculation(3) meet_elem valid_le_reflexive valid_par_elem valid_seq_mono)
  moreover have "le V (par V (meet V r1 r2) a2) (par V r2 a2)"
    by (smt (verit, ccfv_SIG) CVA.is_complete_def CVA.meet_def V_complete V_valid assms(3) assms(8) assms(9) meet_el meet_smaller2 valid_le_reflexive valid_par_mono)
  moreover have 2: "le V (seq V (par V r1 a1) (par V (meet V r1 r2) a2)) (seq V (par V r1 a1) (par V r2 a2))"
    by (smt (verit) V_complete V_valid assms(3) assms(5) assms(8) assms(9) calculation(5) meet_elem valid_le_reflexive valid_par_elem valid_seq_mono)

  moreover have 3: "le V (par V (meet V r1 r2) (seq V a1 a2)) (seq V (par V r1 a1) (par V (meet V r1 r2) a2))" 
    using 0 1 valid_transitivity
    by (smt (verit, best) V_complete V_valid assms(3) assms(5) assms(8) assms(9) meet_elem valid_le_transitive valid_par_elem valid_seq_elem) 

  moreover have 4: "le V (par V (meet V r1 r2) (seq V a1 a2)) (seq V (par V r1 a1) (par V r2 a2))"
    using 0 1 2 3 valid_transitivity
    by (smt (verit, ccfv_threshold) V_complete V_valid assms(3) assms(5) assms(8) assms(9) meet_elem valid_le_transitive valid_par_elem valid_seq_elem)

  moreover have 5: "le V (seq V p (par V (meet V r1 r2) (seq V a1 a2))) (seq V p (seq V (par V r1 a1) (par V r2 a2)))"
    by (smt (verit, ccfv_threshold) "4" V_complete V_valid assms(3) assms(4) assms(5) assms(8) assms(9) meet_elem valid_le_reflexive valid_par_elem valid_seq_elem valid_seq_mono) 

  moreover have 6: "(seq V p (seq V (par V r1 a1) (par V r2 a2))) = seq V (seq V p (par V r1 a1)) (par V r2 a2)"
    by (metis CVA.valid_welldefined V_valid assms(3) assms(4) assms(5) assms(8) assms(9) valid_comb_associative valid_par_elem)

  moreover have 7: "le V (seq V p (seq V (par V r1 a1) (par V r2 a2))) (seq V p' (par V r2 a2))"
    by (smt (verit, ccfv_threshold) V_valid assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) hoare_sequential_rule' rg1 valid_le_reflexive valid_par_elem valid_seq_elem) 

  moreover have 8: "le V (seq V p' (par V r2 a2)) p''"
    using rg2 by blast 

  moreover have 9: "le V (seq V p (seq V (par V r1 a1) (par V r2 a2))) p''"
    by (smt (verit, ccfv_SIG) "7" "8" V_valid assms(10) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) valid_le_transitive valid_par_elem valid_seq_elem)

  moreover have 10: "le V (seq V p (par V (meet V r1 r2) (seq V a1 a2))) (seq V p (seq V (par V r1 a1) (par V r2 a2)))"
    using "5" by blast

  moreover have 11: "le V (seq V p (par V (meet V r1 r2) (seq V a1 a2))) p''"
    by (smt (verit, ccfv_SIG) "5" "9" CVA.is_complete_def CVA.meet_def CVA.valid_welldefined V_complete V_valid assms(10) assms(3) assms(4) assms(5) assms(8) assms(9) comb_is_element meet_el valid_elems valid_poset valid_semigroup valid_transitivity) 

  ultimately show ?thesis
    by meson
qed

(* [CKA, Thm 8.6.1] *)
(* Note: in CKA the converse direction is proved, but this would require neut_par refines any
 invariant, which is too strong in many CVA models. *)
proposition rg_neut_par_rule :
  fixes V :: "('A, 'a) CVA" and r g p q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and r_el : "r \<in> elems V" and g_el : "g \<in> elems V" and p_el : "p \<in> elems V"  and q_el : "q \<in> elems V"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
  and "rg V p r (neut_par V (d r)) g q"
shows "hoare V p r q"
  by (metis CVA.valid_welldefined V_valid assms(8) r_el valid_elems valid_neutral_law_right)

(* [CKA, Thm 8.6.2] *)
proposition rg_choice_rule :
  fixes V :: "('A, 'a) CVA" and p q a b r g :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and "r \<in> elems V" and "g \<in> elems V" and "p \<in> elems V" and "q \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
shows "rg V p r (join V a b) g q = (rg V p r a g q \<and> rg V p r b g q)" 
proof (rule iffI, goal_cases)
  case 1
  then show ?case 
  proof -
    have "le V (seq V p (par V r (join V a b))) q \<and> le V (join V a b) g"
      using "1" by blast 
    moreover have "le V a g \<and> le V b g"
      by (smt (verit, best) CVA.join_def V_cont V_valid assms(4) assms(7) assms(8) calculation cocomplete continuous_complete join_el join_greater1 join_greater2 valid_le_transitive)
    moreover have "le V (seq V p (par V r a)) q \<and> le V (seq V p (par V r b)) q"
      by (smt (verit, ccfv_threshold) "1" V_cont V_valid assms(3) assms(5) assms(6) assms(7) assms(8) binary_continuous hoare_choice_rule valid_par_elem)
    ultimately show ?thesis
      by meson
  qed
next
  case 2
  then show ?case 
  proof -
    have "le V (seq V p (par V r a)) q \<and> le V (seq V p (par V r b)) q \<and> le V a g \<and> le V b g"
      using "2" by fastforce
    moreover have "le V (join V a b) g"
      by (smt (verit) "2" CVA.join_def V_cont assms(4) assms(7) assms(8) cocomplete continuous_complete join_property) 
    moreover have "le V (seq V p (par V r (join V a b))) q"
      by (smt (verit, ccfv_threshold) "2" V_cont V_valid assms(3) assms(5) assms(6) assms(7) assms(8) binary_continuous hoare_choice_rule valid_par_elem)
    ultimately show ?thesis
      by blast
  qed
qed

(* [CKA, Thm 8.7] *) 
proposition rg_iteration_rule : 
  fixes V :: "('A, 'a) CVA" and p r a g :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_cont : "is_continuous V"
  and p_el : "p \<in> elems V" and r_el : "r \<in> elems V" and a_el : "a \<in> elems V" and g_el : "g \<in> elems V"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
  and assm_hoare : "hoare V p r p" and assm_rg : "rg V p r a g p"
  and dr_le_da : "d r \<subseteq> d a" (* Note this is equiv. to 1_a \<le> r *)
shows "rg V p r (finite_seq_iter V a) g p"
proof -
  have "le V (finite_seq_iter V a) g" using inv_iter_le [where ?V=V and ?i=g and ?a=a]
    using V_cont V_valid a_el assm_rg g_el inv_g by blast
  
  define "U" where "U = {iter (seq_iter_map V a) n \<star> CVA.bot V |n. n \<in> UNIV}"
  then have "finite_seq_iter V a = sup V U"
    using V_cont V_valid a_el kleene_finite_seq_iter by blast
  moreover have "U \<noteq> {}" using U_def
    by blast 
  moreover have "U \<subseteq> elems V" using U_def
    using V_cont V_valid a_el iter_seq_el by blast 

  define "W" where "W = {seq V p (par V r (iter (seq_iter_map V a) n \<star> CVA.bot V)) |n. n \<in> UNIV}"
  moreover have "W \<noteq> {}" using W_def
    by blast 
  moreover have "W \<subseteq> elems V" using W_def
    using V_cont V_valid a_el iter_seq_el
    by (smt (verit, del_insts) mem_Collect_eq p_el r_el subsetI valid_par_elem valid_seq_elem) 
  moreover have "seq V p (par V r (sup V U)) = seq V p (sup V {par V r u | u . u \<in> U})"
    by (metis (mono_tags, lifting) V_cont V_valid \<open>U \<subseteq> CVA.elems V\<close> calculation(2) continuous_par_dist r_el)
  moreover have "{par V r u | u . u \<in> U} \<noteq> {}" using U_def
    by blast
  moreover have "{par V r u | u . u \<in> U} \<subseteq> elems V" using U_def
    by (smt (z3) Collect_mem_eq Collect_mono_iff V_valid \<open>U \<subseteq> CVA.elems V\<close> r_el valid_par_elem)
  moreover have "seq V p (sup V {par V r u | u . u \<in> U}) = (sup V {seq V p (par V r u) | u . u \<in> U})"
    using V_cont V_valid continuous_seq_dist
    by (smt (verit) Collect_cong calculation(7) calculation(8) mem_Collect_eq p_el)
  moreover have "seq V p (par V r (sup V U))  = sup V {seq V p (par V r u) | u . u \<in> U}"
    using calculation(6) calculation(9) by presburger
  moreover have "{seq V p (par V r u) | u . u \<in> U} = W" 
    using U_def W_def
    by blast
  moreover have "seq V p (par V r (sup V U)) = sup V W" using U_def
    using calculation(10) calculation(11) W_def by presburger
  moreover have "sup V W = seq V p (par V r (sup V U))"
    using W_def calculation(12) by presburger

  moreover have fa: "\<And> n . le V (seq V p (par V r (iter (seq_iter_map V a) n \<star> CVA.bot V ))) p" 
  proof (induct_tac n, goal_cases)
    case (1 n)
    then show ?case 
    proof -
      have "(iter (seq_iter_map V a) 0 \<star> bot V) = bot V"
        using V_cont V_valid a_el iter_seq_zero by blast 
      moreover have "le V (par V r (bot V)) r"
        by (metis V_cont V_valid continuous_complete inv_idem_par inv_r par_bot1 r_el)
      moreover have "le V (seq V p (par V r (bot V))) (seq V p r)"
        by (smt (verit, del_insts) V_cont V_valid bot_elem calculation(2) continuous_complete p_el r_el valid_le_reflexive valid_par_elem valid_seq_mono) 
      ultimately show ?thesis
        by (smt (verit, best) V_cont V_valid assm_hoare complete_bot_el continuous_complete p_el r_el valid_le_transitive valid_par_elem valid_seq_elem)
    qed
  next
    case (2 n m)
    then show ?case 
    proof -
      define "a_m" where "a_m = iter (seq_iter_map V a) m \<star> bot V" 
      have "le V (seq V p (par V r a_m)) p"
        using "2" a_m_def by force 
      moreover have "iter (seq_iter_map V a) (Suc m) \<star> bot V = join V (neut_seq V (d a)) (seq V a (a_m))" 
        using iter_seq_induction [where ?V=V and ?a=a and ?n=m] V_cont V_valid a_el a_m_def by blast
      moreover have "seq V p (par V r (iter (seq_iter_map V a) (Suc m) \<star> bot V)) = seq V p (par V r (join V (neut_seq V (d a)) (seq V a (a_m))))"
        using calculation(2) by presburger
      moreover have "... = seq V p (join V (par V r (neut_seq V (d a))) (par V r (seq V a (a_m))))"
        by (metis CVA.valid_welldefined V_cont V_valid a_el a_m_def binary_continuous d_elem_is_open iter_seq_el r_el valid_neut_seq_elem valid_seq_elem)
      moreover have "... = join V (seq V p (par V r (neut_seq V (d a)))) (seq V p (par V r (seq V a (a_m))))"
        by (metis CVA.valid_welldefined V_cont V_valid a_el a_m_def binary_continuous d_elem_is_open iter_seq_el p_el r_el valid_neut_seq_elem valid_par_elem valid_seq_elem)
      
      moreover have 1: "le V (seq V p (par V r (seq V a (a_m)))) p"
        by (smt (z3) "2" V_cont V_valid a_el a_m_def assm_rg hoare_sequential_rule' inv_dist inv_r iter_seq_el p_el r_el valid_elems valid_par_elem valid_seq_elem)

      moreover have "le V (neut_seq V (d a)) (neut_seq V (d r))" using dr_le_da neut_le_neut [where ?V="seq_algebra V" and ?A="d a" and ?B="d r"]
        by (meson CVA.valid_welldefined V_valid a_el d_elem_is_open r_el)
      moreover have "le V (par V r (neut_seq V (d a))) (par V r (neut_seq V (d r)))"
        by (smt (verit) CVA.valid_welldefined V_valid a_el calculation(7) d_elem_is_open r_el valid_le_reflexive valid_neut_seq_elem valid_par_mono)  
      moreover have "le V (par V r (neut_seq V (d r))) (par V r r)"
        by (smt (verit, ccfv_SIG) CVA.valid_welldefined V_valid d_elem_is_open inv_neut_seq inv_r neutral_is_element r_el valid_le_reflexive valid_par_mono)
      moreover have "par V r r = r"
        using V_valid inv_idem_par inv_r r_el by blast
      moreover have "le V (par V r (neut_seq V (d a))) r"
        by (smt (verit, ccfv_SIG) CVA.valid_welldefined V_valid a_el calculation(10) calculation(7) d_elem_is_open inv_neut_seq inv_r r_el valid_le_reflexive valid_le_transitive valid_neut_seq_elem valid_par_mono)
      moreover have "par V r (neut_seq V (d a)) \<in> elems V"
        by (metis V_cont V_valid a_el fiter_seq.simps(1) fiter_seq_elem r_el valid_par_elem) 
      
      moreover have "le V (seq V p (par V r (neut_seq V (d a)))) (seq V p r)" using valid_seq_mono [where ?V=V]
        by (smt (z3) V_valid calculation(11) calculation(12) p_el r_el valid_le_reflexive)

      moreover have 2: "le V (seq V p (par V r (neut_seq V (d a)))) p"
        by (smt (verit, best) CVA.valid_welldefined V_valid a_el assm_hoare calculation(13) d_elem_is_open p_el r_el valid_le_transitive valid_neut_seq_elem valid_par_elem valid_seq_elem) 

      ultimately show ?thesis
        by (smt (verit) CVA.valid_welldefined V_cont V_valid a_el a_m_def d_elem_is_open hoare_choice_rule iter_seq_el p_el r_el valid_neut_seq_elem valid_par_elem valid_seq_elem)
     qed
    qed
    moreover have "le V (sup V W) p" 
      unfolding sup_def W_def
      using  sup_is_lub [where ?P="poset V" and ?U="W" and ?z=p] W_def
      using V_cont calculation(5) continuous_cocomplete fa p_el by blast 
    moreover have "le V (seq V p (par V r (sup V U))) p"
      using calculation(12) calculation(15) by presburger
    moreover have "le V (seq V p (par V r (finite_seq_iter V a))) p"
      using calculation(1) calculation(16) by presburger
    ultimately show ?thesis using U_def
      using \<open>CVA.le V (finite_seq_iter V a) g\<close> by blast
  qed

end
