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

abbreviation meet :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"meet V \<equiv> OVA.meet (seq_algebra V)"

abbreviation join :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"join V \<equiv>  OVA.join (seq_algebra V)"

abbreviation inf :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"inf V \<equiv> OVA.inf (seq_algebra V)"

abbreviation sup :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"sup V \<equiv> OVA.sup (seq_algebra V)"

(* Properties *)

abbreviation is_complete :: "('A,'a) CVA \<Rightarrow> bool" where
"is_complete V \<equiv> OVA.is_complete (seq_algebra V)"

definition is_right_positively_disjunctive :: "('A,'a) CVA \<Rightarrow> bool" where
"is_right_positively_disjunctive V \<equiv> 
  OVA.is_right_positively_disjunctive (par_algebra V) \<and> OVA.is_right_positively_disjunctive (seq_algebra V)"

(* Constants *)

definition bot :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation" where
"bot V = Poset.bot (poset V)"

definition top :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation" where
"top V = Poset.top (poset V)"

lemma complete_bot_el : "is_complete V \<Longrightarrow> bot V \<in> elems V"
  by (simp add: CVA.bot_def bot_as_inf inf_el)

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

lemma rpd_complete : "is_right_positively_disjunctive V \<Longrightarrow> is_complete V"
  using CVA.is_right_positively_disjunctive_def OVA.is_right_positively_disjunctive_def by blast

lemma rpd_cocomplete : "is_right_positively_disjunctive V \<Longrightarrow> is_cocomplete (poset V)"
  using cocomplete rpd_complete by blast

lemma rpd_seq_dist :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_right_positively_disjunctive V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "seq V a (sup V U) = sup V {seq V a u | u . u \<in> U}"
  using CVA.is_right_positively_disjunctive_def OVA.is_right_positively_disjunctive_def assms(2) assms(3) assms(4) assms(5) by blast
  

lemma right_positively_disjunctive_par :
  fixes V :: "('A, 'a) CVA" and U :: "('A, 'a) Valuation set" and a :: "('A, 'a) Valuation" 
  assumes "valid V" and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
    and "is_right_positively_disjunctive V"
shows "par V a (sup V U) = sup V {par V a u | u . u \<in> U}"
  using assms CVA.is_right_positively_disjunctive_def [where ?V=V] OVA.is_right_positively_disjunctive_def [where ?V="par_algebra V"]
  unfolding is_right_positively_disjunctive_def
  by (metis (no_types, lifting) CVA.valid_welldefined OVA.valid_welldefined)

lemma rpd_par_dist :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_right_positively_disjunctive V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "par V a (sup V U) = sup V {par V a u | u . u \<in> U}"
  using assms CVA.is_right_positively_disjunctive_def [where ?V=V] OVA.is_right_positively_disjunctive_def [where ?V="par_algebra V"]
  unfolding is_right_positively_disjunctive_def
  by (metis (no_types, lifting) CVA.valid_welldefined OVA.valid_welldefined)

lemma rpd_par_dist_symmetric :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_right_positively_disjunctive V"
  and "a \<in> elems V" and "U \<subseteq> elems V" and "U \<noteq> {}"
shows "par V (sup V U) a = sup V {par V u a | u . u \<in> U}" 
proof -
  have "par V (sup V U) a = par V a (sup V U)"
    using assms(1) assms(2) assms(3) assms(4) rpd_cocomplete sup_el valid_par_comm by blast
  moreover have "{par V u a | u . u \<in> U} = {par V a u | u . u \<in> U}"
    using assms(1) assms(3) assms(4) valid_par_comm by blast
  ultimately show ?thesis
    by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) assms(5) rpd_par_dist) 
qed

lemma binary_disjunctive :
  fixes V :: "('A, 'a) CVA" and a b b' :: "('A, 'a) Valuation"
  assumes "valid V" and "is_right_positively_disjunctive V"
  and "a \<in> elems V" and "b \<in> elems V" and "b' \<in> elems V" 
shows "par V a (join V b b') = join V (par V a b) (par V a b')
\<and> seq V a (join V b b') = join V (seq V a b) (seq V a b')"
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
    by (simp add: Poset.join_def calculation(4))
  moreover have "join V (seq V a b) (seq V a b') = sup V {seq V a u | u . u \<in> U}"
    by (simp add: Poset.join_def calculation(5))
  moreover have "join V (seq V b a) (seq V b' a) = sup V {seq V u a | u . u \<in> U}"
    by (simp add: Poset.join_def calculation(6))
  ultimately show ?thesis using  rpd_seq_dist [where ?V=V] rpd_par_dist [where ?V=V] rpd_seq_dist \<open>U \<subseteq> CVA.elems V\<close> assms(1) assms(2) assms(3)
    by presburger 
qed

lemma inf_elem : "is_complete V \<Longrightarrow> U \<subseteq> elems V \<Longrightarrow> inf V U \<in> elems V"
  by (simp add: inf_el) 

lemma sup_elem : "is_complete V \<Longrightarrow> U \<subseteq> elems V \<Longrightarrow> sup V U \<in> elems V"
  by (simp add: complete_equiv_cocomplete sup_el)

lemma meet_elem : "is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> meet V a b \<in> elems V"
  by (simp add: meet_el)

lemma join_elem : "is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> join V a b \<in> elems V"
  by (simp add: complete_equiv_cocomplete join_el)

lemma top_elem : "is_complete V \<Longrightarrow> top V \<in> elems V"
  by (simp add: CVA.top_def Poset.top_def complete_equiv_cocomplete sup_el)

lemma bot_elem : "is_complete V \<Longrightarrow> bot V \<in> elems V"
  by (metis CVA.bot_def Poset.bot_def empty_subsetI sup_elem)

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
      by (smt (z3) CVA.valid_welldefined V_complete V_valid a_elem calculation(1) calculation(1) calculation(8) cocomplete d_elem_is_open join_elem valid_le_reflexive valid_neut_par_elem valid_par_elem)
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
      by (metis CVA.valid_welldefined V_complete V_valid a_elem calculation(2) calculation(3) cocomplete d_elem_is_open valid_neut_seq_elem valid_seq_elem)
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
      by (smt (z3) CVA.valid_welldefined V_complete V_valid a_elem calculation(1) calculation(8) cocomplete d_elem_is_open join_elem valid_le_reflexive valid_neut_seq_elem valid_seq_elem)
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
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) PosetMap.select_convs(2) finite_par_iter_def lfp_is_el par_iter_map_def valid_par_iter_map) 

lemma "infinite_par_iter" : "valid V \<Longrightarrow> is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> infinite_par_iter V a \<in> elems V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) PosetMap.select_convs(2) cocomplete gfp_is_el infinite_par_iter_def par_iter_map_def valid_par_iter_map) 

lemma "finite_seq_iter_el" : "valid V \<Longrightarrow> is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> finite_seq_iter V a \<in> elems V"
  by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) PosetMap.select_convs(2) finite_seq_iter_def lfp_is_el seq_iter_map_def valid_seq_iter_map) 

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
    Poset.fun_app Poset.valid_map_deterministic V_complete V_valid a_star_def a_el finite_seq_iter_def lfp_is_el  seq_iter_map_def valid_seq_iter_map
    by (smt (z3) PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) fst_conv mem_Collect_eq)
  moreover have "le V (neut_seq V (d a)) (join V (neut_seq V (d a)) (seq V a a_star))"
    by (metis CVA.valid_welldefined V_complete V_valid a_star_def a_el cocomplete d_elem_is_open finite_seq_iter_el join_greater1 valid_neut_seq_elem valid_seq_elem) 
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
    Poset.fun_app Poset.valid_map_deterministic V_complete V_valid a_star_def a_el finite_seq_iter_def lfp_is_el  seq_iter_map_def valid_seq_iter_map
    by (smt (z3) PosetMap.select_convs(1) PosetMap.select_convs(2) PosetMap.select_convs(3) fst_conv mem_Collect_eq)
  moreover have "le V (seq V a a_star) (join V (neut_seq V (d a)) (seq V a a_star))" 
    using a_star_def join_greater2 [where ?P="poset V" and ?a="neut_seq V (d a)"]
    by (metis (no_types, lifting) CVA.valid_welldefined PosetMap.select_convs(1) PosetMap.select_convs(2) V_complete V_valid assms(3) cocomplete d_elem_is_open finite_seq_iter_def lfp_is_el seq_iter_map_def valid_neut_seq_elem valid_seq_elem valid_seq_iter_map)
  moreover have "le V (neut_seq V (d a)) a_star"
     using V_complete V_valid a_star_def a_el skip_le_finite_seq_iter by blast 
  moreover have "le V (seq V a (neut_seq V (d a))) (seq V a a_star)"
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_complete V_valid \<open>a_star \<in> CVA.elems V\<close> a_el calculation(4) cocomplete d_elem_is_open is_cocomplete_def valid_monotone valid_neut_seq_elem valid_reflexivity valid_semigroup) 
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid \<open>a_star \<in> CVA.elems V\<close> a_el valid_le_transitive valid_neutral_law_right valid_seq_elem) 
qed

lemma id_le_seq_iter : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V" 
shows "le V a (finite_seq_iter V a)"
  using V_rpd V_valid a_el rpd_complete id_le_finite_seq_iter by blast

lemma kleene_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V"
shows "finite_seq_iter V a = sup V { (iter (seq_iter_map V a) n) \<star> (bot V) | n . n \<in> UNIV}"
proof - 
  define "f_a" where "f_a = seq_iter_map V a"
  have "finite_seq_iter V a = lfp f_a"
    by (simp add: finite_seq_iter_def f_a_def) 
  moreover have "Poset.valid_map f_a"
    using V_rpd V_valid a_el f_a_def is_right_positively_disjunctive_def valid_seq_iter_map
    using rpd_complete by blast   
  moreover have "(\<And>A. A \<subseteq> elems V \<Longrightarrow> A \<noteq> {} \<Longrightarrow> f_a \<star> Poset.sup (poset V) A = Poset.sup (poset V) {f_a \<star> a |a. a \<in> A})" 
  proof -
    fix A
    assume "A \<subseteq> elems V"
    assume "A \<noteq> {}"
    define "sup_A" where "sup_A = Poset.sup (CVA.poset V) A"
    have "sup_A \<in> elems V"
      using V_rpd \<open>A \<subseteq> CVA.elems V\<close> cocomplete is_right_positively_disjunctive_def sup_A_def sup_el rpd_cocomplete by blast 
    moreover have "Poset.valid_map f_a \<and> el (PosetMap.dom f_a) = elems V" 
    using V_rpd V_valid a_el f_a_def is_right_positively_disjunctive_def valid_seq_iter_map
    by (smt (verit, ccfv_threshold) PosetMap.select_convs(1) \<open>Poset.valid_map f_a\<close> seq_iter_map_def)
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
      using  calculation
      by metis
    moreover have 1: "{seq V a u | u . u \<in> A} \<noteq> {}" 
      using \<open>A \<noteq> {}\<close> by blast
    moreover have 2: "{seq V a u |u. u \<in> A} \<subseteq> elems V"
      by (smt (verit) V_valid \<open>A \<subseteq> CVA.elems V\<close> a_el mem_Collect_eq subset_iff valid_seq_elem)
    moreover have 3: " neut_seq V (d a) \<in> elems V"
      by (meson CVA.valid_welldefined V_valid a_el d_elem_is_open valid_neut_seq_elem) 
    moreover have 4: "is_cocomplete (poset V)" using V_rpd is_right_positively_disjunctive_def [where ?V=V]
      using rpd_cocomplete by auto
    moreover have 5: "{Poset.join (CVA.poset V) (neut_seq V (d a)) u |u. u \<in> {seq V a u |u. u \<in> A}} = {Poset.join (CVA.poset V) (neut_seq V (d a)) (seq V a u) | u . u \<in> A}"
      by blast
    moreover have "join V (neut_seq V (d a)) (sup V {seq V a u | u . u \<in> A}) = sup V {join V (neut_seq V (d a)) (seq V a u) | u . u \<in> A}" 
      unfolding join_def sup_def
      using 5 4 2 1 3 sup_dist_join1 [where ?P="poset V" and ?a="neut_seq V (d a)" and ?U="{seq V a u | u . u \<in> A}"]
      by (simp add: join_def sup_def) 
    moreover have "join V (neut_seq V (d a)) (sup V {seq V a u | u . u \<in> A}) \<in> elems V"
      by (metis (no_types, lifting) "2" "3" "4" join_el sup_el)
    moreover have "sup V {join V (neut_seq V (d a)) (seq V a u) | u . u \<in> A} \<in> elems V"
      using calculation(13) calculation(14) by presburger 
    moreover have "f_a \<star> Poset.sup (poset V) A = join V (neut_seq V (d a)) (seq V a (Poset.sup (poset V) A))"
      using calculation(4) sup_A_def by blast 
    moreover have "seq V a (sup V A) = sup V {seq V a u | u . u \<in> A}" using V_rpd is_right_positively_disjunctive_def [where ?V=V]
      using \<open>A \<noteq> {}\<close> \<open>A \<subseteq> CVA.elems V\<close> a_el OVA.is_right_positively_disjunctive_def by blast  
    ultimately show "f_a \<star> Poset.sup (poset V) A = Poset.sup (poset V) {f_a \<star> a |a. a \<in> A}" unfolding f_a_def seq_iter_map_def
      by simp
  qed
  moreover have "Poset.is_complete (CVA.poset V)" using V_rpd rpd_complete by blast 
  moreover have "Poset.valid_map f_a \<and> PosetMap.dom f_a = CVA.poset V \<and> PosetMap.cod f_a = CVA.poset V"
    by (smt (verit, ccfv_SIG) PosetMap.select_convs(1) PosetMap.select_convs(2) calculation(2) f_a_def seq_iter_map_def) 
  moreover have "Poset.is_continuous f_a"
    by (smt (verit, ccfv_SIG) Collect_cong Poset.is_continuous_def calculation(3) calculation(5) is_directed_def)  
  ultimately show ?thesis using kleene_lfp [where ?P="poset V" and ?f=f_a]  
    unfolding f_a_def finite_seq_iter_def sup_def bot_def
    by fastforce
qed

lemma iter_seq_el: 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V" 
shows "iter (seq_iter_map V a) n \<star> bot V \<in> elems V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) V_rpd V_valid a_el complete_bot_el rpd_complete dom_cod_seq_iter_map iter_el seq_iter_map_def valid_seq_iter_map)

lemma iter_seq_zero : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V" 
shows "iter (seq_iter_map V a) 0 \<star> bot V = bot V"
  by (metis (no_types, lifting) PosetMap.select_convs(1) V_rpd V_valid a_el complete_bot_el rpd_complete iter_zero_app seq_iter_map_def valid_seq_iter_map)

lemma iter_seq_induction : 
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and n :: "nat"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V" 
shows "iter (seq_iter_map V a) (Suc n) \<star> bot V = join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) n \<star> bot V)))"
proof -
  have "Poset.valid_map (seq_iter_map V a)"
    using V_rpd V_valid a_el rpd_complete valid_seq_iter_map by blast
  moreover have "Poset.valid_map (iter (seq_iter_map V a) n)"
    by (simp add: calculation dom_cod_seq_iter_map iter_valid)
  moreover have "(iter (seq_iter_map V a) n \<star> bot V) \<in> elems V"
    by (metis (no_types, lifting) PosetMap.select_convs(1) V_rpd calculation(1) complete_bot_el rpd_complete dom_cod_seq_iter_map iter_el seq_iter_map_def)
  moreover have "iter (seq_iter_map V a) (Suc n) \<star> bot V = seq_iter_map V a \<star> ((iter (seq_iter_map V a) n \<star> bot V))"
    using compose_app_assoc [where ?f="seq_iter_map V a" and ?g="iter (seq_iter_map V a) n" and ?a="bot V"]
    by (metis (no_types, lifting) Poset.compose_app_assoc Poset.iter.simps(2) PosetMap.select_convs(1) V_rpd calculation(1) calculation(2) cod_iter complete_bot_el rpd_complete dom_cod_seq_iter_map dom_iter seq_iter_map_def)
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
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
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
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V"
shows "le V (seq V a (bot V)) a"
  by (metis CVA.valid_welldefined V_rpd V_valid a_el rpd_complete d_elem_is_open seq_bot1 valid_neut_seq_elem valid_neutral_law_right) 

lemma fiter_seq_is_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V"
shows "finite_seq_iter V a = sup V {fiter_seq V a n | n . n \<in> UNIV}" (is "?L = ?R")
proof -
  have "?L \<in> elems V \<and> ?R \<in> elems V"
    by (smt (verit, del_insts) Collect_mem_eq Collect_mono_iff V_rpd V_valid a_el rpd_complete finite_seq_iter_el fiter_seq_elem sup_elem) 
  moreover have "le V ?L ?R"
  proof -
    let ?U = "{fiter_seq V a n | n . n \<in> UNIV}"
    have "?U \<noteq> {} \<and> ?U \<subseteq> elems V"
      by (smt (verit, ccfv_SIG) Collect_empty_eq UNIV_witness V_rpd V_valid a_el fiter_seq_elem mem_Collect_eq subset_iff)
    moreover have "?R \<in> el (Poset.dom (seq_iter_map V a))"
      by (smt (verit, best) PosetMap.select_convs(1) \<open>finite_seq_iter V a \<in> CVA.elems V \<and> CVA.sup V {fiter_seq V a n |n. n \<in> UNIV} \<in> CVA.elems V\<close> seq_iter_map_def)
    moreover have "(seq_iter_map V a) \<star> ?R = join V (neut_seq V (d a)) (seq V a ?R)"
      using seq_iter_map_def [where ?V=V and ?x=a] Poset.fun_app3 [where ?f="seq_iter_map V a" and ?a="?R"] calculation
      by (smt (verit, ccfv_threshold) Poset.fun_app_iff PosetMap.select_convs(3) V_rpd V_valid \<open>finite_seq_iter V a \<in> CVA.elems V \<and> CVA.sup V {fiter_seq V a n |n. n \<in> UNIV} \<in> CVA.elems V\<close> a_el rpd_complete mem_Collect_eq valid_seq_iter_map)
    moreover have "\<And> n . le V (fiter_seq V a n) ?R" using sup_greater [where ?P="poset V" and ?U="?U"]
      by (metis (mono_tags, lifting) UNIV_I V_rpd calculation(1) rpd_cocomplete mem_Collect_eq)
    moreover have "le V (neut_seq V (d a)) ?R"
      by (metis (no_types, lifting) calculation(4) fiter_seq.simps(1))
    moreover have "{seq V a (fiter_seq V a n) | n . n \<in> UNIV} = {seq V a u |u. u \<in> {fiter_seq V a n |n. n \<in> UNIV}}" by blast
    moreover have "seq V a ?R = sup V {seq V a (fiter_seq V a n) | n . n \<in> UNIV}"
      using V_rpd rpd_seq_dist [where ?V=V and ?a=a and ?U="?U"]
      using V_valid a_el calculation(1) calculation(6) by presburger
    moreover have "\<And> n . seq V a (fiter_seq V a n) = fiter_seq V a (n+1)"
      by auto 
    moreover have "seq V a ?R = sup V {fiter_seq V a (n + 1) |n. n \<in> UNIV}"
      using calculation(7) by force 
    moreover have "{fiter_seq V a (n + 1) |n. n \<in> UNIV} \<subseteq> ?U"
      by blast
    moreover have "le V (seq V a ?R) ?R"
      by (smt (verit, best) Poset.sup_mono V_rpd calculation(1) calculation(10) calculation(9) rpd_cocomplete dual_order.trans)
    moreover have "le V (seq_iter_map V a \<star> ?R) ?R"
      by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_rpd V_valid \<open>finite_seq_iter V a \<in> CVA.elems V \<and> CVA.sup V {fiter_seq V a n |n. n \<in> UNIV} \<in> CVA.elems V\<close> a_el calculation(11) calculation(3) calculation(5) rpd_cocomplete d_elem_is_open join_property neutral_is_element valid_seq_elem) 
    ultimately show ?thesis
      by (metis (no_types, lifting) Poset.lfp_lowerbound PosetMap.select_convs(1) V_rpd V_valid a_el rpd_complete dom_cod_seq_iter_map finite_seq_iter_def seq_iter_map_def valid_seq_iter_map)
  qed
    moreover have "le V ?R ?L"
    proof -
      have "\<And> n . le V (fiter_seq V a n) ?L" 
      proof (induct_tac n, goal_cases)
        case (1 n)
        then show ?case
          by (metis V_rpd V_valid a_el rpd_complete fiter_seq.simps(1) skip_le_finite_seq_iter) 
      next
        case (2 n m)
        then show ?case 
        proof -
          let ?f = "seq_iter_map V a"
          assume "le V (fiter_seq V a m) (finite_seq_iter V a)"
          moreover have "fiter_seq V a m \<in> el (Poset.dom ?f) \<and> (finite_seq_iter V a) \<in> el (Poset.dom ?f) "
            by (metis (mono_tags, lifting) PosetMap.select_convs(1) V_rpd V_valid \<open>finite_seq_iter V a \<in> CVA.elems V \<and> CVA.sup V {fiter_seq V a n |n. n \<in> UNIV} \<in> CVA.elems V\<close> a_el fiter_seq_elem seq_iter_map_def)
          moreover have "le V (?f \<star> (fiter_seq V a m)) (?f \<star> (finite_seq_iter V a))" using Poset.valid_map_monotone [where ?f="?f"]
            by (metis (no_types, lifting) PosetMap.select_convs(1) V_rpd V_valid \<open>CVA.le V (fiter_seq V a m) (finite_seq_iter V a)\<close> a_el calculation(2) rpd_complete dom_cod_seq_iter_map seq_iter_map_def valid_seq_iter_map)
          moreover have "fiter_seq V a (Suc m) = seq V a (fiter_seq V a m)"
            by auto 
          moreover have "?f \<star> (fiter_seq V a m) = join V (neut_seq V (d a)) (seq V a (fiter_seq V a m))" 
            using Poset.fun_app3 [where ?f="?f" and ?a="fiter_seq V a m"]
            by (smt (verit, ccfv_SIG) Poset.fun_app_iff PosetMap.select_convs(3) V_rpd V_valid a_el rpd_complete fiter_seq_elem mem_Collect_eq seq_iter_map_def valid_seq_iter_map) 
          moreover have "le V (seq V a (fiter_seq V a m)) (?f \<star> (fiter_seq V a m))"
            by (metis (no_types, lifting) CVA.valid_welldefined V_rpd V_valid a_el calculation(5) rpd_cocomplete d_elem_is_open fiter_seq_elem join_greater neutral_is_element valid_seq_elem)
          moreover have "?f \<star> (finite_seq_iter V a) = finite_seq_iter V a"
            by (smt (verit) Poset.lfp_unfold PosetMap.select_convs(2) V_rpd V_valid a_el rpd_complete dom_cod_seq_iter_map finite_seq_iter_def seq_iter_map_def valid_seq_iter_map) 
          moreover have 0: "le V (fiter_seq V a (Suc m)) (?f \<star> (fiter_seq V a m))"
            using calculation(4) calculation(6) by presburger 
          moreover have 1: "le V (?f \<star> (fiter_seq V a m)) (finite_seq_iter V a)"
            using calculation(3) calculation(7) by auto
          thus "le V (fiter_seq V a (Suc m)) (finite_seq_iter V a)"
            using 0 1 Poset.valid_transitivity [where ?P="poset V"]
            by (smt (verit, ccfv_threshold) V_rpd V_valid \<open>finite_seq_iter V a \<in> CVA.elems V \<and> CVA.sup V {fiter_seq V a n |n. n \<in> UNIV} \<in> CVA.elems V\<close> a_el calculation(4) calculation(5) rpd_complete fiter_seq.simps(1) fiter_seq_elem join_elem valid_le_transitive)
        qed
      qed
      thus ?thesis
        by (smt (verit) V_rpd V_valid a_el calculation(1) rpd_cocomplete fiter_seq_elem mem_Collect_eq subsetI sup_is_lub)  
    qed
 ultimately show ?thesis
   using V_valid valid_le_antisymmetric by blast
qed

lemma seq_finite_seq_iter :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V"
shows "seq V (finite_seq_iter V a) (finite_seq_iter V a) = finite_seq_iter V a"
  oops

lemma ka_finite_seq_iter : "todo" oops (* "(a + b)\<^emph> = a\<^emph> \<sqdot> (b \<sqdot> a\<^emph>)\<^emph>" *)

(* b + x \<sqdot> a \<le> x \<Rightarrow> b \<sqdot> a\<^emph> \<le> x *)
lemma star_induction_left :
  fixes V :: "('A, 'a) CVA" and a b x :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" and x_el : "x \<in> elems V"
  and lhs : "le V (join V b (seq V x a)) x"
shows "le V (seq V b (finite_seq_iter V a)) x" using kleene_finite_seq_iter [where ?V=V and ?a=a] 
  oops

(*b + a \<sqdot> x \<le> x \<Rightarrow> a\<^emph> \<sqdot> b \<le> x *) 
lemma star_induction_right :
  fixes V :: "('A, 'a) CVA" and a b x :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
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
  defines "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V (par V \<epsilon>A \<epsilon>A) \<epsilon>A"
  by (smt (z3) A_open CVA.valid_welldefined V_valid \<epsilon>A_def comb_is_element fst_conv neutral_is_element valid_domain_law valid_elems valid_neutral_law_left valid_neutral_law_right valid_weak_exchange) 

lemma delta_le_delta_seq_delta :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A"
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

end
