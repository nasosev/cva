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
"invariant V i \<equiv> le V (neut_seq V (d i)) i \<and>  seq V i i = i \<and> par V i i = i \<and> (\<forall> a b . a \<in> elems V \<and> b \<in> elems V \<longrightarrow> le V (par V i (seq V a b)) (seq V (par V i a) (par V i b)))"

definition meet :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"meet V a b = Poset.meet (poset V) a b"

definition join :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"join V a b = Poset.join (poset V) a b"

definition inf :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"inf V U = Poset.inf (poset V) U"

definition sup :: "('A,'a) CVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"sup V U = Poset.sup (poset V) U"

(* Properties *)

(* Todo: prove Poset.complete_equiv_cocomplete to remove redundancy here *)
definition is_complete :: "('A,'a) CVA \<Rightarrow> bool" where
"is_complete V \<equiv> Poset.is_complete (OVA.poset (seq_algebra V)) \<and> Poset.is_cocomplete (OVA.poset (seq_algebra V))"

definition is_quantalic :: "('A,'a) CVA \<Rightarrow> bool" where
"is_quantalic V \<equiv> is_complete V \<and> (\<forall> a U . U \<subseteq> elems V \<longrightarrow> a \<in> elems V \<longrightarrow>
  par V a (sup V U) = sup V {par V a u | u . u \<in> U} \<and>
  seq V a (sup V U) = sup V {seq V a u | u . u \<in> U} \<and>
  seq V (sup V U) a = sup V {seq V u a | u . u \<in> U})"

(* Constants *)
definition top :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation" where
"top V = Poset.top (poset V)"

definition bot :: "('A, 'a) CVA \<Rightarrow> ('A, 'a) Valuation" where
"bot V = Poset.bot (poset V)"

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

(* Lattice and quantale *) 

lemma quantalic_par_com :
  fixes V :: "('A, 'a) CVA" and a :: "('A, 'a) Valuation" and U :: "(('A, 'a) Valuation) set"
  assumes "valid V" and "is_quantalic V"
  and "a \<in> elems V" and "U \<subseteq> elems V"
shows "par V (sup V U) a = sup V {par V u a | u . u \<in> U}" 
proof -
  have "par V (sup V U) a = par V a (sup V U)"
    by (metis (no_types, opaque_lifting) CVA.is_complete_def CVA.sup_def assms(1) assms(2) assms(3) assms(4) is_quantalic_def sup_el valid_par_comm)
  moreover have "{par V u a | u . u \<in> U} = {par V a u | u . u \<in> U}"
    using assms(1) assms(3) assms(4) valid_par_comm by blast
  ultimately show ?thesis
  proof -
    have "par V a (CVA.sup V U) = CVA.sup V {par V a p |p. p \<in> U}"
      using assms(3) assms(4) assms(2) is_quantalic_def by blast
    then show ?thesis
      using \<open>par V (CVA.sup V U) a = par V a (CVA.sup V U)\<close> \<open>{par V u a |u. u \<in> U} = {par V a u |u. u \<in> U}\<close> by presburger
  qed 
qed

lemma binary_quantalic :
  fixes V :: "('A, 'a) CVA" and a b b' :: "('A, 'a) Valuation"
  assumes "valid V" and "is_quantalic V"
  and "a \<in> elems V" and "b \<in> elems V" and "b' \<in> elems V" 
shows "par V a (join V b b') = join V (par V a b) (par V a b')
\<and> seq V a (join V b b') = join V (seq V a b) (seq V a b')
\<and> seq V (join V b b') a = join V (seq V b a) (seq V b' a)"
proof -
  define "U" where "U = {b, b'}" 
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
    by (simp add: CVA.join_def CVA.sup_def Poset.join_def calculation(3))
  moreover have "join V (seq V a b) (seq V a b') = sup V {seq V a u | u . u \<in> U}"
    by (simp add: CVA.join_def CVA.sup_def Poset.join_def calculation(4))
  moreover have "join V (seq V b a) (seq V b' a) = sup V {seq V u a | u . u \<in> U}"
    by (simp add: CVA.join_def CVA.sup_def Poset.join_def calculation(5))
  ultimately show ?thesis using is_quantalic_def [where ?V=V ]
    using \<open>U \<subseteq> CVA.elems V\<close> assms(2) assms(3) by presburger
qed

lemma inf_elem : "is_complete V \<Longrightarrow> U \<subseteq> elems V \<Longrightarrow> inf V U \<in> elems V"
  by (simp add: CVA.inf_def CVA.is_complete_def inf_el) 

lemma sup_elem : "is_complete V \<Longrightarrow> U \<subseteq> elems V \<Longrightarrow> sup V U \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.sup_def sup_el)

lemma meet_elem : "is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> meet V a b \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.meet_def meet_el)

lemma join_elem : "is_complete V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> join V a b \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.join_def join_el)

lemma top_elem : "is_complete V \<Longrightarrow> top V \<in> elems V"
  by (simp add: CVA.is_complete_def CVA.top_def Poset.top_def sup_el)

lemma bot_elem : "is_complete V \<Longrightarrow> bot V \<in> elems V"
  by (simp add: CVA.bot_def CVA.is_complete_def Poset.bot_def sup_el) 

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

(* Hoare logic rules: https://en.wikipedia.org/wiki/Hoare_logic#Rules *)

(* [Proposition 3, TMCVA] *)
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

(* To recover the ordinary frame rule, we must constrain so that 'par V a (neut_seq V (d f) = a' *)
(* See https://en.wikipedia.org/wiki/Separation_logic#Reasoning_about_programs:_triples_and_proof_rules 
 where there is an additional condition mod(C) \<inter> fv(R) = \<emptyset> *)
proposition hoare_frame_rule :
  fixes V :: "('A, 'a) CVA" and p f a q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "f \<in> elems V" and "a \<in> elems V" and "q \<in> elems V" 
  and "hoare V p a q" 
shows "hoare V (par V f p) (par V a (neut_seq V (d f))) (par V f q)" 
proof - 
  have "le V (seq V p a) q"
    using assms(6) by force 
  moreover have "le V (par V f (seq V p a)) (par V f q)"
    by (smt (verit, ccfv_threshold) V_valid assms(2) assms(3) assms(4) assms(5) calculation valid_le_reflexive valid_par_mono valid_seq_elem) 
  ultimately show ?thesis
    by (smt (verit) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) d_elem_is_open neutral_is_element valid_neutral_law_right valid_par_comm valid_par_elem valid_poset valid_semigroup valid_seq_elem valid_transitivity valid_weak_exchange)
qed

proposition hoare_neut_seq_rule :
  fixes V :: "('A, 'a) CVA" and p:: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V"
  shows "hoare V p (neut_seq V (d p)) p"
  by (metis CVA.valid_welldefined V_valid assms(2) valid_le_reflexive valid_neutral_law_right)

proposition hoare_composition_rule :
  fixes V :: "('A, 'a) CVA" and p q r a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "q \<in> elems V" and "r \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
  and "hoare V p a q" and "hoare V q b r"
shows "hoare V p (seq V a b) r"
  by (smt (verit) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) valid_comb_associative valid_le_reflexive valid_le_transitive valid_seq_elem valid_seq_mono)

proposition hoare_consequence_rule :
  fixes V :: "('A, 'a) CVA" and p p' q q' a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "p' \<in> elems V" and "q \<in> elems V" and "q' \<in> elems V" and "a \<in> elems V"
  and "le V p' p" and "le V q q'" and "hoare V p a q"
shows "hoare V p' a q'"
  by (smt (verit) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) comb_is_element valid_gc_poset valid_monotone valid_poset valid_reflexivity valid_semigroup valid_transitivity)  

(*
proposition hoare_failure_rule :
  fixes V :: "('A, 'a) CVA" and p q :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_quantalic : "is_quantalic V"
  and "p \<in> elems V" and "q \<in> elems V"
shows "hoare V p (bot V) q" 
proof -
  have "seq V p (bot V) = sup V {seq V p u | u.  u \<in> {}}" using is_quantalic_def [where ?V=V]
  proof -
    have f1: "\<And>c. sup (CVA.poset (c::('A, 'a) CVA)) {} = CVA.bot c"
      by (simp add: CVA.bot_def Poset.bot_def)
    have f2: "\<And>p P. p \<notin> CVA.elems V \<or> \<not> P \<subseteq> CVA.elems V \<or> sup (CVA.poset V) {seq V p pa |pa. pa \<in> P} = seq V p (sup (CVA.poset V) P)"
      by (smt (z3) CVA.sup_def V_quantalic \<open>is_quantalic V \<equiv> CVA.is_complete V \<and> (\<forall>a U. U \<subseteq> CVA.elems V \<longrightarrow> a \<in> CVA.elems V \<longrightarrow> par V a (CVA.sup V U) = CVA.sup V {par V a u |u. u \<in> U} \<and> seq V a (CVA.sup V U) = CVA.sup V {seq V a u |u. u \<in> U} \<and> seq V (CVA.sup V U) a = CVA.sup V {seq V u a |u. u \<in> U})\<close>)
    have "p \<in> CVA.elems V \<and> {} \<subseteq> CVA.elems V"
      using assms(3) by blast
    then have "sup (CVA.poset V) {seq V p pa |pa. pa \<in> {}} = seq V p (CVA.bot V)"
      using f2 f1 by presburger
    then show ?thesis
      by (simp add: CVA.sup_def)
  qed
  moreover have "sup V {seq V p u | u.  u \<in> {}} = bot V"
    by (simp add: CVA.bot_def CVA.sup_def Poset.bot_def) 
  moreover have "le V (bot V) q"
  ultimately show ?thesis
  *)


proposition hoare_choice_rule :
  fixes V :: "('A, 'a) CVA" and p q a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_quantalic : "is_quantalic V"
  and "p \<in> elems V" and "q \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
shows "hoare V p (join V a b) q = (hoare V p a q \<and> hoare V p b q)" 
proof (rule iffI, goal_cases)
  case 1
  then show ?case 
  proof -
    have "le V (seq V p (join V a b)) q"
      using "1" by blast 
    moreover have "seq V p (join V a b) = join V (seq V p a) (seq V p b)"
      using V_quantalic V_valid assms(3) assms(5) assms(6) binary_quantalic by blast 
    moreover have "le V (seq V p a) (seq V p (join V a b)) \<and> le V (seq V p b) (seq V p (join V a b))" 
      using join_greater [where ?P="poset V" and ?a="seq V p a" and ?b="seq V p b"]
      by (metis (no_types, opaque_lifting) CVA.is_complete_def CVA.join_def CVA.valid_welldefined V_quantalic V_valid assms(3) assms(5) assms(6) calculation(2) comb_is_element is_quantalic_def)
    moreover have "le V (seq V p a) q \<and> le V (seq V p b) q"
      by (smt (verit, del_insts) "1" V_quantalic V_valid assms(3) assms(4) assms(5) assms(6) calculation(3) is_quantalic_def join_elem valid_le_transitive valid_seq_elem) 
    ultimately show ?thesis
      by force
  qed
next
  case 2
  then show ?case
    by (smt (verit, del_insts) CVA.is_complete_def CVA.join_def V_quantalic V_valid assms(3) assms(4) assms(5) assms(6) binary_quantalic is_quantalic_def join_property valid_seq_elem) 
qed


(* Rely-guarantee logic rules: 

1. van Staden, Stephan. "On rely-guarantee reasoning." Mathematics of Program Construction: 12th International Conference, MPC 2015, Königswinter, Germany, June 29--July 1, 2015. Proceedings 12. Springer International Publishing, 2015.
2. Hoare, CAR Tony, et al. "Concurrent kleene algebra." CONCUR 2009-Concurrency Theory: 20th International Conference, CONCUR 2009, Bologna, Italy, September 1-4, 2009. Proceedings 20. Springer Berlin Heidelberg, 2009.
3. Hoare, Tony, et al. "Concurrent Kleene algebra and its foundations." The Journal of Logic and Algebraic Programming 80.6 (2011): 266-296. 

Todo : - identify minimal invariance property
       - develop further properties of invariants (closures, lattice, etc.)
       - assume completeness for infima/suprema/iteration rules
*)

proposition rg_sequential_rule :
  fixes V :: "('A, 'a) CVA" and r g p p' p'' a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and r_el : "r \<in> elems V" and g_el : "g \<in> elems V" and p_el : "p \<in> elems V" and p'_el : "p' \<in> elems V" and p''_el : "p'' \<in> elems V" and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  and rg1 : "rg V p r a g p'" and rg2 : "rg V p' r b g p''"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
shows "rg V p r (seq V a b) g p''"
proof - 
  define "gl" (infixl \<open>\<preceq>\<close> 54) where "a \<preceq> b = le V a b" for a b
  define "sc" (infixl \<open>\<Zsemi>\<close> 55) where "a \<Zsemi> b = seq V a b" for a b
  define "pc" (infixl \<open>\<parallel>\<close> 55) where "a \<parallel> b = par V a b" for a b 

  have "p \<Zsemi> (r \<parallel> a) \<preceq> p' \<and> a \<preceq> g"
    using gl_def pc_def rg1 sc_def by auto
  moreover have "(p' \<Zsemi> (r \<parallel> b)) \<preceq> p'' \<and> (b \<preceq> g)"
    using gl_def pc_def rg2 sc_def by auto               
  moreover have guar : "a \<Zsemi> b \<preceq> g"  unfolding gl_def sc_def using invariant_def [where ?V=V and ?i=g]
    by (smt (z3) V_valid a_el b_el g_el inv_g rg1 rg2 valid_seq_mono)
  moreover have "(p \<Zsemi> (r \<parallel> a)) \<preceq> p'"
   using calculation(1) by fastforce
  moreover have "(p \<Zsemi> (r \<parallel> a)) \<Zsemi> (r \<parallel> b) \<preceq> p' \<Zsemi> (r \<parallel> b)" 
    using gl_def pc_def sc_def calculation(4) valid_seq_mono [where ?V=V and ?a="p \<Zsemi> (r \<parallel> a)" and ?a'="p'" and b="r \<parallel> b" and b'="r \<parallel> b" ] 
    CVA.valid_welldefined Poset.valid_def V_valid a_el b_el comb_is_element p'_el p_el r_el valid_elems valid_poset valid_semigroup
    by (smt (verit)) 
  moreover have "p \<Zsemi> ((r \<parallel> a) \<Zsemi> (r \<parallel> b)) = (p \<Zsemi> (r \<parallel> a) \<Zsemi> (r \<parallel> b))" using valid_seq_assoc [where ?V=V]
    by (smt (verit) CVA.valid_welldefined V_valid a_el b_el p_el pc_def r_el sc_def valid_comb_associative valid_par_elem) 
  moreover have "r \<parallel> (a \<Zsemi> b) \<preceq> (r \<parallel> a) \<Zsemi> (r \<parallel> b)" using invariant_def
    using \<open>(\<Zsemi>) \<equiv> seq V\<close> \<open>(\<parallel>) \<equiv> par V\<close> \<open>(\<preceq>) \<equiv> CVA.le V\<close> a_el b_el inv_r by blast
  moreover have "p \<in> elems V \<and> (r \<parallel> (a \<Zsemi> b)) \<in> elems V \<and> ((r \<parallel> a) \<Zsemi> (r \<parallel> b)) \<in> elems V"
    by (metis V_valid a_el b_el p_el pc_def r_el sc_def valid_par_elem valid_seq_elem)  
  moreover have "p \<Zsemi> (r \<parallel> (a \<Zsemi> b)) \<preceq> p \<Zsemi> ((r \<parallel> a) \<Zsemi> (r \<parallel> b))" using gl_def pc_def sc_def 
      valid_seq_mono [where ?V=V and a=p and a'=p and ?b="r \<parallel> (a \<Zsemi> b)" and b'="(r \<parallel> a) \<Zsemi> (r \<parallel> b)"] calculation
    by (smt (verit) CVA.valid_welldefined Poset.valid_def V_valid valid_poset valid_semigroup) 
  moreover have "p \<Zsemi> (r \<parallel> (a \<Zsemi> b)) \<preceq> p' \<Zsemi> (r \<parallel> b)" using gl_def pc_def sc_def calculation valid_le_transitive [where ?V=V]
    by (smt (verit, ccfv_threshold) V_valid b_el p'_el r_el valid_par_elem valid_seq_elem)
  moreover have "p \<Zsemi> (r \<parallel> (a \<Zsemi> b)) \<preceq> p''" unfolding gl_def pc_def sc_def using calculation valid_le_transitive [where ?V=V]
    by (smt (verit, best) V_valid b_el fst_conv gl_def p''_el p'_el pc_def prod.exhaust_sel r_el rg2 sc_def snd_conv valid_par_elem valid_seq_elem)
  ultimately show ?thesis
    using \<open>(\<Zsemi>) \<equiv> seq V\<close> \<open>(\<parallel>) \<equiv> par V\<close> gl_def by blast 
qed

(* Note Thm 8.4 of [2,3] in a CKA parallel restricted to invariants corresponds to supremum in the
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
   by (smt (verit, ccfv_threshold) V_valid assms(10) assms(11) assms(5) assms(8) assms(9) hoare_consequence_rule meet_elems meet_p1p2 valid_par_elem valid_seq_elem) 

  moreover have "le V (seq V (meet V p1 p2) (par V (meet V r1 r2) (par V a1 a2))) (meet V q1 q2)" using meet_property 1111 0000
    by (smt (verit, ccfv_SIG) CVA.is_complete_def CVA.meet_def V_complete V_valid assms(10) assms(11) assms(5) assms(6) meet_elems valid_par_elem valid_seq_elem) 

  ultimately show ?thesis
    by force 
qed

proposition rg_neut_par_rule :
  fixes V :: "('A, 'a) CVA" and p r g q :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "r \<in> elems V" and "g \<in> elems V" and "q \<in> elems V"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
  and "rg V p r (neut_par V (d r)) g q" 
shows "hoare V p r q"
  by (metis CVA.valid_welldefined V_valid assms(3) assms(8) valid_elems valid_neutral_law_right) 

(*
proposition rg_choice_rule :
  fixes V :: "('A, 'a) CVA" and p r g q :: "('A,'a) Valuation" and U :: "(('A,'a) Valuation) set"
  assumes V_valid : "valid V"
  and V_complete : "is_complete V"
  and V_quantale : "is_quantalic V"
  and "p \<in> elems V" and "r \<in> elems V" and "U \<subseteq> elems V" and "g \<in> elems V" and "q \<in> elems V"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
shows "rg V p r (sup V U) g q = (\<forall> u. u \<in> U \<longrightarrow> rg V p r u g q)"
proof (rule iffI, goal_cases)
  case 1
  then show ?case 
next
  case 2
  then show ?case 
qed
*)

end
