section \<open> CVA.thy \<close>

theory CVA
  imports Main OVA
begin

(* CVA type (concurrent valuation algebra) *)
record ('A, 'a) CVA =
  par_algebra :: "('A, 'a) OVA"
  seq_algebra :: "('A, 'a) OVA"

abbreviation prealgebra :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Prealgebra" where
"prealgebra V \<equiv> OVA.prealgebra (par_algebra V)"

abbreviation elems :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> OVA.elems (par_algebra V)"

abbreviation (input) space :: "('A,'a) CVA \<Rightarrow> 'A Space" where
"space V \<equiv> OVA.space (par_algebra V)"

abbreviation par :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"par V \<equiv> OVA.comb (par_algebra V)"

abbreviation seq :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"seq V \<equiv> OVA.comb (seq_algebra V)"

abbreviation le :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"le V \<equiv> OVA.le (par_algebra V)"

abbreviation local_le :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V \<equiv> OVA.local_le (par_algebra V)"

abbreviation neut_par :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_par V \<equiv> OVA.neut (par_algebra V)"

abbreviation neut_seq :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_seq V \<equiv> OVA.neut (seq_algebra V)"

abbreviation res :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"res V \<equiv> OVA.res (par_algebra V)"

abbreviation ext :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"ext V \<equiv>  OVA.ext (par_algebra V)"

definition valid :: "('A, 'a) CVA \<Rightarrow> bool" where
  "valid V \<equiv>
    let
        par = OVA.comb (par_algebra V);
        seq = OVA.comb (seq_algebra V);
        le = OVA.le (par_algebra V);

        \<delta> = OVA.neut (par_algebra V);
        \<epsilon> = OVA.neut (seq_algebra V);


        welldefined = OVA.valid (par_algebra V)
                      \<and> OVA.valid (seq_algebra V)
                      \<and> (OVA.prealgebra (par_algebra V) = OVA.prealgebra (seq_algebra V));

        commutativity = \<forall> a b . par a b = par b a;

        weak_exchange = \<forall> a b c d. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> c \<in> elems V \<longrightarrow> d \<in> elems V \<longrightarrow>
                         le (seq (par a b) (par c d)) (par (seq a c) (seq b d)) ;

        neutral_law_par = (\<forall>A . A \<in> opens (space V) \<longrightarrow> le (seq (\<delta> A) (\<delta> A)) (\<delta> A));

        neutral_law_seq = (\<forall>A . A \<in> opens (space V) \<longrightarrow> le (\<epsilon> A) (par (\<epsilon> A) (\<epsilon> A)))
    in
      welldefined \<and> commutativity \<and> weak_exchange \<and> neutral_law_par \<and> neutral_law_seq"

abbreviation hoare :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"hoare V p a q \<equiv> le V (seq V p a) q" 
 
(* Validity *)

lemma valid_welldefined: "valid V \<Longrightarrow> OVA.valid (par_algebra V) \<and> OVA.valid (seq_algebra V) \<and> (OVA.prealgebra (par_algebra V) = OVA.prealgebra (seq_algebra V))"
  unfolding valid_def
  by metis

lemma valid_commutativity: "valid V \<Longrightarrow> \<forall> a b . OVA.comb (par_algebra V) a b = OVA.comb (par_algebra V) b a"
  unfolding valid_def
  by metis

lemma valid_elems :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "elems V = OVA.elems (seq_algebra V)"
  by (metis CVA.valid_welldefined assms valid_gc_poset)

lemma valid_le :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "le V = OVA.le (seq_algebra V)"
  by (metis (mono_tags, opaque_lifting) CVA.valid_welldefined assms valid_gc_poset) 

lemma local_le :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "local_le V = OVA.local_le (seq_algebra V)"
  by (simp add: CVA.valid_welldefined assms valid_gc_poset)

lemma valid_weak_exchange: "valid V \<Longrightarrow> a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> a3 \<in> elems V \<Longrightarrow> a4 \<in> elems V \<Longrightarrow>
                        le V (seq V (par V a1 a2) (par V a3 a4)) (par V (seq V a1 a3) (seq V a2 a4))"
  unfolding valid_def
  by presburger

lemma valid_neutral_law_par: "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow>  \<delta>A = (neut_par V A)
  \<Longrightarrow> le V (seq V \<delta>A \<delta>A) \<delta>A"
  unfolding valid_def
  by meson

lemma valid_neutral_law_seq: "valid V \<Longrightarrow>  A \<in> opens (space V) \<Longrightarrow> \<epsilon>A = (neut_seq V A)
  \<Longrightarrow> le V \<epsilon>A (par V \<epsilon>A \<epsilon>A)"
  unfolding valid_def
  by meson

lemma valid_res: "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> elems V \<Longrightarrow> res V A a = OVA.res (seq_algebra V) A a"
  unfolding valid_def
  by (metis res_def valid_gc_poset)

lemma valid_ext: 
  fixes V :: "('A, 'a) CVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and A_open : "A \<in> opens (space V)" 
  and b_elem : "b \<in> elems V" 
  and B_leq_A : "d b \<subseteq> A"
  defines "ex \<equiv> ext V" and "ex' \<equiv> OVA.ext (seq_algebra V)"
  shows "ex A b = ex' A b"
  unfolding valid_def
proof -
(*
    fix b
    assume "b \<in> elems V" 
    fix A
    assume "A \<in> opens (space V)"
    assume "B \<subseteq> A" 
*)
    define "B" where "B = d b"
    define "pr" where "pr = res V"
    have "local_le V B (pr B (ex A b)) b"
      by (metis A_open B_def B_leq_A CVA.valid_welldefined Grothendieck.local_le OVA.valid_welldefined V_valid b_elem ex_def galois_insertion pr_def valid_poset valid_reflexivity)
     moreover have "A \<in> opens (space V) \<and> B \<in> opens (space V)"
       using A_open B_def CVA.valid_welldefined V_valid b_elem d_elem_is_open by blast 
    moreover have lhs:"local_le V A (ex A b) (ex' A b)" using valid_res [where ?V=V] OVA.res_ext_adjunction [where
   ?V="seq_algebra V" and ?A=A and ?B=B and ?a="(ex A b)" and ?b=b]
      by (metis (no_types, lifting) B_def B_leq_A CVA.valid_welldefined V_valid b_elem calculation(1) calculation(2) d_ext ex'_def ex_def ext_elem pr_def valid_elems)
    moreover have "local_le V B (pr B (ex' A b)) b"
      by (metis B_def B_leq_A CVA.valid_welldefined V_valid b_elem calculation(1) calculation(2) ex'_def ex_def galois_insertion ext_elem pr_def valid_elems valid_res) 
    moreover have rhs:"local_le V A (ex' A b) (ex A b)" using valid_res [where ?V=V] OVA.res_ext_adjunction [where
   ?V="par_algebra V" and ?A=A and ?B=B and ?a="(ex' A b)" and ?b=b]
      by (metis (full_types) B_def B_leq_A CVA.valid_welldefined V_valid b_elem calculation(2) calculation(4) d_ext ex'_def ex_def ext_elem pr_def valid_elems) 
    moreover have "ex' A b = ex A b" using calculation
      by (metis B_def B_leq_A CVA.valid_welldefined V_valid b_elem d_ext e_ext ex'_def ex_def prod.collapse valid_antisymmetry valid_elems valid_ob valid_prealgebra)     
    ultimately show "ex A b = ex' A b"
      by presburger 
  qed

(* To-do: can we actually prove ex = ex' with fun ext? *)
lemma valid_ext_funext: 
  fixes V :: "('A, 'a) CVA"
  defines "ex \<equiv> ext V" and "ex' \<equiv> OVA.ext (seq_algebra V)"
  shows "ex = ex'"
  oops

(* Paper results *)

(* [Proposition 1 (1/3), CVA] *)
proposition epsilon_le_delta [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V \<epsilon>A \<delta>A"
proof -
  have "\<epsilon>A = seq V \<epsilon>A \<epsilon>A" using assms valid_welldefined [where ?V=V] valid_neutral_law_left
    by (metis fst_conv neutral_is_element) 
  moreover have "\<epsilon>A = par V \<delta>A \<epsilon>A " using assms valid_welldefined [where ?V=V]
      valid_neutral_law_left
    by (metis fst_conv neutral_is_element valid_elems) 
  moreover have "\<epsilon>A = par V \<epsilon>A \<delta>A " using assms valid_welldefined [where ?V=V] 
    by (metis calculation(2) valid_commutativity) 
  moreover have "seq V \<epsilon>A \<epsilon>A = seq V (par V \<delta>A \<epsilon>A) (par V \<epsilon>A \<delta>A)" using calculation assms
    by auto
  moreover have "le V (seq V (par V \<delta>A \<epsilon>A) (par V \<epsilon>A \<delta>A)) (par V (seq V \<delta>A \<epsilon>A) (seq V \<epsilon>A \<delta>A))"
    using calculation assms valid_weak_exchange
    by (metis CVA.valid_welldefined \<delta>A_def \<epsilon>A_def neutral_is_element valid_elems)
  moreover have "(seq V \<delta>A \<epsilon>A) = \<delta>A" using calculation assms
    by (metis CVA.valid_welldefined fst_eqD neutral_is_element valid_elems valid_neutral_law_right)  
 moreover have "(seq V \<epsilon>A \<delta>A ) = \<delta>A" using calculation assms valid_neutral_law_left
   by (metis CVA.valid_welldefined fst_conv neutral_is_element valid_elems) 
  moreover have "(par V (seq V \<delta>A \<epsilon>A) (seq V \<epsilon>A \<delta>A)) = par V \<delta>A \<delta>A" using calculation assms
    by auto
  moreover have "par V \<delta>A \<delta>A = \<delta>A" using assms valid_neutral_law_right
    by (metis CVA.valid_welldefined fst_conv neutral_is_element) 
  ultimately show ?thesis
    by metis
qed

lemma epsilon_par_epsilon_le_epsilon :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V (par V \<epsilon>A \<epsilon>A) \<epsilon>A" 
proof -
  have "le V (par V \<epsilon>A \<epsilon>A) (par V \<epsilon>A \<delta>A)" using assms valid_comb_monotone 
    by (smt (z3) CVA.valid_welldefined comb_is_element fst_conv neutral_is_element valid_domain_law valid_elems valid_neutral_law_left valid_neutral_law_right valid_weak_exchange)
  moreover have "par V \<epsilon>A \<delta>A = \<epsilon>A"
    by (smt (verit) A_open CVA.valid_welldefined V_valid \<delta>A_def \<epsilon>A_def fst_conv neutral_is_element valid_elems valid_neutral_law_right)
  ultimately show ?thesis
    by metis
qed

lemma delta_le_delta_seq_delta :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "le V \<delta>A (seq V \<delta>A \<delta>A)"
proof -
  have "le V (seq V \<epsilon>A \<delta>A) (seq V \<delta>A \<delta>A)" using assms OVA.valid_comb_monotone
 [where ?V="seq_algebra V" and ?a1.0=\<epsilon>A and ?a2.0=\<delta>A and ?b1.0=\<delta>A and ?b2.0=\<delta>A]
    by (smt (verit) CVA.valid_welldefined epsilon_le_delta neutral_is_element valid_gc_poset valid_poset valid_reflexivity valid_semigroup)
  moreover have "seq V \<epsilon>A \<delta>A = \<delta>A"
    by (smt (verit) A_open CVA.valid_welldefined V_valid \<delta>A_def \<epsilon>A_def fst_conv neutral_is_element surj_pair valid_elems valid_neutral_law_left)
  ultimately show ?thesis
    by metis
qed

(* [Proposition 1 (2/3), CVA] *)
proposition delta_seq_delta_eq_delta [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<delta>A \<equiv> neut_par V A"
  shows "(seq V \<delta>A \<delta>A) = \<delta>A"
proof -
  have "le V \<delta>A (seq V \<delta>A \<delta>A)" using assms delta_le_delta_seq_delta
    by blast
  moreover have "le V (seq V \<delta>A \<delta>A) \<delta>A" using assms valid_neutral_law_par [where ?V=V and ?A=A]
    by blast
  ultimately show ?thesis
    by (metis A_open CVA.valid_welldefined V_valid \<delta>A_def comb_is_element neutral_is_element valid_antisymmetry valid_elems valid_poset valid_semigroup)
qed

(* [Proposition 1 (3/3), CVA] *)
proposition epsilon_par_epsilon_eq_epsilon [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)"
  defines "\<epsilon>A \<equiv> neut_seq V A"
  shows "(par V \<epsilon>A \<epsilon>A) = \<epsilon>A"
proof -
  have "le V (par V \<epsilon>A \<epsilon>A) \<epsilon>A" using assms epsilon_par_epsilon_le_epsilon
    by blast
  moreover have "le V \<epsilon>A (par V \<epsilon>A \<epsilon>A)" using assms valid_neutral_law_seq [where ?V=V and ?A=A]
    by blast
  ultimately show ?thesis
    by (metis A_open CVA.valid_welldefined V_valid \<epsilon>A_def comb_is_element neutral_is_element valid_antisymmetry valid_elems valid_poset valid_semigroup)
qed

(* [Proposition 2, CVA] *)
proposition comparitor :
  fixes V :: "('A, 'a) CVA" and a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and neutral_collapse : "neut_par V = neut_seq V"
  and strongly_neutral_seq: "\<forall> A B . seq V (neut_seq V A) (neut_seq V B) = neut_seq V (A \<union> B)" 
  shows "le V (seq V a b) (par V a b)"
proof -
  define "A" where "A = d a"
  define "B" where "B = d b"
  define "pc" where "pc = par V"
  define "sc" where "sc = seq V"
  define "\<gamma>" where "\<gamma> = neut_par V"
  have "A \<union> B \<in> opens (space V)"
    by (metis A_def B_def CVA.valid_welldefined V_valid a_elem b_elem comb_is_element d_elem_is_open fst_conv neutral_is_element strongly_neutral_seq) 
  moreover have "a = pc a (\<gamma> A)" 
    by (metis pc_def A_def CVA.valid_welldefined V_valid \<gamma>_def a_elem valid_neutral_law_right)
  moreover have "b = pc (\<gamma> B) b"
    by (metis pc_def B_def CVA.valid_welldefined V_valid \<gamma>_def b_elem  valid_commutativity valid_neutral_law_right)
  moreover have "sc a b = sc (pc a (\<gamma> A)) (pc (\<gamma> B) b)"
    using \<open>b = pc (\<gamma> B) b\<close> calculation by presburger
  moreover have "le V (sc (pc a (\<gamma> A)) (pc (\<gamma> B) b)) (pc (sc a (\<gamma> B)) (sc (\<gamma> A) b))"
    by (metis (no_types, lifting) A_def B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem d_elem_is_open neutral_is_element pc_def sc_def valid_weak_exchange)
  moreover have "d (sc a (\<gamma> B)) = A \<union> B"
    by (metis (no_types, lifting) A_def B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem d_elem_is_open fst_conv neutral_is_element sc_def valid_domain_law valid_elems) 
  moreover have "sc a (\<gamma> B) = sc (sc a (\<gamma> B)) (\<gamma> (A \<union> B))"using assms valid_neutral_law_right
    by (metis (no_types, lifting) B_def CVA.valid_welldefined \<gamma>_def calculation(6) comb_is_element d_elem_is_open neutral_is_element sc_def valid_elems) 
  moreover have "... = sc a (sc (\<gamma> B) (\<gamma> (A \<union> B)))"
    by (metis (no_types, lifting) B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem calculation(1) d_elem_is_open neutral_is_element sc_def valid_comb_associative valid_elems)
  moreover have "... = sc a (\<gamma> (A \<union> B))"
    by (metis \<gamma>_def neutral_collapse sc_def strongly_neutral_seq sup_commute sup_left_idem) 
  moreover have "... = OVA.ext (seq_algebra V) (A \<union> B) a"  using assms calculation OVA.symmetric_ext [where ?V="seq_algebra V"]
    by (metis (mono_tags, lifting) A_def CVA.valid_welldefined \<gamma>_def sc_def sup_ge1 valid_elems)
  moreover have "... = pc a (\<gamma> (A \<union> B))"
    by (metis A_def CVA.valid_welldefined \<gamma>_def assms(1) assms(2) calculation(1) pc_def sup_ge1 symmetric_ext valid_ext)
  moreover have "sc (\<gamma> A) b = sc (\<gamma> (A \<union> B)) (sc (\<gamma> A) b)"  using assms valid_neutral_law_left
      [where ?V="seq_algebra V"]
    by (smt (verit) A_def B_def CVA.valid_welldefined \<gamma>_def comb_is_element d_elem_is_open d_neut neutral_is_element sc_def valid_domain_law valid_elems) 
  moreover have "... = sc (sc (\<gamma> (A \<union> B)) (\<gamma> A)) b"
    by (metis (no_types, lifting) A_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem calculation(1) d_elem_is_open neutral_is_element sc_def valid_comb_associative valid_elems) 
  moreover have "... = sc (\<gamma> (A \<union> B)) b"
    by (simp add: \<gamma>_def neutral_collapse sc_def strongly_neutral_seq sup_commute) 
  moreover have "... =   OVA.ext (seq_algebra V) (A \<union> B) b"
    by (metis B_def CVA.valid_welldefined V_valid \<gamma>_def b_elem calculation(1) ext_def neutral_collapse sc_def sup_ge2 valid_elems)
  moreover have "... =   pc (\<gamma> (A \<union> B)) b" using valid_ext
    by (metis B_def CVA.valid_welldefined V_valid \<gamma>_def b_elem calculation(1) pc_def sup_ge2 symmetric_ext valid_commutativity) 
  moreover have "pc (sc a (\<gamma> B)) (sc (\<gamma> A) b) = pc (pc a (\<gamma> (A \<union> B))) ( pc (\<gamma> (A \<union> B)) b)"
    using calculation(10) calculation(11) calculation(12) calculation(13) calculation(14) calculation(15) calculation(16) calculation(7) calculation(8) calculation(9) by presburger  
  moreover have "... =   pc a (pc (\<gamma> (A \<union> B)) ( pc (\<gamma> (A \<union> B)) b))" using valid_comb_associative 
    by (metis (no_types, lifting) B_def CVA.valid_welldefined Un_upper2 V_valid \<gamma>_def assms(2) b_elem calculation(1) calculation(16) ext_elem neutral_is_element pc_def valid_elems) 
  moreover have "... =   pc a (pc (\<gamma> (A \<union> B)) b)"   
    by (smt (verit, del_insts) B_def CVA.valid_welldefined Un_upper2 V_valid \<gamma>_def b_elem calculation(1) calculation(16) d_elem_is_open d_ext ext_elem pc_def valid_elems valid_neutral_law_left)
  moreover have "... =   pc a (pc b (\<gamma> (A \<union> B)))"
    by (simp add: V_valid pc_def valid_commutativity) 
moreover have "... =   pc a b"
  by (metis (no_types, lifting) A_def B_def CVA.valid_welldefined V_valid \<gamma>_def assms(2) b_elem calculation(1) comb_is_element neutral_is_element pc_def valid_comb_associative valid_domain_law valid_neutral_law_right) 
  ultimately show ?thesis
    by (metis pc_def sc_def) 
qed

lemma neutral_collapse_strongly_neutral :
  fixes V :: "('A, 'a) CVA" and A B :: "'A Open"
  defines "\<gamma> \<equiv> neut_par V"
  assumes V_valid : "valid V" and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)"
  and neutral_collapse : "neut_par V = neut_seq V"
shows "seq V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B) \<longleftrightarrow> par V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)"
proof standard
  assume "seq V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)"
  define "pc" where "pc = par V"
  define "sc" where "sc = seq V"
  have "A \<union> B \<in> opens (space V)"
    by (metis A_open B_open CVA.valid_welldefined V_valid comb_is_element d_elem_is_open d_neut neutral_is_element valid_domain_law) 
  moreover have "d (pc (\<gamma> A) (\<gamma> B)) = A \<union> B"
    by (metis A_open B_open CVA.valid_welldefined V_valid \<gamma>_def d_neut neutral_is_element pc_def valid_domain_law) 
  moreover have "pc (\<gamma> A) (\<gamma> B) = pc  (\<gamma> (A \<union> B)) (pc (\<gamma> A) (\<gamma> B))"
    by (metis A_open B_open CVA.valid_welldefined V_valid \<gamma>_def calculation(2) comb_is_element neutral_is_element pc_def valid_neutral_law_left)
  moreover have "... = pc (pc  (\<gamma> (A \<union> B)) (\<gamma> A)) (\<gamma> B)"
    using A_open B_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) neutral_is_element pc_def valid_comb_associative by fastforce 
  moreover have "... = pc (ext V (A \<union> B) (\<gamma> A)) (\<gamma> B)"
    by (metis (no_types, lifting) A_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut ext_def neutral_is_element pc_def sup_ge1) 
  moreover have "... = pc (OVA.ext (seq_algebra V) (A \<union> B) (\<gamma> A)) (\<gamma> B)"
    by (metis A_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut neutral_is_element sup_ge1 valid_ext)
    moreover have "... = pc (sc (\<gamma> (A \<union> B)) (\<gamma> A)) (\<gamma> B)"
      by (metis (no_types, lifting) A_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element sc_def sup_ge1)
    moreover have "... = pc (\<gamma> (A \<union> B)) (\<gamma> B)"
      by (smt (verit) A_open B_open CVA.valid_welldefined V_valid \<gamma>_def \<open>seq V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)\<close> calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element pc_def sc_def sup_ge1 symmetric_ext valid_comb_associative valid_commutativity valid_elems valid_neutral_law_right) 
  moreover have "... = ext V (A \<union> B) (\<gamma> B)"
    by (metis (no_types, lifting) B_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut ext_def neutral_is_element pc_def sup_commute sup_ge1) 
  moreover have "... = \<gamma> (A \<union> B)"
    by (smt (verit) A_open B_open CVA.valid_welldefined V_valid \<gamma>_def \<open>seq V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)\<close> calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element sup_ge2 valid_comb_associative valid_ext valid_neutral_law_right)
  show " par V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)"
    by (metis \<open>CVA.ext V (A \<union> B) (\<gamma> B) = \<gamma> (A \<union> B)\<close> calculation(3) calculation(4) calculation(5) calculation(6) calculation(7) calculation(8) calculation(9) pc_def) 
next
  assume "par V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)"
  define "sc" where "sc = seq V"
  define "pc" where "pc = par V"
  have "A \<union> B \<in> opens (space V)"
    by (metis A_open B_open CVA.valid_welldefined V_valid comb_is_element d_elem_is_open d_neut neutral_is_element valid_domain_law)
  moreover have "d (sc (\<gamma> A) (\<gamma> B)) = A \<union> B"
    using A_open B_open CVA.valid_welldefined V_valid \<gamma>_def neutral_is_element sc_def valid_elems by fastforce
  moreover have "sc (\<gamma> A) (\<gamma> B) = sc  (\<gamma> (A \<union> B)) (sc (\<gamma> A) (\<gamma> B))"
    by (metis A_open B_open CVA.valid_welldefined V_valid \<gamma>_def calculation(2) comb_is_element neutral_collapse neutral_is_element sc_def valid_neutral_law_left)
  moreover have "... = sc (sc  (\<gamma> (A \<union> B)) (\<gamma> A)) (\<gamma> B)"
    by (metis (no_types, lifting) A_open B_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) neutral_is_element sc_def valid_comb_associative valid_elems) 
  moreover have "... = sc (ext V (A \<union> B) (\<gamma> A)) (\<gamma> B)"
    by (metis (no_types, lifting) A_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element sc_def sup_ge1 valid_ext) 
    moreover have "... = sc (pc (\<gamma> (A \<union> B)) (\<gamma> A)) (\<gamma> B)"
      by (metis (no_types, lifting) A_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut ext_def neutral_is_element pc_def sup_ge1) 
    moreover have "... = sc (\<gamma> (A \<union> B)) (\<gamma> B)" 
      by (smt (verit) A_open B_open CVA.valid_welldefined V_valid \<gamma>_def \<open>par V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)\<close> calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element sc_def pc_def sup_ge1 symmetric_ext valid_comb_associative valid_commutativity valid_elems valid_neutral_law_right) 
  moreover have "... = ext V (A \<union> B) (\<gamma> B)"
    by (metis (no_types, lifting) B_open CVA.valid_welldefined V_valid \<gamma>_def calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element sc_def sup_ge2 valid_ext) 
  moreover have "... = \<gamma> (A \<union> B)"
    by (smt (verit) A_open B_open CVA.valid_welldefined V_valid \<gamma>_def \<open>par V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)\<close> calculation(1) d_neut ext_def local.neutral_collapse neutral_is_element sup_ge2 valid_comb_associative valid_ext valid_neutral_law_right)
  show " seq V (\<gamma> A) (\<gamma> B) = \<gamma> (A \<union> B)"
    by (metis \<open>CVA.ext V (A \<union> B) (\<gamma> B) = \<gamma> (A \<union> B)\<close> calculation(3) calculation(4) calculation(5) calculation(6) calculation(7) calculation(8) sc_def) 
qed

(* [Proposition 3, CVA] *)
proposition hoare_concurrency_rule  :
  fixes V :: "('A, 'a) CVA" and p p' a a' q q' :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and "p \<in> elems V" and "p' \<in> elems V" and "a \<in> elems V" and "a' \<in> elems V" and "q \<in> elems V" and "q' \<in> elems V"
  and "hoare V p a q" and "hoare V p' a' q'"
  shows "hoare V (par V p p') (par V a a') (par V q q')"
proof -
  define "sc" where "sc = seq V"
  define "pc" where "pc = par V"
  define "gl" where "gl = le V"
  have "gl (sc p a) q"
    using assms(8) gl_def sc_def by blast 
  moreover have "gl (sc p' a') q'"
    using assms(9) gl_def sc_def by blast 
  moreover have "gl  (sc (pc p p') (pc a a')) (pc (sc p a) (sc p' a'))"
    using V_valid assms(2) assms(3) assms(4) assms(5) gl_def pc_def sc_def valid_weak_exchange by blast
moreover have "gl (pc (sc p a) (sc p' a')) (pc q q')"
  by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) comb_is_element gl_def pc_def sc_def valid_elems valid_monotone valid_semigroup) 
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) comb_is_element gl_def pc_def sc_def valid_elems valid_poset valid_semigroup valid_transitivity) 
qed

end
