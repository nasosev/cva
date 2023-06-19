theory CVA
  imports Main OVA
begin

record ('A, 'a) CVA =
  par_algebra :: "('A, 'a) OVA"
  seq_algebra :: "('A, 'a) OVA"

abbreviation presheaf :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Presheaf" where
"presheaf V \<equiv> OVA.presheaf (par_algebra V)"

abbreviation elems :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> OVA.elems (par_algebra V)"

abbreviation opens :: "('A,'a) CVA \<Rightarrow> 'A Open set" where
"opens V \<equiv> OVA.opens (par_algebra V)"

abbreviation par :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"par V \<equiv> OVA.comb (par_algebra V)"

abbreviation seq :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"seq V \<equiv> OVA.comb (seq_algebra V)"

abbreviation gle :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle V \<equiv> OVA.gle (par_algebra V)"

abbreviation local_le :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V \<equiv> OVA.local_le (par_algebra V)"

abbreviation neut_par :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_par V \<equiv> OVA.neut (par_algebra V)"

abbreviation neut_seq :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_seq V \<equiv> OVA.neut (seq_algebra V)"

abbreviation gprj :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gprj V \<equiv> OVA.gprj (par_algebra V)"

abbreviation gext :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gext V \<equiv>  OVA.gext (par_algebra V)"

definition valid :: "('A, 'a) CVA \<Rightarrow> bool" where
  "valid V \<equiv>
    let
        par = OVA.comb (par_algebra V);
        seq = OVA.comb (seq_algebra V);
        gle = OVA.gle (par_algebra V);

        \<delta> = OVA.neut (par_algebra V);
        \<epsilon> = OVA.neut (seq_algebra V);


        welldefined = OVA.valid (par_algebra V)
                      \<and> OVA.valid (seq_algebra V)
                      \<and> (OVA.presheaf (par_algebra V) = OVA.presheaf (seq_algebra V));

        commutativity = \<forall> a b . par a b = par b a;

        weak_exchange = \<forall> a b c d. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> c \<in> elems V \<longrightarrow> d \<in> elems V \<longrightarrow>
                         gle (seq (par a b) (par c d)) (par (seq a c) (seq b d)) ;

        neutral_law_par = (\<forall>A . A \<in> opens V \<longrightarrow> gle (seq (\<delta> A) (\<delta> A)) (\<delta> A));

        neutral_law_seq = (\<forall>A . A \<in> opens V \<longrightarrow> gle (\<epsilon> A) (par (\<epsilon> A) (\<epsilon> A)))
    in
      welldefined \<and> commutativity \<and> weak_exchange \<and> neutral_law_par \<and> neutral_law_seq"

(* LEMMAS *)

(* Validity *)

lemma valid_welldefined: "valid V \<Longrightarrow> OVA.valid (par_algebra V) \<and> OVA.valid (seq_algebra V) \<and> (OVA.presheaf (par_algebra V) = OVA.presheaf (seq_algebra V))"
  unfolding valid_def
  by metis

lemma valid_commutativity: "valid V \<Longrightarrow> \<forall> a b . OVA.comb (par_algebra V) a b = OVA.comb (par_algebra V) b a"
  unfolding valid_def
  by metis

lemma valid_elems :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "elems V = OVA.elems (seq_algebra V)"
  by (simp add: CVA.valid_welldefined assms valid_gc_poset)

lemma valid_gle :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "gle V = OVA.gle (seq_algebra V)"
  by (simp add: CVA.valid_welldefined assms valid_gc_poset)

lemma local_le :
  fixes V :: "('A, 'a) CVA"
  assumes "valid V"
  shows "local_le V = OVA.local_le (seq_algebra V)"
  by (simp add: CVA.valid_welldefined assms valid_gc_poset)

lemma valid_weak_exchange: "valid V \<Longrightarrow> a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> a3 \<in> elems V \<Longrightarrow> a4 \<in> elems V \<Longrightarrow>
                        gle V (seq V (par V a1 a2) (par V a3 a4)) (par V (seq V a1 a3) (seq V a2 a4))"
  unfolding valid_def
  by presburger

lemma valid_neutral_law_par: "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow>  \<delta>A = (neut_par V A)
  \<Longrightarrow> gle V (seq V \<delta>A \<delta>A) \<delta>A"
  unfolding valid_def
  by meson

lemma valid_neutral_law_seq: "valid V \<Longrightarrow>  A \<in> opens V \<Longrightarrow> \<epsilon>A = (neut_seq V A)
  \<Longrightarrow> gle V \<epsilon>A (par V \<epsilon>A \<epsilon>A)"
  unfolding valid_def
  by meson

lemma valid_gprj: "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a \<in> elems V \<Longrightarrow> gprj V A a = OVA.gprj (seq_algebra V) A a"
  unfolding valid_def
  by (simp add: gprj_def valid_gc_poset)


(* This follows from uniqueness of adjoints. *)
lemma valid_gext: 
  fixes V :: "('A, 'a) CVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" 
  and A_open : "A \<in> opens V" 
  and b_elem : "b \<in> elems V" 
  and B_leq_A : "d b \<subseteq> A"
  defines "ex \<equiv> gext V" and "ex' \<equiv> OVA.gext (seq_algebra V)"
  shows "ex A b = ex' A b"
  unfolding valid_def
proof -
(*
    fix b
    assume "b \<in> elems V" 
    fix A
    assume "A \<in> opens V"
    assume "B \<subseteq> A" 
*)
    define "B" where "B = d b"
    define "pr" where "pr = gprj V"
    have "local_le V B (pr B (ex A b)) b"
      by (metis A_open B_def B_leq_A CVA.valid_welldefined Grothendieck.local_le V_valid b_elem ex_def galois_insertion local_inclusion_domain pr_def valid_gc_poset valid_poset valid_presheaf valid_reflexivity valid_semigroup) 
     moreover have "A \<in> opens V \<and> B \<in> opens V"
      using B_def CVA.valid_welldefined V_valid \<open>A \<in> Space.opens (Presheaf.space (CVA.presheaf V))\<close> \<open>b \<in> Semigroup.elems (OVA.semigroup (par_algebra V))\<close> local_inclusion_domain by blast 
    moreover have lhs:"local_le V A (ex A b) (ex' A b)" using valid_gprj [where ?V=V] OVA.prj_ext_adjunction [where
   ?V="seq_algebra V" and ?A=A and ?B=B and ?a="(ex A b)" and ?b=b]
      by (smt (verit, ccfv_threshold) B_def B_leq_A CVA.valid_welldefined V_valid b_elem calculation(1) calculation(2) d_gext ex'_def ex_def gext_elem pr_def valid_elems) 
    moreover have "local_le V B (pr B (ex' A b)) b"
      by (metis B_def B_leq_A CVA.valid_welldefined V_valid b_elem calculation(1) calculation(2) ex'_def ex_def galois_insertion gext_elem pr_def valid_elems valid_gprj) 
    moreover have rhs:"local_le V A (ex' A b) (ex A b)" using valid_gprj [where ?V=V] OVA.prj_ext_adjunction [where
   ?V="par_algebra V" and ?A=A and ?B=B and ?a="(ex' A b)" and ?b=b]
      by (metis (full_types) B_def B_leq_A CVA.valid_welldefined V_valid b_elem calculation(2) calculation(4) d_gext ex'_def ex_def gext_elem pr_def valid_elems) 
    moreover have "ex' A b = ex A b" using calculation
      by (metis B_def B_leq_A CVA.valid_welldefined V_valid b_elem d_gext e_gext ex'_def ex_def prod.collapse valid_antisymmetry valid_elems valid_ob valid_presheaf)     
    ultimately show "ex A b = ex' A b"
      by presburger 
  qed

(*  To-do: can we actually prove ex = ex' with fun ext? *)
lemma valid_gext_funext: 
  fixes V :: "('A, 'a) CVA"
  defines "ex \<equiv> gext V" and "ex' \<equiv> OVA.gext (seq_algebra V)"
  shows "ex = ex'"
  oops

(* Paper results *)

(* [Proposition 1, CVA] *)
proposition epsilon_le_delta [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens V"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "gle V \<epsilon>A \<delta>A"
proof -
  have "\<epsilon>A = seq V \<epsilon>A \<epsilon>A" using assms valid_welldefined [where ?V=V] valid_neutral_law_left
      [where ?V="seq_algebra V" and ?A=A and ?a=\<epsilon>A and ?\<epsilon>="neut_seq V"]
    by (simp add: \<epsilon>A_def neutral_is_element)
  moreover have "\<epsilon>A = par V \<delta>A \<epsilon>A " using assms valid_welldefined [where ?V=V] valid_neutral_law_left
      [where ?V="par_algebra V" and ?A=A and ?a=\<epsilon>A and ?\<epsilon>="neut_par V"]
    by (simp add: \<delta>A_def \<epsilon>A_def neutral_is_element valid_elems)
  moreover have "\<epsilon>A = par V \<epsilon>A \<delta>A " using assms valid_welldefined [where ?V=V]
      valid_neutral_law_right
      [where ?V="par_algebra V" and ?A=A and ?a=\<epsilon>A and ?\<epsilon>="neut_par V"]
    by (simp add: \<delta>A_def \<epsilon>A_def neutral_is_element valid_elems)
  moreover have "seq V \<epsilon>A \<epsilon>A = seq V (par V \<delta>A \<epsilon>A) (par V \<epsilon>A \<delta>A)" using calculation assms
    by auto
  moreover have "gle V (seq V (par V \<delta>A \<epsilon>A) (par V \<epsilon>A \<delta>A)) (par V (seq V \<delta>A \<epsilon>A) (seq V \<epsilon>A \<delta>A))"
    using calculation assms valid_weak_exchange
    by (metis CVA.valid_welldefined \<delta>A_def \<epsilon>A_def neutral_is_element valid_elems)
  moreover have "(seq V \<delta>A \<epsilon>A) = \<delta>A" using calculation assms valid_neutral_law_right
[where ?V="seq_algebra V" and ?A=A and ?a=\<delta>A and ?\<epsilon>="neut_seq V"]
    by (metis CVA.valid_welldefined \<delta>A_def \<epsilon>A_def fstI neutral_is_element valid_elems)
 moreover have "(seq V \<epsilon>A \<delta>A ) = \<delta>A" using calculation assms valid_neutral_law_left
[where ?V="seq_algebra V" and ?A=A and ?a=\<delta>A and ?\<epsilon>="neut_seq V"]
   by (metis CVA.valid_welldefined \<delta>A_def \<epsilon>A_def fstI neutral_is_element valid_elems)
  moreover have "(par V (seq V \<delta>A \<epsilon>A) (seq V \<epsilon>A \<delta>A)) = par V \<delta>A \<delta>A" using calculation assms
    by auto
  moreover have "par V \<delta>A \<delta>A = \<delta>A" using assms valid_neutral_law_right
[where ?V="par_algebra V" and ?A=A and ?a=\<delta>A and ?\<epsilon>="neut_par V"]
    by (simp add: CVA.valid_welldefined \<delta>A_def neutral_is_element)
  ultimately show ?thesis
    by metis
qed

lemma epsilon_par_epsilon_le_epsilon :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens V"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "gle V (par V \<epsilon>A \<epsilon>A) \<epsilon>A"
proof -
  have "gle V (par V \<epsilon>A \<epsilon>A) (par V \<epsilon>A \<delta>A)" using assms OVA.combine_monotone
 [where ?V="par_algebra V" and ?a1.0=\<epsilon>A and ?a2.0=\<epsilon>A and ?b1.0=\<epsilon>A and ?b2.0=\<delta>A]
    by (smt (verit) CVA.valid_welldefined epsilon_le_delta neutral_is_element valid_elems valid_poset valid_reflexivity valid_semigroup)
  moreover have "par V \<epsilon>A \<delta>A = \<epsilon>A"
    by (smt (verit) A_open CVA.valid_welldefined V_valid \<delta>A_def \<epsilon>A_def fst_conv neutral_is_element valid_elems valid_neutral_law_right)
  ultimately show ?thesis
    by metis
qed

lemma delta_le_delta_seq_delta :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens V"
  defines "\<delta>A \<equiv> neut_par V A" and "\<epsilon>A \<equiv> neut_seq V A"
  shows "gle V \<delta>A (seq V \<delta>A \<delta>A)"
proof -
  have "gle V (seq V \<epsilon>A \<delta>A) (seq V \<delta>A \<delta>A)" using assms OVA.combine_monotone
 [where ?V="seq_algebra V" and ?a1.0=\<epsilon>A and ?a2.0=\<delta>A and ?b1.0=\<delta>A and ?b2.0=\<delta>A]
    by (smt (verit) CVA.valid_welldefined epsilon_le_delta neutral_is_element valid_gc_poset valid_poset valid_reflexivity valid_semigroup)
  moreover have "seq V \<epsilon>A \<delta>A = \<delta>A"
    by (smt (verit) A_open CVA.valid_welldefined V_valid \<delta>A_def \<epsilon>A_def fst_conv neutral_is_element surj_pair valid_elems valid_neutral_law_left)
  ultimately show ?thesis
    by metis
qed

(* [Proposition 1 cont., CVA] *)
proposition epsilon_par_epsilon_eq_epsilon [simp] :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens V"
  defines "\<epsilon>A \<equiv> neut_seq V A"
  shows "(par V \<epsilon>A \<epsilon>A) = \<epsilon>A"
proof -
  have "gle V (par V \<epsilon>A \<epsilon>A) \<epsilon>A" using assms epsilon_par_epsilon_le_epsilon
    by blast
  moreover have "gle V \<epsilon>A (par V \<epsilon>A \<epsilon>A)" using assms valid_neutral_law_seq [where ?V=V and ?A=A]
    by blast
  ultimately show ?thesis
    by (metis A_open CVA.valid_welldefined V_valid \<epsilon>A_def comb_is_element neutral_is_element valid_antisymmetry valid_elems valid_poset valid_semigroup)
qed

(* [Proposition 2, CVA] *)
(* Note we can assume either strongly_neutral_seq or strongly_neutral_par .*)
proposition neutral_collapse [simp] :
  fixes V :: "('A, 'a) CVA" and a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and neutral_collapse : "neut_par V = neut_seq V"
  and strongly_neutral_seq: "\<forall> A B . seq V (neut_seq V A) (neut_seq V B) = neut_seq V (A \<union> B)" 
  shows "gle V (seq V a b) (par V a b)"
proof -
  define "A" where "A = d a"
  define "B" where "B = d b"
  define "pc" where "pc = par V"
  define "sc" where "sc = seq V"
  define "\<gamma>" where "\<gamma> = neut_par V"
  have "A \<union> B \<in> opens V"
    by (metis A_def B_def CVA.valid_welldefined V_valid a_elem b_elem comb_is_element fst_conv local_inclusion_domain neutral_is_element strongly_neutral_seq) 
  moreover have "a = pc a (\<gamma> A)"
    by (metis pc_def A_def CVA.valid_welldefined V_valid \<gamma>_def a_elem local_inclusion_domain valid_neutral_law_right)
  moreover have "b = pc (\<gamma> B) b"
    by (metis pc_def B_def CVA.valid_welldefined V_valid \<gamma>_def b_elem local_inclusion_domain valid_commutativity valid_neutral_law_right)
  
  moreover have "sc a b = sc (pc a (\<gamma> A)) (pc (\<gamma> B) b)"
    using \<open>b = pc (\<gamma> B) b\<close> calculation by presburger
  moreover have "gle V (sc (pc a (\<gamma> A)) (pc (\<gamma> B) b)) (pc (sc a (\<gamma> B)) (sc (\<gamma> A) b))"
    by (metis pc_def sc_def A_def B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem local_inclusion_domain neutral_is_element valid_weak_exchange)
  moreover have "d (sc a (\<gamma> B)) = A \<union> B"
    by (metis A_def B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem fst_conv local_inclusion_domain neutral_is_element sc_def valid_domain_law valid_elems)
  moreover have "sc a (\<gamma> B) = sc (sc a (\<gamma> B)) (\<gamma> (A \<union> B))"using assms valid_neutral_law_right
      [where ?V="seq_algebra V" and ?A="A \<union> B" and ?a="sc a (\<gamma> B)" and ?\<epsilon>=\<gamma>]
    by (metis (no_types, lifting) B_def CVA.valid_welldefined \<gamma>_def calculation(6) comb_is_element local_inclusion_domain neutral_is_element sc_def valid_elems) 
  moreover have "... = sc a (sc (\<gamma> B) (\<gamma> (A \<union> B)))"
    by (metis (no_types, lifting) A_def B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem comb_is_element local_inclusion_domain neutral_collapse neutral_is_element sc_def strongly_neutral_seq valid_comb_associative valid_elems)  
  moreover have "... = sc a (\<gamma> (A \<union> B))"
    by (metis \<gamma>_def neutral_collapse sc_def strongly_neutral_seq sup_commute sup_left_idem) 
  moreover have "... = OVA.gext (seq_algebra V) (A \<union> B) a"  using assms calculation OVA.symmetric_gext [where ?V="seq_algebra V"]
    by (simp add: A_def CVA.valid_welldefined \<gamma>_def sc_def valid_elems)
  moreover have "... = pc a (\<gamma> (A \<union> B))"
    by (metis A_def CVA.valid_welldefined \<gamma>_def assms(1) assms(2) calculation(1) pc_def sup_ge1 symmetric_gext valid_gext)
      
  moreover have "sc (\<gamma> A) b = sc (\<gamma> (A \<union> B)) (sc (\<gamma> A) b)"  using assms valid_neutral_law_left
      [where ?V="seq_algebra V" and ?A="A \<union> B" and ?a="sc (\<gamma> A) b" and ?\<epsilon>=\<gamma>]
    by (smt (verit, best) A_def B_def CVA.valid_welldefined \<gamma>_def comb_is_element d_neut local_inclusion_domain neutral_is_element sc_def valid_domain_law valid_elems valid_neutral_law_left)
  moreover have "... = sc (sc (\<gamma> (A \<union> B)) (\<gamma> A)) b"
    by (metis (no_types, lifting) A_def B_def CVA.valid_welldefined V_valid \<gamma>_def a_elem b_elem comb_is_element local_inclusion_domain neutral_collapse neutral_is_element sc_def strongly_neutral_seq valid_comb_associative valid_elems)   
  moreover have "... = sc (\<gamma> (A \<union> B)) b"
    by (simp add: \<gamma>_def neutral_collapse sc_def strongly_neutral_seq sup_commute) 
  moreover have "... =   OVA.gext (seq_algebra V) (A \<union> B) b"
    by (metis B_def CVA.valid_welldefined V_valid \<gamma>_def b_elem calculation(1) gext_def neutral_collapse sc_def sup_ge2 valid_elems)
  moreover have "... =   pc (\<gamma> (A \<union> B)) b" using valid_gext
    by (metis B_def CVA.valid_welldefined V_valid \<gamma>_def b_elem calculation(1) pc_def sup_ge2 symmetric_gext valid_commutativity) 
  moreover have "pc (sc a (\<gamma> B)) (sc (\<gamma> A) b) = pc (pc a (\<gamma> (A \<union> B))) ( pc (\<gamma> (A \<union> B)) b)"
    using calculation(10) calculation(11) calculation(12) calculation(13) calculation(14) calculation(15) calculation(16) calculation(7) calculation(8) calculation(9) by presburger  
  moreover have "... =   pc a (pc (\<gamma> (A \<union> B)) ( pc (\<gamma> (A \<union> B)) b))" using valid_comb_associative 
    by (metis (no_types, lifting) B_def CVA.valid_welldefined Un_upper2 V_valid \<gamma>_def assms(2) b_elem calculation(1) calculation(16) d_elem_is_open gext_elem neutral_is_element pc_def valid_elems) 
  moreover have "... =   pc a (pc (\<gamma> (A \<union> B)) b)"   
    by (smt (verit, del_insts) B_def CVA.valid_welldefined Un_upper2 V_valid \<gamma>_def b_elem calculation(1) calculation(16) d_elem_is_open d_gext gext_elem pc_def valid_elems valid_neutral_law_left)
  moreover have "... =   pc a (pc b (\<gamma> (A \<union> B)))"
    by (simp add: V_valid pc_def valid_commutativity) 
moreover have "... =   pc a b"
  by (metis (no_types, lifting) A_def B_def CVA.valid_welldefined V_valid \<gamma>_def assms(2) b_elem calculation(1) comb_is_element neutral_is_element pc_def valid_comb_associative valid_domain_law valid_neutral_law_right) 
  ultimately show ?thesis
    by (metis pc_def sc_def) 
qed


end
