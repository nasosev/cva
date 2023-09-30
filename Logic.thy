section \<open> Logic.thy \<close>

theory Logic
  imports Main CVA
begin

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

proposition hoare_res_rule4 :
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

proposition hoare_res_rule5 :
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
  assumes V_valid : "valid V" and V_quantalic : "is_right_positively_disjunctive V"
  and seq_right_strict : "\<forall> a \<in> elems V . seq V a (bot V) = bot V"
  and "p \<in> elems V" and "q \<in> elems V"
shows "hoare V p (bot V) q"
  by (metis CVA.bot_def V_quantalic assms(4) assms(5) bot_min cocomplete rpd_complete seq_right_strict) 

(* [CKA, Lemma 5.2.7] *)
proposition hoare_choice_rule :
  fixes V :: "('A, 'a) CVA" and p q a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and "p \<in> elems V" and "q \<in> elems V" and "a \<in> elems V" and "b \<in> elems V"
shows "hoare V p (join V a b) q = (hoare V p a q \<and> hoare V p b q)" 
proof (rule iffI, goal_cases)
  case 1
  then show ?case 
  proof -
    have "le V (seq V p (join V a b)) q"
      using "1" by blast 
    moreover have "seq V p (join V a b) = join V (seq V p a) (seq V p b)"
      using V_rpd V_valid assms(3) assms(5) assms(6) binary_disjunctive by blast 
    moreover have "seq V p a \<in> elems V \<and> seq V p b \<in> elems V"
      using V_valid assms(3) assms(5) assms(6) valid_seq_elem by blast
    moreover have "le V (seq V p a) (seq V p (join V a b)) \<and> le V (seq V p b) (seq V p (join V a b))" 
      using join_greater [where ?P="poset V" and ?a="seq V p a" and ?b="seq V p b"]
      by (metis (no_types, opaque_lifting) V_rpd calculation(2) calculation(3) cocomplete is_right_positively_disjunctive_def) 
    moreover have "le V (seq V p a) q \<and> le V (seq V p b) q"
      by (smt (verit, best) "1" V_rpd V_valid assms(4) calculation(2) calculation(3) calculation(4) is_right_positively_disjunctive_def join_elem valid_le_transitive)
    ultimately show ?thesis
      by force
  qed
next
  case 2
  then show ?case
  proof 
    assume "le V (seq V p a) q" 
    assume "le V (seq V p b) q" 
    then have "le V (join V (seq V p a) (seq V p b)) q"
      by (smt (verit, ccfv_threshold) V_rpd V_valid \<open>hoare V p a q\<close> assms(3) assms(4) assms(5) assms(6) rpd_cocomplete join_property valid_seq_elem)
    thus "hoare V p (join V a b) q"
      by (metis V_rpd V_valid assms(3) assms(5) assms(6) binary_disjunctive)
  qed
qed

(* [CKA, Lemma 5.2.8] *)
proposition hoare_iteration_rule : 
  fixes V :: "('A, 'a) CVA" and p a:: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
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
    using V_rpd V_valid a_el by blast
  moreover have "Poset.valid_map (seq_iter_map V a)" using valid_seq_iter_map [where ?V=V and ?x=a] using V_valid V_rpd
    using a_el rpd_complete by blast
  moreover have "\<And> n . ((iter (seq_iter_map V a) n) \<star> (bot V)) \<in> elems V" using iter_el
    by (metis (no_types, lifting) PosetMap.select_convs(1) PosetMap.select_convs(2) V_rpd calculation(2) complete_bot_el rpd_complete seq_iter_map_def)
  moreover have "\<And> n . seq V p ((iter (seq_iter_map V a) n) \<star> (bot V)) \<in> elems V"
    using V_valid calculation(3) p_el valid_seq_elem by blast   

  moreover have "\<And> n . le V (seq V p ((iter (seq_iter_map V a) n) \<star> (bot V))) p" 
  proof -
    fix n
    show "le V (seq V p ((iter (seq_iter_map V a) n) \<star> (bot V))) p"
    proof (induct_tac n, goal_cases)
      case 1
      then show ?case
        by (smt (verit, best) V_rpd V_valid \<open>hoare V p a p\<close> a_el calculation(3) rpd_complete iter_seq_zero p_el seq_bot1 valid_le_transitive valid_seq_elem) 
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
          using V_rpd V_valid a_el iter_seq_induction by blast
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
          by (smt (verit, best) CVA.valid_welldefined V_rpd V_valid a_el calculation(4) d_elem_is_open p_el valid_neut_seq_elem valid_seq_elem)
        ultimately show "hoare V p (iter (seq_iter_map V a) (Suc n) \<star> bot V) p"
          by presburger 
    qed
  qed
  qed
  moreover have "pU \<subseteq> elems V"
    using pU_def calculation(4) by fastforce 
  moreover have "le V (sup V pU) p" 
    using sup_is_lub [where ?P="poset V" and ?z=p and ?U=pU] pU_def
    by (smt (z3) V_rpd calculation(5) calculation(6) cocomplete rpd_complete mem_Collect_eq p_el)
  moreover have "U \<noteq> {}"
    using U_def by blast
  moreover have 0 : "pU = {seq V p u |u. u \<in> U}" unfolding U_def pU_def 
    by blast
  moreover have 00: "sup V pU = sup V {seq V p u |u. u \<in> U}"
    using "0" by auto
  moreover have "seq V p (sup V U) = sup V pU " 
    using U_def pU_def 00 V_rpd rpd_complete [where ?V=V] is_right_positively_disjunctive_def [where ?V=V]
    by (smt (z3) Collect_cong calculation(3) calculation(8) mem_Collect_eq p_el subsetI)
  moreover have "sup V { seq V p ((iter (seq_iter_map V a) n) \<star> (bot V)) | n . n \<in> UNIV} = seq V p (finite_seq_iter V a)" 
    using calculation(1) calculation(11) pU_def by presburger
  ultimately show "le V (seq V p (finite_seq_iter V a)) p"
    by force 
qed
next
  case 2
  then show ?case
    by (smt (verit) V_rpd V_valid p_el a_el finite_seq_iter_el hoare_weakening_rule hoare_neut_seq_rule hoare_neut_seq_rule' id_le_finite_seq_iter is_right_positively_disjunctive_def valid_seq_elem valid_seq_mono) 
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
  and i_el : "i \<in> elems V" and inv_i : "invariant V i" and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" 
  and di_eq_da_eq_db : "d i = d a \<and> d i = d b"
shows "le V (seq V i (par V a b)) (par V (seq V i a) (seq V i b))"
  by (smt (verit) V_valid a_el b_el inv_i invariant_def i_el valid_weak_exchange) 

lemma inv_dist_par2 :
  fixes V :: "('A, 'a) CVA" and i a b :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i" and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" 
  and di_eq_da_eq_db : "d i = d a \<and> d i = d b"
shows "le V (seq V (par V a b) i) (par V (seq V a i) (seq V b i))"
  by (smt (verit) V_valid a_el b_el inv_i invariant_def i_el valid_weak_exchange)

lemma inv_iter :
  fixes V :: "('A, 'a) CVA" and i:: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i" 
shows "invariant V (finite_seq_iter V i)" 
  oops

lemma inv_iter_le :
  fixes V :: "('A, 'a) CVA" and a i :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i"  and a_el : "a \<in> elems V"
  and a_le_i : "le V a i"
shows "le V (finite_seq_iter V a) i" 
proof -
  define "U" where "U = {iter (seq_iter_map V a) n \<star> CVA.bot V |n. n \<in> UNIV}"
  then have "finite_seq_iter V a = sup V U"
    using V_rpd V_valid a_el kleene_finite_seq_iter by blast
  moreover have "\<And> n . le V ( (iter (seq_iter_map V a) n) \<star> (bot V)) i" 
    proof (induct_tac n, goal_cases)
      case (1 n)
      then show ?case
        by (metis CVA.bot_def V_rpd V_valid a_el bot_min cocomplete rpd_complete i_el iter_seq_zero) 
    next
      case (2 n m)
      then show ?case 
      proof -
        have "iter (seq_iter_map V a) (Suc m) \<star> bot V = join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) m \<star> bot V)))" 
          using iter_seq_induction [where ?V=V and ?n=m and ?a=a] V_rpd V_valid a_el by fastforce 
        moreover have "d i \<subseteq> d a"
          using CVA.valid_welldefined V_valid a_el a_le_i i_el by blast
        moreover have "le V (neut_seq V (d a)) (neut_seq V (d i))" using neut_le_neut 
          by (metis CVA.valid_welldefined V_valid a_el d_elem_is_open i_el calculation(2))
        moreover have "le V (neut_seq V (d a)) i"
          by (smt (verit, ccfv_threshold) CVA.valid_welldefined V_valid a_el calculation(3) d_elem_is_open i_el inv_i inv_neut_seq valid_le_transitive valid_neut_seq_elem)
        moreover have "le V ((iter (seq_iter_map V a) m \<star> bot V)) i"
          using "2" by blast
        moreover have "le V (seq V a ((iter (seq_iter_map V a) m \<star> bot V))) (seq V a i)" using valid_seq_mono iter_seq_el
          using "2" V_rpd V_valid a_el i_el valid_le_reflexive by blast
        moreover have "le V (seq V a i) i"
          by (smt (verit, del_insts) V_valid a_el a_le_i i_el inv_i inv_idem_seq valid_le_reflexive valid_seq_mono)
        moreover have "le V (seq V a ((iter (seq_iter_map V a) m \<star> bot V))) i"
          by (smt (verit, ccfv_threshold) V_rpd V_valid a_el calculation(7) calculation(6) i_el iter_seq_el valid_le_transitive valid_seq_elem) 
        moreover have "le V (join V (neut_seq V (d a)) (seq V a ((iter (seq_iter_map V a) m \<star> bot V)))) i"
          by (smt (verit, del_insts) CVA.valid_welldefined V_rpd V_valid a_el calculation(4) calculation(8) cocomplete rpd_complete d_elem_is_open i_el iter_seq_el join_property neutral_is_element valid_seq_elem)
        ultimately show ?thesis
          by presburger 
      qed
    qed
    moreover have "U \<subseteq> CVA.elems V " using U_def
      by (smt (verit) PosetMap.select_convs(1) PosetMap.select_convs(2) V_rpd V_valid a_el complete_bot_el rpd_complete iter_el mem_Collect_eq seq_iter_map_def subsetI valid_seq_iter_map) 
    moreover have "le V (sup V U) i"
      using sup_is_lub [where ?P="poset V" and ?U="U" and ?z=i] U_def
      using V_rpd calculation(2) calculation(3) cocomplete rpd_complete i_el
      by blast 
    ultimately show ?thesis
      by presburger 
  qed

lemma inv_par_le_par_iter :
  fixes V :: "('A, 'a) CVA" and a a' i i' :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and i_el : "i \<in> elems V" and inv_i : "invariant V i"  and a_el : "a \<in> elems V"
  and i'_el : "i' \<in> elems V" and inv_i' : "invariant V i'"  and a'_el : "a' \<in> elems V"
  and a_le_i : "le V a i" and a'_le_i' : "le V a' i'"
shows "le V (par V a a') (par V (finite_seq_iter V i) (finite_seq_iter V i'))" 
proof -
  have "le V a (finite_seq_iter V i)"
    by (smt (verit, del_insts) V_rpd V_valid a_el a_le_i rpd_complete finite_seq_iter_el i_el id_le_seq_iter valid_le_transitive)
  moreover have "le V a' (finite_seq_iter V i')"
    by (smt (verit, del_insts) V_rpd V_valid a'_el a'_le_i' rpd_complete finite_seq_iter_el i'_el id_le_seq_iter valid_le_transitive)
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) V_rpd V_valid a'_el a_el rpd_complete finite_seq_iter_el i'_el i_el valid_par_mono)
qed

lemma inv_par_iter_par1 :
  fixes V :: "('A, 'a) CVA" and a i :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
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
    by simp

  moreover have meet_r1r2 : "le V (meet V r1 r2) r1 \<and> le V (meet V r1 r2) r2"
    using V_complete meet_smaller1 [where ?P="poset V" and ?a=r1 and ?b=r2] meet_smaller2 [where ?P="poset V" and ?a=r1 and ?b=r2] assms
    by simp

  moreover have meet_elems : "meet V p1 p2 \<in> elems V \<and> meet V r1 r2 \<in> elems V \<and> meet V q1 q2 \<in> elems V"
    by (metis V_complete assms(11) assms(3) assms(4) assms(6) assms(8) assms(9) meet_el)

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
    by (smt (verit, ccfv_SIG) V_complete V_valid assms(10) assms(11) assms(5) assms(6) meet_elems valid_par_elem valid_seq_elem) 

  ultimately show ?thesis
    by force 
qed

(* [CKA, Thm 8.5] *)
(* Note that in a CKA we get a parallel of guarantees rather than a sequential composite; 
this would follow from `comparitor` above *)
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
    by (smt (verit) V_complete V_valid assms(3) assms(5) assms(8) cocomplete is_cocomplete_def meet_el meet_smaller1 valid_par_mono valid_reflexivity) 
  moreover have 1: "le V (seq V (par V (meet V r1 r2) a1) (par V (meet V r1 r2) a2)) (seq V (par V r1 a1) (par V (meet V r1 r2) a2))"
    by (smt (verit) V_complete V_valid assms(3) assms(5) assms(8) assms(9) calculation(3) meet_elem valid_le_reflexive valid_par_elem valid_seq_mono)
  moreover have "le V (par V (meet V r1 r2) a2) (par V r2 a2)"
    by (smt (verit, ccfv_SIG) V_complete V_valid assms(3) assms(8) assms(9) meet_el meet_smaller2 valid_le_reflexive valid_par_mono)
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
    by (smt (verit, ccfv_SIG) "5" "9" CVA.valid_welldefined V_complete V_valid assms(10) assms(3) assms(4) assms(5) assms(8) assms(9) comb_is_element meet_el valid_elems valid_poset valid_semigroup valid_transitivity) 

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
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
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
      by (smt (verit, best) V_rpd V_valid assms(4) assms(7) assms(8) calculation cocomplete rpd_complete join_el join_greater1 join_greater2 valid_le_transitive)
    moreover have "le V (seq V p (par V r a)) q \<and> le V (seq V p (par V r b)) q"
      by (smt (verit, ccfv_threshold) "1" V_rpd V_valid assms(3) assms(5) assms(6) assms(7) assms(8) binary_disjunctive hoare_choice_rule valid_par_elem)
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
      by (smt (verit) "2" V_rpd assms(4) assms(7) assms(8) cocomplete rpd_complete join_property) 
    moreover have "le V (seq V p (par V r (join V a b))) q"
      by (smt (verit, ccfv_threshold) "2" V_rpd V_valid assms(3) assms(5) assms(6) assms(7) assms(8) binary_disjunctive hoare_choice_rule valid_par_elem)
    ultimately show ?thesis
      by blast
  qed
qed

(* [CKA, Thm 8.7] *) 
proposition rg_iteration_rule : 
  fixes V :: "('A, 'a) CVA" and p r a g :: "('A,'a) Valuation"
  assumes V_valid : "valid V" and V_rpd : "is_right_positively_disjunctive V"
  and p_el : "p \<in> elems V" and r_el : "r \<in> elems V" and a_el : "a \<in> elems V" and g_el : "g \<in> elems V"
  and inv_r : "invariant V r" and inv_g : "invariant V g"
  and assm_hoare : "hoare V p r p" and assm_rg : "rg V p r a g p"
  and dr_le_da : "d r \<subseteq> d a" (* Note this is equiv. to 1_a \<le> r *)
shows "rg V p r (finite_seq_iter V a) g p"
proof -
  have "le V (finite_seq_iter V a) g" using inv_iter_le [where ?V=V and ?i=g and ?a=a]
    using V_rpd V_valid a_el assm_rg g_el inv_g by blast
  
  define "U" where "U = {iter (seq_iter_map V a) n \<star> CVA.bot V |n. n \<in> UNIV}"
  then have "finite_seq_iter V a = sup V U"
    using V_rpd V_valid a_el kleene_finite_seq_iter by blast
  moreover have "U \<noteq> {}" using U_def
    by blast 
  moreover have "U \<subseteq> elems V" using U_def
    using V_rpd V_valid a_el iter_seq_el by blast 

  define "W" where "W = {seq V p (par V r (iter (seq_iter_map V a) n \<star> CVA.bot V)) |n. n \<in> UNIV}"
  moreover have "W \<noteq> {}" using W_def
    by blast 
  moreover have "W \<subseteq> elems V" using W_def
    using V_rpd V_valid a_el iter_seq_el
    by (smt (verit, del_insts) mem_Collect_eq p_el r_el subsetI valid_par_elem valid_seq_elem) 
  moreover have "seq V p (par V r (sup V U)) = seq V p (sup V {par V r u | u . u \<in> U})"
    by (metis (mono_tags, lifting) V_rpd V_valid \<open>U \<subseteq> CVA.elems V\<close> calculation(2) rpd_par_dist r_el)
  moreover have "{par V r u | u . u \<in> U} \<noteq> {}" using U_def
    by blast
  moreover have "{par V r u | u . u \<in> U} \<subseteq> elems V" using U_def
    by (smt (z3) Collect_mem_eq Collect_mono_iff V_valid \<open>U \<subseteq> CVA.elems V\<close> r_el valid_par_elem)
  moreover have "seq V p (sup V {par V r u | u . u \<in> U}) = (sup V {seq V p (par V r u) | u . u \<in> U})"
    using V_rpd V_valid rpd_seq_dist
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
        using V_rpd V_valid a_el iter_seq_zero by blast 
      moreover have "le V (par V r (bot V)) r"
        by (metis V_rpd V_valid rpd_complete inv_idem_par inv_r par_bot1 r_el)
      moreover have "le V (seq V p (par V r (bot V))) (seq V p r)"
        by (smt (verit, del_insts) V_rpd V_valid bot_elem calculation(2) rpd_complete p_el r_el valid_le_reflexive valid_par_elem valid_seq_mono) 
      ultimately show ?thesis
        by (smt (verit, best) V_rpd V_valid assm_hoare complete_bot_el rpd_complete p_el r_el valid_le_transitive valid_par_elem valid_seq_elem)
    qed
  next
    case (2 n m)
    then show ?case 
    proof -
      define "a_m" where "a_m = iter (seq_iter_map V a) m \<star> bot V" 
      have "le V (seq V p (par V r a_m)) p"
        using "2" a_m_def by force 
      moreover have "iter (seq_iter_map V a) (Suc m) \<star> bot V = join V (neut_seq V (d a)) (seq V a (a_m))" 
        using iter_seq_induction [where ?V=V and ?a=a and ?n=m] V_rpd V_valid a_el a_m_def by blast
      moreover have "seq V p (par V r (iter (seq_iter_map V a) (Suc m) \<star> bot V)) = seq V p (par V r (join V (neut_seq V (d a)) (seq V a (a_m))))"
        using calculation(2) by presburger
      moreover have "... = seq V p (join V (par V r (neut_seq V (d a))) (par V r (seq V a (a_m))))"
        by (metis CVA.valid_welldefined V_rpd V_valid a_el a_m_def binary_disjunctive d_elem_is_open iter_seq_el r_el valid_neut_seq_elem valid_seq_elem)
      moreover have "... = join V (seq V p (par V r (neut_seq V (d a)))) (seq V p (par V r (seq V a (a_m))))"
        by (metis CVA.valid_welldefined V_rpd V_valid a_el a_m_def binary_disjunctive d_elem_is_open iter_seq_el p_el r_el valid_neut_seq_elem valid_par_elem valid_seq_elem)
      
      moreover have 1: "le V (seq V p (par V r (seq V a (a_m)))) p"
        by (smt (z3) "2" V_rpd V_valid a_el a_m_def assm_rg hoare_sequential_rule' inv_dist inv_r iter_seq_el p_el r_el valid_elems valid_par_elem valid_seq_elem)

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
        by (metis V_rpd V_valid a_el fiter_seq.simps(1) fiter_seq_elem r_el valid_par_elem) 
      
      moreover have "le V (seq V p (par V r (neut_seq V (d a)))) (seq V p r)" using valid_seq_mono [where ?V=V]
        by (smt (z3) V_valid calculation(11) calculation(12) p_el r_el valid_le_reflexive)

      moreover have 2: "le V (seq V p (par V r (neut_seq V (d a)))) p"
        by (smt (verit, best) CVA.valid_welldefined V_valid a_el assm_hoare calculation(13) d_elem_is_open p_el r_el valid_le_transitive valid_neut_seq_elem valid_par_elem valid_seq_elem) 

      ultimately show ?thesis
        by (smt (verit) CVA.valid_welldefined V_rpd V_valid a_el a_m_def d_elem_is_open hoare_choice_rule iter_seq_el p_el r_el valid_neut_seq_elem valid_par_elem valid_seq_elem)
     qed
    qed
    moreover have "le V (sup V W) p" 
      unfolding sup_def W_def
      using  sup_is_lub [where ?P="poset V" and ?U="W" and ?z=p] W_def
      using V_rpd calculation(5) rpd_cocomplete fa p_el
      by (smt (z3) mem_Collect_eq sup_def) 
    moreover have "le V (seq V p (par V r (sup V U))) p"
      using calculation(12) calculation(15) by presburger
    moreover have "le V (seq V p (par V r (finite_seq_iter V a))) p"
      using calculation(1) calculation(16) by presburger
    ultimately show ?thesis using U_def
      using \<open>CVA.le V (finite_seq_iter V a) g\<close> by blast
  qed

end