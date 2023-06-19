theory CVA
  imports Main OVA
begin

record ('A, 'a) CVA =
  par_algebra :: "('A, 'a) OVA"
  seq_algebra :: "('A, 'a) OVA"

abbreviation (input) presheaf :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Presheaf" where
"presheaf V \<equiv> OVA.presheaf (par_algebra V)"

abbreviation (input) elems :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> OVA.elems (par_algebra V)"

abbreviation (input) opens :: "('A,'a) CVA \<Rightarrow> 'A Open set" where
"opens V \<equiv> OVA.opens (par_algebra V)"

abbreviation (input) par :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"par V \<equiv> OVA.comb (par_algebra V)"

abbreviation (input) seq :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"seq V \<equiv> OVA.comb (seq_algebra V)"

abbreviation (input) gle :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle V \<equiv> OVA.gle (par_algebra V)"

abbreviation (input) local_le :: "('A,'a) CVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V \<equiv> OVA.local_le (par_algebra V)"

abbreviation (input) neut_par :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_par V \<equiv> OVA.neut (par_algebra V)"

abbreviation (input) neut_seq :: "('A, 'a) CVA \<Rightarrow> ('A Open \<Rightarrow> ('A, 'a) Valuation)" where
"neut_seq V \<equiv> OVA.neut (seq_algebra V)"

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

        neutral_law_par = (\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems V \<longrightarrow> gle (\<epsilon> A) (par (\<epsilon> A) (\<epsilon> A)));

        neutral_law_seq = (\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems V \<longrightarrow> gle (seq (\<delta> A) (\<delta> A)) (\<delta> A))
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
  
lemma valid_neutral_law_par: "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a \<in> elems V \<Longrightarrow> gle V (neut_par V A) (par V (neut_par V A) (neut_par V A))"
  unfolding valid_def
  by (smt (z3) fst_conv neutral_is_element valid_neutral_law_left valid_poset valid_reflexivity valid_semigroup)

lemma valid_neutral_law_seq: "valid V \<Longrightarrow>  A \<in> opens V \<Longrightarrow> a \<in> elems V \<Longrightarrow> gle V (seq V (neut_seq V A) (neut_seq V A)) (neut_seq V A)"
  unfolding valid_def
  by (smt (z3) d_neut neutral_is_element valid_gc_poset valid_neutral_law_right valid_poset valid_reflexivity valid_semigroup)

(* Paper results *)

lemma neut_seq_le_neut_par :
  fixes V :: "('A, 'a) CVA" and A :: "'A Open"
  assumes V_valid : "valid V" and A_open : "A \<in> opens V"
  shows "local_le V A (neut_seq V A) (neut_par V A)"
proof - 
  define "\<epsilon>A" where "\<epsilon>A = neut_seq V A"
  define "\<delta>A" where "\<delta>A = neut_par V A"
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
    by presburger
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
    by presburger 
  moreover have "par V \<delta>A \<delta>A = \<delta>A" using assms valid_neutral_law_right 
[where ?V="par_algebra V" and ?A=A and ?a=\<delta>A and ?\<epsilon>="neut_par V"]
    by (simp add: CVA.valid_welldefined \<delta>A_def neutral_is_element) 
  ultimately show ?thesis
    by (metis A_open CVA.valid_welldefined Grothendieck.local_le V_valid \<delta>A_def \<epsilon>A_def fst_eqD neutral_is_element valid_gc_poset valid_presheaf) 
qed

end
