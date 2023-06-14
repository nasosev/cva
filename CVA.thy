theory CVA
  imports Main OVA
begin

record ('A, 'a) CVA =
  par_algebra :: "('A, 'a) OVA"
  seq_algebra :: "('A, 'a) OVA"

definition elems :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V = OVA.elems (par_algebra V)"

definition opens :: "('A,'a) CVA \<Rightarrow> 'A Open set" where
"opens V = Space.opens (space (par_algebra V))"

definition par :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"par V =  OVA.comb (par_algebra V)"

definition seq :: "('A,'a) CVA \<Rightarrow>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"seq V =  OVA.comb (par_algebra V)"

definition gle :: "('A,'a) CVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle V = OVA.gle (par_algebra V)"

definition neut_par :: "('A, 'a) CVA \<Rightarrow> ('A set \<Rightarrow> ('A, 'a) Valuation)" where
"neut_par V  = OVA.neut (par_algebra V)"

definition neut_seq :: "('A, 'a) CVA \<Rightarrow> ('A set \<Rightarrow> ('A, 'a) Valuation)" where
"neut_seq V  = OVA.neut (seq_algebra V)"

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


lemma valid_welldefined: "valid V \<Longrightarrow> OVA.valid (par_algebra V) \<and> OVA.valid (seq_algebra V) \<and> (OVA.presheaf (par_algebra V) = OVA.presheaf (seq_algebra V))"
  unfolding valid_def
  by metis

lemma valid_commutativity: "valid V \<Longrightarrow> \<forall> a b . OVA.comb (par_algebra V) a b = OVA.comb (par_algebra V) b a"
  unfolding valid_def
  by metis

lemma valid_weak_exchange: "valid V \<Longrightarrow> \<forall> a b c d. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> c \<in> elems V \<longrightarrow> d \<in> elems V \<longrightarrow>
                        gle V (seq V (par V a b) (par V c d)) (par V (seq V a c) (seq V b d))"
  unfolding valid_def
  oops

lemma valid_neutral_law_par: "valid V \<Longrightarrow> (\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems V \<longrightarrow> gle V (neut_par V A) (par V (neut_par V A) (neut_par V A)))"
  unfolding valid_def
  oops

lemma valid_neutral_law_seq: "valid V \<Longrightarrow> (\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems V \<longrightarrow> gle V (seq V (neut_seq V A) (neut_seq V A)) (neut_seq V A))"
  unfolding valid_def
oops


end
