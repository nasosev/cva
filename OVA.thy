section \<open> OVA.thy \<close>

theory OVA
  imports Main Poset Grothendieck Semigroup Prealgebra
begin

type_synonym ('A, 'a) Valuation = "('A set \<times> 'a)"

(* OVA type (ordered valuation algebra) *)

record ('A, 'a) OVA =
  prealgebra :: "('A, 'a) Prealgebra"
  neutral :: "('A, unit, 'a) PrealgebraMap"
  semigroup :: "(('A, 'a) Valuation) Semigroup"

abbreviation ob :: "('A, 'a) OVA \<Rightarrow> ('A Open, 'a Poset) Function" where
"ob V \<equiv> Prealgebra.ob (prealgebra V)"

abbreviation ar :: "('A, 'a) OVA \<Rightarrow> ('A Inclusion, ('a, 'a) PosetMap) Function" where
"ar V \<equiv> Prealgebra.ar (prealgebra V)"

abbreviation comb :: "('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"comb V a b \<equiv> (Semigroup.mult (semigroup V)) \<star> (a, b)"

(*
abbreviation comb\_V :: "('A, 'a) Valuation \<Rightarrow> ('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" ("\_ \<otimes>\<langle>\_\<rangle> \_") where
"comb\_V a V b \<equiv> (Semigroup.mult (semigroup V)) \<star> (a, b)"
*)

abbreviation neut :: "('A, 'a) OVA \<Rightarrow> 'A set \<Rightarrow> ('A, 'a) Valuation" where
"neut V A \<equiv> (A, (Prealgebra.nat (neutral V) \<cdot> A) \<star> ())"

abbreviation poset :: "('A,'a) OVA \<Rightarrow> (('A, 'a) Valuation) Poset" where
"poset V \<equiv> Semigroup.poset (semigroup V)"

abbreviation le :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"le V a b \<equiv> Poset.le (poset V) a b"

abbreviation elems :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> Poset.el (poset V)"

(*
abbreviation le\_V :: "('A, 'a) Valuation \<Rightarrow> ('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" ("\_ \<preceq>\<langle>\_\<rangle> \_") where
"le\_V a V b \<equiv> Poset.le (Semigroup.poset (semigroup V)) a b"
*)

definition "OVA_local_le_undefined_domain_mismatch _ _ \<equiv> undefined"

(* Note the parameter A is actually redundant *)
abbreviation (input) local_le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V A a a' \<equiv> 
  if A = d a \<and> A = d a' 
  then Poset.le (ob V \<cdot> A) (e a) (e a')
  else OVA_local_le_undefined_domain_mismatch a a'"

abbreviation space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space V \<equiv> Prealgebra.space (prealgebra V)"

abbreviation (input) local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems V A \<equiv> Poset.el (ob V \<cdot> A)"

definition "OVA_res_undefined_bad_args _ _ \<equiv> undefined"

definition res :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"res V B a \<equiv>
  if a \<in> elems V \<and> B \<in> opens (space V) \<and> B \<subseteq> d a
  then (B, ar V \<cdot> (make_inc B (d a)) \<star> (e a))
  else OVA_res_undefined_bad_args B a"

definition "OVA_ext_undefined_bad_args _ _ \<equiv> undefined"

definition ext :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"ext V A b \<equiv>
  if b \<in> elems V \<and> A \<in> opens (space V) \<and> d b \<subseteq> A
  then comb V (neut V A) b
  else OVA_ext_undefined_bad_args A b"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid V \<equiv>
    let
        welldefined = Prealgebra.valid (prealgebra V)
                      \<and> Semigroup.valid (semigroup V)
                      \<and> Prealgebra.valid_map (neutral V)
                      \<and> Prealgebra.cod (neutral V) = prealgebra V
                      \<and> Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)
                      \<and> Semigroup.poset (semigroup V) = gc (prealgebra V);
        domain_law = \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> d (comb V a b) = d a \<union> d b;
        neutral_law_left = \<forall>A a. A \<in> opens (space V) \<longrightarrow> a \<in> elems V \<longrightarrow> comb V (neut V (d a)) a = a;
        neutral_law_right = \<forall>A a. A \<in> opens (space V) \<and> a \<in> elems V \<longrightarrow> comb V a (neut V (d a)) = a;
        comb_law_left = \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             res V (d a) (comb V a b) = comb V a (res V (d a \<inter> d b) b);
        comb_law_right = \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             res V (d b) (comb V a b) = comb V (res V (d a \<inter> d b) a) b
    in
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"

(* Properties *)

definition is_commutative :: "('A, 'a) OVA \<Rightarrow> bool" where
"is_commutative V \<equiv> \<forall> a b . a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> comb V a b = comb V b a"

definition is_strongly_neutral :: "('A, 'a) OVA \<Rightarrow> bool" where
"is_strongly_neutral V \<equiv> \<forall> A B . A \<in> opens (space V) \<longrightarrow> B \<in> opens (space V) \<longrightarrow> comb V (neut V A) (neut V B) = neut V (A \<union> B)"

(* Validity *)

lemma validI [intro] :
  fixes V :: "('A,'a) OVA"
  assumes welldefined : "Prealgebra.valid (prealgebra V)
                      \<and> Semigroup.valid (semigroup V)
                      \<and> Prealgebra.valid_map (neutral V)
                      \<and> Prealgebra.cod (neutral V) = prealgebra V
                      \<and> Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)
                      \<and> Semigroup.poset (semigroup V) = gc (prealgebra V)"
  assumes domain_law : "\<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> d (comb V a b) = d a \<union> d b"
  assumes neutral_law_left : "\<forall>A a. A \<in> opens (space V) \<longrightarrow> a \<in> elems V \<longrightarrow> comb V (neut V (d a)) a = a"
  assumes neutral_law_right: "\<forall>A a. A \<in> opens (space V) \<and> a \<in> elems V \<longrightarrow> comb V a (neut V (d a)) = a"
  assumes comb_law_left : "\<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             res V (d a) (comb V a b) = comb V a (res V (d a \<inter> d b) b)"
  assumes comb_law_right : "\<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             res V (d b) (comb V a b) = comb V (res V (d a \<inter> d b) a) b"
  shows "valid V"
  unfolding valid_def
  apply (simp_all add: Let_def)
  apply safe
  apply (simp add: welldefined)
  using welldefined apply blast
  using welldefined apply blast
  using welldefined apply blast
  using welldefined apply blast
  using welldefined apply auto[1]
  using welldefined apply auto[1]
        apply (simp add: domain_law)
  apply (simp add: domain_law)
      apply (simp add: domain_law)
  using neutral_law_left apply auto[1]
  using neutral_law_right apply force
  using comb_law_left apply auto[1]
  using comb_law_right by auto

lemma valid_welldefined  :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Prealgebra.valid (prealgebra V)
                      \<and> Semigroup.valid (semigroup V)
                      \<and> Prealgebra.valid_map (neutral V)
                      \<and> Prealgebra.cod (neutral V) = prealgebra V
                      \<and> Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)
                      \<and> Semigroup.poset (semigroup V) = gc (prealgebra V)" 
  unfolding valid_def
  using OVA.valid_def assms by auto

lemma valid_prealgebra :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Prealgebra.valid (prealgebra V)"
  by (simp add: OVA.valid_welldefined assms)

lemma valid_semigroup :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Semigroup.valid (semigroup V)"
  using OVA.valid_welldefined assms by blast

lemma valid_neutral :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Prealgebra.valid_map (neutral V)"
  by (simp add: OVA.valid_welldefined assms)

lemma valid_codomain :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Prealgebra.cod (neutral V) = prealgebra V"
  using OVA.valid_welldefined assms by blast 

lemma valid_domain :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)"
  using OVA.valid_welldefined assms by blast

lemma valid_gc_poset :
  fixes V :: "('A,'a) OVA"
  assumes V_valid : "valid V"
  shows "Semigroup.poset (semigroup V) = gc (prealgebra V)"
  using OVA.valid_welldefined assms by blast

lemma valid_le :
  fixes V :: "('A,'a) OVA"  and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  and a_le_b : "le V a b"
  shows "d b \<subseteq> d a \<and> local_le V (d b) (res V (d b) a) b"
proof
  show "d b \<subseteq> d a" using assms
    by (metis d_antitone valid_gc_poset valid_prealgebra)
next
  define "i" where "i = make_inc (d b) (d a)"
  define "pr_B" where "pr_B = ar V \<cdot> i"
  define "ea_B" where "ea_B = pr_B \<star> (e a)"
  define "FA" where "FA = ob V \<cdot> d a"
  define "FB" where "FB = ob V \<cdot> d b"
  have "e a \<in> Poset.el FA"
    by (metis FA_def V_valid a_el gc_elem_local valid_gc_poset valid_prealgebra)
  moreover have  B_le_A: "d b \<subseteq> d a"
    by (metis OVA.valid_welldefined V_valid a_el a_le_b b_el d_antitone)
  moreover have "i \<in> inclusions (space V)" using B_le_A V_valid
    by (metis (no_types, lifting) CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) a_el b_el i_def inclusions_def local_dom valid_gc_poset valid_prealgebra)
  moreover have psh_valid : "Prealgebra.valid (prealgebra V)"
    by (simp add: V_valid valid_prealgebra)
  moreover have "Poset.valid_map pr_B"
    using calculation(3) pr_B_def psh_valid valid_ar by blast
  moreover have "Poset.dom pr_B = FA \<and> Poset.cod pr_B = FB"
    using FA_def FB_def calculation(3) i_def pr_B_def psh_valid by auto
  moreover have "ea_B \<in> Poset.el FB"
    by (metis Poset.fun_app2 calculation(1) calculation(5) calculation(6) ea_B_def)
  moreover have "e b \<in> Poset.el FB"
    by (metis FB_def V_valid b_el gc_elem_local psh_valid valid_gc_poset)
  moreover have "Poset.le (poset V) a b"
    using a_le_b by blast
  moreover have "Poset.le FB ea_B (e b)" 
    using psh_valid a_el b_el a_le_b FB_def ea_B_def pr_B_def
i_def V_valid  valid_gc_poset valid_gc_le_unwrap [where ?Aa=a and ?Bb=b and ?F="prealgebra V"]
    by force
  moreover have "d b = d (res V (d b) a) \<and> d b = d b"
    by (metis B_le_A Inclusion.select_convs(1) a_el calculation(3) fstI i_def res_def valid_inc_dom)
  ultimately show "local_le V (d b) (res V (d b) a) b"
    by (metis FB_def Inclusion.simps(1) a_el ea_B_def i_def pr_B_def res_def snd_conv valid_inc_dom) 
qed

lemma valid_domain_law : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> d (comb V a b) = d a \<union> d b"
  unfolding valid_def
  by meson

lemma valid_neutral_law_left : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> comb V (neut V (d a)) a = a"
  unfolding valid_def
  by (metis local_dom)

lemma valid_neutral_law_right : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> comb V a (neut V (d a)) = a"
  unfolding valid_def
  by (metis local_dom)

lemma valid_comb_law_left : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow>
      res V (d a) (comb V a b) = comb V a (res V (d a \<inter> d b) b)"
  unfolding valid_def
  by meson

lemma valid_comb_law_right : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow>
      res V (d b) (comb V a b) = comb V (res V (d a \<inter> d b) a) b"
  unfolding valid_def
  by meson

lemma valid_comb_associative : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow>
      comb V (comb V a b) c = comb V a (comb V b c)"
  unfolding valid_def
  by (meson valid_associative)

lemma valid_comb_monotone : "valid V \<Longrightarrow> a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> b1 \<in> elems V \<Longrightarrow> b2 \<in> elems V
\<Longrightarrow> le V a1 a2 \<Longrightarrow> le V b1 b2
\<Longrightarrow> le V (comb V a1 b1) (comb V a2 b2)"
  by (smt (verit) valid_monotone valid_semigroup)

(* Don't mark this as [intro] *)
lemma leI : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> d b \<subseteq> d a 
\<Longrightarrow> Poset.le (ob V \<cdot> d b) ((ar V \<cdot> (make_inc (d b) (d a))) \<star> e a) (e b) \<Longrightarrow> le V a b" 
  using valid_gc_poset [where ?V=V] gc_leI [where ?a=a and ?b=b and ?F="prealgebra V"]
  by simp 

lemma leD [dest] : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> le V a b
\<Longrightarrow> d b \<subseteq> d a \<and> Poset.le (ob V \<cdot> d b) ((ar V \<cdot> (make_inc (d b) (d a))) \<star> e a) (e b)" 
using valid_prealgebra [where ?V=V] valid_le [where ?V=V]
  by (smt (verit, ccfv_threshold) fst_conv local_dom res_def snd_conv valid_gc_poset) 

lemma le_eq : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> le V a b
= (d b \<subseteq> d a \<and>  Poset.le (ob V \<cdot> d b) ((ar V \<cdot> (make_inc (d b) (d a))) \<star> e a) (e b))"
using  gc_le_eq [where ?F="prealgebra V" and ?a=a and ?b=b] valid_gc_poset [where ?V=V]
  by force 

lemma le_rel : "le_rel (gc (prealgebra V)) = { ((A, a), (B, b)) .
 A \<in> opens (space V) \<and> B \<in> opens (space V) 
 \<and> a \<in> Poset.el (ob V \<cdot> A) \<and> b \<in> Poset.el (ob V \<cdot> B)
 \<and> B \<subseteq> A \<and> Poset.le (ob V \<cdot> B) (ar V \<cdot> (make_inc B A) \<star> a) b }" 
  using  gc_le_rel [where ?F="prealgebra V"] valid_gc_poset [where ?V=V]
  by force

lemma local_inclusion_element : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> e a \<in> el (ob V \<cdot> d a)"
  by (metis OVA.valid_welldefined gc_elem_local)

lemma global_inclusion_element : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> Poset.el ((ob V) \<cdot> A)
\<Longrightarrow>  (A, a) \<in> elems V"
  by (metis local_elem_gc valid_gc_poset valid_prealgebra) 

lemma d_elem_is_open : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> d a \<in> opens (space V)"
  by (metis local_dom valid_gc_poset valid_prealgebra)

lemma d_neut [simp] : "A \<in> opens (space V) \<Longrightarrow> d (neut V A) = A"
  by simp

lemma d_comb [simp] : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow> b \<in> elems V  \<Longrightarrow> d (comb V a b) = d a \<union> d b"
by (simp add: valid_domain_law)

lemma d_res [simp] : "a \<in> elems V \<Longrightarrow> B \<in> opens (space V) \<Longrightarrow> B \<subseteq> d a \<Longrightarrow> d (res V B a) = B"
  by (simp add: res_def)

lemma comb_is_element :
fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "comb V a b \<in> elems V"
proof -
  define "ab" where "ab = comb V a b"
  have "ab \<equiv> (Semigroup.mult (semigroup V)) \<star> (a, b)"
    using ab_def by presburger 
  moreover have "Poset.valid_map (mult (semigroup V))"
    by (simp add: V_valid valid_semigroup valid_welldefined_map) 
  moreover have "Poset.dom (mult (semigroup V)) = poset V \<times>\<times> poset V"
    by (simp add: V_valid valid_semigroup valid_welldefined_dom) 
  moreover have "(a,b) \<in> Poset.el (poset V \<times>\<times> poset V)"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def SigmaI a_el b_el)
  ultimately show ?thesis
    using Poset.fun_app2 by fastforce 
qed

lemma res_elem :
fixes V :: "('A,'a) OVA" and B :: "'A Open" and a :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
assumes a_el : "a \<in> elems V"
and "B \<subseteq> d a" and "B \<in> opens (space V)"
defines "a_B \<equiv> res V B a"
shows "a_B \<in> elems V"
proof -
  have "(B, ar V \<cdot> \<lparr>Inclusion.dom = B, cod = d a\<rparr> \<star> e a) \<in> el (PosetMap.cod (mult (OVA.semigroup V))) "
  proof -
    define "i" where "i = make_inc B (d a)"
    define "f" where "f = ar V \<cdot> i"
    define "FA" where "FA \<equiv> ((ob V) \<cdot> d a)"
    define "FB" where "FB \<equiv> ((ob V) \<cdot> B)"
  
    have "Prealgebra.valid (prealgebra V)"
      by (simp add: assms(1) valid_prealgebra)
    moreover have "d a \<in> opens (space V)"
      using assms(1) assms(3) d_elem_is_open a_el
      by blast 
    moreover have "Space.valid_inc i"
      by (simp add: assms(3) assms(4) i_def)
    moreover have  "i \<in> inclusions (space V)"
      using assms(4) calculation(2) calculation(3) i_def inclusions_def by force
    moreover have "f =  ar V \<cdot> i"
      by (simp add: f_def)
    moreover have "Poset.valid_map f" using Prealgebra.valid_ar calculation
      by blast
    moreover have "d a_B = B"
      using a_B_def assms(1) assms(3) assms(4) assms(5) calculation(2) d_res a_el by blast
    moreover have "Poset.cod f = FB"
      using FB_def calculation(1) calculation(4) f_def i_def by auto
    moreover have "Poset.valid FB"
      using Poset.valid_map_welldefined_cod calculation(6) calculation(8) by blast
    moreover have "e a \<in> Poset.el FA"
      using FA_def V_valid a_el local_inclusion_element by blast 
    moreover have "a_B \<equiv> res V B a"
      by (simp add: a_B_def)
    moreover have "e (res V B a) = f \<star> (e a)"
      by (metis a_el assms(3) assms(4) assms(5) f_def res_def i_def snd_conv)
    moreover have "f \<star> (e a) \<in> Poset.el FB"
      by (metis FA_def FB_def Prealgebra.restricted_element assms(3) assms(4) calculation(1) calculation(10) calculation(2) f_def i_def)
    moreover have "f \<star> (e a) = e a_B"
      using a_B_def calculation(12) by force
    moreover have "e a_B \<in>  Poset.el FB"
      by (simp add: a_B_def calculation(12) calculation(13))
    moreover have "a_B \<in> el (poset V)"
      by (metis FB_def V_valid assms(4) calculation(15) calculation(7) global_inclusion_element prod.exhaust_sel)
    ultimately show "(B, ar V \<cdot> make_inc B (d a) \<star> e a) \<in> el (PosetMap.cod
   (mult (OVA.semigroup V)))"
      by (metis (no_types, lifting) comp_eq_dest_lhs i_def prod.exhaust_sel) 
  qed
  show ?thesis
    by (metis (no_types, lifting) \<open>(B, ar V \<cdot> \<lparr>Inclusion.dom = B, cod = d a\<rparr> \<star> e a) \<in> el (PosetMap.cod (mult (OVA.semigroup V)))\<close> a_B_def a_el assms(3) assms(4) assms(5) comp_apply res_def)
qed

lemma neutral_is_element :
fixes V :: "('A,'a) OVA" and A :: "'A Open"
assumes V_valid : "valid V" and "A \<in> opens (space V)"
shows "neut V A \<in> elems V"
proof -
   have "Function.valid_map (PrealgebraMap.nat (neutral V))" using valid_neutral [where ?V=V]
    using V_valid valid_map_nat by blast 
   moreover have "Poset.valid_map (PrealgebraMap.nat (neutral V) \<cdot> A)" using valid_neutral [where ?V=V]
     by (simp add: OVA.valid_welldefined Prealgebra.const_def V_valid assms(2) valid_map_nat_welldefined)  
   moreover have "Poset.cod (PrealgebraMap.nat (neutral V) \<cdot> A) = (ob V) \<cdot>
     A" using Prealgebra.valid_map_def [where ?f="neutral V"]
     by (metis (no_types, lifting) V_valid assms(2) valid_codomain valid_neutral) 
  moreover have "Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)"
    using OVA.valid_welldefined V_valid by blast 
  moreover have "(Prealgebra.ob ( Prealgebra.terminal  (space V))) \<cdot> A = Poset.discrete"
    using Prealgebra.valid_space V_valid assms(2) const_ob valid_prealgebra by blast 
  moreover have "Poset.dom  (PrealgebraMap.nat (neutral V) \<cdot> A) = Poset.discrete" 
using Prealgebra.valid_map_def [where ?f="neutral V"]
  by (metis (no_types, lifting) OVA.valid_welldefined V_valid assms(2) calculation(5))
  moreover have "(PrealgebraMap.nat (neutral V) \<cdot> A \<star> ()) \<in> Poset.el ((ob V)
    \<cdot> A)"
    by (metis Poset.fun_app2 UNIV_unit UNIV_witness V_valid assms(2) calculation(2) calculation(3) calculation(5) calculation(6) singletonD terminal_value valid_prealgebra valid_space) 
ultimately show ?thesis
  by (meson V_valid assms(2) global_inclusion_element) 
qed

lemma neutral_local_element :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"
  assumes V_valid : "valid V"
  and domain : "A \<in> opens (space V)"
shows " e (neut V A) \<in> Poset.el (ob V \<cdot> A)"
    using V_valid assms(2) local_inclusion_element neutral_is_element by fastforce

lemma d_ext [simp] : "valid V \<Longrightarrow> b \<in> elems V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> d b \<subseteq> A \<Longrightarrow> d (ext V A b) = A" 
  unfolding ext_def
  by (smt (verit, best) d_neut neutral_is_element sup.orderE valid_domain_law)

lemma symmetric_ext:
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and b :: "('A,'a) Valuation"
  assumes V_valid: "valid V"
  and A_open : "A \<in> opens (space V)"
  and b_el : "b \<in> elems V" 
  and B_le_A : "d b \<subseteq> A" 
shows "ext V A b = comb V b (neut V A)"
  by (smt (verit, ccfv_SIG) A_open B_le_A V_valid b_el comb_is_element d_ext fst_conv ext_def d_elem_is_open neutral_is_element subset_Un_eq valid_comb_associative valid_domain_law valid_neutral_law_left valid_neutral_law_right)

lemma local_le_imp_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> local_elems V A
 \<Longrightarrow> a' \<in> local_elems V A \<Longrightarrow> local_le V A (A,a) (A,a') \<Longrightarrow> le V (A,a) (A,a')"
  unfolding valid_def
  apply (simp add: Let_def)
  apply safe
  apply meson
  apply meson
     apply meson
    apply clarsimp
    apply (simp add: gc_def)
    apply (metis (no_types, lifting) Poset.ident_app Space.ident_def valid_identity valid_ob)
  apply (meson local_elem_gc)
  by (meson local_elem_gc)

lemma le_eq_local_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> elems V
 \<Longrightarrow> a' \<in> elems V \<Longrightarrow> d a = A \<Longrightarrow> d a'= A \<Longrightarrow> le V a a' = local_le V A a a'"
proof (safe, goal_cases)
  case 1
  then show ?case
    by (metis OVA.valid_welldefined local_le) 
next
  case 2
  then show ?case 
  proof -
    have "valid V"
      by (simp add: "2"(1)) 
    moreover have "a \<in> elems V \<and> a' \<in> elems V"
      using "2"(3) "2"(4) by auto 
    moreover have "A = d a \<and> A = d a'"
      by (simp add: "2"(5) "2"(6)) 
    moreover have "Poset.le (ob V \<cdot> d a) (e a) (e a')"
      using "2"(5) "2"(7) by presburger 
    moreover have "A \<in> opens (space V)"
      by (simp add: "2"(2) "2"(6)) 
    moreover have "e a \<in> local_elems V A \<and> e a' \<in> local_elems V A"
      by (metis "2"(5) "2"(6) calculation(1) calculation(2) gc_elem_local valid_gc_poset valid_prealgebra)
    ultimately show "le V a a'"  
      using local_le_imp_le [where ?V=V and ?A=A and ?a="e a" and ?a'="e a'"] by (metis prod.exhaust_sel)
  qed
qed

lemma res_monotone :
  fixes V :: "('A,'a) OVA" and a1 a2 :: "('A, 'a) Valuation" and B :: "'A Open"
  assumes V_valid: "valid V"
  and "B \<in> opens (space V)"
  and "B \<subseteq> d a1"
  and "d a1 = d a2"
  and "a1 \<in> elems V" and "a2 \<in> elems V" and "le V a1 a2"
shows "le V (res V B a1) (res V B a2)"
proof -
  define "A" where "A = d a1"
  define "i" where "i = make_inc B A"
  define "Fi" where "Fi = (ar V) \<cdot> i"
  define "FA" where "FA = (ob V) \<cdot> A"
  define "FB" where "FB = (ob V) \<cdot> B"
  moreover have "le V a1 a2 \<longrightarrow> Poset.le FA (e a1) (e a2)"
    by (metis A_def FA_def V_valid assms(4) assms(5) assms(6) local_le valid_gc_poset valid_prealgebra) 
  moreover have "local_le V A a1 a2" using assms
    using A_def FA_def calculation(2) by presburger
  moreover have "i \<in> inclusions (space V) \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (no_types, lifting)  inclusions_def A_def CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) V_valid assms(2) assms(3) assms(5) d_elem_is_open i_def)
    moreover have "local_le V B (res V B a1)  (res V B a1)"
      by (metis V_valid assms(2) assms(3) assms(5) d_res res_elem local_inclusion_element valid_ob valid_prealgebra valid_reflexivity) 
    moreover have "d (res V B a1) = B"
      using V_valid assms(2) assms(3) assms(5) by auto
    moreover have "d (res V B a2) = B"
      using V_valid assms(2) assms(3) assms(4) assms(6) by auto 
    ultimately show ?thesis 
      using le_eq_local_le [where ?V=V and ?A=B and ?a="res V B a1" and
        ?a'="res V B a2"] assms
      by (smt (verit) A_def Prealgebra.image global_inclusion_element i_def local_inclusion_element res_def res_monotone snd_conv valid_prealgebra)
    qed

lemma res_monotone_local :
  fixes V :: "('A,'a) OVA" and a1 a2 :: "('A, 'a) Valuation" and B :: "'A Open"
  assumes V_valid: "valid V"
  and "B \<in> opens (space V)"
  and "B \<subseteq> d a1"
  and "d a1 = d a2"
  and "a1 \<in> elems V" and "a2 \<in> elems V" and "le V a1 a2"
shows "local_le V B (res V B a1) (res V B a2)"
  by (metis (no_types, lifting) OVA.res_monotone OVA.valid_welldefined V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) d_res local_le res_elem)

lemma e_res :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  defines "pr \<equiv> res V"
  and "FB \<equiv> ob V \<cdot> B"
  and "a_B \<equiv> res V B a"
  assumes V_valid : "valid V"
  and "B \<subseteq> A" and "B \<in> opens (space V)" and "A \<in> opens (space V)"
  and "d a = A"
  and "a \<in> elems V"
shows "e (a_B) \<in> Poset.el FB"
  by (metis FB_def a_B_def assms(4) assms(5) assms(6)assms(8) assms(9) d_res gc_elem_local res_elem valid_gc_poset valid_prealgebra)

lemma ext_elem :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  "b \<in> elems V" and "A \<in> opens (space V)"
  and  "d b \<subseteq> A"
shows "ext V A b \<in> elems V "
proof -
  have "d b \<subseteq> A \<and> d b \<in> opens (space V) \<and> A \<in> opens (space V)"
    using V_valid assms(2) assms(3) assms(4) d_elem_is_open by blast 
  moreover have "ext V A b = comb V (neut V A) b" using assms calculation ext_def [where ?b=b and
        ?V=V and ?A=A]
    by presburger 
  ultimately show ?thesis
    by (metis V_valid assms(2) comb_is_element neutral_is_element) 
qed

lemma e_ext :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"  and b :: "('A, 'a) Valuation"
  defines "FA \<equiv> ob V \<cdot> A"
  assumes V_valid : "valid V"
  and "d b \<subseteq> A" and "A \<in> opens (space V)"
  and "b \<in> elems V"
shows " e (ext V A b) \<in> Poset.el FA"
  by (metis FA_def V_valid assms(3) assms(4) assms(5) d_ext ext_elem local_inclusion_element) 

(* Paper results *)

(* [Remark 2 (1/3), TMCVA] *)
lemma res_functorial_id :
  fixes V :: "('A,'a) OVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "a \<in> elems V"
shows "res V (d a) a = a"
  unfolding res_def
  apply clarsimp
  by (metis Poset.ident_app Prealgebra.valid_identity Space.ident_def V_valid assms(2) comp_apply d_elem_is_open fst_conv local_inclusion_element prod.expand snd_conv valid_ob valid_prealgebra)

(* [Remark 2 (2/3), TMCVA] *)
lemma res_functorial_trans :
  fixes V :: "('A,'a) OVA" and B C :: "'A Open"  and a :: "('A, 'a) Valuation"
  defines "A \<equiv> d a"
  assumes V_valid : "valid V"
  and B_open : "B \<in> opens (space V)" and C_open : "C \<in> opens (space V)"
  and C_le_B : "C \<subseteq> B" and B_le_A : "B \<subseteq> A"
  and a_el : "a \<in> elems V"
shows "res V C a = (res V C (res V B a))"
proof -
  define "F1" where "F1 = ar V"
  define "i_BA" where "i_BA = make_inc B A"
  define "i_CB" where "i_CB = make_inc C B"
  define "i_CA" where "i_CA = make_inc C A"
  define "f" where "f = F1 \<cdot> i_BA"
  define "g" where "g = F1 \<cdot> i_CB"
  define "h" where "h = F1 \<cdot> i_CA"
  have "res V C a = (C, (F1 \<cdot> i_CA) \<star> (e a))"
    by (smt (verit, ccfv_SIG) A_def B_le_A C_le_B C_open F1_def assms(7) dual_order.trans i_CA_def res_def)
  moreover have "res V B a = (B, f \<star> (e a))"
    by (metis A_def B_le_A B_open F1_def a_el f_def i_BA_def res_def)
  moreover have "res V C (res V B a) = (C, g  \<star> (f \<star> (e a)))"
    by (metis (no_types, lifting) A_def B_le_A B_open C_le_B C_open F1_def V_valid a_el calculation(2) fst_conv g_def i_CB_def res_def res_elem snd_eqD)
  moreover have "Prealgebra.valid (prealgebra V)"
    by (meson OVA.valid_welldefined V_valid)
  moreover have "valid_inc i_CB"
    by (simp add: C_le_B i_CB_def)
  moreover have "i_CB \<in> inclusions (space V)"
    by (simp add: B_open C_le_B C_open i_CB_def inclusions_def)
  moreover have "valid_inc i_BA"
    by (simp add: B_le_A i_BA_def)
    moreover have "i_BA \<in> inclusions (space V)"
      by (metis (no_types, lifting) A_def B_le_A B_open Inclusion.select_convs(1) Inclusion.select_convs(2) V_valid a_el d_elem_is_open i_BA_def inclusions_def mem_Collect_eq)
  moreover have "valid_inc i_CA"
    using assms(5) assms(6) i_CA_def by auto 
  moreover have "i_CA = i_BA \<propto> i_CB" using Space.compose_inc_def
    by (simp add: i_BA_def i_CA_def i_CB_def) 
  moreover have "Poset.valid_map f \<and> Poset.valid_map g \<and> Poset.valid_map h"
    by (metis F1_def Inclusion.select_convs(1) Inclusion.select_convs(2) Poset.compose_valid Prealgebra.valid_composition Prealgebra.valid_welldefined calculation(10) calculation(4) calculation(6) calculation(8) f_def g_def h_def i_BA_def i_CB_def)
  moreover have "Space.cod i_BA = A \<and> Space.dom i_BA = B "
    by (simp add: i_BA_def) 
  moreover have "Space.cod i_CB = B \<and> Space.dom i_CB = C "
    by (simp add: i_CB_def) 
  moreover have "Space.cod i_CA = A \<and> Space.dom i_CA = C "
    by (simp add: i_CA_def) 
  moreover have "Poset.dom f = ob V \<cdot> A"
    by (simp add: F1_def calculation(12) calculation(4) calculation(8) f_def)
  moreover have "Poset.cod f  = ob V \<cdot> B \<and> Poset.dom g  = Prealgebra.ob
      (prealgebra V) \<cdot> B"
      by (simp add: F1_def calculation(12) calculation(13) calculation(4) calculation(6) calculation(8) f_def g_def)
  moreover have " (F1 \<cdot> i_CB) \<star> ((F1 \<cdot> i_BA) \<star> (e a)) =  (F1 \<cdot> i_CA) \<star> (e a)"  using Poset.compose_app_assoc
      by (metis A_def F1_def Prealgebra.valid_composition V_valid a_el calculation(10) calculation(11) calculation(12) calculation(13) calculation(15) calculation(16) calculation(4) calculation(6) calculation(8) f_def g_def local_inclusion_element)
  ultimately show ?thesis
    by (metis f_def g_def)
qed

(* [Remark 2 (3/3), TMCVA] *)
lemma stability:
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid: "valid V"
  and B_le_A : "B \<subseteq> A" and B_open : "B \<in> opens (space V)" and A_open : "A \<in> opens (space V)"
  defines \<epsilon>A_def: "\<epsilon>A \<equiv> neut V A"
  defines \<epsilon>B_def: "\<epsilon>B \<equiv> neut V B"
  defines \<epsilon>A_B_def: "\<epsilon>A_B \<equiv> res V B \<epsilon>A"
  shows "\<epsilon>A_B = \<epsilon>B"
proof -
  define i where "i \<equiv> make_inc B A"
  define "f" where "f = nat (neutral V)"
  define "one" where "one \<equiv> dom (neutral V)"
  moreover have "\<epsilon>A_B = res V B \<epsilon>A"
    by (simp add: \<epsilon>A_B_def)
  moreover have "Space.cod i = A \<and> Space.dom i = B"
    by (simp add: i_def)
  moreover have "i \<in> inclusions (space V)"
    using A_open B_le_A B_open calculation(3) inclusions_def by force
  moreover have "valid_map (neutral V)"
    using V_valid valid_neutral by blast 
  moreover have "Prealgebra.valid one"
    by (simp add: Prealgebra.valid_map_dom calculation(5) one_def)  
  moreover have v1: "Poset.valid_map (Prealgebra.ar one \<cdot> i)" using calculation assms Prealgebra.valid_ar
    [where ?F="prealgebra V" and ?i=i]
    apply clarsimp
    by (metis OVA.valid_welldefined Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def Prealgebra.valid_ar)
  moreover have v2: "Poset.valid_map (f \<cdot> B)"
      by (smt (verit, best) B_open OVA.valid_welldefined Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def Prealgebra.valid_map_welldefined V_valid f_def)
  moreover have "Prealgebra.valid one"
      by (metis OVA.valid_welldefined Prealgebra.valid_map_welldefined one_def V_valid)
  moreover have "(Prealgebra.ar one \<cdot> i ) \<star> ()  = ()"
    by simp
  moreover have "() \<in> Poset.el (Poset.dom  (Prealgebra.ar one \<cdot> i))" using Prealgebra.terminal_value
    using A_open B_le_A B_open V_valid calculation(3) one_def valid_domain valid_prealgebra valid_space inclusions_def  calculation(4) by fastforce
  moreover have "((f \<cdot> B) \<diamondop> (Prealgebra.ar one \<cdot> i)) \<star> () = (f \<cdot> B) \<star> ((Prealgebra.ar one \<cdot> i)) \<star> ()"
    using OVA.valid_welldefined Prealgebra.Prealgebra.select_convs(1) Prealgebra.valid_map_welldefined
    assms calculation res_cod compose_app_assoc f_def inclusions_def
    by (metis (no_types, lifting) Prealgebra.const_def) 
  moreover have "((ar V \<cdot> i) \<diamondop> (f \<cdot> A)) \<star> ()=  e \<epsilon>B"
    using  assms calculation f_def one_def snd_conv valid_map_naturality
    by (metis Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def valid_codomain valid_domain) 
  moreover have "e \<epsilon>A=   (f \<cdot> A) \<star> ()"
    by (simp add: \<epsilon>A_def f_def)
  ultimately show ?thesis
    using Prealgebra.valid_map_welldefined Prealgebra.valid_welldefined 
      assms compose_app_assoc eq_fst_iff f_def res_def i_def neutral_is_element sndI valid_codomain valid_domain
    by (metis (no_types, opaque_lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def)
qed

(* [Remark 3 (1/3), TMCVA] *)
lemma local_mono_eq_global :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a1 a1' a2 a2' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)"
  and a1_el : "a1 \<in> elems V" and a1_d : "d a1 = A"
  and a1'_el : "a1' \<in> elems V" and a1'_d : "d a1' = A"
  and a2_el : "a2 \<in> elems V" and a2_d : "d a2 = A"
  and a2'_el : "a2' \<in> elems V" and a2'_d : "d a2' = A"
shows "le V (comb V a1 a1') (comb V a2 a2') = local_le V A (comb V a1 a1') (comb V a2 a2')"
proof -
  define "b1" where "b1 = comb V a1 a1'" 
  define "b2" where "b2 = comb V a2 a2'" 
  have "b1 \<in> elems V"
    using V_valid a1'_el a1_el b1_def comb_is_element by blast
  moreover have "b2 \<in> elems V"
    using V_valid a2'_el a2_el b2_def comb_is_element by blast 
  ultimately show ?thesis using le_eq_local_le [where ?V=V and ?a=b1 and ?a'=b2]
    using A_open V_valid a1'_d a1'_el a1_d a1_el a2'_d a2'_el a2_d a2_el b1_def b2_def by auto
qed

(* [Remark 3 (2/3), TMCVA] *)
lemma id_le_res :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and B_open : "B \<in> opens (space V)" and B_le_A : "B \<subseteq> d a"
  and a_el : "a \<in> elems V"
shows " le V a (res V B a)"
proof -
  define "A" where "A = d a"
  define "i" where "i = make_inc B (d a)"
  define "Fi" where "Fi = ar V \<cdot> i"
  define "FA" where "FA = ob V \<cdot> A"
  define "FB" where "FB = ob V \<cdot> B"
  define "a_B" where "a_B =  Fi \<star> (e a)"
  have "i \<in> inclusions (space V)"
    using B_le_A B_open V_valid a_el d_elem_is_open i_def inclusions_def
    by (metis (no_types, lifting) CollectI Inclusion.select_convs(1) Inclusion.select_convs(2)) 
  moreover have "res V B a = (B, a_B)"
    by (metis B_le_A B_open Fi_def a_B_def a_el res_def i_def) 
  moreover have "Prealgebra.valid (prealgebra V)"
    by (simp add: V_valid valid_prealgebra)
  moreover have "Poset.valid FB"
    using B_open FB_def calculation(3) valid_ob by blast
  moreover have "Poset.valid_map Fi"
    using Fi_def calculation(1) calculation(3) valid_ar by blast
  moreover have "e a \<in> Poset.el FA"
    using A_def FA_def V_valid a_el local_inclusion_element by blast
  moreover have "Space.cod i = A \<and> Space.dom i = B \<and> i \<in> inclusions (space V)"
    using A_def calculation(1) i_def by auto
  moreover have "a_B \<in> Poset.el FB"
    by (metis B_le_A B_open FB_def V_valid a_el calculation(2) d_elem_is_open e_res snd_eqD)
  moreover have "Poset.le FB a_B a_B"
    by (simp add: calculation(4) calculation(8) valid_reflexivity)
  moreover have "valid V" by fact
  ultimately show ?thesis using assms 
    apply clarsimp
    apply (frule valid_welldefined)
    apply (simp_all add: Let_def gc_def) 
    apply safe
    apply (metis fst_conv subsetD)
    apply (metis (no_types, lifting) FB_def Fi_def a_B_def fst_conv i_def snd_conv)
    apply auto[1]
    using Fi_def a_B_def i_def apply fastforce
    using FB_def by force
qed

lemma elem_le_wrap :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" 
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  and B_le_A : "d b \<subseteq> d a" and a_B_le_b : "local_le V (d b) (res V (d b) a) b"
shows "le V a b"
proof -
  define "F" where "F = prealgebra V"
  define "FA" where "FA = (Prealgebra.ob F) \<cdot> d a"
  define "FB" where "FB = (Prealgebra.ob F) \<cdot> d b"
  define "a_B" where "a_B = res V (d b) a"
  have "a_B \<in> elems V"
    using B_le_A V_valid a_B_def a_el b_el d_elem_is_open res_elem by blast 
  moreover have a1: "Prealgebra.valid F"
    by (metis OVA.valid_welldefined F_def V_valid)
  moreover have "d a \<in> opens (space V)"
    using V_valid a_el d_elem_is_open by blast 
  moreover have "d b \<in> opens (space V)"
    using V_valid b_el d_elem_is_open by blast 
  moreover have "e a \<in> Poset.el FA"
    using FA_def F_def V_valid a_el local_inclusion_element by blast 
  moreover have "e b \<in> Poset.el FB"
    using FB_def F_def V_valid b_el local_inclusion_element by blast 
  moreover have "Prealgebra.space F = space V"
    by (simp add: F_def)
  ultimately show ?thesis  using assms le_eq_local_le [where ?V=V and ?A="d b" and ?a=a_B and
        ?a'=b ]
    by (smt (verit) a_B_def d_res id_le_res valid_poset valid_semigroup valid_transitivity) 
qed

(* [Theorem 1 (1/3), TMCVA] *)
theorem res_ext_adjunction :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and B_le_A : "d b \<subseteq> d a" 
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "local_le V (d b) (res V (d b) a) b = local_le V (d a) a (ext V (d a) b)" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume "?L"
  define "\<epsilon>A" where "\<epsilon>A \<equiv> neut V (d a)"
  define "a_B" where "a_B \<equiv> res V (d b) a"
  have "local_le V (d a) (comb V \<epsilon>A a) (comb V \<epsilon>A a_B)"
    by (smt (verit) B_le_A OVA.valid_welldefined V_valid \<epsilon>A_def a_B_def a_el b_el comb_is_element d_elem_is_open d_res fst_conv id_le_res local_le neutral_is_element res_elem sup.absorb_iff1 valid_domain_law valid_monotone valid_neutral_law_left valid_poset valid_reflexivity) 
  moreover have "local_le V (d a) (comb V \<epsilon>A a_B) (comb V \<epsilon>A b)" using assms a_B_def valid_comb_monotone [where ?V=V] le_eq_local_le [where ?V=V]
    by (smt (verit) OVA.valid_welldefined Poset.valid_def \<epsilon>A_def \<open>if d b = d (res V (d b) a) \<and> d b = d b then Poset.le (ob V \<cdot> d b) (e (res V (d b) a)) (e b) else OVA_local_le_undefined_domain_mismatch (res V (d b) a) b\<close> comb_is_element d_elem_is_open d_res fst_eqD neutral_is_element res_elem sup.absorb_iff1 valid_domain_law valid_poset)
  moreover have "comb V \<epsilon>A b = ext V (d a) b" using \<epsilon>A_def ext_def [where ?V=V and ?A="d a" and ?b=b]
    by (metis B_le_A V_valid a_el b_el d_elem_is_open) 
  ultimately show "?R"
    by (smt (z3) B_le_A V_valid \<epsilon>A_def a_B_def a_el b_el comb_is_element d_elem_is_open d_ext d_res local_inclusion_element neutral_is_element res_elem valid_domain_law valid_neutral_law_left valid_ob valid_prealgebra valid_transitivity)
next
  assume "?R"
  define "\<epsilon>A" where "\<epsilon>A \<equiv> neut V (d a)"
  define "a_B" where "a_B \<equiv> res V (d b) a"
  have "local_le V (d b) a_B (res V (d b) (ext V (d a) b))" using assms a_B_def res_monotone_local [where
          ?V=V and ?B="d b" and ?a1.0=a and ?a2.0="comb V \<epsilon>A b"] le_eq_local_le [where ?V=V]
    by (smt (verit) OVA.res_monotone OVA.valid_welldefined \<open>if d a = d a \<and> d a = d (ext V (d a) b) then Poset.le (ob V \<cdot> d a) (e a) (e (ext V (d a) b)) else OVA_local_le_undefined_domain_mismatch a (ext V (d a) b)\<close> d_elem_is_open d_ext d_res e_res ext_elem local_elem_gc prod.exhaust_sel)
  moreover have "ext V (d a) b = comb V \<epsilon>A b" using ext_def [where ?V=V]
    by (metis B_le_A V_valid \<epsilon>A_def a_el b_el d_elem_is_open) 
  moreover have "(res V (d b) (ext V (d a) b)) = comb V (res V (d a \<inter> d b) \<epsilon>A) b"  using valid_comb_law_right
    by (metis V_valid \<epsilon>A_def a_el b_el calculation(2) d_elem_is_open fst_eqD neutral_is_element)
  moreover have "comb V (res V (d a \<inter> d b) \<epsilon>A) b = comb V (neut V (d b)) b"
    by (metis B_le_A Int_absorb1 V_valid \<epsilon>A_def a_el b_el d_elem_is_open stability) 
  ultimately show "?L"
    by (metis V_valid a_B_def b_el valid_neutral_law_left)
qed

(* [Remark 3 (3/3), TMCVA] *)
lemma laxity :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and B_open :"B \<in> opens (space V)"  and B_le_A : "B \<subseteq> d a"
  and  a_el : "a \<in> elems V" and a_a'_dom : "d a' = d a"
  and a'_elem :  "a' \<in> elems V"
shows "local_le V B (res V B (comb V a a')) (comb V (res V B a) (res V B a'))"
proof -
   define "m1" where "m1 = comb V a a'"
   define "m2" where "m2 = comb V (res V B a) (res V B a')"
   define "m1_B" where "m1_B = res V B m1"
   have "le V a (res V B a)"
     using B_le_A B_open V_valid a_el id_le_res by blast
   moreover have "le V a' (res V B a')"
     by (metis B_le_A B_open V_valid a'_elem a_a'_dom id_le_res)
   moreover have global_le : "le V m1 m2"
     by (smt (verit) B_le_A B_open V_valid a'_elem a_a'_dom a_el calculation(1) calculation(2) m1_def m2_def res_elem valid_comb_monotone)
   moreover have "local_le V B m1_B m2" using V_valid  B_open   global_le valid_le
       [where ?V = V and ?a = m1 and ?b = m2]
      by (smt (z3) B_le_A a'_elem a_a'_dom a_el comb_is_element d_neut d_res m1_B_def m1_def m2_def neutral_is_element res_elem valid_domain_law valid_neutral_law_right)
   ultimately show ?thesis
     using m1_B_def m1_def m2_def by force
qed

(* [Corollary 1 (1/2), TMCVA] *)
corollary strongly_neutral_covariance :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and B_le_A : "B \<subseteq> A" and B_open : "B \<in> opens (space V)" and A_open : "A \<in> opens (space V)"
  and strongly_neutral: "is_strongly_neutral V"
shows "ext V A (neut V B) = neut V A "  
  by (metis (no_types, lifting) V_valid assms fst_eqD ext_def neutral_is_element strongly_neutral sup.absorb_iff1 is_strongly_neutral_def)

(* [Corollary 1 (2/2), TMCVA] *)
corollary strongly_neutral_monoid :
  fixes V :: "('A,'a) OVA" and a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V"
  and strongly_neutral: "is_strongly_neutral V"
defines "identity  \<equiv> neut V {}"
shows "comb V identity a = a \<and> comb V a identity = a "
proof
  define "\<epsilon>A" where "\<epsilon>A = neut V (d a)"
  have "a = comb V \<epsilon>A a "
    by (smt (verit, best) V_valid \<epsilon>A_def a_el d_elem_is_open valid_neutral_law_left)
  moreover have "comb V identity a = comb V identity (comb V \<epsilon>A a)"
    by (smt (verit, best) V_valid \<epsilon>A_def a_el d_elem_is_open valid_neutral_law_left)
  moreover have "... = comb V (comb V identity \<epsilon>A) a" using valid_comb_associative
    by (metis (no_types, opaque_lifting) OVA.valid_welldefined Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def neutral_is_element) 
  moreover have "... = comb V \<epsilon>A a"
    by (metis (no_types, lifting) is_strongly_neutral_def Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def strongly_neutral sup_bot_left valid_prealgebra)
  moreover have "... = a"
    using calculation(1) by presburger
  ultimately show "comb V identity a = a"
    by presburger
next
  define "\<epsilon>A" where "\<epsilon>A = neut V (d a)"
  have "a = comb V a \<epsilon>A "
    by (smt (verit, best) V_valid \<epsilon>A_def a_el d_elem_is_open valid_neutral_law_right)
  moreover have "comb V a identity = comb V (comb V a \<epsilon>A) identity"
    by (smt (verit, best) V_valid \<epsilon>A_def a_el d_elem_is_open valid_neutral_law_right)
  moreover have "... = comb V a (comb V \<epsilon>A identity)" using valid_comb_associative
    by (metis (no_types, lifting) OVA.valid_welldefined Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def neutral_is_element) 
  moreover have "... = comb V a \<epsilon>A"
    by (metis (no_types, lifting) is_strongly_neutral_def Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def strongly_neutral sup_bot.right_neutral valid_prealgebra)
  moreover have "... = a"
    using calculation(1) by presburger
  ultimately show "comb V a identity = a"
    by presburger
qed

(* [Corollary 2 (1/3), TMCVA] *)
corollary galois_insertion :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and b_el : "b \<in> elems V"
  and B_le_A : " d b \<subseteq> A" and A_open : "A \<in> opens (space V)"
  shows "res V (d b) (ext V A b) = b"
proof -                      
  define B where "B \<equiv> d b"
  define \<epsilon>A where "\<epsilon>A \<equiv> neut V A"
  define \<epsilon>B where "\<epsilon>B \<equiv> neut V B"
  have "res V (d b) (ext V A b) = res V B (comb V \<epsilon>A b)" using res_def [where ?V=V] ext_def
        [where ?V=V]
    using A_open B_le_A \<epsilon>A_def b_el B_def by presburger      
  moreover have "... =  comb V (res V (A \<inter> B) \<epsilon>A) b"  using B_def valid_comb_law_right [where ?V=V and ?b=b and ?a=\<epsilon>A]
    using A_open V_valid \<epsilon>A_def b_el neutral_is_element by auto
  moreover have "... =  comb V \<epsilon>B b"
    by (metis A_open B_def B_le_A V_valid \<epsilon>A_def \<epsilon>B_def b_el d_elem_is_open inf.absorb_iff2 stability)
  ultimately show ?thesis
    by (metis B_def V_valid \<epsilon>B_def b_el valid_neutral_law_left) 
qed

(* [Corollary 2 (2/3), TMCVA] *)
corollary galois_closure_extensive :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "a \<in> elems V" 
  and "B \<subseteq> d a" and "B \<in> opens (space V)"
  shows "local_le V (d a) a (ext V (d a) (res V B a))"
proof -
  have "local_le V (d a) a a"
    by (meson V_valid assms(2) d_elem_is_open local_inclusion_element valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V B (res V B a) (res V B a)"
    by (metis OVA.valid_welldefined V_valid assms(2) assms(3) assms(4) d_elem_is_open d_res e_res valid_ob valid_reflexivity)
  moreover have "res V B a \<in> elems V"
    using V_valid assms(2) assms(3) assms(4) res_elem by blast
  moreover have "d (res V B a) = B"
    using assms(2) assms(3) assms(4) by auto
  ultimately show ?thesis using assms res_ext_adjunction [where ?V=V and ?a=a and ?b="res V B a" ]
    by presburger
qed

lemma ext_functorial_trans_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B:: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V"
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)"
  and C_le_B : "d c \<subseteq> B" and B_le_A : "B \<subseteq> A"
  defines "ex \<equiv> ext V"
  and "pr \<equiv> res V"
  shows "le V (ex A c) (ex A (ex B c))"
proof -
  define "C" where "C = d c"
  have "local_le V C c c"
    by (metis C_def OVA.valid_welldefined V_valid c_el d_elem_is_open local_inclusion_element valid_ob valid_reflexivity)
  moreover have "local_le V C (pr C (ex A c)) c"
    by (smt (verit, best) A_open B_le_A C_def C_le_B V_valid c_el calculation dual_order.trans ex_def galois_insertion pr_def)
  moreover have "pr C (pr B (ex A c)) = pr C (ex A c)"
    by (smt (verit, ccfv_SIG) A_open B_le_A B_open C_def C_le_B V_valid c_el d_elem_is_open d_ext dual_order.trans ex_def ext_elem pr_def res_functorial_trans)
  moreover have "local_le V C  (pr C (pr B (ex A c))) c"
    using calculation(2) calculation(3) by presburger
  moreover have "local_le V B (pr B (ex A c)) (ex B c)" 
    using C_def assms calculation d_ext d_res ex_def ext_elem res_elem order_trans pr_def
      res_ext_adjunction [where ?V=V]
    by (smt (verit))
  moreover have "local_le V A (ex A c) (ex A (ex B c))"
    using assms calculation d_ext dual_order.trans ex_def ext_elem pr_def res_ext_adjunction [where ?V=V]
    by (smt (z3))
  moreover have "d (ex A c) = A \<and> d ((ex A (ex B c))) = A"
    by (smt (verit) A_open B_le_A B_open C_le_B V_valid c_el d_ext dual_order.trans ex_def ext_elem) 
    ultimately show ?thesis using assms  d_ext
          dual_order.refl dual_order.trans elem_le_wrap ex_def pr_def galois_insertion [where ?V=V]
          ext_elem [where ?V=V] res_functorial_trans [where ?V=V] le_eq_local_le [where ?V=V]
      by (smt (verit))
qed

lemma ext_functorial_trans_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and c :: "('A, 'a) Valuation"
  defines "ex \<equiv> ext V"
  and "pr \<equiv> res V"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V" 
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)" 
  and C_le_B : "d c \<subseteq> B" and B_le_A : "B \<subseteq> A"
  shows "le V (ex A (ex B c)) (ex A c)"
proof -
  have "local_le V A (ex A (ex B c)) (ex A (ex B c))"
    by (metis A_open B_le_A B_open C_le_B OVA.valid_welldefined V_valid c_el d_ext e_ext ex_def ext_elem valid_ob valid_reflexivity)
  moreover have "local_le V B (pr B (ex A (ex B c))) (ex B c)"
    by (metis A_open B_le_A B_open C_le_B OVA.valid_welldefined V_valid c_el d_ext e_ext ex_def ext_elem galois_insertion pr_def valid_ob valid_reflexivity)
  moreover have "local_le V (d c) (pr (d c) (pr B (ex A (ex B c)))) c"
    by (metis A_open B_le_A B_open C_le_B V_valid c_el d_elem_is_open d_ext ex_def ext_elem galois_insertion local_inclusion_element pr_def valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V (d c) (pr (d c) (ex A (ex B c))) c"
    by (metis (no_types, lifting) A_open B_le_A B_open C_le_B V_valid c_el calculation(3) d_elem_is_open d_ext ex_def ext_elem pr_def res_functorial_trans)
  moreover have "local_le V A (ex A (ex B c)) (ex A c)" using res_ext_adjunction [where ?V=V]
    by (smt (z3) A_open B_le_A B_open C_le_B V_valid c_el calculation(4) d_ext dual_order.trans ex_def ext_elem pr_def) 
  ultimately show ?thesis
    by (smt (verit) A_open B_le_A B_open C_le_B OVA.valid_welldefined V_valid c_el d_ext e_ext ex_def ext_functorial_trans_lhs_imp_rhs local_elem_gc local_le prod.exhaust_sel subset_trans valid_antisymmetry valid_ob)
qed

(* [Theorem 1 (2/3), TMCVA] *)
theorem ext_functorial_id :
  fixes V :: "('A,'a) OVA" and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V"
shows "ext V (d c) c = c"
  by (metis (no_types, lifting) V_valid c_el d_elem_is_open d_ext ext_elem galois_insertion res_functorial_trans subsetI)

(* [Theorem 1 (2/3), TMCVA] *)
theorem ext_functorial_trans :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V"
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)"
  and C_le_B : "d c \<subseteq> B" and B_le_A : "B \<subseteq> A" 
  defines "ex \<equiv> ext V"
  shows "ex A (ex B c) = ex A c"
proof -
  have "le V (ex A (ex B c)) (ex A c)"
    using A_open B_le_A B_open C_le_B V_valid c_el ex_def ext_functorial_trans_rhs_imp_lhs by blast
  moreover have "le V (ex A c)  (ex A (ex B c))"
    using A_open B_le_A B_open C_le_B V_valid c_el ex_def ext_functorial_trans_lhs_imp_rhs by blast
  ultimately show ?thesis
    by (smt (verit, best) A_open B_le_A B_open C_le_B V_valid c_el d_ext dual_order.trans ex_def ext_elem valid_antisymmetry valid_poset valid_semigroup)
qed

(* [Corollary 2 (3/3), TMCVA] *)
corollary galois_closure_idempotent :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d a = A" and "a \<in> elems V"
  defines "ex \<equiv> ext V"
  and "pr \<equiv> res V"
  shows "ex A (pr B (ex A (pr B a))) = ex A (pr B a)"
  by (metis assms(2) assms(3) assms(6) assms(7) assms(8) d_res ex_def galois_insertion res_elem pr_def V_valid)

lemma up_and_down :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "d c \<subseteq> B" and "B \<subseteq> A"  and "c \<in> elems V"
shows "res V B (ext V A c) = ext V B c"
  by (metis V_valid assms(2) assms(3) assms(5) assms(6) assms(7) d_ext ext_elem ext_functorial_trans galois_insertion)

lemma intermediate_extension :
  fixes V :: "('A,'a) OVA" and a c :: "('A, 'a) Valuation" and A B C :: "('A Open)"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V" and c_elem : "c \<in> elems V"
  and dom_A : "d a = A" and dom_c : "d c = C"
  and C_le_B : "C \<subseteq> B" and B_leq_A : "B \<subseteq> A"
  and B_open : "B \<in> opens (space V)"
  assumes le_a_C_c : "local_le V C (res V C a) c"
  shows "local_le V B (res V B a) (ext V B c)"
proof -
  have "A \<in> opens (space V) \<and> B \<in> opens (space V) \<and> C \<in> opens (space V)"
    using B_open a_el c_elem dom_A dom_c d_elem_is_open V_valid by blast
  moreover have "local_le V C (res V C a) c" by fact
  moreover have "local_le V A a (ext V A c)" using res_ext_adjunction
    by (smt (z3) B_leq_A C_le_B a_el c_elem dom_A dom_c dual_order.trans ext_def ext_elem le_a_C_c d_elem_is_open V_valid)
  moreover have "ext V A c = ext V A (ext V B c)" using ext_functorial_trans
    by (metis B_leq_A C_le_B c_elem calculation(1) dom_c V_valid)
  moreover have "local_le V A a (ext V A (ext V B c))"
    by (metis calculation(3) calculation(4))
  ultimately show ?thesis using res_ext_adjunction le_a_C_c
    by (smt (verit, best) B_leq_A C_le_B V_valid a_el c_elem d_ext dom_A dom_c ext_elem)
qed

(* [Corollary 3, TMCVA] *)
corollary locally_complete_imp_complete :
  fixes V :: "('A,'a) OVA"
  defines "F A \<equiv> (ob V) \<cdot> A"
  and "pr \<equiv> res V" and "ex \<equiv> ext V"
  assumes V_valid: "valid V"
  assumes local_completeness: "\<And>A . A \<in> opens (space V) \<Longrightarrow> Poset.is_complete (F A)"
  shows "Poset.is_complete (poset V)"
  unfolding is_complete_def
proof
  show "Poset.valid (poset V)"
    using V_valid by (metis OVA.valid_welldefined valid_gc)
next
  show "(\<forall> U \<subseteq> el (poset V). \<exists> i . is_inf (poset V) U i)"
  proof safe
    fix U
    assume U: "U \<subseteq> elems V"

    define "d_U" where "d_U = \<Union> (d ` U)"
    define "ex_U" where "ex_U = ((e o ex d_U) ` U)"
    define "some_e_U" where "some_e_U = Poset.inf (F (d_U)) ex_U"

    have "d_U \<in> opens (space V)"
      by (smt (verit, best) Prealgebra.valid_space U V_valid d_U_def image_subsetI d_elem_is_open subsetD valid_prealgebra valid_union)
    moreover have "ex_U \<subseteq> Poset.el (F (d_U))"
      by (smt (verit) Sup_upper UN_subset_iff Union_least F_def \<open>U \<subseteq> elems V\<close> calculation comp_apply d_U_def e_ext ex_U_def ex_def image_subsetI in_mono d_elem_is_open V_valid)
    moreover have "some_e_U \<noteq> None" using Poset.complete_inf_not_none
      using calculation(1) calculation(2) local_completeness some_e_U_def F_def V_valid valid_ob valid_prealgebra
      by metis

    obtain e_U where "some_e_U = Some e_U" using \<open>some_e_U \<noteq> None\<close> by auto
   
    moreover have "e_U \<in> Poset.el (F d_U)"
      by (metis (mono_tags, lifting) \<open>some_e_U \<noteq> None\<close> calculation(3) inf_def option.inject someI_ex some_e_U_def)
    define "i" where "i = (d_U, e_U)"
    moreover have "i \<in> elems V"
      by (metis F_def \<open>e_U \<in> el (F d_U)\<close> calculation(1) global_inclusion_element i_def V_valid)
    
    have "Poset.is_inf (poset V) U i"
    proof -
      have "U \<subseteq> el (poset V)"
        by (metis \<open>U \<subseteq> elems V\<close>  )
      moreover have "i \<in> el (poset V)"
        by (metis \<open>i \<in> elems V\<close>  )
      moreover have "(\<forall>u\<in>U. Poset.le (poset V) i u)"
        proof
        fix u
        assume "u \<in> U"
        moreover have "d u \<subseteq> d_U"
          using calculation(1) d_U_def by blast
        moreover have "Poset.valid (F (d_U))"
          using \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> local_completeness
          by (simp add: is_complete_def) 
        moreover have "Poset.is_complete (F (d_U))"
          using \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> local_completeness by blast 
        moreover have "Poset.is_inf (F (d_U)) ex_U e_U" using ex_U_def local_completeness
          by (metis \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> \<open>some_e_U = Some e_U\<close> calculation(3) some_e_U_def some_inf_is_inf)
        moreover have "d i = d_U \<and> d (ex d_U u) = d_U"
          using U V_valid \<open>d_U \<in> opens (OVA.space V)\<close> calculation(1) calculation(2) ex_def i_def by auto 
        moreover have "local_le V (d_U) i (ex d_U u)"
          using F_def \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> calculation(1) calculation(3) calculation(5) calculation(6) ex_U_def i_def inf_smaller by fastforce 
        moreover have "d u = d (pr (d u) i)"
          using U V_valid \<open>i \<in> OVA.elems V\<close> calculation(1) calculation(2) calculation(6) d_elem_is_open d_res pr_def by blast 
        moreover have "local_le V (d u) (pr (d u) i) u"  using res_ext_adjunction [where ?V=V]
          using U V_valid \<open>i \<in> OVA.elems V\<close> calculation(1) calculation(2) calculation(6) calculation(7) ex_def pr_def by blast
        moreover have i_is_lb: "le V i u"  using le_eq_local_le [where ?V=V]
          by (smt (verit) Poset.valid_def U V_valid \<open>i \<in> OVA.elems V\<close> calculation(1) calculation(2) calculation(6) calculation(7) d_elem_is_open ex_def ext_elem galois_insertion id_le_res subset_eq valid_poset valid_semigroup) 
        ultimately show "le V i u"
          by blast
      qed
       moreover have "\<forall>z\<in>el (poset V). (\<forall>u\<in>U. le V z u) \<longrightarrow> le V z i"
       proof standard+
        fix z
        assume "z \<in>  elems V"
        assume "\<forall>u\<in>U. le V z u"
        moreover have lb2: "\<forall> v \<in> U . d v \<subseteq> d z" 
          by (metis (no_types, lifting) OVA.valid_welldefined U V_valid \<open>z \<in> OVA.elems V\<close> calculation d_antitone subset_iff)
        moreover have "d z \<in> opens (space V)"
          using V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> d_elem_is_open by blast
         moreover have "\<forall> v \<in> U .d v \<in> opens (space V)"
           using U V_valid d_elem_is_open by blast
         moreover have "\<forall> v \<in> U .v \<in> elems V"
           using U V_valid d_elem_is_open by blast
        moreover have "\<forall> v \<in> U . local_le V (d v) (pr (d v) z) v" using V_valid valid_le [where ?V
              = V and ?a = z]
          using U \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(1) d_elem_is_open pr_def by blast
        moreover have "\<forall> v \<in> U . Poset.le (F (d v)) (e (pr (d v) z)) (e v)"
          using F_def calculation(6)
          by (metis \<open>z \<in> OVA.elems V\<close> calculation(4) d_res lb2 pr_def) 
        define "z_U" where "z_U = res V d_U z"
        moreover have "\<forall> v \<in> U . pr d_U (ex (d z) v) = ex d_U v" using up_and_down
          by (smt (verit, ccfv_threshold) UN_subset_iff V_valid \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> calculation(3) calculation(4) calculation(5) d_U_def ex_def lb2 pr_def subset_eq)
        moreover have "Poset.valid (F d_U)"
          using \<open>d_U \<in> opens (OVA.space V)\<close> is_complete_def local_completeness by fastforce
        moreover have "d_U \<in> opens (space V)"
          using \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> by blast
        moreover have "d_U \<subseteq> d z"
          by (simp add: UN_subset_iff d_U_def lb2)
        moreover have "z_U \<in> elems V" using z_U_def res_elem [where ?V=V and ?B=d_U and ?a=z] calculation
          using V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> by fastforce
        moreover have "e z_U \<in> Poset.el (F d_U)"
          by (metis V_valid F_def \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(10) calculation(11) calculation(3) e_res z_U_def)
        moreover have "\<forall> v \<in> U . local_le V d_U z_U (ex d_U v)" using z_U_def calculation
         intermediate_extension [where ?V = V and ?B = d_U and ?a = z]
          by (smt (verit) V_valid \<open>\<forall>u\<in>U. OVA.le V i u\<close> \<open>i \<in> OVA.elems V\<close> \<open>z \<in> OVA.elems V\<close> d_antitone ex_def fst_conv i_def pr_def valid_gc_poset valid_prealgebra) 
            moreover have "\<forall> v \<in> U . local_le V (d z) z (ext V (d z) v)" using
                res_ext_adjunction [where ?V=V]
              using V_valid \<open>z \<in> OVA.elems V\<close> calculation(5) calculation(6) lb2 pr_def by blast
              moreover have "\<Union> (d ` U) \<subseteq> d z"
                by (simp add: SUP_least lb2)
        moreover have "d i \<subseteq> d z"
          by (simp add: calculation(11) i_def)
        define "i__Z" where "i__Z = ext V (d z) i"
        moreover have "Poset.le (F d_U) (e ( res V d_U z)) e_U"  using inf_is_glb 
        proof -
          have "Poset.valid (F d_U)"
            using calculation(9) by auto
          moreover have "ex_U \<subseteq> el (F d_U)"
            by (simp add: \<open>ex_U \<subseteq> el (F d_U)\<close>)
          moreover have "e (res V d_U z) \<in> el (F d_U)"
            using \<open>e z_U \<in> el (F d_U)\<close> z_U_def by auto
          moreover have "e_U \<in> el (F d_U)"
            by (simp add: \<open>e_U \<in> el (F d_U)\<close>)
          moreover have "is_inf (F d_U) ex_U e_U"
            using \<open>Poset.valid (F d_U)\<close> \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> \<open>some_e_U = Some e_U\<close> some_e_U_def some_inf_is_inf by fastforce
          moreover have z_U_is_lb : "\<forall> v \<in> U . Poset.le (F d_U) (e (res V d_U z)) (e (ex d_U v))"
            by (metis F_def V_valid \<open>\<forall>u\<in>U. OVA.le V i u\<close> \<open>\<forall>v\<in>U. if d_U = d z_U \<and> d_U = d (ex d_U v) then Poset.le (ob V \<cdot> d_U) (e z_U) (e (ex d_U v)) else OVA_local_le_undefined_domain_mismatch z_U (ex d_U v)\<close> \<open>\<forall>v\<in>U. v \<in> OVA.elems V\<close> \<open>d_U \<in> opens (OVA.space V)\<close> \<open>d_U \<subseteq> d z\<close> \<open>i \<in> OVA.elems V\<close> \<open>z \<in> OVA.elems V\<close> d_antitone d_ext d_res ex_def fst_conv i_def valid_gc_poset valid_prealgebra z_U_def)
          moreover have "\<forall> u \<in> ex_U. Poset.le (F d_U) (e (res V d_U z)) u"  using z_U_is_lb
            by (simp add: ex_U_def)
          moreover have "Poset.le_rel (F d_U) \<subseteq> le_rel (F d_U)"
            by simp
          ultimately show ?thesis
            by (simp add: inf_is_glb)
        qed
        moreover have "Poset.le (poset V) z i" using le_eq_local_le [where ?V=V]
          by (smt (verit) F_def V_valid \<open>i \<in> OVA.elems V\<close> \<open>z \<in> OVA.elems V\<close> calculation(10) calculation(11) calculation(12) calculation(18) fst_conv i_def id_le_res res_def snd_conv valid_poset valid_semigroup valid_transitivity z_U_def) 
        term ?thesis
        ultimately show "Poset.le (OVA.poset V) z i"
          by meson
      qed
      moreover have "is_inf (poset V) U i"
        by (smt (verit) U calculation(2) calculation(3) calculation(4) is_inf_def)
      ultimately show ?thesis
        by linarith
    qed
    show "\<exists>i. is_inf (OVA.poset V) U i"
      using \<open>is_inf (OVA.poset V) U i\<close> by blast 
  qed
qed

(* Extension of local operators *)

definition ext_local :: "('A, 'a) OVA \<Rightarrow> ('A Open, ('a \<times> 'a,'a) PosetMap) Function 
  \<Rightarrow> (('A, 'a) Valuation) Semigroup" where
"ext_local V f = \<lparr> mult =
  \<lparr> PosetMap.dom = OVA.poset V \<times>\<times> OVA.poset V, 
    cod = OVA.poset V,
    func = { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (OVA.poset V \<times>\<times> OVA.poset V) } \<rparr>\<rparr>" 

lemma d_ext_local : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation"  
  and op :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  shows "d (mul (ext_local V f) a b) = d a \<union> d b"
proof -
  define "comb'" where "comb' = mult (ext_local V f)"
  have "Poset.dom comb' = OVA.poset V \<times>\<times> OVA.poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp            
  moreover have 1 : "Poset.func comb' =  { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (OVA.poset V \<times>\<times> OVA.poset V) }"  using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp
  moreover have 2 : "(a,b) \<in> el (Poset.dom comb')"  using comb'_def ext_local_def [where ?V=V and ?f=f]
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def SigmaI a_el b_el calculation(1))
  moreover have "comb' \<star> (a, b) = (d a \<union> d b, f \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V
 (d a \<union> d b) b)))" 
    using comb'_def ext_local_def [where ?V=V and ?f=f] 1 2 Poset.app_def [where ?f=comb' and
        ?a="(a,b)"]
    by (smt (z3) calculation(1) mem_Collect_eq old.prod.inject the_equality) 
  ultimately show ?thesis
    by (simp add: comb'_def)  
qed

lemma e_ext_local : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation"  
  and op :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  shows "e (mul (ext_local V f) a b) =  f \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))"
proof -
  define "comb'" where "comb' = mult (ext_local V f)"
  have "Poset.dom comb' = OVA.poset V \<times>\<times> OVA.poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]    
    by simp            
  moreover have 1 : "Poset.func comb' =  { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (OVA.poset V \<times>\<times> OVA.poset V) }"  using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp
  moreover have 2 : "(a,b) \<in> el (Poset.dom comb')"  using comb'_def ext_local_def [where ?V=V and ?f=f]
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def SigmaI a_el b_el calculation(1))
  moreover have "comb' \<star> (a, b) = (d a \<union> d b, f \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V
 (d a \<union> d b) b)))" 
    using comb'_def ext_local_def [where ?V=V and ?f=f] 1 2 Poset.app_def [where ?f=comb' and
        ?a="(a,b)"]
    by (smt (z3) calculation(1) mem_Collect_eq old.prod.inject the_equality) 
  ultimately show ?thesis
    by (simp add: comb'_def)  
qed

lemma ext_local_el : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation"  
  and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  and V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
shows "mul (ext_local V f) a b \<in> elems V" 
proof -
  define "comb'" where "comb' = mult (ext_local V f)"
  have "Poset.dom comb' = OVA.poset V \<times>\<times> OVA.poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp        
  moreover have  "Poset.cod comb' = OVA.poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp       
  moreover have  "Poset.func comb' =  { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (OVA.poset V \<times>\<times> OVA.poset V) }"  using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp
  moreover have "Poset.valid_map (f \<cdot> (d a \<union> d b))"  using assms
    by (simp add: Prealgebra.valid_space d_elem_is_open valid_prealgebra valid_union2)
  moreover have "(a, b) \<in> el (Poset.dom comb')"  using comb'_def ext_local_def [where ?V=V and ?f=f]
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def SigmaI a_el b_el calculation(1))
  moreover have "Poset.dom (f \<cdot> (d a \<union> d b)) = ob V \<cdot> (d a \<union> d b) \<times>\<times> ob V \<cdot> (d a \<union> d b)"
    by (meson Prealgebra.valid_space V_valid a_el b_el d_elem_is_open f_dom valid_prealgebra valid_union2) 
  moreover have "(e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b)) \<in> el (Poset.dom (f \<cdot> (d a \<union> d
    b)))"
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def Prealgebra.valid_space SigmaI V_valid a_el b_el calculation(6) d_elem_is_open e_ext sup_ge1 sup_ge2 valid_prealgebra valid_union2) 
  ultimately show ?thesis
    by (metis (no_types, lifting) Poset.fun_app2 Prealgebra.valid_space V_valid a_el b_el d_elem_is_open d_ext_local e_ext_local f_cod global_inclusion_element prod.collapse valid_prealgebra valid_union2)  
qed

(* [Lemma 2 (1/2), TMCVA] *)
lemma local_ext_comm_imp_assoc:
  fixes V :: "('A, 'a) OVA" 
  and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and local_assoc : "\<And>A a a' a''. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)  \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> a'' \<in> el (ob V
   \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (f \<cdot> A \<star> (a, a'), a'') = f \<cdot> A \<star> (a, f \<cdot> A \<star> (a', a''))"
  and local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, (f \<cdot> B) \<star> (b, b'))) = (f \<cdot> A) \<star> (e (ext V A (B, b)), e (ext V A (B, b'))) "
shows "\<And> a b c . a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow> 
  comb' (comb' a b) c = comb' a (comb' b c)"
proof (standard, goal_cases)
  case (1 a b c)
  then show ?case 
  proof -
    have "d (comb' a b) = d a \<union> d b"
      using "1"(1) "1"(2) comb'_def d_ext_local by blast
    moreover have "d (comb' (comb' a b) c) = d a \<union> d b \<union> d c" using d_ext_local [where ?V=V and ?a="comb' a b" and ?b=c]
        ext_local_el [where ?V=V and ?a=a and ?b=b] calculation assms
      using "1"(1) "1"(2) "1"(3) by blast 
    moreover have "d (comb' b c) = d b \<union> d c"
      using "1"(2) "1"(3) comb'_def d_ext_local by blast
    moreover have "d (comb' a (comb' b c)) = d a \<union> d b \<union> d c" using d_ext_local [where ?V=V and ?a=a and ?b="comb' b c"]
        ext_local_el [where ?V=V and ?a=b and ?b=c] calculation assms
      using "1"(1) "1"(2) "1"(3) by blast
    ultimately show ?thesis
      by presburger
  qed
next
  case (2 a b c)
  then show ?case 
  proof -
    define "U" where "U = d a \<union> d b \<union> d c"
    have "a \<in> OVA.elems V \<and> b \<in> OVA.elems V \<and> c \<in> OVA.elems V"
      using "2"(1) "2"(2) "2"(3) by blast 
    moreover have "d (comb' a b) = d a \<union> d b"
      using "2"(1) "2"(2) comb'_def d_ext_local by blast 
    moreover have "comb' a b \<in> elems V" using ext_local_el [where ?V=V and ?a=a and ?b=b]
      using "2"(1) "2"(2) V_valid comb'_def f_cod f_dom f_valid f_valid_val by blast
    moreover have "d (comb' b c) = d b \<union> d c"
      using "2"(2) "2"(3) comb'_def d_ext_local by blast 
    moreover have "comb' b c \<in> elems V" using ext_local_el [where ?V=V and ?a=b and ?b=c]
      using "2"(2) "2"(3) V_valid comb'_def f_cod f_dom f_valid f_valid_val by blast 

    moreover have "e (comb' (comb' a b) c) = f \<cdot> U \<star> (
        e (ext V U (comb' a b)),
        e (ext V U c))"
      using e_ext_local assms U_def
      by (metis (no_types, lifting) "2"(3) calculation(2) calculation(3))
    moreover have "... = f \<cdot> U \<star> 
        (e (ext V U (d a \<union> d b, 
            f \<cdot> (d a \<union> d b) \<star> (
                e (ext V (d a \<union> d b) a), 
                e (ext V (d a \<union> d b) b)))),
         e (ext V U c))"
      using assms U_def e_ext_local [where ?V=V and ?a=a and ?b=b] calculation
      by (metis prod.collapse)
    moreover have "... = f \<cdot> U \<star> 
          (f \<cdot> U \<star> (
              e (ext V U (ext V (d a \<union> d b) a)), 
              e (ext V U (ext V (d a \<union> d b) b))),
         e (ext V U c))" using local_ext_comm [where ?B="d a \<union> d b" and ?b="e (ext V (d a \<union> d b) a)"
      and ?b'="e (ext V (d a \<union> d b) b)"]
      by (smt (verit, ccfv_threshold) "2"(1) "2"(2) "2"(3) U_def V_valid comb_is_element d_elem_is_open d_ext e_ext inf_sup_aci(5) prod.exhaust_sel sup.cobounded2 valid_domain_law) 
    moreover have "... = f \<cdot> U \<star> 
          (f \<cdot> U \<star> (
              e (ext V U a), 
              e (ext V U b)),
         e (ext V U c))"
      by (metis (no_types, lifting) Prealgebra.valid_space U_def V_valid calculation(1) d_elem_is_open ext_functorial_trans sup_ge1 sup_ge2 valid_prealgebra valid_union2) 
    moreover have "... = f \<cdot> U \<star> 
         (e (ext V U a),
          f \<cdot> U \<star> (
              e (ext V U b), 
              e (ext V U c)))" using local_assoc [where ?A=U]
      by (smt (verit, best) "2"(1) "2"(2) "2"(3) OVA.valid_welldefined Prealgebra.valid_welldefined U_def V_valid d_elem_is_open d_ext e_ext ext_elem ext_functorial_trans inf_sup_ord(3) inf_sup_ord(4) valid_union2)
    moreover have "... = f \<cdot> U \<star> 
         (e (ext V U a),
          f \<cdot> U \<star> (
              e (ext V U (ext V (d b \<union> d c) b)), 
              e (ext V U (ext V (d b \<union> d c) c))))"
      by (metis (no_types, lifting) "2"(1) "2"(2) "2"(3) U_def V_valid boolean_algebra_cancel.sup1 comb_is_element d_elem_is_open ext_functorial_trans sup.cobounded1 sup.cobounded2 valid_domain_law)
    moreover have "... = f \<cdot> U \<star> 
         (e (ext V U a),
          e (ext V U (d b \<union> d c, f \<cdot> (d b \<union> d c) \<star> (
              e (ext V (d b \<union> d c) b), 
              e (ext V (d b \<union> d c) c)))))"
      by (smt (verit, del_insts) "2"(2) "2"(3) Prealgebra.valid_space U_def V_valid calculation(2) calculation(3) d_elem_is_open d_ext e_ext local_ext_comm prod.collapse sup_assoc sup_commute sup_ge1 valid_prealgebra valid_union2) 
    moreover have "... = f \<cdot> U \<star> 
         (e (ext V U a),
          e (ext V U (comb' b c)))"
          by (metis "2"(2) "2"(3) calculation(4) comb'_def e_ext_local prod.exhaust_sel)
    moreover have "... = e (comb' a (comb' b c))"
      by (metis (no_types, lifting) U_def calculation(1) calculation(4) calculation(5) comb'_def e_ext_local sup_assoc)
    ultimately show ?thesis
      by presburger
  qed
qed

(* [Lemma 2 (2/2), TMCVA] *)
lemma local_assoc_units_imp_ext_comm:
  fixes V :: "('A, 'a) OVA" and i :: "('A Open, 'a) Function"
  and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and units_valid : "Function.valid_map i \<and> Function.dom i = opens (space V)"
  and units_el : "\<And>A. A \<in> opens (space V) \<Longrightarrow> i \<cdot> A \<in> el (ob V \<cdot> A)"
  and local_assoc : "\<And>A a a' a''. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)  \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> a'' \<in> el (ob V
   \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (f \<cdot> A \<star> (a, a'), a'') = f \<cdot> A \<star> (a, f \<cdot> A \<star> (a', a''))"
  and assoc : "\<And> a b c . a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow> 
  comb' (comb' a b) c = comb' a (comb' b c)"
  and units : "\<And>A a. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (i \<cdot> A, a) = a \<and> f \<cdot> A \<star> (a, i \<cdot> A) = a "
shows local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, (f \<cdot> B) \<star> (b, b'))) = (f \<cdot> A) \<star> (e (ext V A (B, b)), e (ext V A (B, b')))"
proof -
  fix A B b b'
  assume B_open: "B \<in> opens (space V)"
  assume A_open : "A \<in> opens (space V)"
  assume B_le_A : "B \<subseteq> A"
  assume b_el : "b \<in> el (ob V \<cdot> B)" 
  assume b'_el :"b' \<in> el (ob V \<cdot> B)"

  have lem : "\<forall> b \<in> el (ob V \<cdot> B) . comb' (B, b) (A, i \<cdot> A) = ext V A (B, b)" 
  proof 
    fix b
    assume "b \<in> el (ob V \<cdot> B)" 
    have "comb' (B, b) (A, i \<cdot> A) = (A, f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (A, i \<cdot> A))))" using assms
      by (smt (verit, del_insts) \<open>A \<in> opens (OVA.space V)\<close> \<open>B \<in> opens (OVA.space V)\<close> \<open>B \<subseteq> A\<close> \<open>b \<in> el (OVA.ob V \<cdot> B)\<close> d_ext_local e_ext_local fst_conv global_inclusion_element prod.expand snd_conv sup.absorb_iff2) 
    moreover have "... =  (A, f \<cdot> A \<star> (e (ext V A (B, b)), i \<cdot> A))" 
      using ext_functorial_id V_valid \<open>A \<in> opens (OVA.space V)\<close> global_inclusion_element units_el by fastforce 
    moreover have "... = ext V A (B, b)"
      by (metis V_valid \<open>A \<in> opens (OVA.space V)\<close> \<open>B \<in> opens (OVA.space V)\<close> \<open>B \<subseteq> A\<close> \<open>b \<in> el (OVA.ob V \<cdot> B)\<close> d_ext e_ext fst_conv global_inclusion_element prod.collapse units) 
    ultimately show "comb' (B, b) (A, i \<cdot> A) = ext V A (B, b)"
      by presburger
  qed
  moreover have "(b, b') \<in> el (Poset.dom (f \<cdot> B))" using product_def
    by (metis (no_types, lifting) B_open Poset.Poset.select_convs(1) SigmaI assms(5) b'_el b_el) 
  moreover have "(f \<cdot> B) \<star> (b, b') \<in> el (ob V \<cdot> B)" using f_cod [where ?A=B] f_dom [where ?A=B] b_el
      b'_el B_open
    by (metis Poset.fun_app Poset.valid_map_cod calculation(2) f_valid_val) 

  moreover have "ext V A (B, (f \<cdot> B) \<star> (b, b')) = comb' (B, (f \<cdot> B) \<star> (b, b')) (A, i \<cdot> A)" using lem
    by (simp add: calculation(3))
  moreover have "... = comb' (comb' (B, b) (B, b')) (A, i \<cdot> A)"
    by (smt (verit) B_open V_valid b'_el b_el comb'_def d_ext_local e_ext_local ext_functorial_id fst_conv global_inclusion_element prod.collapse snd_conv subset_refl sup.orderE) 
  moreover have "... = comb' (comb' (B, b) (A, i \<cdot> A)) (B, b')"
    by (smt (verit) A_open B_le_A B_open V_valid assoc b'_el b_el comb'_def d_ext_local e_ext e_ext_local ext_functorial_id fst_conv global_inclusion_element lem prod.collapse subset_Un_eq sup.orderE units_el) 
  moreover have "... = comb' (comb' (B, b) (A, i \<cdot> A)) (comb' (B, b') (A, i \<cdot> A))"
    by (smt (z3) A_open B_le_A B_open V_valid b'_el b_el comb'_def d_ext_local e_ext e_ext_local ext_functorial_id fst_conv global_inclusion_element lem prod.collapse subset_Un_eq subset_refl sup.orderE units_el) 
  moreover have "... = comb' (ext V A (B, b)) (ext V A (B, b'))"
    using b'_el b_el lem by auto
  moreover have "... = (A, (f \<cdot> A) \<star> (e (ext V A (B, b)), e (ext V A (B, b'))))"
    by (smt (z3) A_open B_le_A B_open V_valid b'_el b_el calculation(3) calculation(4) calculation(5) calculation(6) calculation(7) calculation(8) comb'_def d_ext d_ext_local e_ext_local eq_fst_iff ext_elem ext_functorial_id global_inclusion_element prod.exhaust_sel) 

  ultimately show "e (ext V A (B, (f \<cdot> B) \<star> (b, b'))) = (f \<cdot> A) \<star> (e (ext V A (B, b)), e (ext V A
    (B, b')))"
    by (metis snd_conv) 
qed

lemma up_down_le_down_up : 
  fixes V :: "('A, 'a) OVA" and A B B' C :: "'A Open" and b :: "('A, 'a) Valuation"
  defines "B \<equiv> d b"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)" and B'_open : "B' \<in> opens (space V)" and C_open : "C \<in> opens (space V)"
  and C_le_B : "C \<subseteq> d b" and B_le_A : "d b \<subseteq> A" and C_le_B' : "C \<subseteq> B'" and B'_le_A : "B' \<subseteq> A"
  and b_el : "b \<in> elems V"
shows "local_le V B' (res V B' (ext V A b)) (ext V B' (res V C b))"
proof -
  have "B' = d (res V B' (ext V A b))"
    by (metis A_open B'_le_A B'_open B_le_A V_valid b_el d_ext d_res ext_elem) 
  moreover have "B' = d (ext V B' (res V C b))"
    by (metis B'_open C_le_B C_le_B' C_open V_valid b_el d_ext d_res res_elem)
  moreover have "res V B' (ext V A b) =
    res V B' (res V (B \<union> B') (ext V A (ext V (B \<union> B') b)))" using res_functorial_trans ext_functorial_trans
    by (smt (verit, del_insts) A_open B'_le_A B'_open B_def B_le_A Prealgebra.valid_space V_valid b_el d_elem_is_open d_ext dual_order.eq_iff ext_elem inf_sup_ord(3) le_supI2 sup_least valid_prealgebra valid_union2)
  moreover have "... = res V B' (ext V (B \<union> B') b)" using galois_insertion
    by (metis (no_types, lifting) A_open B'_le_A B'_open B_def B_le_A Prealgebra.valid_space V_valid b_el d_elem_is_open d_ext ext_elem inf_sup_ord(3) sup.idem sup.mono valid_prealgebra valid_union2) 
  moreover have "le V (res V B' (ext V (B \<union> B') b)) (ext V B' (res V C (res V B' (ext V (B \<union> B') b))))" 
    using galois_closure_extensive [where ?V=V and ?B=C and ?a="res V B' (ext V (B \<union> B') b)"] le_eq_local_le [where ?V=V]
    by (smt (verit, best) A_open B'_le_A B'_open B_le_A C_le_B' C_open V_valid b_el calculation(3) calculation(4) d_ext d_res ext_elem res_elem)
  moreover have "ext V B' (res V C (res V B' (ext V (B \<union> B') b))) = ext V B' (res V C (ext V (B \<union> B') b))" using res_functorial_trans
    by (metis (no_types, lifting) B'_open B_def C_le_B' C_open Prealgebra.valid_space V_valid b_el d_elem_is_open d_ext ext_elem sup.cobounded1 sup_commute valid_prealgebra valid_union2)
  moreover have "... = ext V B' (res V C (res V B (ext V (B \<union> B') b)))" using res_functorial_trans
    by (metis (no_types, lifting) B'_open B_def C_le_B C_open Prealgebra.valid_space V_valid b_el d_elem_is_open d_ext ext_elem sup.cobounded1 valid_prealgebra valid_union2) 
  moreover have "... = ext V B' (res V C b)"
    by (metis B'_open B_def Prealgebra.valid_space V_valid b_el d_elem_is_open galois_insertion sup.cobounded1 valid_prealgebra valid_union2) 
  ultimately show ?thesis
    by (metis (no_types, lifting) A_open B'_le_A B'_open B_le_A C_le_B' C_open V_valid b_el d_ext d_res ext_elem local_le res_elem valid_gc_poset valid_prealgebra)
qed

(* [Lemma 3 (1/3), TMCVA] *)
lemma local_mono_ext_comm_imp_laxity:
  fixes V :: "('A, 'a) OVA" and i :: "('A Open, 'a) Function"
  and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and local_mono : "\<And>A a1 a1' a2 a2'. A \<in> opens (space V) \<Longrightarrow> a1 \<in> el (ob V \<cdot> A) \<Longrightarrow> a1' \<in> el (ob V \<cdot> A) \<Longrightarrow> a2 \<in> el (ob V \<cdot> A) \<Longrightarrow> a2' \<in> el (ob V \<cdot> A)
 \<Longrightarrow> Poset.le (ob V \<cdot> A) a1 a1' \<Longrightarrow> Poset.le (ob V \<cdot> A) a2 a2' \<Longrightarrow> Poset.le (ob V \<cdot> A) ((f \<cdot> A) \<star> (a1, a2)) ((f \<cdot> A) \<star> (a1', a2')) "
  and local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, (f \<cdot> B) \<star> (b, b'))) = (f \<cdot> A) \<star> (e (ext V A (B, b)), e (ext V A (B, b')))"
shows "\<And>A B a a'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  a \<in> el (ob V \<cdot> A) \<Longrightarrow> a' \<in> el (ob V \<cdot> A) 
\<Longrightarrow> Poset.le (ob V \<cdot> B) (e (res V B (A, (f \<cdot> A) \<star> (a, a')))) ((f \<cdot> A) \<star> (e (res V B (A, a)), e (res V B (A, a'))))"
proof -
  oops

(* Todo: unknown if this is true *)
lemma laxity2 :
  fixes V :: "('A,'a) OVA" and B B' :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and B_open :"B \<in> opens (space V)"  and B_le_A : "B \<subseteq> d a"
  and B_open :"B' \<in> opens (space V)"  and B'_le_A' : "B' \<subseteq> d a'"
  and a_el : "a \<in> elems V"
  and a'_elem :  "a' \<in> elems V"
shows "le V (res V (B \<union> B') (comb V a a')) (comb V (res V B a) (res V B a'))"
  oops

end
