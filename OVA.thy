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
"le V a b \<equiv> Poset.le (Semigroup.poset (semigroup V)) a b"

abbreviation elems :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> Poset.el (poset V)"

(*
abbreviation le\_V :: "('A, 'a) Valuation \<Rightarrow> ('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" ("\_ \<preceq>\<langle>\_\<rangle> \_") where
"le\_V a V b \<equiv> Poset.le (Semigroup.poset (semigroup V)) a b"
*)

abbreviation (input) local_le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V A a b \<equiv> Poset.le (Prealgebra.ob (prealgebra V) \<cdot> A) (e a) (e b)"

abbreviation space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space V \<equiv> Prealgebra.space (prealgebra V)"

abbreviation (input) local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems V A \<equiv> Poset.el (Prealgebra.ob (prealgebra V) \<cdot> A)"

definition "OVA_res_undefined_bad_args _ _ \<equiv> undefined"

definition res :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"res V B a \<equiv>
  if a \<in> elems V \<and> B \<in> opens (space V) \<and> B \<subseteq> d a
  then (B, Prealgebra.ar (prealgebra V) \<cdot> (Space.make_inc B (d a)) \<star> (e a))
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

abbreviation is_commutative :: "('A, 'a) OVA \<Rightarrow> bool" where
"is_commutative V \<equiv> \<forall> a b . a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> comb V a b = comb V b a"

abbreviation is_strongly_neutral :: "('A, 'a) OVA \<Rightarrow> bool" where
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
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  assumes A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)"
  assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  assumes a_dom : "d a = A" and b_dom : "d b = B"
  assumes a_le_b : "le V a b"
  shows "B \<subseteq> A \<and> local_le V B (res V B a) b"
proof standard
  show "B \<subseteq> A" using assms
    by (metis d_antitone valid_gc_poset valid_prealgebra)
next
  define "i" where "i = Space.make_inc B A"
  define "pr_B" where "pr_B = Prealgebra.ar (prealgebra V) \<cdot> i"
  define "ea_B" where "ea_B = pr_B \<star> (e a)"
  define "FA" where "FA = Prealgebra.ob (prealgebra V) \<cdot> A"
  define "FB" where "FB = Prealgebra.ob (prealgebra V) \<cdot> B"
  have "e a \<in> Poset.el FA"
    by (metis V_valid FA_def a_dom a_el gc_elem_local valid_gc_poset valid_prealgebra)
  moreover have  B_le_A: "B \<subseteq> A"
    using V_valid a_dom a_el a_le_b b_dom b_el d_antitone valid_gc_poset valid_prealgebra
    by metis 
  moreover have "i \<in> inclusions (space V)" using B_le_A V_valid
    by (simp add: A_open B_open i_def) 
  moreover have psh_valid : "Prealgebra.valid (prealgebra V)"
    by (simp add: V_valid valid_prealgebra)
  moreover have "Poset.valid_map pr_B"
    using calculation(3) pr_B_def psh_valid valid_ar by blast
  moreover have "Poset.dom pr_B = FA \<and> Poset.cod pr_B = FB"
    by (simp add: A_open B_le_A B_open FA_def FB_def i_def pr_B_def psh_valid) 
  moreover have "ea_B \<in> Poset.el FB"
    by (metis Poset.fun_app2 calculation(1) calculation(5) calculation(6) ea_B_def)
  moreover have "e b \<in> Poset.el FB"
    by (metis FB_def OVA.valid_welldefined V_valid b_dom b_el gc_elem_local)
  moreover have "Poset.le (poset V) a b"
    using a_le_b by blast
  moreover have "Poset.le FB ea_B (e b)" 
    using psh_valid a_el b_el a_le_b FB_def ea_B_def pr_B_def
i_def V_valid a_dom b_dom valid_gc_poset valid_gc_le_unwrap [where ?Aa=a and ?Bb=b and ?F="prealgebra V"]
    by force   (* or use "apply (rule valid_gc_le_unwrap)" to apply the rule explicitly *)
  show "local_le V B (res V B a) b"
    by (metis B_le_A B_open FB_def \<open>Poset.le FB ea_B (e b)\<close> a_dom a_el ea_B_def res_def i_def pr_B_def snd_eqD)
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

lemma local_inclusion_element : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> e a \<in> el (ob (prealgebra V) \<cdot> d a)"
  by (metis OVA.valid_welldefined gc_elem_local)

lemma global_inclusion_element : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> Poset.el ((Prealgebra.ob (prealgebra V)) \<cdot> A)
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
fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
assumes a_el : "a \<in> elems V" and "d a = A"
and "B \<subseteq> A" and "B \<in> opens (space V)"
defines "a_B \<equiv> res V B a"
shows "a_B \<in> elems V"
proof -
  have "(B, ar (prealgebra V) \<cdot> \<lparr>Inclusion.dom = B, cod = d a\<rparr> \<star> e a) \<in> el (PosetMap.cod (mult (OVA.semigroup V))) "
  proof -
    define "i" where "i = make_inc B (d a)"
    define "f" where "f = ar (prealgebra V) \<cdot> i"
    define "FA" where "FA \<equiv> ((ob (prealgebra V)) \<cdot> A)"
    define "FB" where "FB \<equiv> ((ob (prealgebra V)) \<cdot> B)"
  
    have "Prealgebra.valid (prealgebra V)"
      by (simp add: assms(1) valid_prealgebra)
    moreover have "A \<in> opens (space V)"
      using assms(1) assms(3) d_elem_is_open a_el by blast
    moreover have "Space.valid_inc i"
      by (simp add: assms(3) assms(4) i_def)
    moreover have  "i \<in> inclusions (space V)"
      using assms(3) assms(5) calculation(2) calculation(3) i_def by auto 
    moreover have "f =  ar (prealgebra V) \<cdot> i"
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
      by (metis OVA.valid_welldefined FA_def assms(1) assms(3) a_el gc_elem_local)
    moreover have "a_B \<equiv> res V B a"
      by (simp add: a_B_def)
    moreover have "e (res V B a) = f \<star> (e a)"
      by (metis a_el assms(3) assms(4) assms(5) f_def res_def i_def snd_conv)
    moreover have "f \<star> (e a) \<in> Poset.el FB"
      by (metis (no_types, lifting) FA_def FB_def Inclusion.select_convs(1) Inclusion.select_convs(2) assms(3) calculation(1) calculation(10) calculation(4) f_def i_def image mem_Collect_eq)
    moreover have "f \<star> (e a) = e a_B"
      using a_B_def calculation(12) by force
    moreover have "e a_B \<in>  Poset.el FB"
      by (simp add: a_B_def calculation(12) calculation(13))
    moreover have "a_B \<in> el (poset V)"
      by (metis FB_def assms(1) assms(5) calculation(1) calculation(15) calculation(7) local_elem_gc prod.exhaust_sel valid_gc_poset)
    ultimately show "(B, ar (prealgebra V) \<cdot> make_inc B (d a) \<star> e a) \<in> el (PosetMap.cod
   (mult (OVA.semigroup V)))"
      by (metis (no_types, lifting) comp_eq_dest_lhs i_def prod.exhaust_sel) 
  qed
  show ?thesis
    by (metis (no_types, lifting) \<open>(B, ar (prealgebra V) \<cdot> \<lparr>Inclusion.dom = B, cod = d a\<rparr> \<star> e a) \<in> el (PosetMap.cod (mult (OVA.semigroup V)))\<close> a_B_def a_el assms(3) assms(4) assms(5) comp_apply res_def)
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
   moreover have "Poset.cod (PrealgebraMap.nat (neutral V) \<cdot> A) = (Prealgebra.ob (prealgebra V)) \<cdot>
     A" using Prealgebra.valid_map_def [where ?f="neutral V"]
     by (metis (no_types, lifting) V_valid assms(2) valid_codomain valid_neutral) 
  moreover have "Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)"
    using OVA.valid_welldefined V_valid by blast 
  moreover have "(Prealgebra.ob ( Prealgebra.terminal  (space V))) \<cdot> A = Poset.discrete"
    using Prealgebra.valid_space V_valid assms(2) const_ob valid_prealgebra by blast 
  moreover have "Poset.dom  (PrealgebraMap.nat (neutral V) \<cdot> A) = Poset.discrete" 
using Prealgebra.valid_map_def [where ?f="neutral V"]
  by (metis (no_types, lifting) OVA.valid_welldefined V_valid assms(2) calculation(5))
  moreover have "(PrealgebraMap.nat (neutral V) \<cdot> A \<star> ()) \<in> Poset.el ((Prealgebra.ob (prealgebra V))
    \<cdot> A)"
    by (metis Poset.fun_app2 UNIV_unit UNIV_witness V_valid assms(2) calculation(2) calculation(3) calculation(5) calculation(6) singletonD terminal_value valid_prealgebra valid_space) 
ultimately show ?thesis
  by (meson V_valid assms(2) global_inclusion_element) 
qed

lemma neutral_local_element :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"
  assumes V_valid : "valid V"
  and domain : "A \<in> opens (space V)"
shows " e (neut V A) \<in> Poset.el (Prealgebra.ob (prealgebra V) \<cdot> A)"
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

lemma local_le_imp_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a1 \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> local_le V A (A,a1) (A,a2) \<Longrightarrow> le V (A,a1) (A,a2)"
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

lemma le_eq_local_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a1 \<in> elems V
 \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> d a1 = A \<Longrightarrow> d a2 = A \<Longrightarrow> le V a1 a2 = local_le V A a1 a2"
  by (metis local_le_imp_le local_inclusion_element local_le prod.exhaust_sel valid_gc_poset valid_prealgebra)

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
  define "Fi" where "Fi = (Prealgebra.ar (prealgebra V)) \<cdot> i"
  define "FA" where "FA = (Prealgebra.ob (prealgebra V)) \<cdot> A"
  define "FB" where "FB = (Prealgebra.ob (prealgebra V)) \<cdot> B"
  moreover have "le V a1 a2 \<longrightarrow> Poset.le FA (e a1) (e a2)"
    by (metis A_def FA_def V_valid assms(4) assms(5) assms(6) local_le valid_gc_poset valid_prealgebra) 
  moreover have "local_le V A a1 a2" using assms
    using FA_def calculation(2) by fastforce
  moreover have "i \<in> inclusions (space V) \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (no_types, lifting) A_def CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) V_valid assms(2) assms(3) assms(5) d_elem_is_open i_def)
    moreover have "local_le V B (res V B a1)  (res V B a1)"
      by (metis V_valid assms(2) assms(3) assms(5) d_res res_elem local_inclusion_element valid_ob valid_prealgebra valid_reflexivity) 
    moreover have "d (res V B a1) = B"
      using V_valid assms(2) assms(3) assms(5) by auto
    moreover have "d (res V B a2) = B"
      using V_valid assms(2) assms(3) assms(4) assms(6) by auto 
    ultimately show ?thesis 
      using le_eq_local_le [where ?V=V and ?A=B and ?a1.0="res V B a1" and
        ?a2.0="res V B a2"] assms
        by (metis (no_types, lifting) A_def res_def res_elem i_def local_inclusion_element mem_Collect_eq res_monotone snd_conv valid_prealgebra) 
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
  and "FB \<equiv> Prealgebra.ob (prealgebra V) \<cdot> B"
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
  defines "FA \<equiv> Prealgebra.ob (prealgebra V) \<cdot> A"
  assumes V_valid : "valid V"
  and "d b \<subseteq> A" and "A \<in> opens (space V)"
  and "b \<in> elems V"
shows " e (ext V A b) \<in> Poset.el FA"
  by (metis FA_def V_valid assms(3) assms(4) assms(5) d_ext ext_elem local_inclusion_element) 

(* Paper results *)

(* [Remark 2 (1/2), CVA] *)
lemma res_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "C \<subseteq> B" and "B \<subseteq> A"
  and "d a = A"
  and "a \<in> elems V"
shows "res V C a = (res V C (res V B a))"
proof -
  define "F1" where "F1 = Prealgebra.ar (prealgebra V)"
  define "i_BA" where "i_BA = Space.make_inc B A"
  define "i_CB" where "i_CB = Space.make_inc C B"
  define "i_CA" where "i_CA = Space.make_inc C A"
  define "f" where "f = F1 \<cdot> i_BA"
  define "g" where "g = F1 \<cdot> i_CB"
  define "h" where "h = F1 \<cdot> i_CA"
  have "res V C a = (C, (F1 \<cdot> i_CA) \<star> (e a))"
    by (smt (verit, ccfv_SIG) F1_def assms(4) assms(5) assms(6) assms(7) assms(8) res_def i_CA_def order.trans)
  moreover have "res V B a = (B, f \<star> (e a))"
    by (metis F1_def assms(3) assms(6) assms(7) assms(8) f_def res_def i_BA_def)
  moreover have "res V C (res V B a) = (C, g  \<star> (f \<star> (e a)))"
    by (metis (no_types, lifting) F1_def V_valid assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(2) fst_eqD g_def res_def res_elem i_CB_def snd_eqD) 
  moreover have "Prealgebra.valid (prealgebra V)"
    by (meson OVA.valid_welldefined V_valid)
  moreover have "valid_inc i_CB"
    by (simp add: assms(5) i_CB_def) 
  moreover have "i_CB \<in> inclusions (space V)"
    using assms(3) assms(4) calculation(5) i_CB_def by force 
  moreover have "valid_inc i_BA"
    by (simp add: assms(6) i_BA_def) 
    moreover have "i_BA \<in> inclusions (space V)"
      using assms(2) assms(3) calculation(7) i_BA_def by auto 
moreover have "valid_inc i_CA"
  using assms(5) assms(6) i_CA_def by auto 
  moreover have "i_CA = i_BA \<propto> i_CB" using Space.compose_inc_def
    by (simp add: i_BA_def i_CA_def i_CB_def) 
  moreover have "Poset.valid_map f \<and> Poset.valid_map g \<and> Poset.valid_map h"
    by (metis (no_types, lifting) F1_def Inclusion.select_convs(1) Inclusion.select_convs(2) Prealgebra.valid_welldefined assms(2) assms(3) assms(4) assms(5) assms(6) calculation(4) f_def g_def h_def i_BA_def i_CA_def i_CB_def mem_Collect_eq order.trans) 
  moreover have "Space.cod i_BA = A \<and> Space.dom i_BA = B "
    by (simp add: i_BA_def) 
  moreover have "Space.cod i_CB = B \<and> Space.dom i_CB = C "
    by (simp add: i_CB_def) 
  moreover have "Space.cod i_CA = A \<and> Space.dom i_CA = C "
    by (simp add: i_CA_def) 
  moreover have "Poset.dom f = Prealgebra.ob (prealgebra V) \<cdot> A"
    by (simp add: F1_def assms(2) assms(3) assms(6) calculation(12) calculation(4) f_def) 
    moreover have "Poset.cod f  = Prealgebra.ob (prealgebra V) \<cdot> B \<and> Poset.dom g  = Prealgebra.ob
      (prealgebra V) \<cdot> B"
      by (simp add: F1_def assms(2) assms(3) assms(4) assms(5) assms(6) calculation(12) calculation(13) calculation(4) f_def g_def)  
    moreover have " (F1 \<cdot> i_CB) \<star> ((F1 \<cdot> i_BA) \<star> (e a)) =  (F1 \<cdot> i_CA) \<star> (e a)"  using Poset.compose_app_assoc
      by (metis (no_types, lifting) F1_def V_valid assms(2) assms(3) assms(4) assms(7) assms(8) calculation(10) calculation(11) calculation(12) calculation(13) calculation(4) calculation(5) calculation(7) f_def g_def local_inclusion_element mem_Collect_eq res_cod valid_composition valid_dom)
  ultimately show ?thesis
    by (metis f_def g_def)
qed

(* [Remark 2 (2/2), CVA] *)
lemma stability:
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid: "valid V"
  assumes B_le_A : "B \<subseteq> A" and B_open : "B \<in> opens (space V)" and A_open : "A \<in> opens (space V)"
  defines \<epsilon>A_def: "\<epsilon>A \<equiv> neut V A"
  defines \<epsilon>B_def: "\<epsilon>B \<equiv> neut V B"
  defines \<epsilon>A_B_def: "\<epsilon>A_B \<equiv> res V B \<epsilon>A"
  shows "\<epsilon>A_B = \<epsilon>B"
proof -
  define i where "i \<equiv> Space.make_inc B A"
  define "f" where "f = nat (neutral V)"
  define "one" where "one \<equiv> dom (neutral V)"
  moreover have "\<epsilon>A_B = res V B \<epsilon>A"
    by (simp add: \<epsilon>A_B_def)
  moreover have "Space.cod i = A \<and> Space.dom i = B"
    by (simp add: i_def)
  moreover have "i \<in> inclusions (space V)"
    using A_open B_le_A B_open calculation(3) by force
  moreover have "valid_map (neutral V)"
    using V_valid valid_neutral by blast 
  moreover have "Prealgebra.valid one"
    by (simp add: Prealgebra.valid_map_dom calculation(5) one_def)  
  moreover have v1: "Poset.valid_map (Prealgebra.ar one \<cdot> i)" using calculation assms Prealgebra.valid_ar
    [where ?F="prealgebra V" and ?i=i]
    apply clarsimp
     by (metis (no_types, lifting) OVA.valid_welldefined Poset.ident_valid Prealgebra.valid_welldefined Space.valid_def const_ar mem_Collect_eq terminal_ob)
  moreover have v2: "Poset.valid_map (f \<cdot> B)"
      by (smt (verit, best) B_open OVA.valid_welldefined Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def Prealgebra.valid_map_welldefined V_valid f_def)
  moreover have "Prealgebra.valid one"
      by (metis OVA.valid_welldefined Prealgebra.valid_map_welldefined one_def V_valid)
  moreover have "(Prealgebra.ar one \<cdot> i ) \<star> ()  = ()"
    by simp
  moreover have "() \<in> Poset.el (Poset.dom  (ar one \<cdot> i))" using Prealgebra.terminal_value
    using A_open B_le_A B_open V_valid calculation(3) one_def valid_domain valid_prealgebra valid_space by fastforce 
  moreover have "((f \<cdot> B) \<diamondop> (ar one \<cdot> i)) \<star> () = (f \<cdot> B) \<star> ((ar one \<cdot> i)) \<star> ()"
    using OVA.valid_welldefined Prealgebra.Prealgebra.select_convs(1) Prealgebra.valid_map_welldefined
    assms calculation res_cod compose_app_assoc f_def  
    by (metis (no_types, lifting) Prealgebra.const_def mem_Collect_eq)  
  moreover have "((Prealgebra.ar (prealgebra V) \<cdot> i) \<diamondop> (f \<cdot> A)) \<star> ()=  e \<epsilon>B"
    using  assms calculation f_def one_def snd_conv valid_map_naturality
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def mem_Collect_eq valid_codomain valid_domain) 
  moreover have "e \<epsilon>A=   (f \<cdot> A) \<star> ()"
    by (simp add: \<epsilon>A_def f_def)
  ultimately show ?thesis
    using Prealgebra.valid_map_welldefined Prealgebra.valid_welldefined 
      assms compose_app_assoc eq_fst_iff f_def res_def i_def neutral_is_element singletonI sndI terminal_value valid_codomain valid_domain
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def mem_Collect_eq) 
qed

(* [Remark 3 (1/3), CVA] *)
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
  ultimately show ?thesis using le_eq_local_le [where ?V=V and ?a1.0=b1 and ?a2.0=b2]
    by (metis (full_types) V_valid a1'_d a1'_el a1_d a1_el a2'_d a2'_el a2_d a2_el b1_def b2_def d_elem_is_open d_neut neutral_is_element valid_domain_law valid_neutral_law_right)
qed

(* [Remark 3 (2/3), CVA] *)
lemma id_le_res :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  B_open : "B \<in> opens (space V)"  and B_le_A : "B \<subseteq> d a"
  and  a_el : "a \<in> elems V"
shows " le V a (res V B a)"
proof -
  define "A" where "A = d a"
  define "i" where "i = Space.make_inc B (d a)"
  define "Fi" where "Fi = Prealgebra.ar (prealgebra V) \<cdot> i"
  define "FA" where "FA = Prealgebra.ob (prealgebra V) \<cdot> A"
  define "FB" where "FB = Prealgebra.ob (prealgebra V) \<cdot> B"
  define "a_B" where "a_B =  Fi \<star> (e a)"
  have "i \<in> inclusions (space V)"
    using B_le_A B_open V_valid a_el d_elem_is_open i_def by fastforce 
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
  ultimately show ?thesis  using assms le_eq_local_le [where ?V=V and ?A="d b" and ?a1.0=a_B and
        ?a2.0=b ]
    by (smt (verit) a_B_def d_res id_le_res valid_poset valid_semigroup valid_transitivity) 
qed

(* [Theorem 1 (1/2), CVA] *)
theorem res_ext_adjunction :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  and B_le_A : "d b \<subseteq> d a"
shows "local_le V (d b) (res V (d b) a) b = local_le V (d a) a (ext V (d a) b)"
proof (rule iffI)
  assume "local_le V (d b) (res V (d b) a) b"
  define "\<epsilon>A" where "\<epsilon>A \<equiv> neut V (d a)"
  define "a_B" where "a_B \<equiv> res V (d b) a"
  have "local_le V (d a) (comb V \<epsilon>A a) (comb V \<epsilon>A a_B)"
    by (smt (verit) B_le_A OVA.valid_welldefined V_valid \<epsilon>A_def a_B_def a_el b_el comb_is_element d_elem_is_open d_res fst_conv id_le_res local_le neutral_is_element res_elem sup.absorb_iff1 valid_domain_law valid_monotone valid_neutral_law_left valid_poset valid_reflexivity) 
  moreover have "local_le V (d a) (comb V \<epsilon>A a_B) (comb V \<epsilon>A b)" using assms a_B_def valid_comb_monotone [where ?V=V] le_eq_local_le [where ?V=V]
    by (smt (verit) Poset.valid_def \<epsilon>A_def \<open>Poset.le (Prealgebra.ob (prealgebra V) \<cdot> d b) (e (res V (d b) a)) (e b)\<close> comb_is_element d_elem_is_open d_res fst_eqD neutral_is_element res_elem sup.order_iff valid_domain_law valid_poset valid_semigroup)
  moreover have "comb V \<epsilon>A b = ext V (d a) b" using \<epsilon>A_def ext_def [where ?V=V and ?A="d a" and ?b=b]
    by (metis B_le_A V_valid a_el b_el d_elem_is_open) 
  ultimately show "local_le V (d a) a (ext V (d a) b)"
    by (smt (z3) B_le_A V_valid \<epsilon>A_def a_B_def a_el b_el comb_is_element d_elem_is_open d_ext d_res local_inclusion_element neutral_is_element res_elem valid_domain_law valid_neutral_law_left valid_ob valid_prealgebra valid_transitivity)
next
  assume "local_le V (d a) a (ext V (d a) b)"
  define "\<epsilon>A" where "\<epsilon>A \<equiv> neut V (d a)"
  define "a_B" where "a_B \<equiv> res V (d b) a"
  have "local_le V (d b) a_B (res V (d b) (ext V (d a) b))" using assms a_B_def res_monotone_local [where
          ?V=V and ?B="d b" and ?a1.0=a and ?a2.0="comb V \<epsilon>A b"] le_eq_local_le [where ?V=V]
    by (smt (verit, best) OVA.res_monotone \<open>Poset.le (Prealgebra.ob (prealgebra V) \<cdot> d a) (e a) (e (ext V (d a) b))\<close> d_elem_is_open d_ext d_res ext_elem res_elem)
  moreover have "ext V (d a) b = comb V \<epsilon>A b" using ext_def [where ?V=V]
    by (metis B_le_A V_valid \<epsilon>A_def a_el b_el d_elem_is_open) 
  moreover have "(res V (d b) (ext V (d a) b)) = comb V (res V (d a \<inter> d b) \<epsilon>A) b"  using valid_comb_law_right
    by (metis V_valid \<epsilon>A_def a_el b_el calculation(2) d_elem_is_open fst_eqD neutral_is_element)
  moreover have "comb V (res V (d a \<inter> d b) \<epsilon>A) b = comb V (neut V (d b)) b"
    by (metis B_le_A Int_absorb1 V_valid \<epsilon>A_def a_el b_el d_elem_is_open stability) 
  ultimately show "local_le V (d b) (res V (d b) a) b"
    by (metis V_valid a_B_def b_el valid_neutral_law_left)
qed

(* [Remark 3 (3/3), CVA] *)
lemma laxity :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  A_open : "A \<in> opens (space V)" and B_open :"B \<in> opens (space V)"  and B_le_A : "B \<subseteq> A"
  and  a_el : "a \<in> elems V" and a_dom : "d a = A"
  and a'_elem :  "a' \<in> elems V" and a_dom' : "d a' = A"
shows "local_le V B (res V B (comb V a a')) (comb V (res V B a) (res V B a'))"
proof -
   define "m1" where "m1 = comb V a a'"
   define "m2" where "m2 = comb V (res V B a) (res V B a')"
   define "m1_B" where "m1_B = res V B m1"
   have "le V a (res V B a)"
     using A_open B_le_A B_open a_el a_dom  id_le_res  V_valid by blast
   moreover have "le V a' (res V B a')"
     using A_open B_le_A B_open a'_elem a_dom' id_le_res V_valid by blast
   moreover have global_le : "le V m1 m2"
     by (smt (verit) B_le_A B_open V_valid a'_elem a_dom a_dom' a_el calculation(1) calculation(2) res_elem m1_def m2_def valid_comb_monotone)
   moreover have d_m1 : "d m1 = A"
     using V_valid a'_elem a_dom a_dom' a_el m1_def by auto 
   moreover have d_m1_B : "d m1_B = B"
     using B_le_A B_open V_valid a'_elem a_el comb_is_element d_res d_m1 m1_B_def m1_def by blast
   moreover have d_m2 : "d m2 = B"
     by (metis (no_types, lifting) B_le_A B_open Orderings.order_eq_iff Un_absorb2 V_valid a'_elem a_dom a_dom' a_el d_res res_elem m2_def valid_domain_law) 
   moreover have pm1_el : "m1_B \<in> elems V"
     using B_le_A B_open V_valid a'_elem a_el comb_is_element d_m1 res_elem m1_B_def m1_def by blast
   moreover have m2_el : "m2 \<in> elems V"
     by (metis B_le_A B_open V_valid a'_elem a_dom a_dom' a_el comb_is_element res_elem m2_def)
   moreover have "valid V" by fact
   moreover have m1_el : "m1 \<in> elems V"
     using V_valid a'_elem a_el comb_is_element m1_def by blast
   moreover have "local_le V B m1_B m2" using V_valid A_open B_open m1_el m2_el d_m1 d_m2 m1_B_def  global_le valid_le
       [where ?V = V and ?A = A and ?B = B and ?a = m1 and ?b = m2]
     by fastforce
  ultimately show ?thesis
    using m1_B_def m1_def m2_def by auto
qed

(* [Corollary 1 (1/2), CVA] *)
corollary strongly_neutral_covariance :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and B_le_A : "B \<subseteq> A" and B_open : "B \<in> opens (space V)" and A_open : "A \<in> opens (space V)"
  and strongly_neutral: "is_strongly_neutral V"
shows "ext V A (neut V B) = neut V A "  
  by (metis (no_types, lifting) V_valid assms fst_eqD ext_def neutral_is_element strongly_neutral sup.absorb_iff1)

(* [Corollary 1 (2/2), CVA] *)
corollary strongly_neutral_monoid :
  fixes V :: "('A,'a) OVA" and a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V"
  and strongly_neutral: "is_strongly_neutral V"
defines "identity  \<equiv> neut V {}"
shows "comb V identity a = a \<and> comb V a identity = a "
proof standard
  define "\<epsilon>A" where "\<epsilon>A = neut V (d a)"
  have "a = comb V \<epsilon>A a "
    by (smt (verit, best) V_valid \<epsilon>A_def a_el d_elem_is_open valid_neutral_law_left)
  moreover have "comb V identity a = comb V identity (comb V \<epsilon>A a)"
    by (smt (verit, best) V_valid \<epsilon>A_def a_el d_elem_is_open valid_neutral_law_left)
  moreover have "... = comb V (comb V identity \<epsilon>A) a" using valid_comb_associative
    by (metis (no_types, opaque_lifting) OVA.valid_welldefined Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def neutral_is_element) 
  moreover have "... = comb V \<epsilon>A a"
    by (metis (no_types, lifting) Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def strongly_neutral sup_bot_left valid_prealgebra)
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
    by (metis (no_types, lifting) Prealgebra.valid_welldefined Space.valid_def V_valid \<epsilon>A_def a_el d_elem_is_open identity_def strongly_neutral sup_bot.right_neutral valid_prealgebra)
  moreover have "... = a"
    using calculation(1) by presburger
  ultimately show "comb V a identity = a"
    by presburger
qed

(* [Corollary 2 (1/3), CVA] *)
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

(* [Corollary 2 (2/3), CVA] *)
corollary galois_closure_extensive :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "a \<in> elems V" 
  and "B \<subseteq> d a" and "B \<in> opens (space V)"
  shows "local_le V (d a) a (ext V (d a) (res V B a))"
proof -
  have "local_le V (d a) a a"
    by (meson V_valid assms(2) d_elem_is_open local_inclusion_element valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V B (res V B a) (res V B a)"
    by (meson V_valid assms(2) assms(3) assms(4) d_elem_is_open e_res valid_ob valid_prealgebra valid_reflexivity)
  moreover have "res V B a \<in> elems V"
    using V_valid assms(2) assms(3) assms(4) res_elem by blast
  moreover have "d (res V B a) = B"
    using assms(2) assms(3) assms(4) by auto
  ultimately show ?thesis using assms res_ext_adjunction [where ?V=V and ?a=a and ?b="res V B a" ]
    by presburger
qed

lemma ext_functorial_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B C:: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> ext V"
  and "pr \<equiv> res V"
  shows "le V (ex A c) (ex A (ex B c))"
proof -
  have "local_le V C c c"
    by (metis V_valid assms(4) assms(7) assms(8) local_inclusion_element valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V C (pr C (ex A c)) c"
    by (smt (verit, best) V_valid assms(2) assms(4) assms(5) assms(6) assms(7) assms(8) calculation dual_order.trans ex_def galois_insertion pr_def)
  moreover have "pr C (pr B (ex A c)) = pr C (ex A c)"
    by (smt (verit, del_insts) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_ext dual_order.trans ex_def ext_elem res_functorial d_elem_is_open pr_def V_valid)
  moreover have "local_le V C  (pr C (pr B (ex A c))) c"
    by (simp add: calculation(2) calculation(3))
  moreover have "local_le V B (pr B (ex A c)) (ex B c)"
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_ext d_res ex_def ext_elem res_elem order_trans pr_def res_ext_adjunction)
  moreover have "local_le V A (ex A c) (ex A (ex B c))"
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(5) d_ext dual_order.trans ex_def ext_elem pr_def res_ext_adjunction)
    ultimately show ?thesis
      by (smt (verit) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_ext dual_order.refl dual_order.trans elem_le_wrap ex_def galois_insertion ext_elem res_functorial pr_def)
qed

lemma ext_functorial_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> ext V"
  and "pr \<equiv> res V"
  shows "le V (ex A (ex B c)) (ex A c)"
proof -
  have "local_le V A (ex A (ex B c)) (ex A (ex B c))"
    by (metis V_valid assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_ext e_ext ex_def ext_elem valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V B (pr B (ex A (ex B c))) (ex B c)"
    by (metis V_valid assms(2) assms(3)  assms(5) assms(6) assms(7) assms(8) d_ext e_ext ex_def galois_insertion ext_elem pr_def valid_ob valid_prealgebra valid_reflexivity)
    moreover have "local_le V C (pr C (pr B (ex A (ex B c)))) c"
      by (metis (no_types, lifting) V_valid assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_ext ex_def galois_insertion ext_elem le_eq_local_le d_elem_is_open pr_def valid_poset valid_reflexivity valid_semigroup)
moreover have "local_le V C (pr C (ex A (ex B c))) c"
  by (metis (full_types) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) calculation(3) d_ext ex_def ext_elem res_functorial d_elem_is_open pr_def V_valid)
  moreover have "local_le V A (ex A (ex B c)) (ex A c)" using res_ext_adjunction
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_ext dual_order.trans ex_def ext_elem pr_def)
  ultimately show ?thesis
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_ext dual_order.trans ex_def ext_elem le_eq_local_le)
qed

(* [Theorem 1 (2/2), CVA] *)
theorem ext_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> ext V"
  shows "ex A (ex B c) = ex A c"
proof -
  have "le V (ex A (ex B c)) (ex A c)"
    using assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def ext_functorial_rhs_imp_lhs V_valid by blast
  moreover have "le V (ex A c)  (ex A (ex B c))"
    using assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def ext_functorial_lhs_imp_rhs V_valid by blast
  ultimately show ?thesis
    by (smt (z3) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_ext dual_order.trans ex_def ext_elem valid_antisymmetry valid_poset valid_semigroup)
qed

(* [Corollary 2 (3/3), CVA] *)
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
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" and "C \<in> opens (space V)"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
shows "res V B (ext V A c) = ext V B c"
  by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_ext ext_functorial galois_insertion ext_elem)

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
  moreover have "ext V A c = ext V A (ext V B c)" using ext_functorial
    by (metis B_leq_A C_le_B c_elem calculation(1) dom_c V_valid)
  moreover have "local_le V A a (ext V A (ext V B c))"
    using calculation(3) calculation(4) by auto
  ultimately show ?thesis using res_ext_adjunction le_a_C_c
    by (smt (verit, best) B_leq_A C_le_B V_valid a_el c_elem d_ext dom_A dom_c ext_elem)
qed

(* [Corollary 3, CVA] *)
corollary locally_complete_imp_complete :
  fixes V :: "('A,'a) OVA"
  defines "F A \<equiv> (Prealgebra.ob (prealgebra V)) \<cdot> A"
  and "pr \<equiv> res V" and "ex \<equiv> ext V"
  assumes V_valid: "valid V"
  assumes local_completeness: "\<And>A . A \<in> opens (space V) \<Longrightarrow> Poset.is_complete (F A)"
  shows "Poset.is_complete (poset V)"
proof standard
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
      using calculation(1) calculation(2) local_completeness some_e_U_def by fastforce

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
          using \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> local_completeness by blast
        moreover have "Poset.is_complete (F (d_U))"
          using \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> local_completeness by blast 
        moreover have "Poset.is_inf (F (d_U)) ex_U e_U" using ex_U_def local_completeness
          by (metis \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> \<open>some_e_U = Some e_U\<close> calculation(3) some_e_U_def some_inf_is_inf)
        moreover have "local_le V (d_U) i (ex d_U u)"
          by (smt (verit, del_insts) F_def calculation(1) calculation(5) comp_apply ex_U_def i_def image_iff is_inf_def snd_conv)
        moreover have "local_le V (d u) (pr (d u) i) u"
          by (smt (verit) U V_valid \<open>i \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(1) calculation(2) calculation(6) d_ext d_res elem_le_wrap ex_def fst_eqD galois_insertion ext_elem res_elem res_monotone i_def in_mono d_elem_is_open local_le pr_def subset_Un_eq sup.cobounded2 up_and_down valid_gc_poset valid_prealgebra)
        moreover have i_is_lb: "le V i u"
          by (smt (verit) U V_valid \<open>i \<in> el (poset V)\<close> calculation(1) calculation(2) calculation(7) elem_le_wrap fst_eqD i_def in_mono pr_def)
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
              = V and ?A = "d z" and ?a = z]
          using U \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(1) d_elem_is_open pr_def by blast
        moreover have "\<forall> v \<in> U . Poset.le (F (d v)) (e (pr (d v) z)) (e v)"
          using F_def calculation(6) by presburger
        define "z_U" where "z_U = res V d_U z"
        moreover have "\<forall> v \<in> U . pr d_U (ex (d z) v) = ex d_U v" using up_and_down
          by (smt (verit, ccfv_threshold) UN_subset_iff V_valid \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> calculation(3) calculation(4) calculation(5) d_U_def ex_def lb2 pr_def subset_eq)
        moreover have "Poset.valid (F d_U)"
          by (simp add: \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> local_completeness)
        moreover have "d_U \<in> opens (space V)"
          using \<open>d_U \<in> opens (Prealgebra.space (prealgebra V))\<close> by blast
        moreover have "d_U \<subseteq> d z"
          by (simp add: UN_subset_iff d_U_def lb2)
        moreover have "z_U \<in> elems V" using z_U_def res_elem [where ?V=V and ?B=d_U and ?a=z and
              ?A="d z"] calculation
          using V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> by fastforce
        moreover have "e z_U \<in> Poset.el (F d_U)"
          by (metis V_valid F_def \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(10) calculation(11) calculation(3) e_res z_U_def)
        moreover have "\<forall> v \<in> U . local_le V d_U z_U (ex d_U v)" using z_U_def calculation
         intermediate_extension [where ?V = V and ?B = d_U and ?a = z]
          by (metis V_valid \<open>\<forall>u\<in>U. Poset.le (poset V) i u\<close> \<open>i \<in> Semigroup.elems (OVA.semigroup V)\<close> \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> d_antitone ex_def fst_conv i_def pr_def valid_gc_poset valid_prealgebra)
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
            using F_def \<open>\<forall>v\<in>U. Poset.le (ob (prealgebra V) \<cdot> d_U) (e z_U) (e (ex d_U v))\<close> z_U_def by force
          moreover have "\<forall> u \<in> ex_U. Poset.le (F d_U) (e (res V d_U z)) u"  using z_U_is_lb
            by (simp add: ex_U_def)
          moreover have "Poset.le_rel (F d_U) \<subseteq> le_rel (F d_U)"
            by simp
          ultimately show ?thesis
            by (simp add: inf_is_glb)
        qed
        moreover have "Poset.le (poset V) z i"
          by (metis V_valid F_def \<open>d i \<subseteq> d z\<close> \<open>i \<in> Semigroup.elems (OVA.semigroup V)\<close> \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(18) elem_le_wrap fst_conv i_def snd_conv)
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

end
