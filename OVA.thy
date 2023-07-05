section \<open> OVA.thy \<close>

theory OVA
  imports Main Poset Grothendieck Semigroup Prealgebra
begin

type_synonym ('A, 'a) Valuation = "('A set \<times> 'a)"

(* OVA type (ordered valuation algebra *)

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

abbreviation gle :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle V a b \<equiv> Poset.le (Semigroup.poset (semigroup V)) a b"

abbreviation elems :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> Poset.el (poset V)"

(*
abbreviation gle\_V :: "('A, 'a) Valuation \<Rightarrow> ('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" ("\_ \<preceq>\<langle>\_\<rangle> \_") where
"gle\_V a V b \<equiv> Poset.le (Semigroup.poset (semigroup V)) a b"
*)

abbreviation (input) local_le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V A a b \<equiv> Poset.le (Prealgebra.ob (prealgebra V) \<cdot> A) (e a) (e b)"

abbreviation (input) space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space V \<equiv> Prealgebra.space (prealgebra V)"

abbreviation (input) opens :: "('A,'a) OVA \<Rightarrow> 'A Open set" where
"opens V \<equiv> Space.opens (space V)"

abbreviation (input) inclusions :: "('A,'a) OVA \<Rightarrow> 'A Inclusion set" where
"inclusions V \<equiv> Space.inclusions (space V)"

abbreviation (input) local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems V A \<equiv> Poset.el (Prealgebra.ob (prealgebra V) \<cdot> A)"

definition "OVA_grpj_undefined_bad_args _ _ \<equiv> undefined"

definition gres :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gres V B a \<equiv> let i = Space.make_inc B (d a) in
  if a \<in> elems V \<and> B \<in> opens V \<and> B \<subseteq> d a
  then (B, Prealgebra.ar (prealgebra V) \<cdot> i \<star> (e a))
  else OVA_grpj_undefined_bad_args B a"

definition "OVA_gext_undefined_bad_args _ _ \<equiv> undefined"

definition gext :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gext V A b \<equiv>
  if b \<in> elems V \<and> A \<in> opens V \<and> d b \<subseteq> A
  then comb V (neut V A) b
  else OVA_gext_undefined_bad_args A b"

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
        neutral_law_left = \<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems V \<longrightarrow> comb V (neut V (d a)) a = a;
        neutral_law_right = \<forall>A a. A \<in> opens V \<and> a \<in> elems V \<longrightarrow> comb V a (neut V (d a)) = a;
        comb_law_left = \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             gres V (d a) (comb V a b) = comb V a (gres V (d a \<inter> d b) b);
        comb_law_right = \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             gres V (d b) (comb V a b) = comb V (gres V (d a \<inter> d b) a) b
    in
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"

(* Validity *)

lemma validI :
  fixes V :: "('A,'a) OVA"
  assumes welldefined : "Prealgebra.valid (prealgebra V)
                      \<and> Semigroup.valid (semigroup V)
                      \<and> Prealgebra.valid_map (neutral V)
                      \<and> Prealgebra.cod (neutral V) = prealgebra V
                      \<and> Prealgebra.dom (neutral V) = Prealgebra.terminal (space V)
                      \<and> Semigroup.poset (semigroup V) = gc (prealgebra V)"
  assumes domain_law : "\<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> d (comb V a b) = d a \<union> d b"
  assumes neutral_law_left : "\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems V \<longrightarrow> comb V (neut V (d a)) a = a"
  assumes neutral_law_right: "\<forall>A a. A \<in> opens V \<and> a \<in> elems V \<longrightarrow> comb V a (neut V (d a)) = a"
  assumes comb_law_left : "\<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             gres V (d a) (comb V a b) = comb V a (gres V (d a \<inter> d b) b)"
  assumes comb_law_right : "\<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow>
             gres V (d b) (comb V a b) = comb V (gres V (d a \<inter> d b) a) b"
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

lemma valid_gle :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  assumes A_open : "A \<in> opens V" and B_open : "B \<in> opens V"
  assumes a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  assumes a_dom : "d a = A" and b_dom : "d b = B"
  assumes a_le_b : "gle V a b"
  shows "B \<subseteq> A \<and> local_le V B (gres V B a) b"
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
    by (metis V_valid FA_def a_dom a_elem gc_elem_local valid_gc_poset valid_prealgebra)
  moreover have  B_le_A: "B \<subseteq> A"
    using V_valid a_dom a_elem a_le_b b_dom b_elem d_antitone valid_gc_poset valid_prealgebra
    by metis 
  moreover have "i \<in> inclusions V" using B_le_A V_valid
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
    by (metis FB_def OVA.valid_welldefined V_valid b_dom b_elem gc_elem_local)
  moreover have "le (poset V) a b"
    using a_le_b by blast
  moreover have "le FB ea_B (e b)" 
    using psh_valid a_elem b_elem a_le_b FB_def ea_B_def pr_B_def
i_def V_valid a_dom b_dom valid_gc_poset valid_gc_le_unwrap [where ?Aa = a and ?Bb = b and ?F = "prealgebra V"]
    by force   (* or use "apply (rule valid_gc_le_unwrap)" to apply the rule explicitly *)
  show "local_le V B (gres V B a) b"
    by (metis B_le_A B_open FB_def \<open>le FB ea_B (e b)\<close> a_dom a_elem ea_B_def gres_def i_def pr_B_def snd_eqD)
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
      gres V (d a) (comb V a b) = comb V a (gres V (d a \<inter> d b) b)"
  unfolding valid_def
  by meson

lemma valid_comb_law_right : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow>
      gres V (d b) (comb V a b) = comb V (gres V (d a \<inter> d b) a) b"
  unfolding valid_def
  by meson

lemma valid_comb_associative : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow>
      comb V (comb V a b) c = comb V a (comb V b c)"
  unfolding valid_def
  by (meson valid_associative)

lemma valid_comb_monotone : "valid V \<Longrightarrow>  a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> b1 \<in> elems V \<Longrightarrow> b2 \<in> elems V
\<Longrightarrow> gle V a1 a2 \<Longrightarrow> gle V b1 b2
\<Longrightarrow> gle V (comb V a1 b1) (comb V a2 b2)"
  by (smt (verit) valid_monotone valid_semigroup)

lemma local_inclusion_element : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> e a \<in> el (ob (prealgebra V) \<cdot> d a)"
  by (metis OVA.valid_welldefined gc_elem_local)

lemma global_inclusion_element : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a \<in> Poset.el ((Prealgebra.ob (prealgebra V)) \<cdot> A)
\<Longrightarrow>  (A, a) \<in> elems V"
  by (metis local_elem_gc valid_gc_poset valid_prealgebra) 

lemma d_elem_is_open : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> d a \<in> opens V"
  by (metis local_dom valid_gc_poset valid_prealgebra)

lemma d_neut [simp] : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> d (neut V A) = A"
  by simp

lemma d_comb [simp] : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow> b \<in> elems V  \<Longrightarrow> d (comb V a b) = d a \<union> d b"
by (simp add: valid_domain_law)

lemma d_gres [simp] : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> B \<in> opens V \<Longrightarrow> B \<subseteq> d a \<Longrightarrow> d (gres V B a) = B"
  by (simp add: gres_def)

lemma comb_is_element :
fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
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
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.product_def SigmaI a_elem b_elem)
  ultimately show ?thesis
    using Poset.fun_app2 by fastforce 
qed

lemma gres_elem :
fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
and a_elem : "a \<in> elems V" and "d a = A"
and "B \<subseteq> A" and "B \<in> opens V"
defines "a_B \<equiv> gres V B a"
shows "a_B \<in> elems V"
  unfolding a_B_def gres_def
  apply standard
   apply auto
  using assms(5) apply auto[1]
  using a_elem apply fastforce
  using assms(3) assms(4) apply blast
proof -
  define "i" where "i = make_inc B (d a)"
  define "f" where "f = ar (prealgebra V) \<cdot> i"
  define "FA" where "FA \<equiv> ((ob (prealgebra V)) \<cdot> A)"
  define "FB" where "FB \<equiv> ((ob (prealgebra V)) \<cdot> B)"

  have "Prealgebra.valid (prealgebra V)"
    by (simp add: assms(1) valid_prealgebra)
  moreover have "A \<in> opens V"
    using assms(1) assms(3) d_elem_is_open a_elem by blast
  moreover have "Space.valid_inc i"
    by (simp add: assms(3) assms(4) i_def)
  moreover have  "i \<in> inclusions V"
    using assms(3) assms(5) calculation(2) calculation(3) i_def by auto 
  moreover have "f =  ar (prealgebra V) \<cdot> i"
    by (simp add: f_def)
  moreover have "Poset.valid_map f" using Prealgebra.valid_ar calculation
    by blast
  moreover have "d a_B = B"
    using a_B_def assms(1) assms(3) assms(4) assms(5) calculation(2) d_gres a_elem by blast
  moreover have "Poset.cod f = FB"
    using FB_def calculation(1) calculation(4) f_def i_def by auto
  moreover have "Poset.valid FB"
    using Poset.valid_map_welldefined_cod calculation(6) calculation(8) by blast
  moreover have "e a \<in> Poset.el FA"
    by (metis OVA.valid_welldefined FA_def assms(1) assms(3) a_elem gc_elem_local)
  moreover have "a_B \<equiv> gres V B a"
    by (simp add: a_B_def)
  moreover have "e (gres V B a) = f \<star> (e a)"
    by (metis a_elem assms(3) assms(4) assms(5) f_def gres_def i_def snd_conv)
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

lemma neutral_is_element :
fixes V :: "('A,'a) OVA" and A :: "'A Open"
assumes V_valid : "valid V" and "A \<in> opens V"
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
  and domain : "A \<in> opens V"
shows " e (neut V A) \<in> Poset.el (Prealgebra.ob (prealgebra V) \<cdot> A)"
    using V_valid assms(2) local_inclusion_element neutral_is_element by fastforce

lemma d_gext [simp] : "valid V \<Longrightarrow> b \<in> elems V \<Longrightarrow> A \<in> opens V \<Longrightarrow> d b \<subseteq> A \<Longrightarrow> d (gext V A b) = A" 
  unfolding gext_def
  by (smt (verit, best) d_neut neutral_is_element sup.orderE valid_domain_law)

lemma symmetric_gext:
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and b :: "('A,'a) Valuation"
  assumes V_valid: "valid V"
  and A_open : "A \<in> opens V"
  and b_elem : "b \<in> elems V" 
  and B_le_A : "d b \<subseteq> A" 
shows "gext V A b = comb V b (neut V A)"
  by (smt (verit, ccfv_SIG) A_open B_le_A V_valid b_elem comb_is_element d_gext fst_conv gext_def d_elem_is_open neutral_is_element subset_Un_eq valid_comb_associative valid_domain_law valid_neutral_law_left valid_neutral_law_right)

lemma gres_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A"
  and "d a = A"
  and "a \<in> elems V"
shows "gres V C a = (gres V C (gres V B a))"
proof -
  define "F1" where "F1 = Prealgebra.ar (prealgebra V)"
  define "i_BA" where "i_BA = Space.make_inc B A"
  define "i_CB" where "i_CB = Space.make_inc C B"
  define "i_CA" where "i_CA = Space.make_inc C A"
  define "f" where "f = F1 \<cdot> i_BA"
  define "g" where "g = F1 \<cdot> i_CB"
  define "h" where "h = F1 \<cdot> i_CA"
  have "gres V C a = (C, (F1 \<cdot> i_CA) \<star> (e a))"
    by (smt (verit, ccfv_SIG) F1_def assms(4) assms(5) assms(6) assms(7) assms(8) gres_def i_CA_def order.trans)
  moreover have "gres V B a = (B, f \<star> (e a))"
    by (metis F1_def assms(3) assms(6) assms(7) assms(8) f_def gres_def i_BA_def)
  moreover have "gres V C (gres V B a) = (C, g  \<star> (f \<star> (e a)))"
    by (metis (no_types, lifting) F1_def V_valid assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(2) fst_eqD g_def gres_def gres_elem i_CB_def snd_eqD) 
  moreover have "Prealgebra.valid (prealgebra V)"
    by (meson OVA.valid_welldefined V_valid)
  moreover have "valid_inc i_CB"
    by (simp add: assms(5) i_CB_def) 
  moreover have "i_CB \<in> inclusions V"
    using assms(3) assms(4) calculation(5) i_CB_def by force 
  moreover have "valid_inc i_BA"
    by (simp add: assms(6) i_BA_def) 
    moreover have "i_BA \<in> inclusions V"
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

lemma le_imp_gle : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> local_le V A (A,a1) (A,a2) \<Longrightarrow> gle V (A,a1) (A,a2)"
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

lemma gle_eq_local_le : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> elems V
 \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> d a1 = A \<Longrightarrow> d a2 = A \<Longrightarrow> gle V a1 a2 = local_le V A a1 a2"
  by (metis le_imp_gle local_inclusion_element local_le prod.exhaust_sel valid_gc_poset valid_prealgebra)

lemma gres_monotone :
  fixes V :: "('A,'a) OVA" and a1 a2 :: "('A, 'a) Valuation" and B :: "'A Open"
  assumes V_valid: "valid V"
  and "B \<in> opens V"
  and "B \<subseteq> d a1"
  and "d a1 = d a2"
  and "a1 \<in> elems V" and "a2 \<in> elems V" and "gle V a1 a2"
shows "gle V (gres V B a1) (gres V B a2)"
proof -
  define "A" where "A = d a1"
  define "i" where "i = make_inc B A"
  define "Fi" where "Fi = (Prealgebra.ar (prealgebra V)) \<cdot> i"
  define "FA" where "FA = (Prealgebra.ob (prealgebra V)) \<cdot> A"
  define "FB" where "FB = (Prealgebra.ob (prealgebra V)) \<cdot> B"
  moreover have "gle V a1 a2 \<longrightarrow> Poset.le FA (e a1) (e a2)"
    by (metis A_def FA_def V_valid assms(4) assms(5) assms(6) local_le valid_gc_poset valid_prealgebra) 
  moreover have "local_le V A a1 a2" using assms
    using FA_def calculation(2) by fastforce
  moreover have "i \<in> inclusions V \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (no_types, lifting) A_def CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) V_valid assms(2) assms(3) assms(5) d_elem_is_open i_def)
    moreover have "local_le V B (gres V B a1)  (gres V B a1)"
      by (metis V_valid assms(2) assms(3) assms(5) d_gres gres_elem local_inclusion_element valid_ob valid_prealgebra valid_reflexivity) 
    moreover have "d (gres V B a1) = B"
      using V_valid assms(2) assms(3) assms(5) by auto
    moreover have "d (gres V B a2) = B"
      using V_valid assms(2) assms(3) assms(4) assms(6) by auto 
    ultimately show ?thesis 
      using gle_eq_local_le [where ?V=V and ?A=B and ?a1.0="gres V B a1" and
        ?a2.0="gres V B a2"] assms
        by (metis (no_types, lifting) A_def gres_def gres_elem i_def local_inclusion_element mem_Collect_eq res_monotone snd_conv valid_prealgebra) 
    qed

lemma stability:
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid: "valid V"
  assumes B_le_A : "B \<subseteq> A" and B_open : "B \<in> opens V" and A_open : "A \<in> opens V"
  defines \<epsilon>A_def: "\<epsilon>A \<equiv> neut V A"
  defines \<epsilon>B_def: "\<epsilon>B \<equiv> neut V B"
  defines \<epsilon>A_B_def: "\<epsilon>A_B \<equiv> gres V B \<epsilon>A"
  shows "\<epsilon>A_B = \<epsilon>B"
proof -
  define i where "i \<equiv> Space.make_inc B A"
  define "f" where "f = nat (neutral V)"
  define "one" where "one \<equiv> dom (neutral V)"
  moreover have "\<epsilon>A_B = gres V B \<epsilon>A"
    by (simp add: \<epsilon>A_B_def)
  moreover have "Space.cod i = A \<and> Space.dom i = B"
    by (simp add: i_def)
  moreover have "i \<in> inclusions V"
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
      assms compose_app_assoc eq_fst_iff f_def gres_def i_def neutral_is_element singletonI sndI terminal_value valid_codomain valid_domain
    by (metis (no_types, lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def mem_Collect_eq) 
  qed

(* [Remark 3, CVA]. *)
lemma local_mono_eq_global :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a1 a1' a2 a2' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens V"
  and a1_el : "a1 \<in> elems V" and a1_d : "d a1 = A"
  and a1'_el : "a1' \<in> elems V" and a1'_d : "d a1' = A"
  and a2_el : "a2 \<in> elems V" and a2_d : "d a2 = A"
  and a2'_el : "a2' \<in> elems V" and a2'_d : "d a2' = A"
shows "gle V (comb V a1 a1') (comb V a2 a2') = local_le V A (comb V a1 a1') (comb V a2 a2')"
  using assms comb_is_element d_neut gle_eq_local_le gle_eq_local_le neutral_is_element V_valid
    valid_domain_law valid_neutral_law_right 

  by (smt (verit, ccfv_threshold) assms(10) assms(11) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) comb_is_element d_neut gle_eq_local_le gle_eq_local_le neutral_is_element V_valid valid_domain_law valid_neutral_law_right)

(* [Remark 3 cont., CVA]. *)
lemma id_le_gres :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  "A \<in> opens V" and "B \<in> opens V"  and "B \<subseteq> A"
  and  "a \<in> elems V" and "d a = A"
shows " gle V a (gres V B a)"
proof -
  define "i" where "i = Space.make_inc B (d a)"
  define "Fi" where "Fi = Prealgebra.ar (prealgebra V) \<cdot> i"
  define "FA" where "FA = Prealgebra.ob (prealgebra V) \<cdot> A"
  define "FB" where "FB = Prealgebra.ob (prealgebra V) \<cdot> B"
  define "a_B" where "a_B =  Fi \<star> (e a)"
  have "i \<in> inclusions V"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Prealgebra.valid_space assms(1) assms(2) assms(3) assms(4) assms(6) i_def mem_Collect_eq valid_make_inc valid_prealgebra)
  moreover have "gres V B a = (B, a_B)"
    by (simp add: Fi_def a_B_def assms(3) assms(4) assms(5) assms(6) gres_def i_def)
    moreover have "Prealgebra.valid (prealgebra V)"
    by (meson OVA.valid_welldefined assms(1))
  moreover have "Poset.valid FB"
    using FB_def assms(3) calculation(3) valid_ob by blast
  moreover have "Poset.valid_map Fi"
    using Fi_def calculation(1) calculation(3) valid_ar by blast
  moreover have "e a \<in> Poset.el FA"
    by (metis FA_def assms(1) assms(5) assms(6) local_inclusion_element)
  moreover have "Space.cod i = A \<and> Space.dom i = B \<and> i \<in> inclusions V"
    by (metis Inclusion.select_convs(2) Inclusion.select_convs(3) assms(6) calculation(1) i_def)
  moreover have "a_B \<in> Poset.el FB"
    by (metis FA_def FB_def Fi_def a_B_def calculation(3) calculation(6) calculation(7) image)
    moreover have "Poset.le FB a_B a_B "
      by (simp add: calculation(4) calculation(8) valid_reflexivity)
  moreover have "valid V" by fact
  ultimately show ?thesis
    apply clarsimp
    apply (frule valid_welldefined)
    apply (simp_all add: Let_def)
    apply (simp add: gc_def Let_def)
    apply auto
    using assms(4) assms(6) apply fastforce
    using FB_def Fi_def a_B_def i_def
    apply (metis (no_types, lifting) fst_conv snd_conv) 
    using Fi_def a_B_def i_def  
    using Fi_def a_B_def i_def
    apply (metis assms(4) assms(6) fst_conv in_mono)  
    using assms(2) assms(6)
        apply (metis (no_types, lifting) Fi_def a_B_def fstI i_def snd_eqD)
    apply (metis assms(2) assms(6) fst_conv)
    apply (metis FA_def assms(6) fst_conv) 
    using assms(3) apply presburger
    using FB_def by force
qed

text \<open>
   Lemma `elem\_le\_wrap` ensures that in a valid OVA `V`, if a valuation `a` defined over an open 
   set `A` is locally less than or equal to a valuation `b` defined over a subset `B` of `A` (after 
   `a` is projected onto `B`), then `a` is globally less than or equal to `b`.
\<close>
lemma elem_le_wrap :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" and A B :: "('A Open)"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and dom_A : "d a = A" and dom_B : "d b = B"
  and b_subseteq_a : "B \<subseteq> A" and a_B_le_b : "local_le V B (gres V B a) b"
shows "gle V a b"
proof -
  define "F" where "F = prealgebra V"
  define "FA" where "FA = (Prealgebra.ob F) \<cdot> A"
  define "FB" where "FB = (Prealgebra.ob F) \<cdot> B"
  define "a_B" where "a_B = gres V B a"

  have "d a_B = d b"
    by (metis a_B_def a_elem b_elem b_subseteq_a d_gres dom_A dom_B d_elem_is_open V_valid)

  moreover have "a_B \<in> elems V"
    by (metis a_B_def a_elem b_elem b_subseteq_a dom_A dom_B gres_elem d_elem_is_open V_valid)
  moreover have "b \<in> elems V"
    by (simp add: b_elem)
  moreover have a1: "Prealgebra.valid F"
    by (metis OVA.valid_welldefined F_def V_valid)
  moreover have a2: "A \<in> opens V"
    using a_elem  dom_A dom_B d_elem_is_open V_valid by blast
  moreover have a3: "B \<in> opens V"
    using  b_elem dom_A dom_B d_elem_is_open V_valid by blast
  moreover have a4: "e a \<in> Poset.el FA"
    by (metis FA_def F_def a_elem dom_A local_inclusion_element V_valid)
  moreover have a5: "e b \<in> Poset.el FB"
    by (metis FB_def F_def b_elem dom_B local_inclusion_element V_valid)
  moreover have a6: "B \<subseteq> A"
    by (simp add: b_subseteq_a)
  moreover have a7: "local_le V B a_B b"
    using a_B_def a_B_le_b by fastforce
  moreover have "Prealgebra.space F = space V"
    by (simp add: F_def)
  ultimately show ?thesis using assms gle_eq_local_le [where ?V=V and ?A=B and ?a1.0=a_B and ?a2.0=b ]
    by (smt (verit, best) a_B_def id_le_gres valid_poset valid_semigroup valid_transitivity)
qed

text \<open>
   Lemma `gext\_elem` shows that the extension of a valuation `b` from an open set `B` to a 
   superspace `A` in a valid OVA `V` is an element of `V`.
\<close>
lemma gext_elem :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  "b \<in> elems V" and "B \<in> opens V" and "A \<in> opens V"
  and  "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V" and "d b = B"
defines "ex \<equiv> gext V"
and "b__A \<equiv> gext V A b"
and "com \<equiv> comb V"
shows "b__A \<in> elems V "
proof -
  have "valid V"
    by (simp add: assms(1))
  moreover have "B \<subseteq> A \<and> B \<in> opens V \<and> A \<in> opens V \<and> d b = B"
    by (simp add: assms(3) assms(4) assms(5) assms(8))
  moreover have "b__A = com (neut V A) b"
    by (simp add: assms(2) b__A_def calculation(2) com_def gext_def)
  ultimately show ?thesis
    by (simp add: assms(2) com_def comb_is_element neutral_is_element)
qed

text \<open>
   Lemma `e\_gres` ensures that the embedding of the projection of a valuation `a` defined over an 
   open set `A` onto a subset `B` of `A` in a valid OVA `V` is an element of the poset associated 
   with `B`.
\<close>
lemma e_gres :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  defines "pr \<equiv> gres V"
  and "FB \<equiv> Prealgebra.ob (prealgebra V) \<cdot> B"
  and "a_B \<equiv> gres V B a"
  assumes V_valid : "valid V"
  and "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  and "d a = A"
  and "a \<in> elems V"
shows " e (a_B) \<in> Poset.el FB"
  by (metis FB_def a_B_def assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) d_gres gc_elem_local gres_elem valid_gc_poset valid_prealgebra)

text \<open>
   Lemma `e\_gext` asserts that the embedding of the extension of a valuation `b` from an open 
   set `B` to a superspace `A` in a valid OVA `V` is an element of the poset associated with `A`.
\<close>
lemma e_gext :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and b :: "('A, 'a) Valuation"
  defines "ex \<equiv> gext V"
  and "FA \<equiv> Prealgebra.ob (prealgebra V) \<cdot> A"
  and "b__A \<equiv> gext V A b"
  assumes V_valid : "valid V"
  and "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  and "d b = B"
  and "b \<in> elems V"
shows " e (b__A) \<in> Poset.el FA"
  by (metis FA_def assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) b__A_def d_gext gext_elem local_inclusion_element)

text \<open>
   Lemma `res\_ext\_adjunction\_lhs\_imp\_rhs` indicates that if the projection of a valuation `a` onto 
   a subset `B` of its defining open set `A` is locally less than or equal to another valuation `b` 
   defined over `B` in a valid OVA `V`, then `a` is locally less than or equal to the combination of 
   the neutral element of `A` and `b`.
\<close>
lemma res_ext_adjunction_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  defines "F \<equiv> prealgebra V"
  defines "F0 \<equiv> (\<lambda> A . (ob F) \<cdot> A)"
  defines "\<epsilon>A \<equiv> neut V A"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and a_dom : "d a = A" and b_dom : "d b = B" and "B \<subseteq> A"
  and LHS: "local_le V B (gres V B a) b"
  shows "local_le V A a (comb V \<epsilon>A b)"
proof -
  define "a_B" where "a_B \<equiv> (gres V B a)"
  define "ea_B" where "ea_B \<equiv> e a_B"
  define "eb" where "eb \<equiv> e b"
  define "A" where "A \<equiv> d a"
  define "B" where "B \<equiv> d b"
  moreover have "gle V a a_B"
    by (metis a_B_def assms(9) a_dom b_dom a_elem b_elem id_le_gres d_elem_is_open V_valid)
  moreover have "a = comb V \<epsilon>A a"
    by (smt (verit, best) V_valid \<epsilon>A_def a_dom a_elem d_elem_is_open valid_neutral_law_left)
  moreover have a_B_le_b : "local_le V B (B,ea_B) (B,eb)"
    by (simp add: B_def LHS a_B_def b_dom ea_B_def eb_def)
  moreover have "Poset.valid (F0 A)"
    by (metis A_def Prealgebra.valid_welldefined F0_def F_def a_elem d_elem_is_open V_valid valid_prealgebra)
  moreover have "d \<epsilon>A = A"
    by (simp add: A_def \<epsilon>A_def a_dom)
  moreover have " e \<epsilon>A \<in> Poset.el (F0 A)"  using neutral_local_element
    using A_def F0_def F_def \<epsilon>A_def a_dom a_elem d_elem_is_open V_valid by blast
  moreover have "local_le V A \<epsilon>A \<epsilon>A"
    using F0_def F_def calculation(5) calculation(6) calculation(7) valid_reflexivity by fastforce
    define "gc_poset" where "gc_poset = (Semigroup.poset (semigroup V))"
  moreover have "Poset.valid gc_poset"
    by (metis OVA.valid_welldefined Semigroup.valid_welldefined gc_poset_def V_valid)
  moreover have "\<epsilon>A \<in> Poset.el gc_poset" using gc_poset_def   \<epsilon>A_def
    using a_dom a_elem d_elem_is_open neutral_is_element V_valid by blast
  moreover have "gle V \<epsilon>A \<epsilon>A"
    by (metis calculation(10) calculation(9) gc_poset_def valid_reflexivity)
  moreover have "gle V (comb V \<epsilon>A a) (comb V \<epsilon>A a_B)"
    by (smt (verit) V_valid a_B_def a_dom a_elem assms(9) b_dom b_elem calculation(10) calculation(11) calculation(2) valid_comb_monotone gc_poset_def gres_elem d_elem_is_open)
  moreover have "d a_B = B \<and> d b = B"
    by (metis B_def a_B_def assms(9) d_gres a_dom b_dom a_elem b_elem d_elem_is_open V_valid)
  moreover have "a_B = (B, ea_B) \<and> b = (B, eb)"
    by (metis calculation(13) ea_B_def eb_def prod.collapse)
  moreover have "B \<in> opens V"
    using B_def V_valid b_elem d_elem_is_open by blast
  moreover have "gle V a_B b"  using  calculation a_B_le_b a_B_def gle_eq_local_le [where ?V=V and ?a1.0=a_B and ?a2.0=b and ?A=B]
    by (metis V_valid a_dom a_elem assms(9) b_dom b_elem gres_elem)
  moreover have "gle V (comb V \<epsilon>A a_B) (comb V \<epsilon>A b)"
    by (smt (verit, ccfv_threshold) B_def V_valid a_B_def a_dom a_elem assms(9) b_dom b_elem calculation(10) calculation(11) calculation(15) calculation(16) valid_comb_monotone gc_poset_def gres_elem)
moreover have "gle V (comb V \<epsilon>A a) (comb V \<epsilon>A a_B)"
  using calculation(12) by auto
moreover have "gle V a (comb V \<epsilon>A a_B)"
  using calculation(12) calculation(3) by auto
  moreover have "A \<union> B = A"
    by (simp add: A_def B_def Un_absorb2 assms(9) a_dom b_dom)
  moreover have "d (comb V \<epsilon>A a_B) = A" using valid_domain_law
    by (metis V_valid a_B_def a_dom a_elem assms(9) b_dom calculation(10) calculation(13) calculation(15) calculation(20) calculation(6) gc_poset_def gres_elem)
  ultimately show ?thesis
    by (smt (verit) A_def OVA.valid_welldefined V_valid a_B_def a_dom a_elem assms(9) b_dom b_elem comb_is_element valid_comb_monotone elem_le_wrap local_le valid_domain_law)
qed

text \<open>
   Lemma `res\_ext\_adjunction\_rhs\_imp\_lhs` declares that, in a valid OVA `V`, if a valuation `a` 
   defined over an open set `A` is locally less than or equal to the combination of the neutral 
   element of `A` and a valuation `b` defined over a subset `B` of `A`, then the projection of `a` 
   onto `B` is locally less than or equal to `b`.
\<close>
lemma res_ext_adjunction_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  defines "F \<equiv> prealgebra V"
  defines "F0 \<equiv> (\<lambda> A . (ob F) \<cdot> A)"
  defines "\<epsilon>A \<equiv> neut V A"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens V" and B_open : "B \<in> opens V"
  and B_le_A : "B \<subseteq> A"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and a_dom : "d a = A" and b_dom : "d b = B"
  and RHS: "local_le V A a (comb V \<epsilon>A b)"
shows "local_le V B (gres V B a) b"
proof -
  have "gle V a (comb V \<epsilon>A b)" using assms gle_eq_local_le [where ?V=V and ?a1.0=a and ?A=A and
        ?a2.0="(comb V \<epsilon>A b)"]
    by (metis (no_types, lifting) comb_is_element fst_conv neutral_is_element sup.orderE valid_domain_law)
    moreover have "gle V (gres V B a) (gres V B (comb V \<epsilon>A b))"
      by (metis (no_types, lifting) A_open B_le_A B_open V_valid \<epsilon>A_def a_dom a_elem b_dom b_elem calculation comb_is_element fst_conv gres_monotone neutral_is_element sup.orderE valid_domain_law)
    moreover have "gres V B (comb V \<epsilon>A b) = comb V (gres V (A \<inter> B) \<epsilon>A) b"  using valid_comb_law_right
      by (metis A_open \<epsilon>A_def b_dom b_elem fst_conv neutral_is_element V_valid)
    define "\<epsilon>B" where "\<epsilon>B \<equiv> neut V B"
    moreover have "gres V (A \<inter> B) \<epsilon>A = \<epsilon>B"
      by (simp add: A_open B_le_A B_open \<epsilon>A_def \<epsilon>B_def inf.absorb2 stability V_valid)
    moreover have "comb V (gres V (A \<inter> B) \<epsilon>A) b = b"
      using B_open V_valid \<epsilon>B_def b_dom b_elem calculation(4) valid_neutral_law_left by fastforce
    moreover have "gle V (gres V B a) b"
      using \<open>gres V B (comb V \<epsilon>A b) = comb V (gres V (A \<inter> B) \<epsilon>A) b\<close> calculation(2) calculation(5) by fastforce
    ultimately show ?thesis
      by (metis (no_types, lifting) B_le_A V_valid a_dom a_elem b_dom b_elem d_gres gres_elem d_elem_is_open local_le valid_gc_poset valid_prealgebra)
  qed

text \<open> [Remark 3, CVA].
   This lemma, corresponding to Remark 3 from the CVA paper, states that in a valid OVA, for two valuations
   `a` and `a'` both defined over the same open set `A` which includes another open set `B`, the local order 
   relation holds between the projection of the combination of `a` and `a'` onto `B`, and the combination of 
   the projections of `a` and `a'` onto `B`.
\<close>
lemma laxity :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  A_open : "A \<in> opens V" and B_open :"B \<in> opens V"  and B_le_A : "B \<subseteq> A"
  and  a_elem : "a \<in> elems V" and a_dom : "d a = A"
  and a'_elem :  "a' \<in> elems V" and a_dom' : "d a' = A"
shows "local_le V B (gres V B (comb V a a')) (comb V (gres V B a) (gres V B a'))"
proof -
   define "m1" where "m1 = comb V a a'"
   define "m2" where "m2 = comb V (gres V B a) (gres V B a')"
   define "m1_B" where "m1_B = gres V B m1"
   have "gle V a (gres V B a)"
     using A_open B_le_A B_open a_elem a_dom  id_le_gres  V_valid by blast
   moreover have "gle V a' (gres V B a')"
     using A_open B_le_A B_open a'_elem a_dom' id_le_gres V_valid by blast
   moreover have global_le : "gle V m1 m2"
     by (smt (verit, del_insts) B_le_A B_open V_valid a'_elem a_dom a_dom' a_elem calculation(1) calculation(2) valid_comb_monotone gres_elem m1_def m2_def)
   moreover have d_m1 : "d m1 = A"
     by (simp add: V_valid a'_elem a_elem a_dom a_dom' m1_def valid_domain_law)
   moreover have d_m1_B : "d m1_B = B"
     by (metis m1_B_def B_le_A B_open a'_elem a_elem comb_is_element d_comb d_gres a_dom a_dom' equalityE le_iff_sup d_elem_is_open m1_def V_valid)
   moreover have d_m2 : "d m2 = B"
     by (metis A_open B_le_A B_open V_valid a'_elem a_dom a_dom' a_elem d_gres dual_order.refl gres_elem m2_def sup.order_iff valid_domain_law)
   moreover have pm1_el : "m1_B \<in> elems V"
     by (simp add: m1_B_def B_le_A B_open a'_elem a_elem comb_is_element a_dom a_dom' gres_elem m1_def V_valid valid_domain_law)
   moreover have m2_el : "m2 \<in> elems V"
     by (simp add: B_le_A B_open V_valid a'_elem a_dom a_dom' a_elem comb_is_element gres_elem m2_def)
   moreover have "valid V" by fact
   moreover have m1_el : "m1 \<in> elems V"
     by (simp add: V_valid a'_elem a_elem comb_is_element m1_def)
   moreover have "local_le V B m1_B m2" using V_valid A_open B_open m1_el m2_el d_m1 d_m2 m1_B_def  global_le valid_gle
       [where ?V = V and ?A = A and ?B = B and ?a = m1 and ?b = m2]
     by fastforce
  ultimately show ?thesis
    using m1_B_def m1_def m2_def by auto
qed

text \<open> [Theorem 1, CVA].
   Theorem 1 from the CVA paper is formalized in this theorem. It asserts that, in a valid OVA, the projection 
   of a valuation `a` onto a subset `B` of its defining open set `A` is locally less than or equal to another 
   valuation `b` defined over `B` if and only if `a` is locally less than or equal to the extension of `b` to `A`.
\<close>
theorem res_ext_adjunction :
  fixes V :: "('A,'a) OVA" and  a b :: "('A, 'a) Valuation" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens V" and B_open : "B \<in> opens V"
  and B_le_A : "B \<subseteq> A"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and a_dom : "d a = A" and b_dom : "d b = B"
shows "local_le V B (gres V B a) b = local_le V A a (gext V A b)" (* Isabelle likes equality more than \<longleftrightarrow> *)
proof (rule iffI)
  assume "local_le V B (gres V B a) b"                                                                 
  show "local_le V A a (gext V A b)"  using V_valid a_elem b_elem a_dom b_dom B_le_A
      gext_def [where ?V = V and ?A = A  and ?b = b]
      res_ext_adjunction_lhs_imp_rhs [where ?V = V and ?A = A and ?B = B and ?a = a and ?b = b]
    using A_open \<open>le (ob (prealgebra V) \<cdot> B) (e (gres V B a)) (e b)\<close> by presburger
next
  assume "local_le V A a (gext V A b)"
  show "local_le V B (gres V B a) b" using res_ext_adjunction_rhs_imp_lhs [where ?V = V and ?A = A and ?B = B and ?a = a and ?b = b]
    using A_open B_le_A B_open V_valid
    by (metis \<open>le (ob (prealgebra V) \<cdot> A) (e a) (e (gext V A b))\<close> a_dom a_elem b_dom b_elem gext_def)
  qed

text \<open> [Corollary 1, CVA].
   The first part of Corollary 1 from the CVA paper, stating that for a valid OVA with a strongly neutral 
   combination operation, the extension of the neutral element of a subset `B` of an open set `A` is the neutral 
   element of `A`.
\<close>
corollary strongly_neutral_covariance :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and strongly_neutral: "\<forall> A B . comb V (neut V A) (neut V B) = neut V (A \<union> B)"
  and  "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
defines "ex \<equiv> gext V"
shows "ex A (neut V B) = neut V A "
  by (metis (no_types, lifting) V_valid assms(3) assms(4) assms(5) ex_def fst_eqD gext_def neutral_is_element strongly_neutral sup.absorb_iff1)

text \<open> [Corollary 1 cont., CVA].
   The second part of Corollary 1 from the CVA paper asserts that in a valid OVA where the combination operation 
   is strongly neutral, the combination of any valuation `a` with the identity (the neutral element of the empty 
   set) is `a` itself, irrespective of the order in which the combination operation is performed.
\<close>
corollary strongly_neutral_monoid :
  fixes V :: "('A,'a) OVA" and a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V"
  and strongly_neutral: "\<forall> A B . comb V (neut V A) (neut V B) = neut V (A \<union> B)"
defines "identity  \<equiv> neut V {}"
shows "comb V identity a = a \<and> comb V a identity = a "
proof standard
  define "\<epsilon>A" where "\<epsilon>A = neut V (d a)"
  have "a = comb V \<epsilon>A a "
    by (smt (verit, best) V_valid \<epsilon>A_def a_elem d_elem_is_open valid_neutral_law_left)
  moreover have "comb V identity a = comb V identity (comb V \<epsilon>A a)"
    by (smt (verit, best) V_valid \<epsilon>A_def a_elem d_elem_is_open valid_neutral_law_left)
  moreover have "... = comb V (comb V identity \<epsilon>A) a" using valid_comb_associative
    by (metis OVA.valid_space Prealgebra.valid_map_welldefined Space.valid_def V_valid \<epsilon>A_def a_elem identity_def d_elem_is_open neutral_is_element valid_neutral)
  moreover have "... = comb V \<epsilon>A a"
    by (simp add: \<epsilon>A_def identity_def strongly_neutral)
  moreover have "... = a"
    using calculation(1) by presburger
  ultimately show "comb V identity a = a"
    by presburger
next
  define "\<epsilon>A" where "\<epsilon>A = neut V (d a)"
  have "a = comb V a \<epsilon>A "
    by (smt (verit, best) V_valid \<epsilon>A_def a_elem d_elem_is_open valid_neutral_law_right)
  moreover have "comb V a identity = comb V (comb V a \<epsilon>A) identity"
    by (smt (verit, best) V_valid \<epsilon>A_def a_elem d_elem_is_open valid_neutral_law_right)
  moreover have "... = comb V a (comb V \<epsilon>A identity)" using valid_comb_associative
    by (metis OVA.valid_space Prealgebra.valid_map_welldefined Space.valid_def V_valid \<epsilon>A_def a_elem identity_def d_elem_is_open neutral_is_element valid_neutral)
  moreover have "... = comb V a \<epsilon>A"
    by (simp add: \<epsilon>A_def identity_def strongly_neutral)
  moreover have "... = a"
    using calculation(1) by presburger
  ultimately show "comb V a identity = a"
    by presburger
qed

text \<open> [Corollary 2, CVA].
   The first part of Corollary 2 from the CVA paper, stating that in a valid OVA, the projection of the extension 
   of a valuation `b` from a subset `B` of an open set `A` back onto `B` results in `b`.
\<close>
corollary galois_insertion :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "b \<in> elems V" and "d b = B"
  and " B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  defines "pr \<equiv> gres V" and "ex \<equiv> gext V" and "com \<equiv> comb V"
  shows "pr B (ex A b) = b"
proof -
  define \<epsilon>A where "\<epsilon>A \<equiv> neut V A"
  define \<epsilon>B where "\<epsilon>B \<equiv> neut V B"
  have "pr B (ex A b) = pr B (com \<epsilon>A b)"
    by (simp add: \<epsilon>A_def assms(2) assms(3) assms(4) assms(6) com_def ex_def gext_def)
  moreover have "... =  com (pr (A \<inter> B) \<epsilon>A) b"  using valid_comb_law_right pr_def com_def ex_def
    by (metis \<epsilon>A_def assms(2) assms(3) assms(6) fst_conv neutral_is_element V_valid)
  moreover have "... =  com \<epsilon>B b"
  by (simp add: \<epsilon>A_def \<epsilon>B_def assms(4) assms(5) assms(6) inf.absorb2 pr_def stability V_valid)
  ultimately show ?thesis
    by (smt (verit, best) V_valid \<epsilon>A_def assms(2) assms(3) assms(4) assms(5) assms(6) com_def inf.absorb2 pr_def stability valid_neutral_law_left)
qed

text \<open> [Corollary 2 cont., CVA].
   The second part of Corollary 2 from the CVA paper, asserting that for a valid OVA, a valuation `a` defined 
   over an open set `A` is locally less than or equal to the extension of the projection of `a` onto a subset `B` 
   of `A`, back onto `A`.
\<close>
corollary galois_closure_extensive :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "a \<in> elems V" and "d a = A"
  and " B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  shows "local_le V A a (gext V A (gres V B a))"
proof -
  have "valid V" by fact
  moreover have "local_le V A a a"
    by (metis assms(2) assms(3) assms(6) calculation local_inclusion_element valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V B (gres V B a) (gres V B a)"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) e_gres valid_ob valid_prealgebra valid_reflexivity)
  moreover have "gres V B a \<in> elems V"
    using V_valid assms(2) assms(3) assms(4) assms(5) gres_elem by blast
  moreover have "d (gres V B a) = B"
    using V_valid assms(2) assms(3) assms(4) assms(5) assms(6) d_gres by blast
  ultimately show ?thesis using assms res_ext_adjunction [where ?V = V and ?A = A and ?B = B and ?a = a and ?b = "gres V B a" ]
    by blast
qed

text \<open>
   This lemma, related to the functorial property of the extension operation, states that in a valid OVA, 
   the extension of a valuation `c` from a subset `C` of an open set `A` directly to `A` is globally less than 
   or equal to the extension of `c` first to a subset `B` of `A` that includes `C`, and then to `A`.
\<close>
lemma ext_functorial_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gres V"
  shows "gle V (ex A c) (ex A (ex B c))"
proof -
  have "local_le V C c c"
    by (metis V_valid assms(4) assms(7) assms(8) local_inclusion_element valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V C (pr C (ex A c)) c"
    by (smt (verit, best) V_valid assms(2) assms(4) assms(5) assms(6) assms(7) assms(8) calculation dual_order.trans ex_def galois_insertion pr_def)
  moreover have "pr C (pr B (ex A c)) = pr C (ex A c)"
    by (smt (verit, del_insts) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem gres_functorial d_elem_is_open pr_def V_valid)
  moreover have "local_le V C  (pr C (pr B (ex A c))) c"
    by (simp add: calculation(2) calculation(3))
  moreover have "local_le V B (pr B (ex A c)) (ex B c)"
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_gext d_gres ex_def gext_elem gres_elem order_trans pr_def res_ext_adjunction)
  moreover have "local_le V A (ex A c) (ex A (ex B c))"
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(5) d_gext dual_order.trans ex_def gext_elem pr_def res_ext_adjunction)
    ultimately show ?thesis
      by (smt (verit) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.refl dual_order.trans elem_le_wrap ex_def galois_insertion gext_elem gres_functorial pr_def)
qed

text \<open>
   The converse of the previous lemma, asserting that in a valid OVA, the extension of a valuation `c` first to 
   a subset `B` of an open set `A` that includes `C`, and then to `A`, is globally less than or equal to the 
   extension of `c` from `C` directly to `A`.
\<close>
lemma ext_functorial_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gres V"
  shows "gle V (ex A (ex B c)) (ex A c)"
proof -
  have "local_le V A (ex A (ex B c)) (ex A (ex B c))"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext e_gext ex_def gext_elem valid_ob valid_prealgebra valid_reflexivity)
  moreover have "local_le V B (pr B (ex A (ex B c))) (ex B c)"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext e_gext ex_def galois_insertion gext_elem pr_def valid_ob valid_prealgebra valid_reflexivity)
    moreover have "local_le V C (pr C (pr B (ex A (ex B c)))) c"
      by (metis (no_types, lifting) V_valid assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_insertion gext_elem gle_eq_local_le d_elem_is_open pr_def valid_poset valid_reflexivity valid_semigroup)
moreover have "local_le V C (pr C (ex A (ex B c))) c"
  by (metis (full_types) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) calculation(3) d_gext ex_def gext_elem gres_functorial d_elem_is_open pr_def V_valid)
  moreover have "local_le V A (ex A (ex B c)) (ex A c)" using res_ext_adjunction
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_gext dual_order.trans ex_def gext_elem pr_def)
  ultimately show ?thesis
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem gle_eq_local_le)
qed

text \<open> [Theorem 1 cont., CVA].
   Theorem 1 continued from the CVA paper, stating that for a valid OVA, the extension of a valuation `c` from a 
   subset `C` of an open set `A` directly to `A` is globally equal to the extension of `c` first to a subset `B` 
   of `A` that includes `C`, and then to `A`.
\<close>
theorem ext_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  shows "ex A (ex B c) = ex A c"
proof -
  have "gle V (ex A (ex B c)) (ex A c)"
    using assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def ext_functorial_rhs_imp_lhs V_valid by blast
  moreover have "gle V (ex A c)  (ex A (ex B c))"
    using assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def ext_functorial_lhs_imp_rhs V_valid by blast
  ultimately show ?thesis
    by (smt (z3) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem valid_antisymmetry valid_poset valid_semigroup)
qed

text \<open> [Corollary 2 cont., CVA].
   The third part of Corollary 2 from the CVA paper, asserting that for a valid OVA, the extension of the projection 
   of a valuation `a` onto a subset `B` of an open set `A`, back onto `A`, performed twice is the same as 
   performing it once.
\<close>
corollary galois_closure_idempotent :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d a = A" and "a \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gres V"
  shows "ex A (pr B (ex A (pr B a))) = ex A (pr B a)"
  by (metis assms(2) assms(3) assms(6) assms(7) assms(8) d_gres ex_def galois_insertion gres_elem pr_def V_valid)

text \<open>
   This lemma is a variant of the previous ones, which asserts that the projection of the extension of a valuation 
   `c` from a subset `C` of an open set `A` back onto a subset `B` of `A` that includes `C` gives the extension 
   of `c` onto `B`.
\<close>
lemma up_and_down :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gres V"
shows "pr B (ex A c) = ex B c"
proof -
  have "ex A c = ex A (ex B c)" using ext_functorial
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def V_valid)
  moreover have "pr B (ex A (ex B c)) = ex B c"
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_insertion gext_elem pr_def V_valid)
  ultimately show ?thesis
    by auto
qed

text \<open>
   This lemma asserts that for a valid OVA, if a valuation `a` is locally less than or equal to another 
   valuation `c` over a subset `C` of an open set `A`, then the projection of `a` onto a subset `B` of `A` that 
   includes `C` is locally less than or equal to the extension of `c` to `B`.
\<close>
lemma intermediate_extension :
  fixes V :: "('A,'a) OVA" and a c :: "('A, 'a) Valuation" and A B C :: "('A Open)"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and c_elem : "c \<in> elems V"
  and dom_A : "d a = A" and dom_c : "d c = C"
  and C_le_B : "C \<subseteq> B" and B_leq_A : "B \<subseteq> A"
  and B_open : "B \<in> opens V"
  assumes le_a_C_c : "local_le V C (gres V C a) c"
  shows "local_le V B (gres V B a) (gext V B c)"
proof -
  have "A \<in> opens V \<and> B \<in> opens V \<and> C \<in> opens V"
    using B_open a_elem c_elem dom_A dom_c d_elem_is_open V_valid by blast
  moreover have "local_le V C (gres V C a) c" by fact
  moreover have "local_le V A a (gext V A c)" using res_ext_adjunction
    by (smt (z3) B_leq_A C_le_B a_elem c_elem dom_A dom_c dual_order.trans gext_def gext_elem le_a_C_c d_elem_is_open V_valid)
  moreover have "gext V A c = gext V A (gext V B c)" using ext_functorial
    by (metis B_leq_A C_le_B c_elem calculation(1) dom_c V_valid)
  moreover have "local_le V A a (gext V A (gext V B c))"
    using calculation(3) calculation(4) by auto
  ultimately show ?thesis using res_ext_adjunction le_a_C_c
    by (smt (verit, best) B_leq_A C_le_B V_valid a_elem c_elem d_gext dom_A dom_c gext_elem)
qed

text \<open> [Corollary 3, CVA].
   Corollary 3 from the CVA paper, stating that if a valid OVA is locally complete (i.e., every open set is 
   a complete poset), then the entire OVA is a complete poset.
\<close>
corollary locally_complete_imp_complete :
  fixes V :: "('A,'a) OVA"
  defines "F A \<equiv> (Prealgebra.ob (prealgebra V)) \<cdot> A"
  and "pr \<equiv> gres V" and "ex \<equiv> gext V"
  assumes V_valid: "valid V"
  assumes local_completeness: "\<And>A . A \<in> opens V \<Longrightarrow> Poset.is_complete (F A)"
  shows "Poset.is_complete (poset V)"
proof standard+
  show "Poset.valid (poset V)"
    using V_valid by (metis OVA.valid_welldefined valid_gc)
next
  show "(\<forall> U \<subseteq> el (poset V). \<exists> i . is_inf (poset V) U i)"
  proof auto

    fix U :: "(('A,'a) Valuation) set"
    assume U: "U \<subseteq> el (poset V)"

    have "elems V = el (poset V)"
      by (simp add:  )
    hence "U \<subseteq> elems V" using U by simp

    define "d_U" where "d_U = \<Union> (d ` U)"
    define "ex_U" where "ex_U = ((e o ex d_U) ` U)"
    define "some_e_U" where "some_e_U = Poset.inf (F (d_U)) ex_U"

    have "d_U \<in> opens V"
      by (smt (verit, best) Prealgebra.valid_space U V_valid d_U_def image_subsetI d_elem_is_open subsetD valid_prealgebra valid_union)
    moreover have "ex_U \<subseteq> Poset.el (F (d_U))"
      by (smt (verit) Sup_upper UN_subset_iff Union_least F_def \<open>U \<subseteq> elems V\<close> calculation comp_apply d_U_def e_gext ex_U_def ex_def image_subsetI in_mono d_elem_is_open V_valid)

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
          using \<open>d_U \<in> Space.opens (Prealgebra.space (prealgebra V))\<close> local_completeness by blast
        moreover have "Poset.is_complete (F (d_U))"
          by (simp add: \<open>d_U \<in> OVA.opens V\<close> local_completeness)
        moreover have "Poset.is_inf (F (d_U)) ex_U e_U" using ex_U_def local_completeness
          by (metis \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> \<open>some_e_U = Some e_U\<close> calculation(3) some_e_U_def some_inf_is_inf)
        moreover have "local_le V (d_U) i (ex d_U u)"
          by (smt (verit, del_insts) F_def calculation(1) calculation(5) comp_apply ex_U_def i_def image_iff is_inf_def snd_conv)
        moreover have "local_le V (d u) (pr (d u) i) u"
          by (smt (verit) U V_valid \<open>i \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(1) calculation(2) calculation(6) d_gext d_gres elem_le_wrap ex_def fst_eqD galois_insertion gext_elem gres_elem gres_monotone i_def in_mono d_elem_is_open local_le pr_def subset_Un_eq sup.cobounded2 up_and_down valid_gc_poset valid_prealgebra)
        moreover have i_is_lb: "gle V i u"
          by (smt (verit) U V_valid \<open>i \<in> el (poset V)\<close> calculation(1) calculation(2) calculation(7) elem_le_wrap fst_eqD i_def in_mono pr_def)

        ultimately show "gle V i u"
          by blast
      qed

       moreover have " (\<forall>z\<in>el (poset V). (\<forall>u\<in>U. gle V z u) \<longrightarrow> gle V z i)"
       proof standard+ text \<open> Note that standard won't work here, it doesn't lift the second implication
\<close>

        fix z
        assume "z \<in>  elems V"
        assume "\<forall>u\<in>U. gle V z u"
        moreover have lb2: "\<forall> v \<in> U . d v \<subseteq> d z"
          by (smt (verit) U V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation d_antitone in_mono valid_gc_poset valid_prealgebra)
        moreover have "d z \<in> opens V"
          using V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> d_elem_is_open by blast
         moreover have "\<forall> v \<in> U .d v \<in> opens V"
           using U V_valid d_elem_is_open by blast
         moreover have "\<forall> v \<in> U .v \<in> elems V"
           using U V_valid d_elem_is_open by blast
        moreover have "\<forall> v \<in> U . local_le V (d v) (pr (d v) z) v" using V_valid valid_gle [where ?V
              = V and ?A = "d z" and ?a = z]
          using U \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(1) d_elem_is_open pr_def by blast
        moreover have "\<forall> v \<in> U . Poset.le (F (d v)) (e (pr (d v) z)) (e v)"
          using F_def calculation(6) by presburger
        define "z_U" where "z_U = gres V d_U z"
        moreover have "\<forall> v \<in> U . pr d_U (ex (d z) v) = ex d_U v" using up_and_down
          by (smt (verit, ccfv_threshold) UN_subset_iff V_valid \<open>d_U \<in> Space.opens (Prealgebra.space (prealgebra V))\<close> calculation(3) calculation(4) calculation(5) d_U_def ex_def lb2 pr_def subset_eq)
        moreover have "Poset.valid (F d_U)"
          by (simp add: \<open>d_U \<in> Space.opens (Prealgebra.space (prealgebra V))\<close> local_completeness)
        moreover have "d_U \<in> opens V"
          using \<open>d_U \<in> Space.opens (Prealgebra.space (prealgebra V))\<close> by blast
        moreover have "d_U \<subseteq> d z"
          by (simp add: UN_subset_iff d_U_def lb2)
        moreover have "z_U \<in> elems V" using z_U_def gres_elem [where ?V=V and ?B=d_U and ?a=z and
              ?A="d z"] calculation
          using V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> by fastforce
        moreover have "e z_U \<in> Poset.el (F d_U)"
          by (metis V_valid F_def \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(10) calculation(11) calculation(3) e_gres z_U_def)
        moreover have "\<forall> v \<in> U . local_le V d_U z_U (ex d_U v)" using z_U_def calculation
         intermediate_extension [where ?V = V and ?B = d_U and ?a = z]
          by (metis V_valid \<open>\<forall>u\<in>U. le (poset V) i u\<close> \<open>i \<in> Semigroup.elems (OVA.semigroup V)\<close> \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> d_antitone ex_def fst_conv i_def pr_def valid_gc_poset valid_prealgebra)
            moreover have "\<forall> v \<in> U . local_le V (d z) z (gext V (d z) v)" using
                res_ext_adjunction [where ?V=V]
              by (metis V_valid \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(3) calculation(4) calculation(5) calculation(6) lb2 pr_def)
              moreover have "\<Union> (d ` U) \<subseteq> d z"
                by (simp add: SUP_least lb2)
        moreover have "d i \<subseteq> d z"
          by (simp add: calculation(11) i_def)
        define "i__Z" where "i__Z = gext V (d z) i"

        moreover have "Poset.le (F d_U) (e ( gres V d_U z)) e_U"  using inf_is_glb
        proof -
          have "Poset.valid (F d_U)"
            by (simp add: \<open>d_U \<in> OVA.opens V\<close> local_completeness)
          moreover have "ex_U \<subseteq> el (F d_U)"
            by (simp add: \<open>ex_U \<subseteq> el (F d_U)\<close>)
          moreover have "e (gres V d_U z) \<in> el (F d_U)"
            using \<open>e z_U \<in> el (F d_U)\<close> z_U_def by auto
          moreover have "e_U \<in> el (F d_U)"
            by (simp add: \<open>e_U \<in> el (F d_U)\<close>)
          moreover have "is_inf (F d_U) ex_U e_U"
            using \<open>Poset.valid (F d_U)\<close> \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> \<open>some_e_U = Some e_U\<close> some_e_U_def some_inf_is_inf by fastforce
          moreover have z_U_is_lb : "\<forall> v \<in> U . Poset.le (F d_U) (e (gres V d_U z)) (e (ex d_U v))"
            using F_def \<open>\<forall>v\<in>U. le (ob (prealgebra V) \<cdot> d_U) (e z_U) (e (ex d_U v))\<close> z_U_def by force
          moreover have "\<forall> u \<in> ex_U. Poset.le (F d_U) (e (gres V d_U z)) u"  using z_U_is_lb
            by (simp add: ex_U_def)
          moreover have "le_rel (F d_U) \<subseteq> le_rel (F d_U)"
            by simp
          ultimately show ?thesis
            by (simp add: inf_is_glb)
        qed

        moreover have "le (poset V) z i"
          by (metis V_valid F_def \<open>d i \<subseteq> d z\<close> \<open>i \<in> Semigroup.elems (OVA.semigroup V)\<close> \<open>z \<in> Semigroup.elems (OVA.semigroup V)\<close> calculation(18) elem_le_wrap fst_conv i_def snd_conv)

        term ?thesis

        ultimately show "le (OVA.poset V) z i"
          by meson

      qed
      moreover have "is_inf (poset V) U i"
        by (simp add: calculation(1) calculation(2) calculation(3) calculation(4) is_inf_def)

      ultimately show ?thesis
        by linarith
    qed

    show "\<exists>a b. is_inf (OVA.poset V) U (a, b)"
      using \<open>is_inf (OVA.poset V) U i\<close> i_def by blast
  qed
qed

end
