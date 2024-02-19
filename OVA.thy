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
"elems V \<equiv> el (poset V)"

abbreviation local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation set" where
"local_elems V A \<equiv> { (A, a) | a . a \<in> el (ob V \<cdot> A)}"

lemma local_elem_d : "a \<in> local_elems V A \<Longrightarrow> d a = A"
  by auto 

(*
abbreviation le\_V :: "('A, 'a) Valuation \<Rightarrow> ('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" ("\_ \<preceq>\<langle>\_\<rangle> \_") where
"le\_V a V b \<equiv> Poset.le (Semigroup.poset (semigroup V)) a b"
*)

definition "OVA_local_le_undefined_domain_mismatch _ _ \<equiv> undefined"

(* Note the parameter A is actually redundant *)
definition local_le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V A a a' \<equiv> 
  if A = d a \<and> A = d a' 
  then Poset.le (ob V \<cdot> A) (e a) (e a')
  else OVA_local_le_undefined_domain_mismatch a a'"

abbreviation space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space V \<equiv> Prealgebra.space (prealgebra V)"

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

abbreviation meet :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"meet V a b \<equiv> Poset.meet (poset V) a b"

abbreviation join :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"join V a b \<equiv> Poset.join (poset V) a b"

abbreviation inf :: "('A,'a) OVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"inf V U \<equiv> Poset.inf (poset V) U"

abbreviation sup :: "('A,'a) OVA \<Rightarrow> (('A, 'a) Valuation) set \<Rightarrow> ('A, 'a) Valuation" where
"sup V U \<equiv> Poset.sup (poset V) U"

(* Properties *)

abbreviation is_complete :: "('A,'a) OVA \<Rightarrow> bool" where
"is_complete V \<equiv> Poset.is_complete (OVA.poset V)"

lemma cocomplete : "is_complete V = is_cocomplete (poset V)"
  using complete_equiv_cocomplete by blast 

definition is_commutative :: "('A, 'a) OVA \<Rightarrow> bool" where
"is_commutative V \<equiv> \<forall> a b . a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> comb V a b = comb V b a"

definition is_strongly_neutral :: "('A, 'a) OVA \<Rightarrow> bool" where
"is_strongly_neutral V \<equiv> \<forall> A B . A \<in> opens (space V) \<longrightarrow> B \<in> opens (space V) \<longrightarrow> B \<subseteq> A \<longrightarrow> ext V A (neut V B) = neut V A"

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
  have "e a \<in> el FA"
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
  moreover have "ea_B \<in> el FB"
    by (metis Poset.fun_app2 calculation(1) calculation(5) calculation(6) ea_B_def)
  moreover have "e b \<in> el FB"
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
    by (smt (verit) FB_def Inclusion.simps(1) a_el ea_B_def i_def le_eq_local_le local_elem_gc local_le_def local_le_eq_le pr_B_def prod.collapse res_def valid_inc_dom) 
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
  by (smt (verit, del_insts) fst_conv local_dom local_le_def res_def snd_conv valid_gc_poset)

lemma le_eq : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> le V a b
= (d b \<subseteq> d a \<and>  Poset.le (ob V \<cdot> d b) ((ar V \<cdot> (make_inc (d b) (d a))) \<star> e a) (e b))"
using  gc_le_eq [where ?F="prealgebra V" and ?a=a and ?b=b] valid_gc_poset [where ?V=V]
  by force 

lemma le_rel : "le_rel (gc (prealgebra V)) = { ((A, a), (B, b)) .
 A \<in> opens (space V) \<and> B \<in> opens (space V) 
 \<and> a \<in> el (ob V \<cdot> A) \<and> b \<in> el (ob V \<cdot> B)
 \<and> B \<subseteq> A \<and> Poset.le (ob V \<cdot> B) (ar V \<cdot> (make_inc B A) \<star> a) b }" 
  using  gc_le_rel [where ?F="prealgebra V"] valid_gc_poset [where ?V=V]
  by force

lemma elem_is_raw_elem : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> e a \<in> el (ob V \<cdot> d a)"
  by (metis OVA.valid_welldefined gc_elem_local)

lemma raw_elem_is_elem : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> el ((ob V) \<cdot> A)
\<Longrightarrow> (A, a) \<in> elems V"
  by (metis local_elem_gc valid_gc_poset valid_prealgebra) 

lemma elem_is_local_elem : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> a \<in> local_elems V (d a)"
  by (metis (mono_tags, lifting) CollectI elem_is_raw_elem prod.collapse) 

lemma local_elem_is_elem : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> local_elems V A \<Longrightarrow> a \<in> elems V"
  using local_elem_gc valid_gc_poset valid_prealgebra by fastforce

lemma raw_elem_is_local_elem : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A) \<Longrightarrow> (A, a) \<in> local_elems V A"
  by blast

lemma local_elem_is_raw_elem :  "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> local_elems V A \<Longrightarrow> e a \<in> el (ob V \<cdot> A) "
  by auto

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
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Poset.fun_app2 Poset.product_def SigmaI V_valid a_el b_el comp_apply valid_semigroup valid_welldefined_dom valid_welldefined_map)

lemma res_elem :
fixes V :: "('A,'a) OVA" and B :: "'A Open" and a :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
assumes a_el : "a \<in> elems V"
and "B \<subseteq> d a" and "B \<in> opens (space V)"
defines "a_B \<equiv> res V B a"
shows "a_B \<in> elems V"
  by (metis Prealgebra.restricted_element V_valid a_B_def a_el assms(3) assms(4) d_elem_is_open elem_is_raw_elem local_elem_gc res_def valid_gc_poset valid_prealgebra)

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
  moreover have "(PrealgebraMap.nat (neutral V) \<cdot> A \<star> ()) \<in> el ((ob V)
    \<cdot> A)"
    by (metis Poset.fun_app2 UNIV_unit UNIV_witness V_valid assms(2) calculation(2) calculation(3) calculation(5) calculation(6) singletonD terminal_value valid_prealgebra valid_space) 
ultimately show ?thesis
  by (meson V_valid assms(2) raw_elem_is_elem) 
qed

lemma neutral_local_element :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"
  assumes V_valid : "valid V"
  and domain : "A \<in> opens (space V)"
shows " e (neut V A) \<in> el (ob V \<cdot> A)"
    using V_valid assms(2) elem_is_raw_elem neutral_is_element by fastforce

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

lemma le_eq_local_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> elems V
 \<Longrightarrow> a' \<in> elems V \<Longrightarrow> d a = A \<Longrightarrow> d a'= A \<Longrightarrow> le V a a' = local_le V A a a'"
  by (metis OVA.valid_welldefined le_eq_local_le local_le_def)

lemma le_eq_raw_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> elems V
 \<Longrightarrow> a' \<in> elems V \<Longrightarrow> d a = A \<Longrightarrow> d a' = A \<Longrightarrow> le V a a' = Poset.le (ob V \<cdot> A) (e a) (e a')"
  by (metis Grothendieck.le_eq_local_le valid_gc_poset valid_prealgebra) 

lemma local_le_eq_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> local_elems V A
 \<Longrightarrow> a' \<in> local_elems V A \<Longrightarrow> local_le V A a a' = le V a a'"
  using Grothendieck.le_eq_local_le fst_conv local_elem_gc mem_Collect_eq valid_gc_poset valid_prealgebra
  by (smt (verit) OVA.le_eq_local_le) 

lemma local_le_eq_raw_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> local_elems V A
 \<Longrightarrow> a' \<in> local_elems V A \<Longrightarrow> local_le V A a a' = Poset.le (ob V \<cdot> A) (e a) (e a')"
  by (simp add: local_elem_d local_le_def)

lemma raw_le_eq_local_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)
 \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> Poset.le (ob V \<cdot> A) a a' = local_le V A (A, a) (A, a')"
  by (simp add: local_le_def)

lemma raw_le_eq_le : "valid V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)
 \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> Poset.le (ob V \<cdot> A) a a' = le V (A, a) (A, a')"
  by (metis Grothendieck.local_le_eq_le valid_gc_poset valid_prealgebra)  

lemma res_monotone :
  fixes V :: "('A,'a) OVA" and a a' :: "('A, 'a) Valuation" and B :: "'A Open"
  assumes V_valid: "valid V"
  and "B \<in> opens (space V)"
  and "B \<subseteq> d a"
  and "d a = d a'"
  and "a \<in> elems V" and "a' \<in> elems V" and "le V a a'"
shows "le V (res V B a) (res V B a')"
proof -
  define "A" where "A = d a"
  define "i" where "i = make_inc B A"
  define "Fi" where "Fi = (ar V) \<cdot> i"
  define "FA" where "FA = (ob V) \<cdot> A"
  define "FB" where "FB = (ob V) \<cdot> B"
  moreover have "le V a a' \<longrightarrow> Poset.le FA (e a) (e a')"
    by (metis A_def FA_def Grothendieck.le_eq_local_le V_valid assms(4) assms(5) assms(6) valid_gc_poset valid_prealgebra)
  moreover have "local_le V A a a'" using assms
    using A_def FA_def calculation(2)
    by (meson local_le_def) 
  moreover have "i \<in> inclusions (space V) \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (no_types, lifting)  inclusions_def A_def CollectI Inclusion.select_convs(1) Inclusion.select_convs(2) V_valid assms(2) assms(3) assms(5) d_elem_is_open i_def)
  moreover have "d (res V B a) = B"
      using V_valid assms(2) assms(3) assms(5) by auto
  moreover have "d (res V B a') = B"
      using V_valid assms(2) assms(3) assms(4) assms(6) by auto 
  ultimately show ?thesis 
      using le_eq_local_le [where ?V=V and ?A=B and ?a="res V B a" and ?a'="res V B a'"] assms
      by (metis (no_types, lifting) A_def FA_def Prealgebra.image elem_is_raw_elem i_def raw_le_eq_local_le res_def res_elem res_monotone valid_prealgebra) 
    qed

lemma res_monotone_local :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and  a a' :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" 
  and "B \<subseteq> A"
  and "a \<in> local_elems V A" and "a' \<in> local_elems V A" and "local_le V A a a'"
shows "local_le V B (res V B a) (res V B a')"
  by (smt (verit) OVA.le_eq_local_le OVA.res_monotone V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) d_res fst_conv local_elem_gc mem_Collect_eq res_elem valid_gc_poset valid_prealgebra)

lemma e_res :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a :: "('A, 'a) Valuation"
  defines "pr \<equiv> res V"
  and "FB \<equiv> ob V \<cdot> B"
  and "a_B \<equiv> res V B a"
  assumes V_valid : "valid V"
  and "B \<subseteq> A" and "B \<in> opens (space V)" and "A \<in> opens (space V)"
  and "d a = A"
  and "a \<in> elems V"
shows "e (a_B) \<in> el FB"
  by (metis FB_def a_B_def assms(4) assms(5) assms(6)assms(8) assms(9) d_res gc_elem_local res_elem valid_gc_poset valid_prealgebra)

lemma ext_elem :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  "b \<in> elems V" and "A \<in> opens (space V)"
  and  "d b \<subseteq> A"
shows "ext V A b \<in> elems V"
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
shows " e (ext V A b) \<in> el FA"
  by (metis FA_def V_valid assms(3) assms(4) assms(5) d_ext ext_elem elem_is_raw_elem) 

lemma ext_monotone :
  fixes V :: "('A,'a) OVA" and b b' :: "('A, 'a) Valuation" and A :: "'A Open"
  assumes V_valid: "valid V"
  and "A \<in> opens (space V)"
  and "d b \<subseteq> A"
  and "d b = d b'"
  and "b \<in> elems V" and "b' \<in> elems V" and "le V b b'"
shows "le V (ext V A b) (ext V A b')" 
  unfolding ext_def
  using valid_comb_monotone [where ?V=V]
  by (smt (verit) OVA.valid_welldefined Poset.valid_def V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) neutral_is_element valid_poset) 

lemma ext_monotone_local :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and  a a' :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and "A \<in> opens (space V)" and "B \<in> opens (space V)" 
  and "B \<subseteq> A"
  and "b \<in> local_elems V B" and "b' \<in> local_elems V B" and "local_le V B b b'"
shows "local_le V A (ext V A b) (ext V A b')" using ext_monotone [where ?V=V] local_elem_is_elem
    [where ?V=V] local_le_def
    elem_is_local_elem [where ?V=V]
  by (smt (verit) Grothendieck.le_eq_local_le V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) d_ext e_ext fst_conv mem_Collect_eq prod.collapse raw_elem_is_elem valid_gc_poset valid_prealgebra)


lemma local_le_refl :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and a :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and A_open : "A \<in> opens (space V)"
  and a_el : "a \<in> local_elems V A"
shows "local_le V A a a"
  using A_open V_valid a_el valid_ob valid_prealgebra valid_reflexivity local_le_def by fastforce 

lemma local_le_trans :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and a a' a'':: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and A_open : "A \<in> opens (space V)"
  and a_el : "a \<in> local_elems V A" and a'_el : "a' \<in> local_elems V A" and a''_el : "a'' \<in> local_elems V A"
  and a_le_a' : "local_le V A a a'" and a'_le_a'' : "local_le V A a' a''"
shows "local_le V A a a''" using local_le_def
  by (smt (verit, del_insts) A_open V_valid a''_el a'_el a'_le_a'' a_el a_le_a' mem_Collect_eq prod.exhaust_sel prod.inject valid_ob valid_prealgebra valid_transitivity) 

lemma local_le_antisym :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and a a':: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and A_open : "A \<in> opens (space V)"
  and a_el : "a \<in> local_elems V A" and a'_el : "a' \<in> local_elems V A" and a''_el : "a'' \<in> local_elems V A"
  and a_le_a' : "local_le V A a a'" and a'_le_a : "local_le V A a' a"
shows "a = a'" using local_le_def
  by (smt (verit, best) A_open Poset.valid_def V_valid a'_el a_el a_le_a' assms(7) fst_eqD mem_Collect_eq snd_eqD valid_ob valid_prealgebra)

lemma ext_comm :
  fixes V :: "('A, 'a) OVA" and A :: "'A Open" and b b' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)" 
  and b_el : "b \<in> elems V" and b'_el : "b' \<in> elems V"
  and db_eq_db' : "d b = d b'"
  and B_le_A : "d b \<subseteq> A"
shows "ext V A (comb V b b') = comb V (ext V A b) (ext V A b')"
  unfolding ext_def
  by (smt (verit) A_open B_le_A V_valid b'_el b_el comb_is_element comp_eq_dest_lhs db_eq_db' fst_eqD neutral_is_element sup.absorb_iff1 valid_comb_associative valid_domain_law valid_neutral_law_right)

lemma ext_comm_local :
  fixes V :: "('A, 'a) OVA" and A B :: "'A Open" and b b' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)" 
  and b_el : "b \<in> local_elems V B" and b'_el : "b' \<in> local_elems V B"
  and B_le_A : "B \<subseteq> A"
shows "ext V A (comb V b b') = comb V (ext V A b) (ext V A b')"
  using A_open B_le_A V_valid assms(3) assms(4) b'_el ext_comm local_elem_is_elem by fastforce 

(* Paper results *)

(* [Remark 2 (1/3), TMCVA] *)
lemma res_functorial_id :
  fixes V :: "('A,'a) OVA" and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "a \<in> elems V"
shows "res V (d a) a = a"
  unfolding res_def
  by (metis (no_types, lifting) Poset.ident_app Prealgebra.valid_identity Space.ident_def V_valid assms(2) d_elem_is_open elem_is_raw_elem fst_conv prod.expand snd_conv subset_eq valid_ob valid_prealgebra)

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
      by (metis A_def F1_def Prealgebra.valid_composition V_valid a_el calculation(10) calculation(11) calculation(12) calculation(13) calculation(15) calculation(16) calculation(4) calculation(6) calculation(8) f_def g_def elem_is_raw_elem)
  ultimately show ?thesis
    by (metis f_def g_def)
qed

lemma res_comm :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "res V (d a \<inter> d b) (comb V a b) = comb V (res V (d a \<inter> d b) a) (res V (d a \<inter> d b) b)"
proof -
  have "res V (d a \<inter> d b) (comb V a b) = res V (d a \<inter> d b) (res V (d a) (comb V a b))"
    by (metis (no_types, opaque_lifting) Prealgebra.valid_space V_valid a_el b_el comb_is_element d_elem_is_open inf_le1 res_functorial_trans sup_ge1 valid_domain_law valid_inter valid_prealgebra) 
  moreover have "... = res V (d a \<inter> d b) (comb V a (res V (d a \<inter> d b) b))"
    by (metis V_valid a_el b_el valid_comb_law_left)
  moreover have "... = comb V (res V (d a \<inter> d b) a) (res V (d a \<inter> d b) b)"
    by (smt (verit, best) Int_commute Int_lower2 Prealgebra.valid_space V_valid a_el b_el d_elem_is_open d_res inf.idem inf_left_commute res_elem valid_comb_law_right valid_inter valid_prealgebra)
  ultimately show ?thesis
    by presburger
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
  define "one" where "one \<equiv> Prealgebra.dom (neutral V)"
  moreover have "\<epsilon>A_B = res V B \<epsilon>A"
    by (simp add: \<epsilon>A_B_def)
  moreover have "Space.cod i = A \<and> Space.dom i = B"
    by (simp add: i_def)
  moreover have "i \<in> inclusions (space V)"
    using A_open B_le_A B_open calculation(3) inclusions_def by force
  moreover have "Prealgebra.valid_map (neutral V)"
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
  moreover have "() \<in> el (Poset.dom  (Prealgebra.ar one \<cdot> i))" using Prealgebra.terminal_value
    using A_open B_le_A B_open V_valid calculation(3) one_def valid_domain valid_prealgebra valid_space inclusions_def  calculation(4) by fastforce
  moreover have "(f \<cdot> B \<diamondop> (Prealgebra.ar one \<cdot> i)) \<star> () = f \<cdot> B \<star> ((Prealgebra.ar one \<cdot> i)) \<star> ()"
    using OVA.valid_welldefined Prealgebra.Prealgebra.select_convs(1) Prealgebra.valid_map_welldefined
    assms calculation res_cod compose_app_assoc f_def inclusions_def
    by (metis (no_types, lifting) Prealgebra.const_def) 
  moreover have "((ar V \<cdot> i) \<diamondop> f \<cdot> A) \<star> ()=  e \<epsilon>B"
    using  assms calculation f_def one_def snd_conv valid_map_naturality
    by (metis Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def valid_codomain valid_domain) 
  moreover have "e \<epsilon>A=   f \<cdot> A \<star> ()"
    by (simp add: \<epsilon>A_def f_def)
  ultimately show ?thesis
    using Prealgebra.valid_map_welldefined Prealgebra.valid_welldefined 
      assms compose_app_assoc eq_fst_iff f_def res_def i_def neutral_is_element sndI valid_codomain valid_domain
    by (metis (no_types, opaque_lifting) Prealgebra.Prealgebra.select_convs(1) Prealgebra.const_def)
qed

(* [Remark 3, TMCVA] *)
lemma local_mono_eq_global :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a1 a1' a2 a2' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)"
  and a1_el : "a1 \<in> elems V" and a1_d : "d a1 = A"
  and a1'_el : "a1' \<in> elems V" and a1'_d : "d a1' = A"
  and a2_el : "a2 \<in> elems V" and a2_d : "d a2 = A"
  and a2'_el : "a2' \<in> elems V" and a2'_d : "d a2' = A"
shows "le V (comb V a1 a1') (comb V a2 a2') = local_le V A (comb V a1 a1') (comb V a2 a2')"
  by (metis A_open OVA.le_eq_local_le V_valid a1'_d a1'_el a1_d a1_el a2'_d a2'_el a2_d a2_el comb_is_element fst_conv neutral_is_element valid_domain_law valid_neutral_law_right)

lemma id_le_res :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and B_open : "B \<in> opens (space V)" and B_le_A : "B \<subseteq> d a"
  and a_el : "a \<in> elems V"
shows "le V a (res V B a)"
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
  moreover have "e a \<in> el FA"
    using A_def FA_def V_valid a_el elem_is_raw_elem by blast
  moreover have "Space.cod i = A \<and> Space.dom i = B \<and> i \<in> inclusions (space V)"
    using A_def calculation(1) i_def by auto
  moreover have "a_B \<in> el FB"
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
  by (smt (verit, best) B_le_A OVA.le_eq_local_le Poset.valid_def V_valid a_B_le_b a_el b_el d_elem_is_open d_res id_le_res res_elem valid_poset valid_semigroup)

lemma neut_le_neut :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" 
  assumes V_valid : "valid V"
  and B_open :"B \<in> opens (space V)" and A_open :"A \<in> opens (space V)" and B_le_A : "B \<subseteq> A"
shows "le V (neut V A) (neut V B)"
  by (metis (no_types, lifting) A_open B_le_A B_open V_valid elem_le_wrap fst_conv neutral_is_element stability valid_le valid_poset valid_reflexivity valid_semigroup)  

(* [Theorem 1 (1/3), TMCVA] *)
theorem res_ext_adjunction :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and B_le_A : "d b \<subseteq> d a" 
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "local_le V (d b) (res V (d b) a) b = local_le V (d a) a (ext V (d a) b)" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume "?L"
  let ?ea = "neut V (d a)"     
  let ?a_B = "res V (d b) a"
  have "local_le V (d a) (comb V ?ea a) (comb V ?ea ?a_B)"
    by (smt (verit) B_le_A OVA.le_eq_local_le V_valid a_el b_el comb_is_element d_elem_is_open d_res fst_conv id_le_res neutral_is_element res_elem res_functorial_id sup.absorb_iff1 valid_domain_law valid_monotone valid_neutral_law_left valid_semigroup)
  moreover have "local_le V (d a) (comb V ?ea ?a_B) (comb V ?ea b)"
    by (smt (verit) B_le_A OVA.le_eq_local_le OVA.valid_welldefined V_valid \<open>local_le V (d b) (res V (d b) a) b\<close> a_el b_el comb_is_element d_elem_is_open d_res fst_eqD neutral_is_element res_elem sup.order_iff valid_comb_monotone valid_domain_law valid_poset valid_reflexivity)
  moreover have "comb V ?ea b = ext V (d a) b" using ext_def [where ?V=V and ?A="d a" and ?b=b]
    by (metis B_le_A V_valid a_el b_el d_elem_is_open)
  ultimately show "?R"
    by (smt (verit) B_le_A OVA.le_eq_local_le Poset.valid_def V_valid a_el b_el comb_is_element d_elem_is_open d_ext d_res neutral_is_element res_elem valid_domain_law valid_neutral_law_left valid_poset valid_semigroup)
next
  assume "?R"
  let ?ea = "neut V (d a)"     
  let ?a_B = "res V (d b) a"
  have "local_le V (d b) ?a_B (res V (d b) (ext V (d a) b))"
    by (metis (no_types, lifting) B_le_A OVA.le_eq_local_le OVA.res_monotone V_valid \<open>local_le V (d a) a (ext V (d a) b)\<close> a_el b_el d_elem_is_open d_ext d_res ext_elem res_elem) 
  moreover have "ext V (d a) b = comb V ?ea b"  using ext_def [where ?V=V and ?A="d a" and ?b=b]
    by (meson B_le_A V_valid a_el b_el d_elem_is_open)
  moreover have "(res V (d b) (ext V (d a) b)) = comb V (res V (d a \<inter> d b) ?ea) b"
    by (metis V_valid a_el b_el calculation(2) d_elem_is_open fst_conv neutral_is_element valid_comb_law_right) 
  moreover have "comb V (res V (d a \<inter> d b) ?ea) b = comb V (neut V (d b)) b"
    by (metis B_le_A V_valid a_el b_el d_elem_is_open inf_absorb2 stability)
  ultimately show "?L"
    by (metis V_valid b_el valid_neutral_law_left)
qed

lemma le_ext :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "le V a b = (d b \<subseteq> d a \<and> Poset.le (ob V \<cdot> (d a)) (e a) (e (ext V (d a) b)))"
  by (metis V_valid a_el b_el d_elem_is_open d_ext elem_le_wrap local_le_def res_ext_adjunction valid_le)

lemma laxity :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and B_open :"B \<in> opens (space V)"  and B_le_A : "B \<subseteq> d a"
  and  a_el : "a \<in> elems V" and a_a'_dom : "d a' = d a"
  and a'_elem :  "a' \<in> elems V"
shows "local_le V B (res V B (comb V a a')) (comb V (res V B a) (res V B a'))"
  by (smt (verit) B_open V_valid a'_elem a_a'_dom a_el assms(3) comb_is_element d_comb d_res id_le_res order.refl res_elem sup.orderE valid_le valid_monotone valid_semigroup)

lemma ova_comb_local:
  fixes V :: "('A, 'a) OVA"  and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "comb V a b = comb V (ext V (d a \<union> d b) a) (ext V (d a \<union> d b) b)"
proof -
  define "mul" (infixl \<open>\<otimes>\<close> 55) where "a \<otimes> b = comb V a b" for a b
  define "\<epsilon>" where "\<epsilon> = neut V"
  define "AB" where "AB = d a \<union> d b"

  have "a \<otimes> b = (\<epsilon> AB) \<otimes> (\<epsilon> AB) \<otimes> (a \<otimes> b)"
    by (metis (no_types, lifting) AB_def V_valid \<epsilon>_def a_el b_el comb_is_element d_elem_is_open fst_conv mul_def neutral_is_element valid_domain_law valid_neutral_law_left)
  moreover have "... = (\<epsilon> AB \<otimes> a) \<otimes> (\<epsilon> AB \<otimes> b)"
    by (smt (verit, del_insts) AB_def Un_Int_eq(1) V_valid \<epsilon>_def a_el b_el comb_is_element d_elem_is_open fst_conv mul_def neutral_is_element sup_inf_absorb valid_comb_associative valid_domain_law valid_neutral_law_right)
  moreover have "... = (ext V AB a) \<otimes> (ext V AB b)" unfolding ext_def AB_def mul_def \<epsilon>_def 
    using assms
    by (simp add: Prealgebra.valid_space d_elem_is_open valid_prealgebra valid_union2)
  ultimately show ?thesis
    by (simp add: AB_def mul_def) 
qed

(* [Corollary 1 (1/2), TMCVA] *)
corollary strongly_neutral_combination :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and B_open : "B \<in> opens (space V)" and A_open : "A \<in> opens (space V)"
  and strongly_neutral: "is_strongly_neutral V"
shows "comb V (neut V A) (neut V B) = neut V (A \<union> B)"
  by (smt (verit, best) A_open B_open V_valid comb_is_element d_elem_is_open d_neut is_strongly_neutral_def neutral_is_element ova_comb_local strongly_neutral sup_ge1 sup_ge2 valid_domain_law valid_neutral_law_right)

(* [Corollary 1 (2/2), TMCVA] *)
corollary strongly_neutral_monoid :
  fixes V :: "('A,'a) OVA" and a :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and a_el : "a \<in> elems V"
  and strongly_neutral: "is_strongly_neutral V"
shows "comb V (neut V {}) a = a \<and> comb V a (neut V {}) = a"
  by (smt (verit, ccfv_threshold) Prealgebra.valid_space Space.valid_def V_valid a_el d_elem_is_open neutral_is_element strongly_neutral strongly_neutral_combination sup_bot.right_neutral sup_bot_left valid_comb_associative valid_neutral_law_left valid_neutral_law_right valid_prealgebra) 

lemma strongly_neutral_neut_comm :
  fixes V :: "('A,'a) OVA" and a :: "('A, 'a) Valuation" and U :: "'A Open"
  assumes V_valid : "valid V"
  and strongly_neutral : "is_strongly_neutral V"
  and a_el : "a \<in> elems V"
  and U_open :"U \<in> opens (space V)"
shows "comb V a (neut V U) = comb V (neut V U) a"
  by (smt (verit) U_open V_valid a_el comb_is_element d_elem_is_open d_neut neutral_is_element strongly_neutral strongly_neutral_combination subset_Un_eq sup.absorb_iff1 sup.orderE valid_associative valid_domain_law valid_neutral_law_left valid_neutral_law_right valid_semigroup) 

lemma weak_comb_law_left :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" and U :: "'A Open"
  assumes V_valid : "valid V"
  and strongly_neutral : "is_strongly_neutral V"
  and a_el : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and U_open :"U \<in> opens (space V)" and "d a \<subseteq> U" and "U \<subseteq> d a \<union> d b"
shows "res V U (comb V a b) = comb V a (res V (d b \<inter> U) b)" 
proof -
  have "U \<inter> (d a \<union> d b) = U"
    using assms(7) by blast
  moreover have "comb V a b \<in> elems V \<and> d (comb V a b) = d a \<union> d b"
    by (meson V_valid a_el b_elem comb_is_element valid_domain_law)
  moreover have "d (res V U (comb V a b)) = U"
    using U_open assms(7) calculation(2) by auto  
  moreover have "res V U (comb V a b) = comb V (res V U (comb V a b)) (neut V U)"
    by (metis U_open V_valid assms(7) calculation(2) calculation(3) res_elem valid_neutral_law_right)
  moreover have "... = res V U (comb V (comb V a b) (neut V U))"
    by (metis (no_types, lifting) U_open V_valid assms(7) calculation(2) d_neut inf.absorb_iff2 neutral_is_element valid_comb_law_right)
  moreover have "... = res V U (comb V (comb V a (neut V U)) b)"
    by (metis OVA.valid_welldefined U_open V_valid a_el b_elem strongly_neutral_neut_comm neutral_is_element strongly_neutral valid_associative)
  moreover have "... = comb V (comb V a (neut V U)) (res V (U \<inter> d b) b)"
    by (metis U_open V_valid a_el assms(6) b_elem comb_is_element fst_eqD neutral_is_element sup.absorb_iff2 valid_comb_law_left valid_domain_law)
  moreover have "... = comb V (comb V a (res V (U \<inter> d b) b)) (neut V U)"
    by (metis Int_lower2 Prealgebra.valid_space U_open V_valid a_el b_elem d_elem_is_open neutral_is_element res_elem strongly_neutral strongly_neutral_neut_comm valid_comb_associative valid_inter valid_prealgebra)
  moreover have "... = comb V a (res V (U \<inter> d b) b)"
    by (smt (verit, best) Int_lower2 Prealgebra.valid_space U_open V_valid a_el assms(6) b_elem calculation(1) comb_is_element d_elem_is_open d_res inf.absorb_iff2 inf_sup_distrib1 res_elem valid_domain_law valid_inter valid_neutral_law_right valid_prealgebra)
  ultimately show ?thesis
    by (simp add: Int_commute)
qed

lemma weak_comb_law_right :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" and U :: "'A Open"
  assumes V_valid : "valid V"
  and strongly_neutral : "is_strongly_neutral V"
  and a_el : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and U_open :"U \<in> opens (space V)" and "d b \<subseteq> U" and "U \<subseteq> d a \<union> d b"
shows "res V U (comb V a b) = comb V (res V (d a \<inter> U) a) b" 
proof -
  have "U \<inter> (d a \<union> d b) = U"
    using assms(7) by blast
  moreover have "comb V a b \<in> elems V \<and> d (comb V a b) = d a \<union> d b"
    by (meson V_valid a_el b_elem comb_is_element valid_domain_law)
  moreover have "d (res V U (comb V a b)) = U"
    using U_open assms(7) calculation(2) by auto  
  moreover have "res V U (comb V a b) = comb V  (neut V U) (res V U (comb V a b))"
    by (metis U_open V_valid assms(7) calculation(2) calculation(3) res_elem valid_neutral_law_left)
  moreover have "... = res V U (comb V  (neut V U) (comb V a b))"
    by (metis (no_types, lifting) Int_Un_eq(2) Int_commute U_open V_valid assms(7) calculation(1) calculation(2) equalityE fst_conv neutral_is_element strongly_neutral weak_comb_law_left)
  moreover have "... = res V U (comb V a (comb V (neut V U) b))"
    by (metis U_open V_valid a_el b_elem neutral_is_element strongly_neutral strongly_neutral_neut_comm valid_comb_associative)
  moreover have "... = comb V  (res V (U \<inter> d a) a) (comb V (neut V U) b)"
    by (metis Int_commute U_open V_valid a_el assms(6) b_elem comb_is_element fst_conv neutral_is_element sup.orderE valid_comb_law_right valid_domain_law)
  moreover have "... = comb V (comb V (res V (U \<inter> d a) a) b) (neut V U)"
    by (metis Int_lower2 Prealgebra.valid_space U_open V_valid a_el b_elem d_elem_is_open neutral_is_element res_elem strongly_neutral strongly_neutral_neut_comm valid_comb_associative valid_inter valid_prealgebra)
  moreover have "... = comb V (res V (U \<inter> d a) a) b"
    by (smt (verit, best) Int_lower2 Prealgebra.valid_space U_open V_valid a_el assms(6) b_elem calculation(1) comb_is_element d_elem_is_open d_res inf.absorb_iff2 inf_sup_distrib1 res_elem valid_domain_law valid_inter valid_neutral_law_right valid_prealgebra)
  ultimately show ?thesis
    by (simp add: Int_commute)
qed

(* [Corollary 2 (1/2), TMCVA] *)
corollary galois_insertion :
  fixes V :: "('A,'a) OVA" and A :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and b_el : "b \<in> elems V"
  and B_le_A : " d b \<subseteq> A" and A_open : "A \<in> opens (space V)"
  shows "res V (d b) (ext V A b) = b"
  by (smt (verit, best) A_open B_le_A V_valid b_el d_elem_is_open d_ext d_neut ext_comm ext_elem inf.absorb_iff2 neutral_is_element ova_comb_local stability subset_Un_eq sup.absorb_iff1 sup_ge2 valid_comb_law_right valid_neutral_law_left)

lemma ext_le_id :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"  and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)" and B_le_A : "d b \<subseteq> A"
  and b_el : "b \<in> elems V"
shows "le V (ext V A b) b"
  by (metis A_open B_le_A V_valid b_el d_ext elem_le_wrap ext_elem galois_insertion res_functorial_id valid_le valid_poset valid_reflexivity valid_semigroup)

lemma ext_monotone' :
  fixes V :: "('A,'a) OVA" and b b' :: "('A, 'a) Valuation" and A :: "'A Open"
  assumes V_valid: "valid V"
  and "A \<in> opens (space V)"
  and "d b \<subseteq> A"
  and "d b' \<subseteq> A"
  and "b \<in> elems V" and "b' \<in> elems V" and "le V b b'"
shows "le V (ext V A b) (ext V A b')"
  by (smt (verit, best) OVA.le_eq_local_le OVA.valid_welldefined V_valid assms(2) assms(3) assms(5) assms(6) assms(7) d_ext ext_elem ext_le_id res_ext_adjunction valid_le valid_poset valid_transitivity)  

lemma res_monotone' :
  fixes V :: "('A,'a) OVA" and a a' :: "('A, 'a) Valuation" and B :: "'A Open"
  assumes V_valid: "valid V"
  and "B \<in> opens (space V)"
  and "B \<subseteq> d a"
  and "B \<subseteq> d a'"
  and "a \<in> elems V" and "a' \<in> elems V" and "le V a a'"
shows "le V (res V B a) (res V B a')"
  by (smt (verit, ccfv_threshold) OVA.le_eq_local_le OVA.valid_welldefined V_valid assms(2) assms(4) assms(5) assms(6) assms(7) d_res id_le_res res_elem valid_le valid_poset valid_transitivity)

lemma laxity2 :
  fixes V :: "('A,'a) OVA" and B B' :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and B_open :"B \<in> opens (space V)" and B_le_A : "B \<subseteq> d a"
  and B_open :"B' \<in> opens (space V)" and B'_le_A' : "B' \<subseteq> d a'"
  and a_el : "a \<in> elems V"
  and a'_elem : "a' \<in> elems V"
shows "le V (res V (B \<union> B') (comb V a a')) (comb V (res V B a) (res V B' a'))"
  by (smt (verit) B'_le_A' B_le_A B_open Prealgebra.valid_space V_valid a'_elem a_el assms(2) comb_is_element d_res id_le_res res_elem res_functorial_id res_monotone' valid_comb_monotone valid_domain_law valid_le valid_poset valid_prealgebra valid_reflexivity valid_semigroup valid_union2) 

(* [Corollary 2 (2/2), TMCVA] *)
corollary galois_closure_extensive :
  fixes V :: "('A,'a) OVA" and B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "a \<in> elems V" 
  and "B \<subseteq> d a" and "B \<in> opens (space V)"
  shows "local_le V (d a) a (ext V (d a) (res V B a))"
  by (meson V_valid assms(2) assms(3) assms(4) id_le_res res_elem res_ext_adjunction valid_le)

lemma ext_functorial_trans_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B:: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V"
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)"
  and C_le_B : "d c \<subseteq> B" and B_le_A : "B \<subseteq> A"
  shows "le V (ext V A c) (ext V A (ext V B c))"
  by (smt (verit, ccfv_SIG) A_open B_le_A B_open C_le_B V_valid c_el d_elem_is_open d_ext d_res dual_order.trans elem_le_wrap ext_elem res_elem res_ext_adjunction res_functorial_trans valid_le valid_poset valid_reflexivity valid_semigroup) 

lemma ext_functorial_trans_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V" 
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)" 
  and C_le_B : "d c \<subseteq> B" and B_le_A : "B \<subseteq> A"
  shows "le V (ext V A (ext V B c)) (ext V A c)"
  by (smt (verit, ccfv_SIG) A_open B_le_A B_open C_le_B OVA.le_eq_local_le V_valid c_el d_elem_is_open d_ext ext_elem galois_closure_extensive galois_insertion order.trans res_functorial_trans) 

(* [Theorem 1 (2/3), TMCVA] *)
theorem ext_functorial_id :
  fixes V :: "('A,'a) OVA" and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V"
shows "ext V (d c) c = c"
  by (metis (no_types, lifting) V_valid c_el d_elem_is_open d_ext ext_elem galois_insertion res_functorial_trans subsetI)

(* [Theorem 1 (3/3), TMCVA] *)
theorem ext_functorial_trans :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and c_el : "c \<in> elems V"
  and A_open : "A \<in> opens (space V)" and B_open : "B \<in> opens (space V)"
  and C_le_B : "d c \<subseteq> B" and B_le_A : "B \<subseteq> A" 
  shows "ext V A (ext V B c) = ext V A c"
  by (smt (verit, ccfv_threshold) A_open B_le_A B_open C_le_B V_valid c_el d_ext dual_order.trans ext_elem ext_functorial_trans_lhs_imp_rhs ext_functorial_trans_rhs_imp_lhs valid_antisymmetry valid_poset valid_semigroup)

lemma ext_comm' :
  fixes V :: "('A, 'a) OVA" and A :: "'A Open" and b b' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)" 
  and b_el : "b \<in> elems V" and b'_el : "b' \<in> elems V"
  and B_le_A : "d b \<subseteq> A"
  and B'_le_A : "d b' \<subseteq> A"
shows "ext V A (comb V b b') = comb V (ext V A b) (ext V A b')"
proof -
  define "U" where "U = d b \<union> d b'" 
  then have "ext V U (comb V b b') = comb V (ext V U b) (ext V U b')"
    by (metis V_valid b'_el b_el comb_is_element ext_functorial_id ova_comb_local valid_domain_law)
  then show  ?thesis
    by (smt (verit) B'_le_A B_le_A Prealgebra.valid_space Un_least V_valid assms(2) b'_el b_el d_elem_is_open d_ext ext_comm ext_elem ext_functorial_trans order_class.order_eq_iff ova_comb_local sup.coboundedI1 sup.coboundedI2 valid_prealgebra valid_union2)
qed

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
  by (smt (verit, del_insts) B_leq_A B_open C_le_B V_valid a_el c_elem d_elem_is_open d_res dom_A dom_c le_a_C_c res_elem res_ext_adjunction res_functorial_trans)

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
  show "\<forall>U\<subseteq>OVA.elems V. (\<exists>i. is_inf (poset V) U i) \<and> Poset.inf (poset V) U \<in> OVA.elems V"
  proof (rule allI, rule impI)
    fix U
    assume U: "U \<subseteq> elems V"

    define "d_U" where "d_U = \<Union> (d ` U)"
    define "ex_U" where "ex_U = ((e o ex d_U) ` U)"
    define "e_U" where "e_U = Poset.inf (F (d_U)) ex_U"

    have "d_U \<in> opens (space V)"
      by (smt (verit, best) Prealgebra.valid_space U V_valid d_U_def image_subsetI d_elem_is_open subsetD valid_prealgebra valid_union)
    moreover have "ex_U \<subseteq> el (F (d_U))"
      by (smt (verit) Sup_upper UN_subset_iff Union_least F_def \<open>U \<subseteq> elems V\<close> calculation comp_apply d_U_def e_ext ex_U_def ex_def image_subsetI in_mono d_elem_is_open V_valid)
    moreover have "e_U \<in> el (F d_U)"
      using calculation(1) calculation(2) e_U_def inf_el local_completeness by blast 
    define "i" where "i = (d_U, e_U)"
    moreover have "i \<in> elems V"
      by (metis F_def \<open>e_U \<in> el (F d_U)\<close> calculation(1) raw_elem_is_elem i_def V_valid)
    
    have "Poset.is_inf (poset V) U i"
    proof -
      have "U \<subseteq> el (poset V)"
        by (metis \<open>U \<subseteq> elems V\<close>  )
      moreover have "i \<in> el (poset V)"
        by (metis \<open>i \<in> elems V\<close>  )
      moreover have "\<forall>u\<in>U. Poset.le (poset V) i u"
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
          by (smt (verit) \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> calculation(4) e_U_def inf_is_glb inf_smaller is_inf_def)
        moreover have "d i = d_U \<and> d (ex d_U u) = d_U"
          using U V_valid \<open>d_U \<in> opens (OVA.space V)\<close> calculation(1) calculation(2) ex_def i_def by auto 
        moreover have "local_le V (d_U) i (ex d_U u)"
          using F_def \<open>e_U \<in> el (F d_U)\<close> \<open>ex_U \<subseteq> el (F d_U)\<close> calculation(1) calculation(3)
            calculation(5) calculation(6) ex_U_def i_def inf_smaller
          by (simp add: is_inf_def local_le_def)
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
          by (smt (z3) \<open>z \<in> OVA.elems V\<close> calculation(4) d_res lb2 local_le_def pr_def) 
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
        moreover have "e z_U \<in> el (F d_U)"
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
            by (smt (verit, del_insts) \<open>d_U \<in> opens (OVA.space V)\<close> calculation(2) calculation(4) e_U_def inf_is_glb inf_smaller is_inf_def local_completeness) 
          moreover have z_U_is_lb : "\<forall> v \<in> U . Poset.le (F d_U) (e (res V d_U z)) (e (ex d_U v))"
            by (metis (no_types, lifting) F_def V_valid \<open>\<forall>u\<in>U. OVA.le V i u\<close> \<open>\<forall>v\<in>U. local_le V d_U z_U (ex d_U v)\<close> \<open>\<forall>v\<in>U. v \<in> OVA.elems V\<close> \<open>d_U \<in> opens (OVA.space V)\<close> \<open>d_U \<subseteq> d z\<close> \<open>i \<in> OVA.elems V\<close> \<open>z \<in> OVA.elems V\<close> d_antitone d_ext d_res ex_def fst_conv i_def local_le_def valid_gc_poset valid_prealgebra z_U_def)
          moreover have "\<forall> u \<in> ex_U. Poset.le (F d_U) (e (res V d_U z)) u"  using z_U_is_lb
            by (simp add: ex_U_def)
          moreover have "Poset.le_rel (F d_U) \<subseteq> le_rel (F d_U)"
            by simp
          ultimately show ?thesis
            by (simp add: \<open>d_U \<in> opens (OVA.space V)\<close> e_U_def inf_is_glb local_completeness) 
        qed
        moreover have "Poset.le (poset V) z i" using le_eq_local_le [where ?V=V]
          by (smt (verit, del_insts) F_def V_valid \<open>d i \<subseteq> d z\<close> \<open>i \<in> OVA.elems V\<close> \<open>z \<in> OVA.elems V\<close> calculation(10) calculation(18) d_res elem_le_wrap fst_conv i_def local_le_def snd_conv)
        term ?thesis
        ultimately show "Poset.le (poset V) z i"
          by meson
      qed
      moreover have "is_inf (poset V) U i"
        by (smt (verit) U calculation(2) calculation(3) calculation(4) is_inf_def)
      ultimately show ?thesis
        by linarith
    qed
    moreover have "inf V U \<in> OVA.elems V"
      by (smt (verit, best) calculation(4) inf_def is_inf_def someI_ex) 
    ultimately show "(\<exists>i. is_inf (poset V) U i) \<and> inf V U \<in> elems V"
      by blast 
  qed
qed

lemma meet_is_local_meet :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and local_completeness: "\<And>A . A \<in> opens (space V) \<Longrightarrow> Poset.is_complete (ob V \<cdot> A)"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "meet V a b = (d a \<union> d b, Poset.meet (ob V \<cdot> (d a \<union> d b)) (e (ext V (d a \<union> d b) a)) (e (ext V (d a \<union> d b) b)))"
proof -
  let ?ex_a = "e (ext V (d a \<union> d b) a)" 
  let ?ex_b = "e (ext V (d a \<union> d b) b)"
  let ?i = "(d a \<union> d b, Poset.meet (ob V \<cdot> (d a \<union> d b)) ?ex_a ?ex_b)"
  have "?ex_a \<in> el (ob V \<cdot> (d a \<union> d b))"
    by (metis V_valid a_el b_el comb_is_element d_comb d_elem_is_open e_ext sup_ge1) 
  moreover have "?ex_b \<in> el (ob V \<cdot> (d a \<union> d b))"
    by (metis V_valid a_el b_el comb_is_element d_comb d_elem_is_open e_ext sup_ge2)
  moreover have "Poset.is_complete (ob V \<cdot> (d a \<union> d b))"
    by (meson Prealgebra.valid_space V_valid a_el b_el d_elem_is_open local_completeness valid_prealgebra valid_union2) 
  moreover have "e ?i \<in> el (ob V \<cdot> (d a \<union> d b))"
    by (simp add: calculation(1) calculation(2) calculation(3) meet_el) 
  moreover have "le V ?i a"
    by (smt (verit) Prealgebra.valid_space V_valid a_el b_el calculation(1) calculation(2) calculation(3) calculation(4) d_elem_is_open d_ext elem_le_wrap fst_conv local_elem_gc local_le_def meet_smaller1 res_ext_adjunction snd_conv sup_ge1 valid_gc_poset valid_prealgebra valid_union2) 
  moreover have "le V ?i b"
    by (smt (verit) Prealgebra.valid_space V_valid a_el b_el calculation(1) calculation(2) calculation(3) calculation(4) d_elem_is_open d_ext elem_le_wrap meet_smaller prod.exhaust_sel prod.sel(1) prod.sel(2) raw_elem_is_elem raw_le_eq_local_le res_ext_adjunction sup_ge2 valid_prealgebra valid_union2) 
  moreover have "\<And> c . c \<in> elems V \<Longrightarrow> le V c a \<Longrightarrow> le V c b \<Longrightarrow> le V c ?i" 
  proof -
    fix c
    assume "c \<in> elems V"
    assume "le V c a" 
    assume "le V c b"

    have "d a \<subseteq> d c \<and> d b \<subseteq> d c"
      using V_valid \<open>OVA.le V c a\<close> \<open>OVA.le V c b\<close> \<open>c \<in> OVA.elems V\<close> a_el b_el by blast
    moreover have "d ?i \<subseteq> d c"
      using calculation by auto 

    moreover have "Poset.le (ob V \<cdot> (d c)) (e c) (e (ext V (d c) a)) "
      using V_valid \<open>OVA.le V c a\<close> \<open>c \<in> OVA.elems V\<close> a_el le_ext by blast
    moreover have "Poset.le (ob V \<cdot> (d c)) (e c) (e (ext V (d c) b)) "
      using V_valid \<open>OVA.le V c b\<close> \<open>c \<in> OVA.elems V\<close> b_el le_ext by blast

    moreover have "Poset.le (ob V \<cdot> (d a \<union> d b)) (e (res V (d a \<union> d b) c)) (e (ext V (d a \<union> d b) a))"
      by (smt (verit) Prealgebra.valid_space V_valid \<open>OVA.le V c a\<close> \<open>c \<in> OVA.elems V\<close> \<open>e (ext V (d a \<union> d b) a) \<in> el (OVA.ob V \<cdot> (d a \<union> d b))\<close> a_el b_el calculation(2) d_elem_is_open d_ext d_res elem_is_raw_elem fst_conv intermediate_extension prod.collapse raw_le_eq_local_le res_elem sup_ge1 valid_le valid_prealgebra valid_union2) 
    moreover have "Poset.le (ob V \<cdot> (d a \<union> d b)) (e (res V (d a \<union> d b) c)) (e (ext V (d a \<union> d b) b))"
      by (smt (verit) Prealgebra.valid_space V_valid \<open>c \<in> OVA.elems V\<close> a_el b_el calculation(1) calculation(2) calculation(4) d_elem_is_open d_ext d_res elem_is_raw_elem ext_elem fst_conv intermediate_extension prod.exhaust_sel raw_le_eq_local_le res_elem res_ext_adjunction sup_ge2 valid_prealgebra valid_union2) 

    moreover have "Poset.le (ob V \<cdot> (d a \<union> d b)) (e (res V (d a \<union> d b) c)) (e ?i)"
      by (smt (verit) Prealgebra.valid_space V_valid \<open>Poset.is_complete (OVA.ob V \<cdot> (d a \<union> d b))\<close> \<open>c \<in> OVA.elems V\<close> \<open>e (ext V (d a \<union> d b) a) \<in> el (OVA.ob V \<cdot> (d a \<union> d b))\<close> \<open>e (ext V (d a \<union> d b) b) \<in> el (OVA.ob V \<cdot> (d a \<union> d b))\<close> a_el b_el calculation(2) calculation(5) calculation(6) d_elem_is_open e_res fst_conv meet_property snd_conv valid_prealgebra valid_union2)

    ultimately show "le V c ?i"
      by (smt (verit) Prealgebra.valid_space V_valid \<open>c \<in> OVA.elems V\<close> \<open>e (d a \<union> d b, Poset.meet (OVA.ob V \<cdot> (d a \<union> d b)) (e (ext V (d a \<union> d b) a)) (e (ext V (d a \<union> d b) b))) \<in> el (OVA.ob V \<cdot> (d a \<union> d b))\<close> a_el b_el d_elem_is_open d_res elem_is_raw_elem elem_le_wrap fst_conv prod.exhaust_sel raw_elem_is_elem raw_le_eq_local_le res_elem valid_prealgebra valid_union2)
  qed
  moreover have "is_complete V"
    using V_valid local_completeness locally_complete_imp_complete by auto 
  moreover have "is_inf (poset V) {a, b} ?i"
    by (smt (verit) OVA.valid_welldefined Poset.valid_def Prealgebra.valid_welldefined V_valid a_el b_el calculation(8) calculation(1) calculation(2) calculation(3) calculation(5) calculation(6) calculation(7) complete_meet_is_inf d_elem_is_open is_complete_def meet_comm meet_el meet_property meet_smaller2 raw_elem_is_elem valid_union2)
  moreover have "?i = meet V a b"
    by (smt (verit) Poset.inf_unique V_valid a_el b_el calculation(9) calculation(8) complete_meet_is_inf is_inf_def valid_poset valid_semigroup) 
  ultimately show ?thesis
    by simp 
qed

(* Unknown if this is true. Could also make the conclusion of the form "valid [OVA]" *)
lemma meet_ova :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and V_complete : "is_complete V"
  and local_completeness: "\<And>A . A \<in> opens (space V) \<Longrightarrow> Poset.is_complete (ob V \<cdot> A)"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "res V (d a) (meet V a b) = meet V a (res V (d a \<inter> d b) b)"
  oops

lemma join_is_local_join :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation"
  assumes V_valid: "valid V"
  and local_completeness: "\<And>A . A \<in> opens (space V) \<Longrightarrow> Poset.is_complete (ob V \<cdot> A)"
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
shows "join V a b = (d a \<inter> d b, Poset.join (ob V \<cdot> (d a \<inter> d b)) (e (res V (d a \<inter> d b) a)) (e (res V (d a \<inter> d b) b)))"
proof -
  let ?re_a = "e (res V (d a \<inter> d b) a)" 
  let ?re_b = "e (res V (d a \<inter> d b) b)"
  let ?s = "(d a \<inter> d b, Poset.join (ob V \<cdot> (d a \<inter> d b)) ?re_a ?re_b)"
  have "?re_a \<in> el (ob V \<cdot> (d a \<inter> d b))"
    by (meson Prealgebra.valid_space V_valid a_el b_el d_elem_is_open e_res inf_le1 valid_inter valid_prealgebra)
  moreover have "?re_b \<in> el (ob V \<cdot> (d a \<inter> d b))"
    by (meson Int_lower2 Prealgebra.valid_space V_valid a_el b_el d_elem_is_open e_res valid_inter valid_prealgebra)
  moreover have "Poset.is_complete (ob V \<cdot> (d a \<inter> d b))"
    by (meson Prealgebra.valid_space V_valid a_el b_el d_elem_is_open local_completeness valid_inter valid_prealgebra)
  moreover have "e ?s \<in> el (ob V \<cdot> (d a \<inter> d b))"
    using calculation(1) calculation(2) calculation(3) complete_equiv_cocomplete join_el by fastforce
  moreover have "le V a ?s"
    by (smt (z3) Prealgebra.valid_space V_valid a_el b_el calculation(1) calculation(2) calculation(3) calculation(4) complete_equiv_cocomplete d_elem_is_open d_res elem_le_wrap fst_conv inf_le1 join_greater1 local_elem_gc local_le_def snd_conv valid_gc_poset valid_inter valid_prealgebra)
  moreover have "le V b ?s"
    by (smt (verit) Int_lower2 Prealgebra.valid_space V_valid a_el b_el calculation(1) calculation(2) calculation(3) calculation(4) complete_equiv_cocomplete d_elem_is_open d_res elem_le_wrap fst_conv join_greater2 local_elem_gc local_le_def snd_conv valid_gc_poset valid_inter valid_prealgebra)
  moreover have "\<And> c . c \<in> elems V \<Longrightarrow> le V a c \<Longrightarrow> le V b c \<Longrightarrow> le V ?s c" 
  proof -
    fix c
    assume "c \<in> elems V"
    assume "le V a c" 
    assume "le V b c"

    have "d c \<subseteq> d a \<and> d c \<subseteq> d b"
      using V_valid \<open>OVA.le V a c\<close> \<open>OVA.le V b c\<close> \<open>c \<in> OVA.elems V\<close> a_el b_el by blast 
    moreover have "d c \<subseteq> d ?s"
      using calculation by auto 

    moreover have "Poset.le (ob V \<cdot> (d a)) (e a) (e (ext V (d a) c)) "
      by (metis V_valid \<open>OVA.le V a c\<close> \<open>c \<in> OVA.elems V\<close> a_el d_elem_is_open d_ext e_ext elem_is_raw_elem prod.exhaust_sel raw_le_eq_local_le res_ext_adjunction valid_le) 
    moreover have "Poset.le (ob V \<cdot> (d b)) (e b) (e (ext V (d b) c)) "
      by (metis V_valid \<open>OVA.le V b c\<close> \<open>c \<in> OVA.elems V\<close> b_el d_elem_is_open d_ext e_ext elem_is_raw_elem prod.exhaust_sel raw_le_eq_local_le res_ext_adjunction valid_le)

    moreover have "Poset.le (ob V \<cdot> (d a \<inter> d b)) (e (res V (d a \<inter> d b) a)) (e (ext V (d a \<inter> d b) c))"
      by (smt (verit) Prealgebra.valid_space V_valid \<open>OVA.le V a c\<close> \<open>c \<in> OVA.elems V\<close> \<open>e (res V (d a \<inter> d b) a) \<in> el (OVA.ob V \<cdot> (d a \<inter> d b))\<close> a_el b_el calculation(2) d_elem_is_open d_ext d_res e_ext fst_conv inf_le1 intermediate_extension prod.exhaust_sel raw_le_eq_local_le valid_inter valid_le valid_prealgebra)
    moreover have "Poset.le (ob V \<cdot> (d a \<inter> d b)) (e (res V (d a \<inter> d b) b)) (e (ext V (d a \<inter> d b) c))"
      by (smt (verit) Int_lower2 Prealgebra.valid_space V_valid \<open>OVA.le V b c\<close> \<open>c \<in> OVA.elems V\<close> \<open>e (res V (d a \<inter> d b) b) \<in> el (OVA.ob V \<cdot> (d a \<inter> d b))\<close> a_el b_el calculation(2) d_elem_is_open d_ext d_res e_ext fst_conv intermediate_extension prod.exhaust_sel raw_le_eq_local_le valid_inter valid_le valid_prealgebra)

    moreover have "Poset.le (ob V \<cdot> (d a \<inter> d b)) (e ?s) (e (ext V (d a \<inter> d b) c))"
      by (smt (verit, del_insts) Prealgebra.valid_space V_valid \<open>Poset.is_complete (OVA.ob V \<cdot> (d a \<inter> d b))\<close> \<open>c \<in> OVA.elems V\<close> \<open>e (res V (d a \<inter> d b) a) \<in> el (OVA.ob V \<cdot> (d a \<inter> d b))\<close> \<open>e (res V (d a \<inter> d b) b) \<in> el (OVA.ob V \<cdot> (d a \<inter> d b))\<close> a_el b_el calculation(2) calculation(5) calculation(6) complete_equiv_cocomplete d_elem_is_open e_ext fst_conv join_property snd_conv valid_inter valid_prealgebra)
    ultimately show "le V ?s c"
      by (smt (verit) Prealgebra.valid_space V_valid \<open>c \<in> OVA.elems V\<close> \<open>e (d a \<inter> d b, Poset.join (OVA.ob V \<cdot> (d a \<inter> d b)) (e (res V (d a \<inter> d b) a)) (e (res V (d a \<inter> d b) b))) \<in> el (OVA.ob V \<cdot> (d a \<inter> d b))\<close> a_el b_el d_elem_is_open d_ext elem_le_wrap fst_conv local_le_def raw_elem_is_elem res_ext_adjunction snd_conv valid_inter valid_prealgebra)
  qed
  moreover have "is_complete V \<and> Poset.is_cocomplete (poset V)"
    using V_valid cocomplete local_completeness locally_complete_imp_complete by blast
  moreover have "is_sup (poset V) {a, b} ?s"
    by (smt (verit) OVA.valid_welldefined Prealgebra.valid_welldefined Space.valid_def V_valid a_el b_el calculation(8) calculation(1) calculation(2) calculation(3) calculation(5) calculation(6) calculation(7) cocomplete cocomplete_join_is_sup complete_equiv_cocomplete d_elem_is_open is_complete_def join_el join_greater join_property raw_elem_is_elem valid_antisymmetry)
  moreover have "?s = join V a b"
    by (smt (verit) Poset.sup_unique V_valid a_el b_el calculation(8) calculation(9) cocomplete_join_is_sup is_sup_def valid_poset valid_semigroup)
  ultimately show ?thesis
    by simp 
qed

(* Extension of local operators *)

definition ext_local :: "('A, 'a) OVA \<Rightarrow> ('A Open, ('a \<times> 'a,'a) PosetMap) Function 
  \<Rightarrow> (('A, 'a) Valuation) Semigroup" where
"ext_local V f = \<lparr> mult =
  \<lparr> PosetMap.dom = poset V \<times>\<times> poset V, 
    cod = poset V,
    func = { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (poset V \<times>\<times> poset V) } \<rparr>\<rparr>" 

lemma d_ext_local : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation" and op :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  shows "d (mul (ext_local V f) a b) = d a \<union> d b"
proof -
  define "comb'" where "comb' = mult (ext_local V f)"
  have "Poset.dom comb' = poset V \<times>\<times> poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp            
  moreover have 1 : "Poset.func comb' =  { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (poset V \<times>\<times> poset V) }"  using comb'_def ext_local_def [where ?V=V and
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
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation" and op :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  shows "e (mul (ext_local V f) a b) =  f \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))"
proof -
  define "comb'" where "comb' = mult (ext_local V f)"
  have "Poset.dom comb' = poset V \<times>\<times> poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]    
    by simp            
  moreover have 1 : "Poset.func comb' =  { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (poset V \<times>\<times> poset V) }"  using comb'_def ext_local_def [where ?V=V and
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

lemma ext_local_elem : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes V_valid : "valid V" 
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" 
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
shows "mul (ext_local V f) a b \<in> elems V" 
proof -
  define "comb'" where "comb' = mult (ext_local V f)"
  have "Poset.dom comb' = poset V \<times>\<times> poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp        
  moreover have  "Poset.cod comb' = poset V" using comb'_def ext_local_def [where ?V=V and
        ?f=f]
    by simp       
  moreover have  "Poset.func comb' =  { ((a, b), (d a \<union> d b, (f \<cdot> (d a \<union> d b)) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b))))
            |a b . (a,b) \<in> el (poset V \<times>\<times> poset V) }"  using comb'_def ext_local_def [where ?V=V and
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
    by (metis (no_types, lifting) Poset.fun_app2 Prealgebra.valid_space V_valid a_el b_el d_elem_is_open d_ext_local e_ext_local f_cod raw_elem_is_elem prod.collapse valid_prealgebra valid_union2)  
qed

lemma ext_local_local_elem : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes V_valid : "valid V" 
  and a_el : "a \<in> elems V" and b_el : "b \<in> elems V" 
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
shows "mul (ext_local V f) a b \<in> local_elems V (d a \<union> d b)" 
  using ext_local_elem [where ?V=V and ?a=a and ?b=b and ?f=f] elem_is_local_elem [where ?V=V and
      ?a=a]
  by (smt (verit) CollectI V_valid a_el b_el d_ext_local elem_is_raw_elem f_cod f_dom f_valid f_valid_val prod.collapse)

lemma ext_local_value : 
  fixes V :: "('A, 'a) OVA"  and a b :: "('A,'a) Valuation" and op :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  assumes a_el : "a \<in> elems V" and b_el : "b \<in> elems V"
  shows "mul (ext_local V f) a b =  (d a \<union> d b, f \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b)))"
  by (metis a_el b_el d_ext_local e_ext_local prod.collapse)

(* [Lemma 1 (1/2), TMCVA] *)
lemma local_mono_ext_comm_imp_assoc:
  fixes V :: "('A, 'a) OVA" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and local_assoc : "\<And>A a a' a''. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)  \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> a'' \<in> el (ob V
   \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (f \<cdot> A \<star> (a, a'), a'') = f \<cdot> A \<star> (a, f \<cdot> A \<star> (a', a''))"
  and local_mono : "\<And>A a1 a1' a2 a2'. A \<in> opens (space V) \<Longrightarrow> a1 \<in> local_elems V A \<Longrightarrow> a1' \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> a2' \<in> local_elems V A
 \<Longrightarrow> local_le V A a1 a1' \<Longrightarrow> local_le V A a2 a2' \<Longrightarrow> local_le V A (A, (f \<cdot> A \<star> (e a1, e a2))) (A, (f \<cdot> A \<star> (e a1', e a2')))"
  and local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, f \<cdot> B \<star> (b, b'))) = f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))) "
shows "\<And> a b c . a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow> 
  comb' (comb' a b) c = comb' a (comb' b c)"
proof (standard, goal_cases)
  case (1 a b c)
  then show ?case 
  proof -
    have "d (comb' a b) = d a \<union> d b"
      using "1"(1) "1"(2) comb'_def d_ext_local by blast
    moreover have "d (comb' (comb' a b) c) = d a \<union> d b \<union> d c" using d_ext_local [where ?V=V and ?a="comb' a b" and ?b=c]
        ext_local_elem [where ?V=V and ?a=a and ?b=b] calculation assms
      using "1"(1) "1"(2) "1"(3) by blast 
    moreover have "d (comb' b c) = d b \<union> d c"
      using "1"(2) "1"(3) comb'_def d_ext_local by blast
    moreover have "d (comb' a (comb' b c)) = d a \<union> d b \<union> d c" using d_ext_local [where ?V=V and ?a=a and ?b="comb' b c"]
        ext_local_elem [where ?V=V and ?a=b and ?b=c] calculation assms
      using "1"(1) "1"(2) "1"(3) by blast
    ultimately show ?thesis
      by presburger
  qed
next
  case (2 a b c)
  then show ?case 
  proof -
    define "U" where "U = d a \<union> d b \<union> d c"
    have "a \<in> elems V \<and> b \<in> elems V \<and> c \<in> elems V"
      using "2"(1) "2"(2) "2"(3) by blast 
    moreover have "d (comb' a b) = d a \<union> d b"
      using "2"(1) "2"(2) comb'_def d_ext_local by blast 
    moreover have "comb' a b \<in> elems V" using ext_local_elem [where ?V=V and ?a=a and ?b=b]
      using "2"(1) "2"(2) V_valid comb'_def f_cod f_dom f_valid f_valid_val by blast
    moreover have "d (comb' b c) = d b \<union> d c"
      using "2"(2) "2"(3) comb'_def d_ext_local by blast 
    moreover have "comb' b c \<in> elems V" using ext_local_elem [where ?V=V and ?a=b and ?b=c]
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
      by (smt (verit) prod.collapse) 
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

lemma local_assoc_units_imp_ext_comm:
  fixes V :: "('A, 'a) OVA" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  and i :: "('A Open, 'a) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and assoc : "\<And> a b c . a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow> 
  comb' (comb' a b) c = comb' a (comb' b c)"
  and units_el : "\<And>A. A \<in> opens (space V) \<Longrightarrow> i \<cdot> A \<in> el (ob V \<cdot> A)"
  and units : "\<And>A a. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (i \<cdot> A, a) = a \<and> f \<cdot> A \<star> (a, i \<cdot> A) = a"
shows local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> ext V A (B, f \<cdot> B \<star> (b, b')) = (A, f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))))"
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
      by (smt (verit, del_insts) \<open>A \<in> opens (OVA.space V)\<close> \<open>B \<in> opens (OVA.space V)\<close> \<open>B \<subseteq> A\<close> \<open>b \<in> el (OVA.ob V \<cdot> B)\<close> d_ext_local e_ext_local fst_conv raw_elem_is_elem prod.expand snd_conv sup.absorb_iff2) 
    moreover have "... =  (A, f \<cdot> A \<star> (e (ext V A (B, b)), i \<cdot> A))" 
      using ext_functorial_id V_valid \<open>A \<in> opens (OVA.space V)\<close> raw_elem_is_elem units_el by fastforce 
    moreover have "... = ext V A (B, b)"
      by (metis V_valid \<open>A \<in> opens (OVA.space V)\<close> \<open>B \<in> opens (OVA.space V)\<close> \<open>B \<subseteq> A\<close> \<open>b \<in> el (OVA.ob V \<cdot> B)\<close> d_ext e_ext fst_conv raw_elem_is_elem prod.collapse units) 
    ultimately show "comb' (B, b) (A, i \<cdot> A) = ext V A (B, b)"
      by presburger
  qed
  moreover have "(b, b') \<in> el (Poset.dom (f \<cdot> B))" using product_def
    by (metis (no_types, lifting) B_open Poset.Poset.select_convs(1) SigmaI assms(5) b'_el b_el) 
  moreover have "f \<cdot> B \<star> (b, b') \<in> el (ob V \<cdot> B)" using f_cod [where ?A=B] f_dom [where ?A=B] b_el
      b'_el B_open
    by (metis Poset.fun_app Poset.valid_map_cod calculation(2) f_valid_val) 

  moreover have "ext V A (B, f \<cdot> B \<star> (b, b')) = comb' (B, f \<cdot> B \<star> (b, b')) (A, i \<cdot> A)" using lem
    by (simp add: calculation(3))
  moreover have "... = comb' (comb' (B, b) (B, b')) (A, i \<cdot> A)"
    by (smt (verit) B_open V_valid b'_el b_el comb'_def d_ext_local e_ext_local ext_functorial_id fst_conv raw_elem_is_elem prod.collapse snd_conv subset_refl sup.orderE) 
  moreover have "... = comb' (comb' (B, b) (A, i \<cdot> A)) (B, b')"
    by (smt (verit) A_open B_le_A B_open V_valid assoc b'_el b_el comb'_def d_ext_local e_ext e_ext_local ext_functorial_id fst_conv raw_elem_is_elem lem prod.collapse subset_Un_eq sup.orderE units_el) 
  moreover have "... = comb' (comb' (B, b) (A, i \<cdot> A)) (comb' (B, b') (A, i \<cdot> A))"
    by (smt (z3) A_open B_le_A B_open V_valid b'_el b_el comb'_def d_ext_local e_ext e_ext_local ext_functorial_id fst_conv raw_elem_is_elem lem prod.collapse subset_Un_eq subset_refl sup.orderE units_el) 
  moreover have "... = comb' (ext V A (B, b)) (ext V A (B, b'))"
    using b'_el b_el lem by auto
  moreover have "... = (A, f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))))"
    by (smt (z3) A_open B_le_A B_open V_valid b'_el b_el calculation(3) calculation(4) calculation(5) calculation(6) calculation(7) calculation(8) comb'_def d_ext d_ext_local e_ext_local eq_fst_iff ext_elem ext_functorial_id raw_elem_is_elem prod.exhaust_sel) 

  ultimately show "ext V A (B, f \<cdot> B \<star> (b, b')) = (A, f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A
    (B, b'))))"
    by simp
qed

lemma up_down_le_down_up : 
  fixes V :: "('A, 'a) OVA" and A B B' C :: "'A Open" and b :: "('A, 'a) Valuation"
  defines "B \<equiv> d b"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens (space V)" and B'_open : "B' \<in> opens (space V)" and C_open : "C \<in> opens (space V)"
  and C_le_B : "C \<subseteq> d b" and B_le_A : "d b \<subseteq> A" and C_le_B' : "C \<subseteq> B'" and B'_le_A : "B' \<subseteq> A"
  and b_el : "b \<in> elems V"
shows "local_le V B' (res V B' (ext V A b)) (ext V B' (res V C b))"
  by (smt (verit, del_insts) A_open B'_le_A B'_open B_le_A C_le_B C_le_B' C_open V_valid b_el d_elem_is_open d_ext d_res ext_elem galois_insertion id_le_res intermediate_extension res_elem res_functorial_trans valid_le)

lemma local_mono_ext_comm_imp_laxity:
  fixes V :: "('A, 'a) OVA" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and local_assoc : "\<And>A a a' a''. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)  \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> a'' \<in> el (ob V
   \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (f \<cdot> A \<star> (a, a'), a'') = f \<cdot> A \<star> (a, f \<cdot> A \<star> (a', a''))"
  and local_mono : "\<And>A a1 a1' a2 a2'. A \<in> opens (space V) \<Longrightarrow> a1 \<in> local_elems V A \<Longrightarrow> a1' \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> a2' \<in> local_elems V A
 \<Longrightarrow> local_le V A a1 a1' \<Longrightarrow> local_le V A a2 a2' \<Longrightarrow> local_le V A (A, (f \<cdot> A \<star> (e a1, e a2))) (A, (f \<cdot> A \<star> (e a1', e a2')))"
  and local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, f \<cdot> B \<star> (b, b'))) = f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))) "
shows "\<And>A B a a'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  a \<in> local_elems V A \<Longrightarrow> a' \<in> local_elems V A
\<Longrightarrow> local_le V B (res V B (A, f \<cdot> A \<star> (e a, e a'))) (B, (f \<cdot> B \<star> (e (res V B a), e (res V B a'))))"
proof -
  fix A B a a'
  assume B_open :"B \<in> opens (space V)"
  assume A_open : "A \<in> opens (space V)"
  assume B_le_A : "B \<subseteq> A"
  assume a_el : "a \<in> local_elems V A"
  assume a'_el : "a'\<in> local_elems V A"

  define "a_B" where "a_B = res V B a"
  define "a'_B" where "a'_B = res V B a'"

  have "e a_B \<in> el (ob V \<cdot> B)" using a_B_def
    using A_open B_le_A B_open V_valid a_el e_res raw_elem_is_elem by fastforce
  moreover have "e a'_B \<in> el (ob V \<cdot> B)" using a'_B_def
    using A_open B_le_A B_open V_valid a'_el e_res raw_elem_is_elem by fastforce
  moreover have "(e a_B, e a'_B) \<in> el (Poset.dom (f \<cdot> B))"
    by (simp add: Poset.product_def \<open>B \<in> opens (OVA.space V)\<close> calculation(1) calculation(2) f_dom)  

  moreover have "local_le V A
      a 
      (ext V A a_B)" 
    using galois_closure_extensive [where ?V=V] a_B_def
    by (smt (verit, best) A_open B_le_A B_open V_valid a_el fst_conv mem_Collect_eq raw_elem_is_elem)
  moreover have "local_le V A 
      a' 
      (ext V A a'_B)" 
    using galois_closure_extensive [where ?V=V] a'_B_def
    by (smt (verit, best) A_open B_le_A B_open V_valid a'_el fst_conv mem_Collect_eq raw_elem_is_elem)

  moreover have "local_le V A  
      (A, (f \<cdot> A \<star> (e a, e a')))
      (A, (f \<cdot> A \<star> (e (ext V A a_B), e (ext V A a'_B))))" 
    using a_B_def a'_B_def local_mono [where
    ?A=A and ?a1.0="a" and ?a2.0="a'" and ?a1'="ext V A a_B" and ?a2'="ext V A a'_B"]
    by (smt (verit) A_open B_le_A B_open V_valid a'_el a_el calculation(1) calculation(2) calculation(4) calculation(5) d_ext d_res e_ext fst_conv mem_Collect_eq prod.collapse raw_elem_is_elem) 

  moreover have "(A, (f \<cdot> A \<star> 
      ((e (ext V A a_B)), 
       (e (ext V A a'_B))))) =
      ext V A (B, (f \<cdot> B \<star> (e a_B, e a'_B)))" using local_ext_comm [where ?B=B and ?A=A] a_B_def
    a'_B_def A_open B_le_A B_open V_valid a'_el a_el calculation(1) calculation(2) d_res fst_conv mem_Collect_eq prod.collapse raw_elem_is_elem
    by (smt (verit, del_insts) Poset.fun_app2 calculation(3) d_ext f_cod f_valid_val) 

  moreover have "local_le V A
      (A, (f \<cdot> A \<star> (e a, e a')))
      (ext V A (B, (f \<cdot> B \<star> (e a_B, e a'_B))))"
    by (metis calculation(6) calculation(7)) 

  moreover have "local_le V B
      (res V B (A, (f \<cdot> A \<star> (e a, e a'))))
      (res V B (ext V A (B, (f \<cdot> B \<star> (e a_B, e a'_B)))))"
    using res_monotone_local [where ?V=V and ?A=A and ?B=B and  ?a="(A, (f \<cdot> A \<star> (e a, e a')))" and a'="ext V A (B, (f \<cdot>
            B \<star> ((e a_B), (e a'_B))))"] B_open A_open B_le_A  V_valid a_B_def a'_B_def
    by (smt (verit) Pair_inject Poset.Poset.select_convs(1) Poset.fun_app2 Poset.product_def a'_el a_el calculation(3) calculation(7) calculation(8) e_ext f_cod f_dom f_valid_val mem_Collect_eq mem_Sigma_iff prod.collapse raw_elem_is_elem) 

  moreover have "res V B (ext V A (B, (f \<cdot> B \<star> (e a_B, e a'_B)))) =
    (B, f \<cdot> B \<star> (e a_B, e a'_B))"
    by (metis A_open B_le_A B_open Poset.fun_app Poset.valid_map_cod V_valid calculation(3) f_cod f_valid_val fst_conv galois_insertion raw_elem_is_elem)

  ultimately show "local_le V B (res V B (A, f \<cdot> A \<star> (e a, e a'))) (B, (f \<cdot> B \<star> (e (res V B a), e (res V B a'))))"
    by (metis (no_types, lifting) a'_B_def a_B_def)
qed

(* [Lemma 1 (2/2), TMCVA] *)
lemma local_mono_ext_comm_imp_mono:
  fixes V :: "('A, 'a) OVA" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and local_assoc : "\<And>A a a' a''. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)  \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> a'' \<in> el (ob V
   \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (f \<cdot> A \<star> (a, a'), a'') = f \<cdot> A \<star> (a, f \<cdot> A \<star> (a', a''))"
  and local_mono : "\<And>A a1 a1' a2 a2'. A \<in> opens (space V) \<Longrightarrow> a1 \<in> local_elems V A \<Longrightarrow> a1' \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> a2' \<in> local_elems V A
 \<Longrightarrow> local_le V A a1 a1' \<Longrightarrow> local_le V A a2 a2' \<Longrightarrow> local_le V A (A, (f \<cdot> A \<star> (e a1, e a2))) (A, (f \<cdot> A \<star> (e a1', e a2')))"
  and local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, f \<cdot> B \<star> (b, b'))) = f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))) "
shows "\<And>a1 a2 b1 b2. 
 a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> b1 \<in> elems V \<Longrightarrow> b2 \<in> elems V
\<Longrightarrow> le V a1 b1 \<Longrightarrow> le V a2 b2
\<Longrightarrow> le V (comb' a1 a2) (comb' b1 b2)"
proof -
  fix a1 a2 b1 b2
  assume a1_el : "a1 \<in> elems V"
  assume a2_el : "a2 \<in> elems V"
  assume b1_el : "b1 \<in> elems V"
  assume b2_el : "b2 \<in> elems V"
  assume a1_le_b1 : "le V a1 b1"
  assume a2_le_b2 : "le V a2 b2"
  define "A1" where "A1 = d a1"
  define "A2" where "A2 = d a2"
  define "B1" where "B1 = d b1"
  define "B2" where "B2 = d b2"
  define "a1'" where "a1' = ext V (A1 \<union> A2) a1"
  define "a2'" where "a2' = ext V (A1 \<union> A2) a2"

  have "B1 \<subseteq> A1 \<and> B2 \<subseteq> A2" using A1_def A2_def B1_def B2_def a1_le_b1 a2_le_b2 a1_el a2_el b1_el
      b2_el
    using V_valid by blast 

  moreover have B1B2: "B1 \<union> B2 \<in> opens (space V) \<and> A1 \<union> A2 \<in> opens (space V)"
    by (metis A1_def A2_def B1_def B2_def Prealgebra.valid_space V_valid a1_el a2_el b1_el b2_el d_elem_is_open valid_prealgebra valid_union2) 

  moreover have a1_le_b1_local : "local_le V B1 (res V B1 a1) b1" using A1_def B1_def a1_le_b1 a1_el b1_el
      valid_le [where ?V=V and ?a=a1 and ?b=b1]
    using V_valid by fastforce

  moreover have a2_le_b2_local : "local_le V B2 (res V B2 a2) b2" using A2_def B2_def a2_le_b2 a2_el
      b2_el valid_le [where ?V=V and ?a=a2 and ?b=b2]
    using V_valid by fastforce

  moreover have 0: "res V (B1 \<union> B2) (comb' a1 a2) =
    res V (B1 \<union> B2) (A1 \<union> A2, (f \<cdot> (A1 \<union> A2) \<star> (e a1', e a2')))"
    by (smt (verit, del_insts) A1_def A2_def a1_el a2_el a1'_def a2'_def comb'_def d_ext_local e_ext_local prod.collapse) 

  moreover have a1'_local_el : "a1' \<in> local_elems V (A1 \<union> A2)"
    by (smt (verit) A1_def A2_def CollectI Prealgebra.valid_space V_valid a1'_def a1_el a2_el d_elem_is_open d_ext e_ext prod.collapse sup_ge1 valid_prealgebra valid_union2)
  
  moreover have a2'_local_el : "a2' \<in> local_elems V (A1 \<union> A2)"
    by (smt (verit, ccfv_threshold) A1_def A2_def Prealgebra.valid_space V_valid a1_el a2'_def a2_el d_elem_is_open d_ext e_ext inf_sup_aci(5) mem_Collect_eq prod.collapse sup_ge1 valid_prealgebra valid_union2) 

  moreover have 00: "local_le V (B1 \<union> B2)
    (res V (B1 \<union> B2) (A1 \<union> A2, (f \<cdot> (A1 \<union> A2) \<star> (e a1', e a2'))))
    (B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')))" 
    using local_mono_ext_comm_imp_laxity [where ?V=V and ?f=f and ?B="B1 \<union> B2" and ?A="A1 \<union> A2" and a=a1' and a'=a2']   a1'_def a2'_def A1_def A2_def B1_def B2_def a1_le_b1 a2_le_b2 a1_el a2_el b1_el
      assms calculation le_sup_iff subsetI subset_antisym sup_ge1 sup.mono
    by (smt (z3))

  moreover have 1: "local_le V (B1 \<union> B2) (res V (B1 \<union> B2) a1') (ext V (B1 \<union> B2) (res V B1 a1))" 
    using B1_def B2_def a1'_def up_down_le_down_up [where ?V=V and ?A="A1 \<union> A2" and
        B'="B1 \<union> B2" and ?C=B1 and ?b=a1]
    by (metis A1_def V_valid a1_el b1_el calculation(1) calculation(2) d_elem_is_open sup.mono sup_ge1)

  moreover have 11: "B1 \<union> B2 = d (ext V (B1 \<union> B2) (res V B1 a1)) \<and> B1 \<union> B2 = d (ext V (B1 \<union> B2) b1)"  using assms
      d_ext [where ?V=V and ?A="B1 \<union> B2"] d_res [where ?V=V and ?B=B1]
    by (metis (no_types, lifting) A1_def B1_def a1_el b1_el calculation(1) calculation(2) d_elem_is_open res_elem sup_ge1)

  moreover have 111: "local_le V (B1 \<union> B2) (ext V (B1 \<union> B2) (res V B1 a1)) (ext V (B1 \<union> B2) b1)" using
     11  A1_def B1_def a1_le_b1_local valid_le [where ?V=V and ?a=a1 and ?b=b1] 
       d_ext [where ?V=V and ?A="B1 \<union> B2"] d_res [where ?V=V and ?B=B1] 
       ext_monotone_local [where ?V=V and ?A="B1 \<union> B2"]
    by (smt (verit, del_insts) V_valid a1_el a1_le_b1 b1_el calculation(2) d_elem_is_open elem_is_raw_elem mem_Collect_eq prod.collapse res_elem sup_ge1)

  moreover have 1111: "local_le V (B1 \<union> B2) (res V (B1 \<union> B2) a1') (ext V (B1 \<union> B2) b1)" using 1 11 111 local_le_trans
    by (smt (verit) A1_def B1_def V_valid a1'_def a1_el b1_el calculation(1) calculation(2) d_elem_is_open d_ext d_res e_ext e_res ext_elem local_le_def res_elem sup.mono sup_ge1 valid_ob valid_prealgebra valid_transitivity)

  moreover have 2: "local_le V (B1 \<union> B2) (res V (B1 \<union> B2) a2') (ext V (B1 \<union> B2) (res V B2 a2))" 
    using B1_def B2_def a2'_def up_down_le_down_up [where ?V=V and ?A="A1 \<union> A2" and
        B'="B1 \<union> B2" and ?C=B2 and ?b=a2]
    by (metis A2_def Un_mono V_valid a2_el b2_el calculation(1) calculation(2) d_elem_is_open sup.cobounded2)

  moreover have 22: "B1 \<union> B2 = d (ext V (B1 \<union> B2) (res V B2 a2)) \<and> B1 \<union> B2 = d (ext V (B1 \<union> B2) b2)"  using assms
      d_ext [where ?V=V and ?A="B1 \<union> B2"] d_res [where ?V=V and ?B=B2]
    by (metis (mono_tags, lifting) A2_def B2_def a2_el b2_el calculation(1) calculation(2) d_elem_is_open res_elem sup.cobounded2)

  moreover have 222: "local_le V (B1 \<union> B2) (ext V (B1 \<union> B2) (res V B2 a2)) (ext V (B1 \<union> B2) b2)" using
     22  A2_def B2_def a2_le_b2_local valid_le [where ?V=V and ?a=a2 and ?b=b2] 
       d_ext [where ?V=V and ?A="B1 \<union> B2"] d_res [where ?V=V and ?B=B2] 
       ext_monotone_local [where ?V=V and ?A="B1 \<union> B2"]
    by (metis (no_types, lifting) V_valid a2_el a2_le_b2 b2_el calculation(2) d_elem_is_open ext_elem galois_insertion res_elem res_ext_adjunction sup_ge2)

  moreover have 2222: "local_le V (B1 \<union> B2) (res V (B1 \<union> B2) a2') (ext V (B1 \<union> B2) b2)" using 2 22
      222 local_le_trans
    by (smt (verit) A2_def B2_def V_valid a2'_def a2_el b2_el calculation(1) calculation(2) d_elem_is_open d_ext d_res e_ext e_res ext_elem local_le_def res_elem sup.mono sup_ge2 valid_ob valid_prealgebra valid_transitivity) 

  moreover have el1: "res V (B1 \<union> B2) a1' \<in> local_elems V (B1 \<union> B2)" using A1_def A2_def B1_def B2_def B1B2 a1'_def elem_is_local_elem [where
        ?V=V]
    by (smt (verit, del_insts) V_valid a1_el calculation(1) d_ext d_res e_res ext_elem mem_Collect_eq prod.collapse sup.mono sup_ge1)  
  moreover have el2 : "ext V (B1 \<union> B2) b1 \<in> local_elems V (B1 \<union> B2)" using A1_def A2_def B1_def B2_def B1B2 elem_is_local_elem [where
        ?V=V]
    by (smt (verit) "11" V_valid b1_el e_ext mem_Collect_eq prod.collapse sup_ge1)
  moreover have el3: "res V (B1 \<union> B2) a2' \<in> local_elems V (B1 \<union> B2)" using A1_def A2_def B1_def B2_def B1B2 a2'_def elem_is_local_elem [where
        ?V=V]
    by (smt (verit) V_valid a2_el calculation(1) d_ext d_res e_res ext_elem mem_Collect_eq prod.collapse sup.mono sup_ge2)
  moreover have el4 : "ext V (B1 \<union> B2) b2 \<in> local_elems V (B1 \<union> B2)" using A1_def A2_def B1_def B2_def B1B2 elem_is_local_elem [where
        ?V=V]
    by (smt (verit) "22" V_valid b2_el e_ext mem_Collect_eq prod.collapse sup_ge2)

  moreover have 3: "local_le V (B1 \<union> B2)
    (B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')))
    (B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (ext V (B1 \<union> B2) b1), e (ext V (B1 \<union> B2) b2)))" 
    using B1B2 1111 2222 local_mono [where ?A="B1 \<union> B2" and ?a1.0="res V (B1 \<union> B2) a1'" and ?a1'="ext V (B1 \<union> B2) b1"
 and ?a2.0="res V (B1 \<union> B2) a2'" and ?a2'="ext V (B1 \<union> B2) b2"] el1 el2 el3 el4
    by blast

  moreover have 4: "(B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (ext V (B1 \<union> B2) b1), e (ext V (B1 \<union> B2) b2)))
  = comb' b1 b2"
    by (smt (verit, best) B1_def B2_def b1_el b2_el comb'_def d_ext_local e_ext_local prod.collapse) 

  moreover have 5: "local_le V (B1 \<union> B2)
    (B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2'))) 
    (comb' b1 b2)"
    using "3" "4" by force 

  moreover have 6: "local_le V (B1 \<union> B2) 
    (res V (B1 \<union> B2) (comb' a1 a2))
    (B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')))"
    using "0" "00" by presburger

  moreover have "comb' a1 a2 \<in> elems V" using comb'_def  ext_local_elem [where ?V=V and ?a=a1 and
        ?b=a2 and ?f=f]
    using V_valid a1_el a2_el f_cod f_dom f_valid f_valid_val by fastforce 

  moreover have "comb' b1 b2 \<in> elems V" using comb'_def  ext_local_elem [where ?V=V and ?a=b1 and
        ?b=b2 and ?f=f]
    using V_valid b1_el b2_el f_cod f_dom f_valid f_valid_val by fastforce 

  moreover have 7: "comb' b1 b2 \<in> local_elems V (B1 \<union> B2)" using elem_is_local_elem
    by (smt (verit) "4" V_valid calculation(26) fst_conv mem_Collect_eq)

  moreover have "res V (B1 \<union> B2) (comb' a1 a2) \<in> elems V" using res_elem [where ?V=V and
        ?a="comb' a1 a2" and ?B="B1 \<union> B2"]
    by (metis A1_def A2_def B1B2 V_valid a1_el a2_el calculation(1) calculation(25) comb'_def d_ext_local sup.mono)

  moreover have 8: "res V (B1 \<union> B2) (comb' a1 a2) \<in> local_elems V (B1 \<union> B2)" using elem_is_local_elem
    by (smt (verit) A1_def A2_def B1B2 CollectI V_valid a1_el a2_el calculation(1) calculation(28) calculation(25) comb'_def d_ext_local d_res elem_is_raw_elem res_def snd_conv sup.mono)

  moreover have "res V (B1 \<union> B2) a1' \<in> local_elems V (B1 \<union> B2)" using assms calculation
    by meson 

  moreover have "res V (B1 \<union> B2) a2' \<in> local_elems V (B1 \<union> B2)" using assms calculation
    by meson       

  moreover have "e (res V (B1 \<union> B2) a1') \<in> el (ob V \<cdot> (B1 \<union> B2))"
    using el1 by auto 

  moreover have "e (res V (B1 \<union> B2) a2') \<in> el (ob V \<cdot> (B1 \<union> B2))"
    using el3 by force 

  moreover have "(e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')) \<in> el (Poset.dom (f \<cdot> (B1 \<union>
 B2)))" using assms calculation product_def [where ?P="ob V \<cdot> (B1 \<union> B2)" and ?Q="ob V \<cdot> (B1 \<union> B2)"] 
local_elem_is_raw_elem [where ?V=V and ?A="B1 \<union> B2"]
    by (metis (no_types, lifting) Poset.Poset.select_convs(1) SigmaI) 

  moreover have "f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')) \<in> el (ob V \<cdot> (B1
    \<union> B2))" using assms calculation
    by (metis (no_types, opaque_lifting) Poset.fun_app2) 

  moreover have 9: "(B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')))  \<in>
 local_elems V (B1 \<union> B2)" using assms calculation
    by blast 

  moreover have 10: "local_le V (B1 \<union> B2) (res V (B1 \<union> B2) (comb' a1 a2)) (comb' b1 b2)" using 5 6 B1B2
      local_le_trans [where ?V=V and ?A="B1 \<union> B2" and a="res V (B1 \<union> B2) (comb' a1 a2)" 
and a'="(B1 \<union> B2, f \<cdot> (B1 \<union> B2) \<star> (e (res V (B1 \<union> B2) a1'), e (res V (B1 \<union> B2) a2')))"
and a''="comb' b1 b2"] 7 8 9
    using V_valid by blast

  ultimately show "le V (comb' a1 a2) (comb' b1 b2)" using 10
    by (smt (verit, ccfv_threshold) A1_def A2_def Un_absorb1 Un_upper1 V_valid a1_el a2_el comb'_def d_ext_local elem_le_wrap fst_conv inf_sup_aci(7) sup.orderE)
qed

lemma local_mono_ext_comm_imp_lax_comb:
  fixes V :: "('A, 'a) OVA" and f :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "comb' \<equiv> mul (ext_local V f)"
  assumes V_valid : "valid V"
  and f_valid : "Function.valid_map f" 
  and f_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (f \<cdot> A)" 
  and f_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (f \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and f_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (f \<cdot> A) = ob V \<cdot> A" 
  and local_assoc : "\<And>A a a' a''. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A)  \<Longrightarrow> a' \<in> el (ob V \<cdot> A) \<Longrightarrow> a'' \<in> el (ob V
   \<cdot> A) \<Longrightarrow> f \<cdot> A \<star> (f \<cdot> A \<star> (a, a'), a'') = f \<cdot> A \<star> (a, f \<cdot> A \<star> (a', a''))"
  and local_mono : "\<And>A a1 a1' a2 a2'. A \<in> opens (space V) \<Longrightarrow> a1 \<in> local_elems V A \<Longrightarrow> a1' \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> a2' \<in> local_elems V A
 \<Longrightarrow> local_le V A a1 a1' \<Longrightarrow> local_le V A a2 a2' \<Longrightarrow> local_le V A (A, (f \<cdot> A \<star> (e a1, e a2))) (A, (f \<cdot> A \<star> (e a1', e a2')))"
  and local_ext_comm : "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> e (ext V A (B, f \<cdot> B \<star> (b, b'))) = f \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))) "
shows "\<And>a b. a \<in> elems V \<Longrightarrow> b \<in> elems V 
\<Longrightarrow> le V (comb' a b) (comb' a (res V (d a \<inter> d b) b))
\<and> le V (comb' a b) (comb' (res V (d a \<inter> d b) a) b)"
proof (intro conjI, goal_cases)
  case (1 a b)
  then show ?case
  proof -
    fix a b
    assume a_el : "a \<in> elems V"
    assume b_el : "b \<in> elems V"
    have "le V b (res V (d a \<inter> d b) b)"
      by (meson Prealgebra.valid_space V_valid a_el b_el d_elem_is_open id_le_res inf_le2 valid_inter valid_prealgebra) 
    thus "le V (comb' a b) (comb' a (res V (d a \<inter> d b) b))"  
      using local_mono_ext_comm_imp_mono [where ?V=V and ?f=f and ?a1.0="a" and ?a2.0="b" and ?b1.0="a" and ?b2.0="res V (d a \<inter> d b) b"]
      by (smt (z3) Prealgebra.valid_space V_valid a_el b_el comb'_def d_elem_is_open f_cod f_dom f_valid f_valid_val inf_le2 local.local_ext_comm local_assoc local_mono res_elem valid_inter valid_poset valid_prealgebra valid_reflexivity valid_semigroup) 
  qed
next
  case (2 a b)
  then show ?case
   proof -
    fix a b
    assume a_el : "a \<in> elems V"
    assume b_el : "b \<in> elems V"
    have "le V a (res V (d a \<inter> d b) a)"
      by (meson Prealgebra.valid_space V_valid a_el b_el d_elem_is_open id_le_res inf_sup_ord(1) valid_inter valid_prealgebra) 
    thus "le V (comb' a b) (comb' (res V (d a \<inter> d b) a) b)"  
      using local_mono_ext_comm_imp_mono [where ?V=V and ?f=f and ?a1.0="a" and ?a2.0="b" and ?b1.0="res V (d a \<inter> d b) a" and ?b2.0="b"]
      by (smt (z3) Prealgebra.valid_space V_valid a_el b_el comb'_def d_elem_is_open f_cod f_dom f_valid f_valid_val inf_sup_ord(1) local.local_ext_comm local_assoc local_mono res_elem valid_inter valid_poset valid_prealgebra valid_reflexivity valid_semigroup)
  qed
qed

(* [Lemma 2, TMCVA] *)
lemma local_weak_exchange_imp_weak_exchange:
  fixes V V' :: "('A, 'a) OVA"
  and p :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  and s :: "('A Open, ('a \<times> 'a,'a) PosetMap) Function"
  defines "par \<equiv> mul (ext_local V p)" and "seq \<equiv> mul (ext_local V' s)"
  assumes V_valid : "valid V" and V'_valid : "valid V'"
  and V_V'_prealg : "prealgebra V = prealgebra V'"
  and p_valid : "Function.valid_map p" 
  and p_valid_val : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.valid_map (p \<cdot> A)" 
  and p_dom : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.dom (p \<cdot> A) = ob V \<cdot> A \<times>\<times> ob V \<cdot> A" 
  and p_cod : "\<And>A. A \<in> opens (space V) \<Longrightarrow> Poset.cod (p \<cdot> A) = ob V \<cdot> A" 
  and s_valid : "Function.valid_map s" 
  and s_valid_val : "\<And>A. A \<in> opens (space V') \<Longrightarrow> Poset.valid_map (s \<cdot> A)" 
  and s_dom : "\<And>A. A \<in> opens (space V') \<Longrightarrow> Poset.dom (s \<cdot> A) = ob V' \<cdot> A \<times>\<times> ob V' \<cdot> A" 
  and s_cod : "\<And>A. A \<in> opens (space V') \<Longrightarrow> Poset.cod (s \<cdot> A) = ob V' \<cdot> A" 
  and local_weak_exchange : "\<And> A a b c d. A \<in> opens (space V) \<Longrightarrow> a \<in> local_elems V A
 \<Longrightarrow> b \<in> local_elems V A \<Longrightarrow> c \<in> local_elems V A \<Longrightarrow> d \<in> local_elems V A 
 \<Longrightarrow> local_le V A 
      (A, (s \<cdot> A \<star> (p \<cdot> A \<star> (e a, e b), p \<cdot> A \<star> (e c, e d)))) 
      (A, (p \<cdot> A \<star> (s \<cdot> A \<star> (e a, e c), s \<cdot> A \<star> (e b, e d))))"
  and par : "comb V = par" and seq : "comb V' = seq"
shows "\<And>a b c d. a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow> d \<in> elems V \<Longrightarrow>
                         le V (seq (par a b) (par c d)) (par (seq a c) (seq b d))"
proof -
  fix a b c x
  assume a_el : "a \<in> elems V"
  assume b_el : "b \<in> elems V"
  assume c_el : "c \<in> elems V"
  assume x_el : "x \<in> elems V"

  define "U" where "U = d a \<union> d b \<union> d c \<union> d x" 

  have "U \<in> opens (space V)"
    by (metis Prealgebra.valid_space U_def V_valid a_el b_el c_el d_elem_is_open valid_prealgebra valid_union2 x_el)
  moreover have space_same : "space V = space V'"
    by (simp add: V_V'_prealg)
  moreover have elems_same : "elems V = elems V'"
    by (metis V'_valid V_valid V_V'_prealg valid_gc_poset)
  moreover have local_elems_same : "\<And> A . local_elems V A = local_elems V' A"
    using V_V'_prealg by presburger
  moreover have ext_is_ext': "\<And> A b . b \<in> elems V \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> d b \<subseteq> A \<Longrightarrow> ext V A b = ext V' A b" 
  proof -
    fix A b
    assume "b \<in> elems V"
    assume "A \<in> opens (space V)"
    assume "d b \<subseteq> A"

    have "local_le V (d b) (res V (d b) (ext V A b)) b" using galois_insertion [where ?V=V and ?A=A and ?b=b]
      by (metis V_valid \<open>A \<in> opens (OVA.space V)\<close> \<open>b \<in> OVA.elems V\<close> \<open>d b \<subseteq> A\<close> res_functorial_id valid_le valid_poset valid_reflexivity valid_semigroup)
    moreover have lhs: "local_le V A (ext V A b) (ext V' A b)"
      by (smt (verit, best) OVA.le_eq_local_le V'_valid V_V'_prealg V_valid \<open>A \<in> opens (OVA.space V)\<close> \<open>b \<in> OVA.elems V\<close> \<open>d b \<subseteq> A\<close> d_elem_is_open d_ext ext_elem galois_insertion id_le_res res_ext_adjunction valid_gc_poset valid_le)
    moreover have "local_le V' (d b) (res V' (d b) (ext V' A b)) b" using galois_insertion [where ?V=V' and ?A=A and ?b=b]
      by (metis OVA.valid_welldefined V'_valid V_V'_prealg \<open>A \<in> opens (OVA.space V)\<close> \<open>b \<in> OVA.elems V\<close> \<open>d b \<subseteq> A\<close> elems_same res_functorial_id valid_le valid_poset valid_reflexivity)
    moreover have rhs : "local_le V' A (ext V' A b) (ext V A b)"
      by (smt (verit, ccfv_threshold) OVA.le_eq_local_le V'_valid V_V'_prealg V_valid \<open>A \<in> opens (OVA.space V)\<close> \<open>b \<in> OVA.elems V\<close> \<open>d b \<subseteq> A\<close> d_elem_is_open d_ext ext_elem galois_insertion id_le_res res_ext_adjunction valid_gc_poset valid_le) 
    moreover have rhs' : "local_le V A (ext V' A b) (ext V A b)"
      by (metis V_V'_prealg local_le_def rhs) 
    ultimately show "ext V A b = ext V' A b"
      by (smt (verit) V'_valid V_V'_prealg V_valid \<open>A \<in> opens (OVA.space V)\<close> \<open>b \<in> OVA.elems V\<close> \<open>d b \<subseteq> A\<close> d_ext e_ext elems_same local_le_def prod.expand valid_antisymmetry valid_ob valid_prealgebra)
  qed

  moreover have "d (par a b) = d a \<union> d b"
    using a_el assms(1) b_el d_ext_local by blast
  moreover have "d (par c x) = d c \<union> d x"
    using c_el x_el assms(1) d_ext_local by blast  
  moreover have "d (seq a c) = d a \<union> d c"
    using a_el c_el d_ext_local seq_def elems_same
    by blast 
  moreover have "d (seq b x) = d b \<union> d x" 
    using b_el x_el d_ext_local seq_def elems_same by blast 
  moreover have "par a b \<in> elems V" using par_def ext_local_elem [where ?V=V and ?a=a and ?b=b and ?f=p]
    using V_valid a_el b_el p_cod p_dom p_valid p_valid_val by fastforce
  moreover have "par c x \<in> elems V" using par_def ext_local_elem [where ?V=V and ?a=c and ?b=x and ?f=p]
    using V_valid c_el p_cod p_dom p_valid p_valid_val x_el by fastforce
  moreover have "seq a c \<in> elems V" using seq_def ext_local_elem [where ?V=V' and ?a=a and ?b=c and ?f=s]
    using V'_valid a_el c_el s_cod s_dom s_valid s_valid_val elems_same by fastforce
  moreover have "seq b x \<in> elems V" using seq_def ext_local_elem [where ?V=V and ?a=b and ?b=x and ?f=s]
    using V'_valid b_el x_el s_cod s_dom s_valid s_valid_val elems_same
    by (metis (no_types, lifting) comb_is_element seq) 

  define "delta" where "delta = \<lparr> Function.cod = UNIV, func = { (A, e (neut V A)) | A . A \<in> opens (space V)} \<rparr>"
  define "epsilon" where "epsilon = \<lparr> Function.cod = UNIV, func = { (A, e (neut V' A)) | A . A \<in> opens (space V')} \<rparr>"

  moreover have delta_valid : "Function.valid_map delta" unfolding delta_def Function.valid_map_def
    by fastforce
  moreover have epsilon_valid : "Function.valid_map epsilon" unfolding epsilon_def Function.valid_map_def
    by fastforce

  moreover have assoc_par : "\<And> a b c . a \<in> elems V \<Longrightarrow> b \<in> elems V \<Longrightarrow> c \<in> elems V \<Longrightarrow> 
    par (par a b) c = par a (par b c)"
    using V_valid par valid_comb_associative by fastforce
  moreover have assoc_seq : "\<And> a b c . a \<in> elems V' \<Longrightarrow> b \<in> elems V' \<Longrightarrow> c \<in> elems V' \<Longrightarrow> 
    seq (seq a b) c = seq a (seq b c)"
      using V'_valid seq valid_comb_associative by fastforce

  moreover have units_el_par : "\<And>A. A \<in> opens (space V) \<Longrightarrow> delta \<cdot> A \<in> el (ob V \<cdot> A)" unfolding
      delta_def
    using Function.fun_app_iff V_valid delta_def delta_valid neutral_local_element by fastforce
  moreover have units_el_seq : "\<And>A. A \<in> opens (space V') \<Longrightarrow> epsilon \<cdot> A \<in> el (ob V' \<cdot> A)" unfolding
      epsilon_def
    using Function.fun_app_iff V'_valid epsilon_def epsilon_valid neutral_local_element by fastforce

  moreover have units_par : "\<And>A a. A \<in> opens (space V) \<Longrightarrow> a \<in> el (ob V \<cdot> A) \<Longrightarrow> p \<cdot> A \<star> (delta \<cdot> A, a)
    = a \<and> p \<cdot> A \<star> (a, delta \<cdot> A) = a" unfolding delta_def
  proof -
    fix A a
    assume A_open : "A \<in> opens (OVA.space V) "
    assume a_el : "a \<in> el (ob V \<cdot> A)"

    have "(A, a) = par (neut V A) (A, a)"
      by (metis A_open V_valid a_el fst_conv local_elem_gc par valid_gc_poset valid_neutral_law_left valid_prealgebra) 
    moreover have "... = (A, p \<cdot> A \<star> (e (ext V A (neut V A)), e (ext V A (A, a))))"
      by (smt (verit, ccfv_threshold) A_open V_valid \<open>(A, a) = par (neut V A) (A, a)\<close> a_el e_ext_local fst_conv neutral_is_element par par_def raw_elem_is_elem snd_conv valid_domain_law)                      
    moreover have "... = (A, p \<cdot> A \<star> (e (neut V A), a))"
      using A_open V_valid a_el ext_functorial_id neutral_is_element raw_elem_is_elem by fastforce 
    moreover have "... = (A, p \<cdot> A \<star> (delta \<cdot> A, a))"
      using A_open Function.fun_app_iff delta_def delta_valid by fastforce
    ultimately have "a = p \<cdot> A \<star> (delta \<cdot> A, a)"
      by (metis prod.inject) 

    have "(A, a) = par (A, a) (neut V A)"
      by (metis A_open V_valid a_el fst_conv local_elem_gc par valid_gc_poset valid_neutral_law_right valid_prealgebra)
    moreover have "... = (A, p \<cdot> A \<star> (e (ext V A (A, a)), e (ext V A (neut V A))))"
      by (smt (verit) A_open V_valid a_el calculation e_ext_local fst_conv neutral_is_element par par_def raw_elem_is_elem snd_conv valid_domain_law) 
    moreover have "... = (A, p \<cdot> A \<star> (a, e (neut V A)))"
      using A_open V_valid a_el ext_functorial_id neutral_is_element raw_elem_is_elem by fastforce 
    moreover have "... = (A, p \<cdot> A \<star> (a, delta \<cdot> A))"
      using A_open Function.fun_app_iff delta_def delta_valid by fastforce
    ultimately have "a = p \<cdot> A \<star> (a, delta \<cdot> A)"
      by (metis prod.inject) 

    show "p \<cdot> A \<star> (\<lparr>Function.cod = UNIV, func = {(A, e (neut V A)) |A. A \<in> opens (OVA.space V)}\<rparr> \<cdot> A, a) = a \<and>
           p \<cdot> A \<star> (a, \<lparr>Function.cod = UNIV, func = {(A, e (neut V A)) |A. A \<in> opens (OVA.space V)}\<rparr>
 \<cdot> A) = a"
      using \<open>a = p \<cdot> A \<star> (a, delta \<cdot> A)\<close> \<open>a = p \<cdot> A \<star> (delta \<cdot> A, a)\<close> delta_def by force 
  qed

  moreover have units_seq : "\<And>A a. A \<in> opens (space V') \<Longrightarrow> a \<in> el (ob V' \<cdot> A) \<Longrightarrow> s \<cdot> A \<star> (epsilon \<cdot> A, a)
    = a \<and> s \<cdot> A \<star> (a, epsilon \<cdot> A) = a" unfolding epsilon_def
  proof -
    fix A a
    assume A_open : "A \<in> opens (space V') "
    assume a_el : "a \<in> el (ob V' \<cdot> A)"

    have "(A, a) = seq (neut V' A) (A, a)"
      by (metis A_open V'_valid a_el fst_conv local_elem_gc seq valid_gc_poset valid_neutral_law_left valid_prealgebra) 
    moreover have "... = (A, s \<cdot> A \<star> (e (ext V' A (neut V' A)), e (ext V' A (A, a))))"
      by (smt (verit, ccfv_threshold) A_open V'_valid \<open>(A, a) = seq (neut V' A) (A, a)\<close> a_el e_ext_local fst_conv neutral_is_element seq seq_def raw_elem_is_elem snd_conv valid_domain_law)                      
    moreover have "... = (A, s \<cdot> A \<star> (e (neut V' A), a))"
      using A_open V'_valid a_el ext_functorial_id neutral_is_element raw_elem_is_elem by fastforce 
    moreover have "... = (A, s \<cdot> A \<star> (epsilon \<cdot> A, a))"
      using A_open Function.fun_app_iff epsilon_def epsilon_valid by fastforce
    ultimately have "a = s \<cdot> A \<star> (epsilon \<cdot> A, a)"
      by (metis prod.inject) 

    have "(A, a) = seq (A, a) (neut V' A)"
      by (metis A_open V'_valid a_el fst_conv local_elem_gc seq valid_gc_poset valid_neutral_law_right valid_prealgebra)
    moreover have "... = (A, s \<cdot> A \<star> (e (ext V' A (A, a)), e (ext V' A (neut V' A))))"
      by (smt (verit) A_open V'_valid a_el calculation e_ext_local fst_conv neutral_is_element seq seq_def raw_elem_is_elem snd_conv valid_domain_law) 
    moreover have "... = (A, s \<cdot> A \<star> (a, e (neut V' A)))"
      using A_open V'_valid a_el ext_functorial_id neutral_is_element raw_elem_is_elem by fastforce 
    moreover have "... = (A, s \<cdot> A \<star> (a, epsilon \<cdot> A))"
      using A_open Function.fun_app_iff epsilon_def epsilon_valid by fastforce
    ultimately have "a = s \<cdot> A \<star> (a, epsilon \<cdot> A)"
      by (metis prod.inject) 

    show "s \<cdot> A \<star> (\<lparr>Function.cod = UNIV, func = {(A, e (neut V' A)) |A. A \<in> opens (space V')}\<rparr> \<cdot> A, a) = a \<and>
           s \<cdot> A \<star> (a, \<lparr>Function.cod = UNIV, func = {(A, e (neut V' A)) |A. A \<in> opens (space V')}\<rparr>
 \<cdot> A) = a"
      using \<open>a = s \<cdot> A \<star> (a, epsilon \<cdot> A)\<close> \<open>a = s \<cdot> A \<star> (epsilon \<cdot> A, a)\<close> epsilon_def by force 
  qed

  moreover have local_ext_comm_par :  "\<And>A B b b'. B \<in> opens (space V) \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V \<cdot> B) \<Longrightarrow> b' \<in> el (ob V \<cdot> B)
  \<Longrightarrow> ext V A (B, p \<cdot> B \<star> (b, b')) = (A, p \<cdot> A \<star> (e (ext V A (B, b)), e (ext V A (B, b'))))" 
    using local_assoc_units_imp_ext_comm [where ?V=V and ?f=p and ?i=delta] 
        V_valid  assoc_par units_el_par units_par p_valid p_valid_val p_dom p_cod
        par_def
    by blast  

  moreover have local_ext_comm_seq :  "\<And>A B b b'. B \<in> opens (space V') \<Longrightarrow> A \<in> opens (space V') \<Longrightarrow> B \<subseteq> A \<Longrightarrow>
  b \<in> el (ob V' \<cdot> B) \<Longrightarrow> b' \<in> el (ob V' \<cdot> B)
  \<Longrightarrow> ext V' A (B, s \<cdot> B \<star> (b, b')) = (A, s \<cdot> A \<star> (e (ext V' A (B, b)), e (ext V' A (B, b'))))" (* use
 `apply (subst local_assoc_units_imp_ext_comm)` to check that the goal actually matches *)
    using local_assoc_units_imp_ext_comm [where ?V=V' and ?f=s and ?i=epsilon] 
        V'_valid  assoc_seq units_el_seq units_seq s_valid s_valid_val s_dom s_cod
        seq_def
    by blast  

  moreover have a0: "seq (par a b) (par c x) =
        (U, (s \<cdot> U \<star> (e (ext V' U (par a b)), e (ext V' U (par c x)))))" (is "?L0 = ?R0")
    using U_def seq_def e_ext_local [where ?V=V' and ?f=s and ?a="par a b" and ?b="par c x"]
    by (metis (no_types, lifting) calculation(11) calculation(7) calculation(6) calculation(10) d_ext_local elems_same prod.collapse sup_assoc)

  moreover have p0 : "par a b = (d a \<union> d b,  p \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union>
    d b) b)))" using U_def par_def e_ext_local [where ?V=V and ?f=p and ?a=a and ?b=b]
    by (metis a_el b_el calculation(6) prod.collapse)

  moreover have p1 : "par c x = (d c \<union> d x, p \<cdot> (d c \<union> d x) \<star> (e (ext V (d c \<union> d x) c), e (ext V (d c \<union> d x) x)))" 
    using U_def par_def e_ext_local [where ?V=V and ?f=p and ?a=c and ?b=x]
    by (metis c_el calculation(7) surjective_pairing x_el)

  moreover have a1: "?R0 =
        (U, s \<cdot> U \<star> 
       (e (ext V' U (d a \<union> d b, p \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b)))), 
        e (ext V' U (d c \<union> d x, p \<cdot> (d c \<union> d x) \<star> (e (ext V (d c \<union> d x) c), e (ext V (d c \<union> d x) x))))))"  (is "?L1 = ?R1")
     using p0 p1
     by presburger

   moreover have p3: "d a \<union> d b \<in> opens (OVA.space V) \<and>  U \<in> opens (OVA.space V) \<and> d a \<union> d b \<subseteq> U"
     by (metis Prealgebra.valid_space U_def Un_subset_iff V_valid c_el calculation(6) calculation(10) d_elem_is_open sup_ge1 valid_prealgebra valid_union2 x_el)

   moreover have p4: "e (ext V (d a \<union> d b) a) \<in> el (ob V \<cdot> (d a \<union> d b)) \<and> e (ext V (d a \<union> d b) b) \<in> el
     (ob V \<cdot> (d a \<union> d b))"
     by (meson V_valid a_el b_el e_ext inf_sup_ord(3) p3 sup_ge2)  

   moreover have p5 : "ext V U (d a \<union> d b, p \<cdot> (d a \<union> d b) \<star> (e (ext V (d a \<union> d b) a), e (ext V (d a \<union> d b) b)))
   = (U, p \<cdot> U \<star> (e (ext V U (ext V (d a \<union> d b) a)), e (ext V U (ext V (d a \<union> d b) b))))"
     using p3 p4 local_ext_comm_par [where ?A=U and ?B="d a \<union> d b" and ?b="e (ext V (d a \<union> d b) a)" and ?b'="e
    (ext V (d a \<union> d b) b)"] ext_is_ext'
     by (metis Un_upper1 Un_upper2 V_valid a_el b_el d_ext prod.collapse)

   moreover have p6: "d c \<union> d x \<in> opens (OVA.space V) \<and> U \<in> opens (OVA.space V) \<and> d c \<union> d x \<subseteq> U"
     by (metis (no_types, opaque_lifting) U_def V_valid calculation(11) calculation(7) d_elem_is_open p3 sup_commute sup_ge2 sup_left_commute) 

   moreover have p7 : "e (ext V (d c \<union> d x) c) \<in> el (ob V \<cdot> (d c \<union> d x)) \<and> e (ext V (d c \<union> d x)
 x) \<in> el (ob V \<cdot> (d c \<union> d x))"
     by (meson V_valid c_el e_ext p6 sup.cobounded2 sup_ge1 x_el) 

   moreover have p8 : "ext V U (d c \<union> d x, p \<cdot> (d c \<union> d x) \<star> (e (ext V (d c \<union> d x) c), e (ext V (d c \<union> d x) x)))
   = (U, p \<cdot> U \<star> (e (ext V U (ext V (d c \<union> d x) c)), e (ext V U (ext V (d c \<union> d x) x))))"
     using p6 p7 local_ext_comm_par [where ?A=U and ?B="d c \<union> d x" and ?b="e (ext V (d c \<union> d x) c)" and ?b'="e
    (ext V (d c \<union> d x) x)"] ext_is_ext'
     by (metis Un_upper1 Un_upper2 V_valid c_el x_el d_ext prod.collapse)

   moreover have a2: "?R1 =
        (U, s \<cdot> U \<star> 
       (p \<cdot> U \<star> (e (ext V U (ext V (d a \<union> d b) a)), e (ext V U (ext V (d a \<union> d b) b))), 
        p \<cdot> U \<star> (e (ext V U (ext V (d c \<union> d x) c)), e (ext V U (ext V (d c \<union> d x) x)))))"  (is "?L2 = ?R2")
     using p5 p8 ext_is_ext'
     using calculation(10) calculation(11) p0 p1 p3 p6 by fastforce

   moreover have a3: "... =
        (U, s \<cdot> U \<star> 
       (p \<cdot> U \<star> (e (ext V U a), e (ext V U b)), 
        p \<cdot> U \<star> (e (ext V U c), e (ext V U x))))" (is "?L3 = ?R3")
     using ext_functorial_trans [where ?V=V] V_valid a_el b_el c_el p3 p6 x_el by auto

   moreover have p10: "ext V U a \<in> local_elems V U" using a_el U_def elem_is_local_elem [where ?V=V and
         ?a="ext V U a"] ext_elem [where ?V=V and ?A=U and ?b=a]
     using V_valid p3 by fastforce 

   moreover have p11: "ext V U b \<in> local_elems V U" using b_el U_def elem_is_local_elem [where ?V=V and
         ?a="ext V U b"] ext_elem [where ?V=V and ?A=U and ?b=b]
     using V_valid p3 by fastforce 

   moreover have p12: "ext V U c \<in> local_elems V U" using c_el U_def elem_is_local_elem [where ?V=V and
         ?a="ext V U c"] ext_elem [where ?V=V and ?A=U and ?b=c]
     using V_valid p6 by fastforce

   moreover have p13: "ext V U x \<in> local_elems V U" using x_el U_def elem_is_local_elem [where ?V=V and
         ?a="ext V U x"] ext_elem [where ?V=V and ?A=U and ?b=x]
     using V_valid p6 by fastforce 

   moreover have a4 : "local_le V U
      (U, (s \<cdot> U \<star> (p \<cdot> U \<star> (e (ext V U a), e (ext V U b)), p \<cdot> U \<star> (e (ext V U c), e (ext V U x))))) 
      (U, (p \<cdot> U \<star> (s \<cdot> U \<star> (e (ext V U a), e (ext V U c)), s \<cdot> U \<star> (e (ext V U b), e (ext V U x)))))" 
     using local_weak_exchange [where ?A=U and ?a="ext V U a" and ?b="ext V U b" and ?c="ext
     V U c" and ?d="ext V U x"] p10 p11 p12 p13
     using calculation(1) by blast

   moreover have s1: "ext V U (ext V (d a \<union> d c) a) = ext V U a"
     by (metis Un_subset_iff V_valid a_el calculation(12) calculation(8) d_elem_is_open ext_functorial_trans p3 p6 sup_ge1)
   moreover have s2: "ext V U (ext V (d a \<union> d c) c) = ext V U c"
     by (metis Un_subset_iff V_valid c_el calculation(12) calculation(8) d_elem_is_open ext_functorial_trans p3 p6 sup_ge2) 
   moreover have s3: "ext V U (ext V (d b \<union> d x) b) = ext V U b"
     by (meson Prealgebra.valid_space Un_upper1 V_valid b_el d_elem_is_open ext_functorial_trans le_sup_iff p3 p6 valid_prealgebra valid_union2 x_el) 
   moreover have s4: "ext V U (ext V (d b \<union> d x) x) = ext V U x"
     by (meson Prealgebra.valid_space Un_subset_iff V_valid b_el d_elem_is_open ext_functorial_trans p3 p6 sup_ge2 valid_prealgebra valid_union2 x_el)

   moreover have a5: "(U, (p \<cdot> U \<star> (s \<cdot> U \<star> (e (ext V U a), e (ext V U c)), s \<cdot> U \<star> (e (ext V U b), e (ext V U x)))))
      = (U, (p \<cdot> U \<star> (s \<cdot> U \<star> (e (ext V U (ext V (d a \<union> d c) a)), e (ext V U (ext V (d a \<union> d c) c))), s \<cdot> U \<star> (e (ext V U (ext V (d b \<union> d x) b)), e (ext V U
 (ext V (d b \<union> d x) x))))))" (is "?L4 = ?R4")
     using s1 s2 s3 s4
     by presburger 

   moreover have s5: "d a \<union> d c \<in> opens (space V') \<and> U \<in> opens (space V') \<and>  d a \<union> d c \<subseteq> U"
     by (metis Un_subset_iff V_V'_prealg V_valid calculation(12) calculation(8) d_elem_is_open p3 p6)

   moreover have s6: "e (ext V (d a \<union> d c) a) \<in> el (ob V' \<cdot> (d a \<union> d c)) \<and> e (ext V (d a \<union> d c) c) \<in>
 el (ob V' \<cdot> (d a \<union> d c))"
     by (metis V_V'_prealg V_valid a_el c_el calculation(46) e_ext sup_ge1 sup_ge2) 

   moreover have s7: "(U, s \<cdot> U \<star> (e (ext V U (ext V (d a \<union> d c) a)), e (ext V U (ext V (d a \<union> d c) c))))
    = ext V' U (d a \<union> d c, s \<cdot> (d a \<union> d c) \<star> (e (ext V (d a \<union> d c) a), e (ext V (d a \<union> d c) c)))"
     using local_ext_comm_seq [where ?A=U and ?B="d a \<union> d c" and ?b="e (ext V (d a \<union> d c) a)" and
         ?b'="e (ext V (d a \<union> d c) c)"] s5 s6 ext_is_ext'
     by (metis V_V'_prealg V_valid a_el c_el d_ext ext_elem prod.collapse sup_ge1 sup_ge2) 

   moreover have s8: "d b \<union> d x \<in> opens (space V') \<and> U \<in> opens (space V') \<and>  d b \<union> d x \<subseteq> U"
     by (metis Un_subset_iff V'_valid \<open>seq b x \<in> OVA.elems V\<close> calculation(9) d_elem_is_open elems_same p3 p6 s5)

   moreover have s9: "e (ext V (d b \<union> d x) b) \<in> el (ob V' \<cdot> (d b \<union> d x)) \<and> e (ext V (d b \<union> d x) x) \<in>
 el (ob V' \<cdot> (d b \<union> d x))"
     by (metis V_V'_prealg V_valid b_el e_ext s8 sup_ge1 sup_ge2 x_el)

   moreover have s10: "(U, s \<cdot> U \<star> (e (ext V U (ext V (d b \<union> d x) b)), e (ext V U (ext V (d b \<union> d x) x))))
    = ext V' U (d b \<union> d x, s \<cdot> (d b \<union> d x) \<star> (e (ext V (d b \<union> d x) b), e (ext V (d b \<union> d x) x)))"
     using local_ext_comm_seq [where ?A=U and ?B="d b \<union> d x" and ?b="e (ext V (d b \<union> d x) b)" and
         ?b'="e (ext V (d b \<union> d x) x)"] s5 s6 ext_is_ext'
     by (metis V_V'_prealg V_valid b_el d_ext ext_elem prod.collapse s8 s9 sup_ge1 sup_ge2 x_el)

   moreover have a6: "?R4 = (U, (p \<cdot> U \<star> 
  (e (ext V' U (d a \<union> d c, s \<cdot> (d a \<union> d c) \<star> (e (ext V (d a \<union> d c) a), e (ext V (d a \<union> d c) c)))), 
   e (ext V' U (d b \<union> d x, s \<cdot> (d b \<union> d x) \<star> (e (ext V (d b \<union> d x) b), e (ext V (d b \<union> d x)
     x)))))))" (is "?L5 = ?R5")
     using s7 s10
     by (metis snd_conv) 

   moreover have a7: "... = (U, (p \<cdot> U \<star> 
  (e (ext V' U (seq a c)), 
   e (ext V' U (seq b x)))))" (is "?L6 = ?R6")
     using seq_def e_ext_local [where ?V=V']
     by (smt (z3) UnCI a_el b_el c_el calculation(2) calculation(46) calculation(49) d_ext_local elems_same ext_is_ext' prod.collapse subsetI x_el)

   moreover have a8: "... = (U, (p \<cdot> U \<star> 
  (e (ext V U (seq a c)), 
   e (ext V U (seq b x)))))" (is "?L7 = ?R7")
     using \<open>seq b x \<in> OVA.elems V\<close> calculation(12) calculation(8) calculation(9) ext_is_ext' p3 s5 s8 by presburger 

   moreover have s11 : "seq a c \<in> elems V \<and> seq b x \<in> elems V"
     using \<open>seq b x \<in> OVA.elems V\<close> calculation(12) by linarith 

   moreover have s12 : "U = d (seq a c) \<union> d (seq b x)"
     using U_def calculation(8) calculation(9) by auto 

   moreover have a9: "?R7 = par (seq a c) (seq b x)" using s11 s12 par_def e_ext_local [where ?V=V and ?f=p and ?a="seq a c" and ?b="seq b x"]
     by (metis d_ext_local prod.collapse) 

   show "le V (seq (par a b) (par c x)) (par (seq a c) (seq b x))"
     using a1 a2 a3 a4 a5 a6 a7 a8 local_le_eq_le [where ?V=V and ?A=U]
     by (smt (z3) OVA.le_eq_local_le V'_valid V_valid a9 assms(15) calculation(10) calculation(11) calculation(24) calculation(28) calculation(55) comb_is_element elems_same fst_conv seq) 
 qed


end
