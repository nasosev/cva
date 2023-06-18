theory OVA
  imports Main Presheaf Semigroup Grothendieck Poset
begin

type_synonym ('A, 'a) Valuation = "('A set \<times> 'a)"

record ('A, 'a) OVA =
  presheaf :: "('A, 'a) Presheaf"
  neutral :: "('A, unit, 'a) PresheafMap"
  ordered_semigroup :: "(('A, 'a) Valuation) Semigroup"

abbreviation comb :: "('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"comb V a b \<equiv> (Semigroup.mult (ordered_semigroup V)) $$ (a, b)"

(*
abbreviation comb_V :: "('A, 'a) Valuation \<Rightarrow> ('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" ("_ \<otimes>\<langle>_\<rangle> _") where
"comb_V a V b \<equiv> (Semigroup.mult (ordered_semigroup V)) $$ (a, b)"
*)

abbreviation neut :: "('A, 'a) OVA \<Rightarrow> 'A set \<Rightarrow> ('A, 'a) Valuation" where
"neut V A \<equiv> (A, (Presheaf.nat (neutral V) $ A) $$ ())"

abbreviation poset :: "('A,'a) OVA \<Rightarrow> (('A, 'a) Valuation) Poset" where
"poset V \<equiv> Semigroup.poset (ordered_semigroup V)"

abbreviation (input) gle :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle V a b \<equiv> Poset.le (Semigroup.poset (ordered_semigroup V)) a b"

(*
abbreviation gle_V :: "('A, 'a) Valuation \<Rightarrow> ('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" ("_ \<preceq>\<langle>_\<rangle> _") where
"gle_V a V b \<equiv> Poset.le (Semigroup.poset (ordered_semigroup V)) a b"
*)

abbreviation (input) local_le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"local_le V A a b \<equiv> Poset.le (Presheaf.ob (presheaf V) $ A) (e a) (e b)"

abbreviation (input) space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space V \<equiv> Presheaf.space (presheaf V)"

abbreviation (input) elems :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V \<equiv> Poset.el (poset V)"

abbreviation (input) opens :: "('A,'a) OVA \<Rightarrow> 'A Open set" where
"opens V \<equiv> Space.opens (space V)"

abbreviation (input) inclusions :: "('A,'a) OVA \<Rightarrow> 'A Inclusion set" where
"inclusions V \<equiv> Space.inclusions (space V)"

abbreviation (input) local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems V A \<equiv> Poset.el (Presheaf.ob (presheaf V) $ A)"

definition gprj :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gprj V B a \<equiv> let i = (Space.make_inclusion (space V) B (d a)) in
  if B \<in> opens V \<and>  B \<subseteq> d a
  then (B, Presheaf.ar (presheaf V) $ i $$ (e a))
  else undefined"

definition gext :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gext V A b \<equiv> if A \<in> opens V \<and> d b \<subseteq> A then (comb V (neut V A) b) else undefined"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid V \<equiv>
    let
        \<Phi> = presheaf V;
        E = neutral V;
        \<epsilon> = neut V;
        T = space V;
        S = ordered_semigroup V;
        com = comb V;
        elems = elems V;
        pr = gprj V;

        welldefined = Presheaf.valid \<Phi>
                      \<and> Semigroup.valid S
                      \<and> Presheaf.valid_map E
                      \<and> T = Presheaf.map_space E
                      \<and> Presheaf.cod E = \<Phi>
                      \<and> Presheaf.dom E = Presheaf.terminal T
                      \<and> Semigroup.poset S = gc \<Phi>;

        domain_law = \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow> d (com a b) = d a \<union> d b;
        neutral_law_left = (\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> com (\<epsilon> A) a = a);
        neutral_law_right = (\<forall>A a. A \<in> opens V \<and> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> com a (\<epsilon> A) = a);
        comb_law_left = (\<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
             pr (d a) (com a b) = com a (pr (d a \<inter> d b) b));
        comb_law_right = (\<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
             pr (d b) (com a b) = com (pr (d a \<inter> d b) a) b)
    in
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"

(* LEMMAS *)

lemma validI :
  fixes V :: "('A,'a) OVA"
  defines "\<Phi> \<equiv> presheaf V"
  defines "E \<equiv> neutral V"
  defines "\<epsilon> \<equiv> neut V"
  defines "T \<equiv> space V"
  defines "S \<equiv> ordered_semigroup V"
  defines "com \<equiv> comb V"
  defines "elem \<equiv> elems V"
  defines "pr \<equiv> gprj V"
  assumes welldefined : "Presheaf.valid \<Phi> \<and> Semigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> Semigroup.poset S = gc \<Phi>"
  assumes domain_law : " \<forall> a b . a \<in> elem \<longrightarrow> b \<in> elem \<longrightarrow> d (com a b) = d a \<union> d b"
  assumes neutral_law_left : "( \<forall> A a . A \<in> opens V \<longrightarrow> a \<in> elem \<longrightarrow> d a = A \<longrightarrow> com (\<epsilon> A) a = a)"
  assumes neutral_law_right : "(\<forall> A a .A \<in> opens V \<and> a \<in> elem \<longrightarrow> d a = A \<longrightarrow> com a (\<epsilon> A) = a)"
  assumes comb_law_left : "(\<forall> a b . a \<in> elem \<longrightarrow> b \<in> elem \<longrightarrow>
             pr (d a) (com a b) = com a (pr (d a \<inter> d b) b))"
  assumes comb_law_right : "(\<forall> a b . a \<in> elem \<longrightarrow> b \<in> elem \<longrightarrow>
              pr (d b) (com a b) = com (pr (d a \<inter> d b) a) b)"
  shows "valid V"
  unfolding valid_def
  apply (simp_all add: Let_def)
  apply safe
  using \<Phi>_def welldefined apply blast
  using S_def welldefined apply blast
  using E_def welldefined apply blast
  using E_def T_def welldefined apply fastforce
  using E_def \<Phi>_def welldefined apply blast
  using E_def T_def welldefined apply fastforce
  using S_def \<Phi>_def welldefined apply fastforce
  using com_def domain_law elem_def apply simp
  using com_def domain_law elem_def apply simp
  using com_def domain_law elem_def apply simp
  using T_def \<epsilon>_def com_def elem_def neutral_law_left apply simp
  using T_def \<epsilon>_def com_def elem_def neutral_law_right apply simp
  using comb_law_left elem_def com_def pr_def apply simp
  using comb_law_right elem_def com_def pr_def by simp

lemma valid_welldefined  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<Phi> = presheaf V; E = neutral V; \<epsilon> = neut V; T = space V; S = ordered_semigroup V in
    Presheaf.valid \<Phi> \<and> Semigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> Semigroup.poset S = gc \<Phi>"
  by (simp add: valid_def Let_def)

lemma valid_presheaf :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> Presheaf.valid (presheaf V)"
  by (simp add: valid_def Let_def)

lemma valid_semigroup :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> Semigroup.valid (ordered_semigroup V)"
  by (simp add: valid_def Let_def)

lemma valid_neutral :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> Presheaf.valid_map (neutral V)"
  by (simp add: valid_def Let_def)

lemma valid_space :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> space V = Presheaf.map_space (neutral V)"
  by (simp add: valid_def Let_def)

lemma valid_codomain :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> Presheaf.cod (neutral V) = presheaf V"
  by (simp add: valid_def Let_def)

lemma valid_domain :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> Presheaf.dom (neutral V) = Presheaf.terminal (space V)"
  by (simp add: valid_def Let_def)

lemma valid_gc_poset :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> Semigroup.poset (ordered_semigroup V) = gc (presheaf V)"
  by (meson OVA.valid_welldefined)

lemma valid_gle :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  assumes A_open : "A \<in> opens V" and B_open : "B \<in> opens V"
  assumes a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  assumes a_dom : "d a = A" and b_dom : "d b = B"
  assumes a_le_b : "gle V a b"
  shows "B \<subseteq> A \<and> local_le V B (gprj V B a) b"
proof standard
  show "B \<subseteq> A"
    using V_valid a_dom a_elem a_le_b b_dom b_elem d_antitone valid_gc_poset valid_presheaf by blast 
next 
  define "i" where "i = Space.make_inclusion (space V) B A" 
  define "pr_B" where "pr_B = Presheaf.ar (presheaf V) $ i" 
  define "ea_B" where "ea_B = pr_B $$ (e a)" 
  define "\<Phi>A" where "\<Phi>A = Presheaf.ob (presheaf V) $ A"
  define "\<Phi>B" where "\<Phi>B = Presheaf.ob (presheaf V) $ B"
  have "e a \<in> Poset.el \<Phi>A"
    by (metis V_valid \<Phi>A_def a_dom a_elem gc_elem_local valid_gc_poset valid_presheaf)  
  moreover have  B_le_A: "B \<subseteq> A"
    using V_valid a_dom a_elem a_le_b b_dom b_elem d_antitone valid_gc_poset valid_presheaf by blast  
  moreover have "i \<in> inclusions V" using B_le_A V_valid
    by (metis (mono_tags, lifting) A_open B_open Inclusion.select_convs(1) Presheaf.valid_space i_def inclusions_def make_inclusion_def mem_Collect_eq valid_make_inclusion valid_presheaf)
  moreover have psh_valid : "Presheaf.valid (presheaf V)"
    by (simp add: V_valid valid_presheaf) 
  moreover have "Poset.valid_map pr_B"
    using calculation(3) calculation(4) pr_B_def valid_ar by blast 
  moreover have "Poset.dom pr_B = \<Phi>A \<and> Poset.cod pr_B = \<Phi>B"
    by (metis Inclusion.simps(2) Inclusion.simps(3) \<Phi>A_def \<Phi>B_def calculation(3) calculation(4) cod_proj dom_proj i_def make_inclusion_def pr_B_def) 
  moreover have "ea_B \<in> Poset.el \<Phi>B"
    by (metis Poset.fun_app2 calculation(1) calculation(5) calculation(6) ea_B_def)
  moreover have "e b \<in> Poset.el \<Phi>B"
    by (metis V_valid \<Phi>B_def b_dom b_elem calculation(4) gc_elem_local valid_gc_poset) 
  moreover have "le (poset V) a b"
    using a_le_b by blast 
  moreover have "le \<Phi>B ea_B (e b)"  using psh_valid a_elem b_elem a_le_b \<Phi>B_def ea_B_def pr_B_def 
i_def V_valid a_dom b_dom valid_gc_poset valid_gc_le_unwrap [where ?Aa = a and ?Bb = b and ?\<Phi> = "presheaf V"]
    by force   (* or use "apply (rule valid_gc_le_unwrap)" to apply the rule explicitly *)
  show "local_le V B (gprj V B a) b"
    by (metis B_le_A B_open \<Phi>B_def \<open>le \<Phi>B ea_B (e b)\<close> a_dom ea_B_def eq_snd_iff gprj_def i_def pr_B_def) 
qed

lemma valid_domain_law  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow>
    \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> d (comb V a b) = d a \<union> d b"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_left  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<epsilon> = neut V; com = comb V; elems = elems V in
    \<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> com (\<epsilon> A) a = a"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_right  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let  \<epsilon> = neut V; com = comb V; elems = elems V in
    \<forall>A a. A \<in> opens V \<and> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> com a (\<epsilon> A) = a"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_left  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<Phi> = presheaf V; T = space V; S = ordered_semigroup V; com = comb V; elems = elems V; pr = gprj V in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
      pr (d a) (com a b) = com a (pr (d a \<inter> d b) b)"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_right  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<Phi> = presheaf V; T = space V; S = ordered_semigroup V; com = comb V; elems = elems V; pr = gprj V in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
      pr (d b) (com a b) = com (pr (d a \<inter> d b) a) b"
  by (simp add: valid_def Let_def)

lemma neutral_is_element :
fixes V :: "('A,'a) OVA" and A :: "'A Open"
defines "\<epsilon>A \<equiv> neut V A"
assumes "valid V" and "A \<in> opens V"
shows "neut V A \<in> elems V"
proof -
   have "Poset.valid_map  (PresheafMap.nat (neutral V) $ A)"
     by (metis  OVA.valid_welldefined Presheaf.valid_map_welldefined assms(2) assms(3))
    moreover have "Poset.cod (PresheafMap.nat (neutral V) $ A) = (Presheaf.ob (presheaf V)) $ A"
      by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined assms(2) assms(3))
  moreover have "Presheaf.dom (neutral V) = Presheaf.terminal (space V)"
    by (meson OVA.valid_welldefined assms(2))
moreover have "(Presheaf.ob ( Presheaf.terminal  (space V))) $ A = Poset.discrete"
  by (metis Presheaf.Presheaf.select_convs(2) UNIV_I assms(3) const_app terminal_def)
  moreover have "Poset.dom  (PresheafMap.nat (neutral V) $ A) = Poset.discrete"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined assms(2) assms(3) calculation(4))
  moreover have "(PresheafMap.nat (neutral V) $ A $$ ()) \<in> Poset.el ((Presheaf.ob (presheaf V)) $ A)"
    by (metis OVA.valid_welldefined Poset.fun_app2 Presheaf.valid_welldefined UNIV_unit UNIV_witness assms(2) assms(3) calculation(1) calculation(2) calculation(4) calculation(5) singletonD terminal_value)
ultimately show ?thesis
  by (metis OVA.valid_welldefined assms(2) assms(3) local_elem_gc)
qed

lemma neutral_local_element :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"
  defines "\<epsilon>A \<equiv> neut V A"
  defines "\<epsilon> \<equiv> Presheaf.nat (neutral V)"
  defines "\<Phi>A \<equiv> Presheaf.ob (presheaf V) $ A"
  assumes V_valid : "valid V"
  and domain : "A \<in> opens V"
shows " e \<epsilon>A \<in> Poset.el \<Phi>A"
proof -
  have "Poset.valid_map (\<epsilon> $ A)"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined \<epsilon>_def domain V_valid)
  moreover have "Poset.cod (\<epsilon> $ A) = \<Phi>A"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined \<Phi>A_def \<epsilon>_def domain V_valid)
  moreover have "e \<epsilon>A =  (\<epsilon> $ A) $$ ()"
    by (simp add: \<epsilon>A_def \<epsilon>_def)
  moreover have "Poset.dom  (\<epsilon> $ A) = Presheaf.ob (Presheaf.terminal (space V)) $ A"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined \<epsilon>_def domain V_valid)
  moreover have "(Poset.dom (\<epsilon> $ A)) =  Poset.discrete" using Presheaf.terminal_def
    by (metis Presheaf.Presheaf.select_convs(2) UNIV_I calculation(4) const_app domain)
  moreover have "() \<in> Poset.el (Poset.dom (\<epsilon> $ A))"
    by (simp add: calculation(5) discrete_def)
    ultimately show ?thesis
      by (metis Poset.fun_app2)
  qed

lemma d_elem_is_open : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> A = d a \<Longrightarrow> A \<in> opens V"
  by (metis local_dom valid_gc_poset valid_presheaf)

lemma d_neut : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> \<epsilon>A = neut V A \<Longrightarrow> d \<epsilon>A = A"
  by simp

lemma d_comb : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow>  b \<in> elems V  ==>  A \<in> opens V
\<Longrightarrow> B \<in> opens V \<Longrightarrow> d a = A \<Longrightarrow> d b = B \<Longrightarrow> ab = comb V a b
\<Longrightarrow> d ab = A \<union> B"
by (simp add: valid_domain_law)

lemma d_gprj : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow>  B \<in> opens V
\<Longrightarrow> A \<in> opens V \<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d a = A \<Longrightarrow>  a_B = gprj V B a
\<Longrightarrow> d a_B = B"
  by (simp add: gprj_def)

lemma d_gext : "valid V \<Longrightarrow>  b \<in> elems V \<Longrightarrow>  B \<in> opens V
\<Longrightarrow> A \<in> opens V\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d b = B \<Longrightarrow>  b__A = gext V A b
\<Longrightarrow> d b__A = A"
  by (simp add: d_neut gext_def neutral_is_element sup.order_iff valid_domain_law)

lemma comb_is_element :
fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
assumes V_valid : "valid V"
and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
and a_dom : "d a = A" and b_dom : "d b = B"
shows "comb V a b \<in> elems V"
  by (meson Poset.valid_welldefined a_elem b_elem V_valid valid_monotone valid_poset valid_reflexivity valid_semigroup)

lemma gprj_is_element :
fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a :: "('A, 'a) Valuation"
assumes "valid V"
and a_elem : "a \<in> elems V" and "d a = A"
and "B \<subseteq> A" and "B \<in> opens V"
defines "a_B \<equiv> gprj V B a"
shows "a_B \<in> elems V"
  unfolding a_B_def gprj_def
  apply standard
   apply auto
  using assms(5) apply auto[1]
  using assms(3) assms(4) apply blast
proof -
  define "i" where "i = make_inclusion (Presheaf.space (presheaf V)) B (d a)"
  define "f" where "f = ar (presheaf V) $ i"
  define "\<Phi>A" where "\<Phi>A \<equiv> ((ob (presheaf V)) $ A)"
  define "\<Phi>B" where "\<Phi>B \<equiv> ((ob (presheaf V)) $ B)"

  have "Presheaf.valid (presheaf V)"
    by (simp add: assms(1) valid_presheaf)
  moreover have "A \<in> opens V"
    using assms(1) assms(3) d_elem_is_open a_elem by blast
  moreover have "Space.valid_inclusion i"
    using Presheaf.valid_space assms(3) assms(4) assms(5) calculation(1) calculation(2) i_def valid_make_inclusion by blast
  moreover have  "i \<in> inclusions V"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) calculation(3) i_def inclusions_def make_inclusion_def mem_Collect_eq)
  moreover have "f =  ar (presheaf V) $ i"
    by (simp add: f_def)
  moreover have "Poset.valid_map f" using Presheaf.valid_ar calculation
    by blast
  moreover have "d a_B = B"
    using a_B_def assms(1) assms(3) assms(4) assms(5) calculation(2) d_gprj a_elem by blast
  moreover have "Poset.cod f = \<Phi>B"
    by (metis Inclusion.select_convs(2) \<Phi>B_def calculation(1) calculation(4) cod_proj f_def i_def make_inclusion_def)
  moreover have "Poset.valid \<Phi>B"
    using Poset.valid_cod calculation(6) calculation(8) by blast
  moreover have "e a \<in> Poset.el \<Phi>A"
    by (metis OVA.valid_welldefined \<Phi>A_def assms(1) assms(3) a_elem gc_elem_local)
  moreover have "a_B \<equiv> gprj V B a"
    by (simp add: a_B_def)
  moreover have "e (gprj V B a) = f $$ (e a)"
    by (simp add: assms(3) assms(4) assms(5) f_def gprj_def i_def)
  moreover have "f $$ (e a) \<in> Poset.el \<Phi>B"
    by (metis Inclusion.simps(3) Poset.fun_app2 \<Phi>A_def assms(3) calculation(1) calculation(10) calculation(4) calculation(6) calculation(8) dom_proj f_def i_def make_inclusion_def)
  moreover have "f $$ (e a) = e a_B"
    using a_B_def calculation(12) by force
  moreover have "e a_B \<in>  Poset.el \<Phi>B"
    by (simp add: a_B_def calculation(12) calculation(13))
  moreover have "a_B \<in> el (poset V)"
    by (metis \<Phi>B_def assms(1) assms(5) calculation(1) calculation(15) calculation(7) local_elem_gc prod.exhaust_sel valid_gc_poset)
  ultimately show "(B, ar (presheaf V) $ make_inclusion (Presheaf.space (presheaf V)) B (d a) $$ e a) \<in> el (OVA.poset V)"
    using i_def by fastforce
qed

lemma local_inclusion_element : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> A = d a \<Longrightarrow> ea = e a
\<Longrightarrow> \<Phi> = (presheaf V) \<Longrightarrow> ob_A = ob \<Phi> $ A
\<Longrightarrow> ea \<in> el ob_A"
  by (metis OVA.valid_welldefined gc_elem_local)

lemma global_inclusion_element : "valid V \<Longrightarrow> A \<in> opens V
\<Longrightarrow> \<Phi> = presheaf V \<Longrightarrow> \<Phi>A =(Presheaf.ob \<Phi>) $ A \<Longrightarrow> a \<in> Poset.el \<Phi>A
\<Longrightarrow>  (A, a) \<in> elems V"
  by (metis OVA.valid_welldefined local_elem_gc)

lemma local_inclusion_domain : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> A = d a \<Longrightarrow> A \<in> opens V"
  by (metis OVA.valid_welldefined local_dom)

lemma gprj_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A"
  and "d a = A"
  and "a \<in> elems V"
defines "pr \<equiv> gprj V"
shows "pr C a = (pr C (pr B a))"
proof -
  define "\<Phi>1" where "\<Phi>1 = Presheaf.ar (presheaf V)"
  define "i_BA" where "i_BA = Space.make_inclusion (space V) B A"
  define "i_CB" where "i_CB = Space.make_inclusion (space V) C B"
  define "i_CA" where "i_CA = Space.make_inclusion (space V) C A"
  define "f" where "f = \<Phi>1 $ i_BA"
  define "g" where "g = \<Phi>1 $ i_CB"
  define "h" where "h = \<Phi>1 $ i_CA"
  have "pr C a = (C, (\<Phi>1 $ i_CA) $$ (e a))"
    by (metis (no_types, lifting) \<Phi>1_def assms(4) assms(5) assms(6) assms(7) gprj_def i_CA_def order.trans pr_def)
  moreover have "pr B a = (B, f $$ (e a))"
    by (simp add: \<Phi>1_def assms(3) assms(6) assms(7) f_def gprj_def i_BA_def pr_def)
  moreover have "pr C (pr B a) = (C, g  $$ (f $$ (e a)))"
    by (metis (no_types, lifting) \<Phi>1_def assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(2) d_gprj g_def gprj_def i_CB_def pr_def snd_conv V_valid)
  moreover have "Presheaf.valid (presheaf V)"
    by (meson OVA.valid_welldefined V_valid)
  moreover have "Space.valid_inclusion i_CB \<and> Space.space i_CB = space V"
    by (metis Inclusion.select_convs(1) Presheaf.valid_space assms(3) assms(4) assms(5) calculation(4) i_CB_def make_inclusion_def valid_make_inclusion)
  moreover have "i_CB \<in> inclusions V"
    using calculation(5) inclusions_def by blast
  moreover have "Space.valid_inclusion i_BA \<and> Space.space i_BA = space V"
    by (metis Inclusion.select_convs(1) Presheaf.valid_space assms(2) assms(3) assms(6) calculation(4) i_BA_def make_inclusion_def valid_make_inclusion)
    moreover have "i_BA \<in> inclusions V"
      using Space.inclusions_def calculation(7) by blast
moreover have "Space.valid_inclusion i_CA \<and> Space.space i_CA = space V"
  by (metis Inclusion.select_convs(1) Presheaf.valid_space assms(2) assms(4) assms(5) assms(6) calculation(4) i_CA_def make_inclusion_def order.trans valid_make_inclusion)
  moreover have "i_CA = Space.compose i_BA i_CB" using Space.compose_def
    by (metis Inclusion.select_convs(2) Inclusion.select_convs(3) calculation(5) calculation(7) i_BA_def i_CA_def i_CB_def make_inclusion_def)
  moreover have "Poset.valid_map f \<and> Poset.valid_map g \<and> Poset.valid_map h"
    using \<Phi>1_def calculation(4) calculation(6) calculation(8) calculation(9) f_def g_def h_def inclusions_def valid_ar by fastforce
  moreover have "Space.cod i_BA = A \<and> Space.dom i_BA = B "
    by (simp add: i_BA_def make_inclusion_def)
  moreover have "Space.cod i_CB = B \<and> Space.dom i_CB = C "
    by (simp add: i_CB_def make_inclusion_def)
  moreover have "Space.cod i_CA = A \<and> Space.dom i_CA = C "
    by (simp add: i_CA_def make_inclusion_def)
  moreover have "Poset.dom f = Presheaf.ob (presheaf V) $ A"
    by (metis \<Phi>1_def calculation(12) calculation(4) calculation(8) dom_proj f_def)
    moreover have "Poset.cod f  = Presheaf.ob (presheaf V) $ B \<and> Poset.dom g  = Presheaf.ob (presheaf V) $ B"
      by (metis \<Phi>1_def calculation(12) calculation(13) calculation(4) calculation(6) calculation(8) cod_proj dom_proj f_def g_def)
    moreover have " (\<Phi>1 $ i_CB) $$ ((\<Phi>1 $ i_BA) $$ (e a)) =  (\<Phi>1 $ i_CA) $$ (e a)"  using Poset.compose_app
      by (metis \<Phi>1_def assms(7) assms(8) calculation(10) calculation(11) calculation(12) calculation(13) calculation(15) calculation(16) calculation(4) calculation(6) calculation(8) f_def g_def local_inclusion_element V_valid valid_composition)
  ultimately show ?thesis
    by (metis f_def g_def)
qed

lemma combine_monotone : "valid V \<Longrightarrow>  a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> b1 \<in> elems V \<Longrightarrow> b2 \<in> elems V
\<Longrightarrow> gle V a1 a2 \<Longrightarrow> gle V b1 b2
\<Longrightarrow> gle V (comb V a1 b1) (comb V a2 b2)"
  by (metis OVA.valid_welldefined valid_monotone)

lemma le_imp_gle : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> local_le V A (A,a1) (A,a2) \<Longrightarrow> gle V (A,a1) (A,a2)"
  apply (frule valid_welldefined)
  apply (simp_all add: Let_def)
  apply safe
  apply auto
  apply (simp add: gc_def)
  apply (simp_all add: Let_def)
  using valid_gc_1 valid_map_space valid_ob by fastforce


lemma gle_eq_local_le : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> elems V
 \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> d a1 = A \<Longrightarrow> d a2 = A \<Longrightarrow> gle V a1 a2 = local_le V A a1 a2"
  by (metis le_imp_gle local_inclusion_element local_le prod.exhaust_sel valid_gc_poset valid_presheaf)

lemma gprj_monotone :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a1 a2 :: "('A, 'a) Valuation"
  defines "pr \<equiv> gprj V"
  and "gl \<equiv> gle V"
  assumes V_valid: "valid V"
  and "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  and "d a1 = A" and "d a2 = A"
  and "a1 \<in> elems V" and "a2 \<in> elems V" and "gl a1 a2"
shows "gl (pr B a1) (pr B a2)"
proof -
  define "i" where "i = make_inclusion (OVA.space V) B (fst a1)"
  define "\<Phi>i" where "\<Phi>i = (Presheaf.ar (presheaf V)) $ i"
  define "\<Phi>A" where "\<Phi>A = (Presheaf.ob (presheaf V)) $ A"
  define "\<Phi>B" where "\<Phi>B = (Presheaf.ob (presheaf V)) $ B"
  moreover have "gl a1 a2 \<longrightarrow> Poset.le \<Phi>A (e a1) (e a2)"
    apply (simp add: gl_def)
    using gle_eq_local_le
    by (metis \<Phi>A_def assms(10) assms(6) assms(7) assms(8) assms(9) V_valid)
  moreover have "Poset.le \<Phi>A (e a1) (e a2)"
    using assms(11) calculation(2) by blast
  moreover have "i \<in> inclusions V \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (mono_tags, lifting) Inclusion.select_convs(2) Inclusion.select_convs(3) Inclusion.simps(1) OVA.valid_welldefined Presheaf.valid_welldefined assms(4) assms(5) assms(6) assms(7) i_def inclusions_def make_inclusion_def mem_Collect_eq V_valid valid_inclusionI)
  moreover have "Poset.le \<Phi>B (\<Phi>i $$ (e a1)) (\<Phi>i $$ (e a2))" using Presheaf.prj_monotone
    by (metis OVA.valid_welldefined \<Phi>A_def \<Phi>B_def \<Phi>i_def assms(10) assms(7) assms(9) calculation(3) calculation(4) local_inclusion_element V_valid)
  ultimately show ?thesis
    by (metis \<Phi>i_def assms(10) assms(4) assms(5) assms(7) assms(8) assms(9) gl_def gprj_def i_def image le_imp_gle local_inclusion_element pr_def snd_conv V_valid valid_presheaf)
qed

lemma stability:
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid: "valid V"
  assumes "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  defines \<epsilon>A_def: "\<epsilon>A \<equiv> neut V A"
  defines \<epsilon>B_def: "\<epsilon>B \<equiv> neut V B"
  defines \<epsilon>A_B_def: "\<epsilon>A_B \<equiv> gprj V B \<epsilon>A"
  shows "\<epsilon>A_B = \<epsilon>B"
proof -
  define i where "i \<equiv> Space.make_inclusion (space V) B A"
  define "f" where "f = nat (neutral V)"
  define "one" where "one \<equiv> dom (neutral V)"
  moreover have "\<epsilon>A_B = gprj V B \<epsilon>A"
    by (simp add: \<epsilon>A_B_def)
  moreover have "Space.cod i = A \<and> Space.dom i = B"
    by (simp add: i_def make_inclusion_def)
  moreover have "i \<in> inclusions V"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.valid_welldefined Presheaf.valid_welldefined assms(2) assms(3) assms(4) calculation(3) i_def inclusions_def make_inclusion_def mem_Collect_eq V_valid valid_inclusion_def)
    moreover have v1: "Poset.valid_map  (Presheaf.ar one $ i)"
      by (metis OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined calculation(4) one_def terminal_def V_valid valid_ar)
      moreover have v2: "Poset.valid_map (f $ B)"
        by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined assms(3) f_def V_valid)
    moreover have "Presheaf.valid one"
      by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined one_def V_valid)
  moreover have "(Presheaf.ar one $ i ) $$ ()  = ()"
    by simp
moreover have "() \<in> Poset.el (Poset.dom  (ar one $ i))" using Presheaf.terminal_value
  by (metis OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined Presheaf.valid_welldefined UNIV_unit assms(4) calculation(3) calculation(4) iso_tuple_UNIV_I one_def terminal_def V_valid)
moreover have "((f $ B) \<cdot> (ar one $ i)) $$ () = ((f $ B) $$ ((ar one $ i)) $$ ())"
  by (metis OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined assms(3) calculation(3) calculation(4) calculation(9) cod_proj compose_app f_def one_def terminal_def v1 V_valid)
  moreover have "((Presheaf.ar (presheaf V) $ i) \<cdot> (f $ A)) $$ ()=  e \<epsilon>B"
    by (metis OVA.valid_welldefined \<epsilon>B_def calculation(10) calculation(3) calculation(4) calculation(8) f_def one_def snd_conv V_valid valid_map_naturality)
  moreover have "e \<epsilon>A=   (f $ A) $$ ()"
    by (simp add: \<epsilon>A_def f_def)
  ultimately show ?thesis
    by (metis (no_types, lifting) OVA.valid_welldefined Presheaf.valid_map_welldefined Presheaf.valid_welldefined \<epsilon>A_def \<epsilon>B_def assms(2) assms(3) assms(4) compose_app eq_fst_iff f_def gprj_def i_def singletonI sndI terminal_value V_valid)
qed

(* [Remark 3, CVA] *)
lemma local_mono_eq_global :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a1 a1' a2 a2' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and A_open "A \<in> opens V"
  and  "a1 \<in> elems V" and "d a1 = A"
  and  "a1' \<in> elems V" and "d a1' = A"
  and  "a2 \<in> elems V" and "d a2 = A"
  and  "a2' \<in> elems V" and "d a2' = A"
shows "gle V (comb V a1 a1') (comb V a2 a2') = local_le V A (comb V a1 a1') (comb V a2 a2')"
  by (smt (verit, ccfv_threshold) assms(10) assms(11) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) comb_is_element d_neut gle_eq_local_le gle_eq_local_le neutral_is_element V_valid valid_domain_law valid_neutral_law_right)

(* [Remark 3 cont., CVA] *)
lemma id_le_gprj :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes "valid V"
  and  "A \<in> opens V" and "B \<in> opens V"  and "B \<subseteq> A"
  and  "a \<in> elems V" and "d a = A"
shows " gle V a (gprj V B a)"
proof -
  define "i" where "i = Space.make_inclusion (space V) B (d a)"
  define "\<Phi>i" where "\<Phi>i = Presheaf.ar (presheaf V) $ i"
  define "\<Phi>A" where "\<Phi>A = Presheaf.ob (presheaf V) $ A"
  define "\<Phi>B" where "\<Phi>B = Presheaf.ob (presheaf V) $ B"
  define "a_B" where "a_B =  \<Phi>i $$ (e a)"
  have "i \<in> inclusions V"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Presheaf.valid_space assms(1) assms(2) assms(3) assms(4) assms(6) i_def inclusions_def make_inclusion_def mem_Collect_eq valid_make_inclusion valid_presheaf)
  moreover have "gprj V B a = (B, a_B)"
    by (simp add: \<Phi>i_def a_B_def assms(3) assms(4) assms(6) gprj_def i_def)
    moreover have "Presheaf.valid (presheaf V)"
    by (meson OVA.valid_welldefined assms(1))
  moreover have "Poset.valid \<Phi>B"
    using \<Phi>B_def assms(3) calculation(3) valid_ob by blast
  moreover have "Poset.valid_map \<Phi>i"
    using \<Phi>i_def calculation(1) calculation(3) valid_ar by blast
  moreover have "e a \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def assms(1) assms(5) assms(6) local_inclusion_element)
  moreover have "Space.cod i = A \<and> Space.dom i = B \<and> i \<in> inclusions V"
    by (metis Inclusion.select_convs(2) Inclusion.select_convs(3) assms(6) calculation(1) i_def make_inclusion_def)
  moreover have "a_B \<in> Poset.el \<Phi>B"
    by (metis \<Phi>A_def \<Phi>B_def \<Phi>i_def a_B_def calculation(3) calculation(6) calculation(7) image)
    moreover have "Poset.le \<Phi>B a_B a_B "
      by (simp add: calculation(4) calculation(8) valid_reflexivity)
  moreover have "valid V" by fact
  ultimately show ?thesis apply (simp add:   )
    apply (frule valid_welldefined)
    apply (simp_all add: Let_def)
    apply (simp add: gc_def Let_def)
    apply auto
         apply (metis assms(2) assms(6) fst_conv)
    apply (metis assms(3))
    apply (metis \<Phi>A_def assms(6) fst_eqD)
    using \<Phi>B_def apply force
    apply (metis assms(4) assms(6) fst_conv subsetD)
    by (metis (mono_tags, opaque_lifting) \<Phi>B_def \<Phi>i_def a_B_def fst_conv i_def snd_conv)
qed

lemma elem_le_wrap :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" and A B :: "('A Open)"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and dom_A : "d a = A" and dom_B : "d b = B"
  and b_subseteq_a : "B \<subseteq> A" and a_B_le_b : "local_le V B (gprj V B a) b"
shows "gle V a b"
proof -
  define "\<Phi>" where "\<Phi> = presheaf V"
  define "\<Phi>A" where "\<Phi>A = (Presheaf.ob \<Phi>) $ A"
  define "\<Phi>B" where "\<Phi>B = (Presheaf.ob \<Phi>) $ B"
  define "a_B" where "a_B = gprj V B a"

  have "d a_B = d b"
    by (metis a_B_def a_elem b_elem b_subseteq_a d_gprj dom_A dom_B local_inclusion_domain V_valid)

  moreover have "a_B \<in> elems V"
    by (metis a_B_def a_elem b_elem b_subseteq_a dom_A dom_B gprj_is_element local_inclusion_domain V_valid)
  moreover have "b \<in> elems V"
    by (simp add: b_elem)
  moreover have a1: "Presheaf.valid \<Phi>"
    by (metis OVA.valid_welldefined \<Phi>_def V_valid)
  moreover have a2: "A \<in> opens V"
    using a_elem  dom_A dom_B local_inclusion_domain V_valid by blast
  moreover have a3: "B \<in> opens V"
    using  b_elem dom_A dom_B local_inclusion_domain V_valid by blast
  moreover have a4: "e a \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def \<Phi>_def a_elem dom_A local_inclusion_element V_valid)
  moreover have a5: "e b \<in> Poset.el \<Phi>B"
    by (metis \<Phi>B_def \<Phi>_def b_elem dom_B local_inclusion_element V_valid)
  moreover have a6: "B \<subseteq> A"
    by (simp add: b_subseteq_a)
  moreover have a7: "local_le V B a_B b"
    using a_B_def a_B_le_b by fastforce
  moreover have "Presheaf.space \<Phi> = space V"
    by (simp add: \<Phi>_def)
  ultimately show ?thesis
    by (metis \<Phi>_def a_B_def a_elem dom_A dom_B id_le_gprj gle_eq_local_le V_valid valid_gc valid_gc_poset valid_transitivity)
    qed

lemma gprj_elem : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow>  B \<in> opens V
\<Longrightarrow> A \<in> opens V\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d a = A \<Longrightarrow>  a_B = gprj V B a \<Longrightarrow> a_B \<in> elems V"
  by (metis OVA.valid_welldefined id_le_gprj valid_gc_welldefined)

lemma gext_elem :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes "valid V"
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
    by (simp add: b__A_def assms(4) assms(5) assms(8) gext_def com_def)
  ultimately show ?thesis
    by (smt (verit) OVA.valid_welldefined Semigroup.valid_def Poset.valid_def assms(2) com_def neutral_is_element valid_monotone)
qed

lemma e_gprj :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  defines "pr \<equiv> gprj V"
  and "\<Phi>B \<equiv> Presheaf.ob (presheaf V) $ B"
  and "a_B \<equiv> gprj V B a"
  assumes "valid V"
  and "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  and "d a = A"
  and "a \<in> elems V"
shows " e (a_B) \<in> Poset.el \<Phi>B"
  by (metis \<Phi>B_def a_B_def assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) d_gprj gc_elem_local gprj_elem valid_gc_poset valid_presheaf)

lemma e_gext :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and b :: "('A, 'a) Valuation"
  defines "ex \<equiv> gext V"
  and "\<Phi>A \<equiv> Presheaf.ob (presheaf V) $ A"
  and "b__A \<equiv> gext V A b"
  assumes "valid V"
  and "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  and "d b = B"
  and "b \<in> elems V"
shows " e (b__A) \<in> Poset.el \<Phi>A"
  by (metis \<Phi>A_def assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) b__A_def d_gext gext_elem local_inclusion_element)

lemma prj_ext_adjunction_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf V"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "\<epsilon>A \<equiv> neut V A"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and a_dom : "d a = A" and b_dom : "d b = B" and "B \<subseteq> A"
  and LHS: "local_le V B (gprj V B a) b"
  shows "local_le V A a (comb V \<epsilon>A b)"
proof -
  define "a_B" where "a_B \<equiv> (gprj V B a)"
  define "ea_B" where "ea_B \<equiv> e a_B"
  define "eb" where "eb \<equiv> e b"
  define "A" where "A \<equiv> d a"
  define "B" where "B \<equiv> d b"
  moreover have "gle V a a_B"
    by (metis a_B_def assms(9) a_dom b_dom a_elem b_elem id_le_gprj local_inclusion_domain V_valid)
  moreover have "a = comb V \<epsilon>A a"
    by (metis \<epsilon>A_def a_dom a_elem local_inclusion_domain V_valid valid_neutral_law_left)
  moreover have a_B_le_b : "local_le V B (B,ea_B) (B,eb)"
    by (simp add: B_def LHS a_B_def b_dom ea_B_def eb_def)
  moreover have "Poset.valid (\<Phi>0 A)"
    by (metis A_def Presheaf.valid_welldefined \<Phi>0_def \<Phi>_def a_elem local_inclusion_domain V_valid valid_presheaf)
  moreover have "d \<epsilon>A = A"
    by (simp add: A_def \<epsilon>A_def a_dom)
  moreover have " e \<epsilon>A \<in> Poset.el (\<Phi>0 A)"  using neutral_local_element
    using A_def \<Phi>0_def \<Phi>_def \<epsilon>A_def a_dom a_elem local_inclusion_domain V_valid by blast
  moreover have "local_le V A \<epsilon>A \<epsilon>A"
    using \<Phi>0_def \<Phi>_def calculation(5) calculation(6) calculation(7) valid_reflexivity by fastforce
    define "gc_poset" where "gc_poset = (Semigroup.poset (ordered_semigroup V))"
  moreover have "Poset.valid gc_poset"
    by (metis OVA.valid_welldefined Semigroup.valid_welldefined gc_poset_def V_valid)
  moreover have "\<epsilon>A \<in> Poset.el gc_poset" using gc_poset_def   \<epsilon>A_def
    using a_dom a_elem local_inclusion_domain neutral_is_element V_valid by blast
  moreover have "gle V \<epsilon>A \<epsilon>A"
    by (metis calculation(10) calculation(9) gc_poset_def valid_reflexivity)
  moreover have "gle V (comb V \<epsilon>A a) (comb V \<epsilon>A a_B)"
    by (meson OVA.valid_welldefined Semigroup.valid_welldefined Poset.valid_welldefined calculation(11) calculation(2) combine_monotone V_valid)
  moreover have "d a_B = B \<and> d b = B"
    by (metis B_def a_B_def assms(9) d_gprj a_dom b_dom a_elem b_elem local_inclusion_domain V_valid)
  moreover have "a_B = (B, ea_B) \<and> b = (B, eb)"
    by (metis calculation(13) ea_B_def eb_def prod.collapse)
  moreover have "gle V a_B b"  using  a_B_le_b
    by (metis Poset.valid_welldefined calculation(13) calculation(14) calculation(2) calculation(9) b_elem gc_poset_def gle_eq_local_le local_inclusion_domain V_valid)
  moreover have "gle V (comb V \<epsilon>A a_B) (comb V \<epsilon>A b)"
    by (meson OVA.valid_welldefined Semigroup.valid_welldefined Poset.valid_welldefined calculation(11) calculation(15) combine_monotone V_valid)
moreover have "gle V (comb V \<epsilon>A a) (comb V \<epsilon>A a_B)"
  using calculation(12) by auto
moreover have "gle V a (comb V \<epsilon>A a_B)"
  using calculation(12) calculation(3) by auto
  moreover have "A \<union> B = A"
    by (simp add: A_def B_def Un_absorb2 assms(9) a_dom b_dom)
  moreover have "d (comb V \<epsilon>A a_B) = A" using valid_domain_law
    by (metis Poset.valid_welldefined calculation(10) calculation(13) calculation(19) calculation(2) calculation(6) calculation(9) gc_poset_def V_valid)
  ultimately show ?thesis
    by (metis (no_types, lifting) A_def OVA.valid_welldefined Poset.valid_welldefined a_dom local_le V_valid valid_domain_law valid_transitivity)
qed

lemma prj_ext_adjunction_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf V"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "\<epsilon>A \<equiv> neut V A"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens V" and B_open : "B \<in> opens V"
  and B_le_A : "B \<subseteq> A"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and a_dom : "d a = A" and b_dom : "d b = B"
  and RHS: "local_le V A a (comb V \<epsilon>A b)"
shows "local_le V B (gprj V B a) b"
proof -
  have "gle V a (comb V \<epsilon>A b)"
    by (metis A_open B_le_A RHS \<epsilon>A_def comb_is_element a_dom b_dom a_elem b_elem fst_conv gle_eq_local_le neutral_is_element sup.orderE V_valid valid_domain_law)
    moreover have "gle V (gprj V B a) (gprj V B (comb V \<epsilon>A b))"
      by (smt (verit) A_open B_le_A B_open OVA.valid_welldefined Semigroup.valid_def Poset.valid_welldefined \<epsilon>A_def calculation a_dom b_dom b_elem fst_conv gprj_monotone neutral_is_element sup.orderE V_valid valid_domain_law)
    moreover have "gprj V B (comb V \<epsilon>A b) = comb V (gprj V (A \<inter> B) \<epsilon>A) b"  using valid_comb_law_right
      by (metis A_open \<epsilon>A_def b_dom b_elem fst_conv neutral_is_element V_valid)
    define "\<epsilon>B" where "\<epsilon>B \<equiv> neut V B"
    moreover have "gprj V (A \<inter> B) \<epsilon>A = \<epsilon>B"
      by (simp add: A_open B_le_A B_open \<epsilon>A_def \<epsilon>B_def inf.absorb2 stability V_valid)
    moreover have "comb V (gprj V (A \<inter> B) \<epsilon>A) b = b"
      by (metis B_open \<epsilon>B_def calculation(4) b_dom b_elem V_valid valid_neutral_law_left)
    moreover have "gle V (gprj V B a) b"
      using \<open>gprj V B (comb V \<epsilon>A b) = comb V (gprj V (A \<inter> B) \<epsilon>A) b\<close> calculation(2) calculation(5) by fastforce
    ultimately show ?thesis
      by (metis (no_types, lifting) A_open B_le_A B_open d_gprj a_dom b_dom a_elem b_elem gle_eq_local_le gprj_elem V_valid)
  qed

(* [Remark 3, CVA] *)
lemma laxity :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and  A_open : "A \<in> opens V" and B_open :"B \<in> opens V"  and B_le_A : "B \<subseteq> A"
  and  a_elem : "a \<in> elems V" and a_dom : "d a = A"
  and a'_elem :  "a' \<in> elems V" and a_dom' : "d a' = A"
shows "local_le V B (gprj V B (comb V a a')) (comb V (gprj V B a) (gprj V B a'))"
proof -
   define "m1" where "m1 = comb V a a'"
   define "m2" where "m2 = comb V (gprj V B a) (gprj V B a')"
   define "m1_B" where "m1_B = gprj V B m1"
   have "gle V a (gprj V B a)"
     using A_open B_le_A B_open a_elem a_dom  id_le_gprj  V_valid by blast
   moreover have "gle V a' (gprj V B a')"
     using A_open B_le_A B_open a'_elem a_dom' id_le_gprj V_valid by blast
   moreover have global_le : "gle V m1 m2"
     by (metis OVA.valid_welldefined Poset.valid_welldefined calculation(1) calculation(2) combine_monotone m1_def m2_def V_valid valid_poset)
   moreover have d_m1 : "d m1 = A"
     by (simp add: V_valid a'_elem a_elem a_dom a_dom' m1_def valid_domain_law) 
   moreover have d_m1_B : "d m1_B = B"
     by (metis m1_B_def B_le_A B_open a'_elem a_elem comb_is_element d_comb d_gprj a_dom a_dom' equalityE le_iff_sup local_inclusion_domain m1_def V_valid)
   moreover have d_m2 : "d m2 = B"
     by (metis A_open B_le_A B_open Poset.valid_welldefined calculation(1) calculation(2) d_gprj a_dom a_dom' dual_order.refl m2_def sup.order_iff V_valid valid_domain_law valid_poset valid_semigroup)
   moreover have pm1_el : "m1_B \<in> elems V"
     by (simp add: m1_B_def B_le_A B_open a'_elem a_elem comb_is_element a_dom a_dom' gprj_is_element m1_def V_valid valid_domain_law)
   moreover have m2_el : "m2 \<in> elems V"
     by (meson Poset.valid_welldefined calculation(3) V_valid valid_poset valid_semigroup)
   moreover have "valid V" by fact
   moreover have m1_el : "m1 \<in> elems V"
     by (simp add: V_valid a'_elem a_elem comb_is_element m1_def)
   moreover have "local_le V B m1_B m2" using V_valid A_open B_open m1_el m2_el d_m1 d_m2 m1_B_def  global_le valid_gle
       [where ?V = V and ?A = A and ?B = B and ?a = m1 and ?b = m2]
     by fastforce
  ultimately show ?thesis
    using m1_B_def m1_def m2_def by auto 
qed

(* THEOREMS *)

(* [Theorem 1, CVA] *)
theorem prj_ext_adjunction :
  fixes V :: "('A,'a) OVA" and  a b :: "('A, 'a) Valuation" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and A_open : "A \<in> opens V" and B_open : "B \<in> opens V"
  and B_le_A : "B \<subseteq> A"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and a_dom : "d a = A" and b_dom : "d b = B"
shows "local_le V B (gprj V B a) b = local_le V A a (gext V A b)" (* Isabelle likes equality more than \<longleftrightarrow> *)
proof (rule iffI)
  assume "local_le V B (gprj V B a) b"
  show "local_le V A a (gext V A b)"  using V_valid a_elem b_elem a_dom b_dom B_le_A 
      gext_def [where ?V = V and ?A = A  and ?b = b]
      prj_ext_adjunction_lhs_imp_rhs [where ?V = V and ?A = A and ?B = B and ?a = a and ?b = b]
    using A_open \<open>le (ob (presheaf V) $ B) (e (gprj V B a)) (e b)\<close> by presburger 
next
  assume "local_le V A a (gext V A b)"
  show "local_le V B (gprj V B a) b" using prj_ext_adjunction_rhs_imp_lhs [where ?V = V and ?A = A and ?B = B and ?a = a and ?b = b]
    using A_open B_le_A B_open V_valid
    by (metis \<open>le (ob (presheaf V) $ A) (e a) (e (gext V A b))\<close> a_dom a_elem b_dom b_elem gext_def) 
  qed

(* [Corollary 1, CVA] *)
theorem strongly_neutral_covariance :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes V_valid : "valid V"
  and strongly_neutral: "\<forall> A B . comb V (neut V A) (neut V B) = neut V (A \<union> B)"
  and  "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
defines "ex \<equiv> gext V"
shows "ex A (neut V B) = neut V A "
by (metis assms(3) assms(4) assms(5) d_neut ex_def gext_def strongly_neutral sup.absorb_iff1 V_valid)

(* [Corollary 2, CVA] *)
theorem galois_insertion :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "b \<in> elems V" and "d b = B"
  and " B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  defines "pr \<equiv> gprj V" and "ex \<equiv> gext V" and "com \<equiv> comb V"
  shows "pr B (ex A b) = b"
proof -
  define \<epsilon>A where "\<epsilon>A \<equiv> neut V A"
  define \<epsilon>B where "\<epsilon>B \<equiv> neut V B"
  have "pr B (ex A b) = pr B (com \<epsilon>A b)"
    by (simp add: \<epsilon>A_def assms(3) assms(4) assms(6) ex_def gext_def com_def)
  moreover have "... =  com (pr (A \<inter> B) \<epsilon>A) b"  using valid_comb_law_right pr_def com_def ex_def
    by (metis \<epsilon>A_def assms(2) assms(3) assms(6) fst_conv neutral_is_element V_valid)
  moreover have "... =  com \<epsilon>B b"
  by (simp add: \<epsilon>A_def \<epsilon>B_def assms(4) assms(5) assms(6) inf.absorb2 pr_def stability V_valid)
  ultimately show ?thesis
    by (metis \<epsilon>B_def \<open>pr B (ex A b) = pr B (com \<epsilon>A b)\<close> assms(2) assms(3) assms(5) com_def valid_neutral_law_left V_valid)
qed

(* [Corollary 2 cont., CVA] *)
theorem galois_closure_extensive :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V" and "a \<in> elems V" and "d a = A"
  and " B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  shows "local_le V A a (gext V A (gprj V B a))"
proof -
  have "valid V" by fact
  moreover have "local_le V A a a"
    by (metis assms(2) assms(3) assms(6) calculation local_inclusion_element valid_ob valid_presheaf valid_reflexivity) 
  moreover have "local_le V B (gprj V B a) (gprj V B a)"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) e_gprj valid_ob valid_presheaf valid_reflexivity) 
  ultimately show ?thesis using prj_ext_adjunction  [where ?V = V and ?A = A and ?B = B and ?a = a and ?b = b ]
    by (smt (verit, best) assms(2) assms(3) assms(4) assms(5) assms(6) d_gprj gprj_elem prj_ext_adjunction)
qed

lemma ext_functorial_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
  shows "gle V (ex A c) (ex A (ex B c))"
proof -
  have "local_le V C c c"
    by (metis V_valid assms(4) assms(7) assms(8) local_inclusion_element valid_ob valid_presheaf valid_reflexivity) 
  moreover have "local_le V C (pr C (ex A c)) c"
    by (smt (verit, best) V_valid assms(2) assms(4) assms(5) assms(6) assms(7) assms(8) calculation dual_order.trans ex_def galois_insertion pr_def) 
  moreover have "pr C (pr B (ex A c)) = pr C (ex A c)"
    by (smt (verit, del_insts) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem gprj_functorial local_inclusion_domain pr_def V_valid)
  moreover have "local_le V C  (pr C (pr B (ex A c))) c"
    by (simp add: calculation(2) calculation(3))
  moreover have "local_le V B (pr B (ex A c)) (ex B c)"
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_gext d_gprj ex_def gext_elem gprj_is_element order_trans pr_def prj_ext_adjunction) 
  moreover have "local_le V A (ex A c) (ex A (ex B c))"
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(5) d_gext dual_order.trans ex_def gext_elem pr_def prj_ext_adjunction) 
    ultimately show ?thesis
      by (smt (verit) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.refl dual_order.trans elem_le_wrap ex_def galois_insertion gext_elem gprj_functorial pr_def) 
qed

lemma ext_functorial_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
  shows "gle V (ex A (ex B c)) (ex A c)"
proof -
  have "local_le V A (ex A (ex B c)) (ex A (ex B c))"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext e_gext ex_def gext_elem valid_ob valid_presheaf valid_reflexivity) 
  moreover have "local_le V B (pr B (ex A (ex B c))) (ex B c)"
    by (metis V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext e_gext ex_def galois_insertion gext_elem pr_def valid_ob valid_presheaf valid_reflexivity) 
    moreover have "local_le V C (pr C (pr B (ex A (ex B c)))) c"
      by (metis (no_types, lifting) V_valid assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_insertion gext_elem gle_eq_local_le local_inclusion_domain pr_def valid_poset valid_reflexivity valid_semigroup) 
moreover have "local_le V C (pr C (ex A (ex B c))) c"
  by (metis (full_types) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) calculation(3) d_gext ex_def gext_elem gprj_functorial local_inclusion_domain pr_def V_valid)
  moreover have "local_le V A (ex A (ex B c)) (ex A c)" using prj_ext_adjunction
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_gext dual_order.trans ex_def gext_elem pr_def)
  ultimately show ?thesis
    by (smt (verit, best) V_valid assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem gle_eq_local_le) 
qed

(* [Theorem 1 cont., CVA] *)
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
    by (meson OVA.valid_welldefined Semigroup.valid_def Poset.valid_welldefined V_valid valid_antisymmetry)
qed

(* [Corollary 2 cont., CVA] *)
lemma galois_closure_idempotent :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d a = A" and "a \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
  shows "ex A (pr B (ex A (pr B a))) = ex A (pr B a)"
  by (metis assms(2) assms(3) assms(6) assms(7) assms(8) d_gprj ex_def galois_insertion gprj_elem pr_def V_valid)

lemma up_and_down :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes V_valid : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
shows "pr B (ex A c) = ex B c"
proof -
  have "ex A c = ex A (ex B c)" using ext_functorial
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def V_valid)
  moreover have "pr B (ex A (ex B c)) = ex B c"
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_insertion gext_elem pr_def V_valid)
  ultimately show ?thesis
    by auto
qed

lemma intermediate_extension :
  fixes V :: "('A,'a) OVA" and a c :: "('A, 'a) Valuation" and A B C :: "('A Open)"
  assumes V_valid : "valid V"
  and a_elem : "a \<in> elems V" and c_elem : "c \<in> elems V"
  and dom_A : "d a = A" and dom_c : "d c = C"
  and C_le_B : "C \<subseteq> B" and B_leq_A : "B \<subseteq> A"
  and B_open : "B \<in> opens V"
  assumes le_a_C_c : "local_le V C (gprj V C a) c"
  shows "local_le V B (gprj V B a) (gext V B c)"
proof -
  have "A \<in> opens V \<and> B \<in> opens V \<and> C \<in> opens V"
    using B_open a_elem c_elem dom_A dom_c local_inclusion_domain V_valid by blast
  moreover have "local_le V C (gprj V C a) c" by fact
  moreover have "local_le V A a (gext V A c)" using prj_ext_adjunction
    by (smt (z3) B_leq_A C_le_B a_elem c_elem dom_A dom_c dual_order.trans gext_def gext_elem le_a_C_c local_inclusion_domain V_valid)
  moreover have "gext V A c = gext V A (gext V B c)" using ext_functorial
    by (metis B_leq_A C_le_B c_elem calculation(1) dom_c V_valid)
  moreover have "local_le V A a (gext V A (gext V B c))"
    using calculation(3) calculation(4) by auto
  ultimately show ?thesis using prj_ext_adjunction le_a_C_c
    by (smt (verit, best) B_leq_A C_le_B V_valid a_elem c_elem d_gext dom_A dom_c gext_elem)
qed

(* [Corollary 3, CVA] *)
lemma locally_complete_imp_complete :
  fixes V :: "('A,'a) OVA"
  defines "\<Phi> A \<equiv> (Presheaf.ob (presheaf V)) $ A"
  and "pr \<equiv> gprj V" and "ex \<equiv> gext V"
  assumes V_valid: "valid V"
  assumes local_completeness: "\<And>A . A \<in> opens V \<Longrightarrow> Poset.is_complete (\<Phi> A)"
  shows "Poset.is_complete (poset V)"
proof
  show "Poset.valid (OVA.poset V)"
    using V_valid by (metis OVA.valid_welldefined valid_gc)
next
  show "(\<forall> U \<subseteq> el (OVA.poset V). \<exists> i . is_inf (OVA.poset V) U i)"
  proof auto
    fix U :: "(('A,'a) Valuation) set"
    assume U: "U \<subseteq> el (OVA.poset V)"

    have "elems V = el (OVA.poset V)"
      by (simp add:  )
    hence "U \<subseteq> elems V" using U by simp


    define "d_U" where "d_U = \<Union> (d ` U)"
    define "ex_U" where "ex_U = ((e o ex d_U) ` U)"
    define "some_e_U" where "some_e_U = Poset.inf (\<Phi> (d_U)) ex_U"

    have "d_U \<in> opens V"
      by (smt (verit, best) Presheaf.valid_space U V_valid d_U_def image_subsetI local_inclusion_domain subsetD valid_presheaf valid_union)
    moreover have "ex_U \<subseteq> Poset.el (\<Phi> (d_U))"
      by (smt (verit) Sup_upper UN_subset_iff Union_least \<Phi>_def \<open>U \<subseteq> elems V\<close> calculation comp_apply d_U_def e_gext ex_U_def ex_def image_subsetI in_mono local_inclusion_domain V_valid)

    moreover have "some_e_U \<noteq> None" using Poset.complete_inf_not_none
      using calculation(1) calculation(2) local_completeness some_e_U_def by fastforce

    obtain e_U where "some_e_U = Some e_U" using \<open>some_e_U \<noteq> None\<close> by auto

    moreover have "e_U \<in> Poset.el (\<Phi> d_U)"
      by (metis (mono_tags, lifting) \<open>some_e_U \<noteq> None\<close> calculation(3) inf_def option.inject someI_ex some_e_U_def)

    define "i" where "i = (d_U, e_U)"
    moreover have "i \<in> elems V"
      by (metis \<Phi>_def \<open>e_U \<in> el (\<Phi> d_U)\<close> calculation(1) global_inclusion_element i_def V_valid)

    have "Poset.is_inf (poset V) U i"
    proof (simp add: is_inf_def   )
      have "U \<subseteq> el (OVA.poset V)"
        by (metis \<open>U \<subseteq> elems V\<close>  )
      moreover have "i \<in> el (OVA.poset V)"
        by (metis \<open>i \<in> elems V\<close>  )
      moreover have "(\<forall>u\<in>U. Poset.le (OVA.poset V) i u)"
        proof auto

        fix a :: "'A set"
        fix b :: "'a"
        define "u" where "u = (a,b)"
        assume "u \<in> U"
        moreover have "d u \<subseteq> d_U"
          using calculation(1) d_U_def by blast
        moreover have "Poset.valid (\<Phi> (d_U))"
          using \<open>d_U \<in> Space.opens (Presheaf.space (presheaf V))\<close> local_completeness by blast 
        moreover have "Poset.is_complete (\<Phi> (d_U))"
          by (simp add: \<open>d_U \<in> OVA.opens V\<close> local_completeness)
        moreover have "Poset.is_inf (\<Phi> (d_U)) ex_U e_U" using ex_U_def local_completeness
          by (metis \<open>e_U \<in> el (\<Phi> d_U)\<close> \<open>ex_U \<subseteq> el (\<Phi> d_U)\<close> \<open>some_e_U = Some e_U\<close> calculation(3) some_e_U_def some_inf_is_inf)
        moreover have "local_le V (d_U) i (ex d_U u)"
          by (metis \<Phi>_def calculation(1) calculation(5) comp_apply ex_U_def i_def image_eqI is_inf_def ll_def snd_conv)
        moreover have "local_le V (d u) (pr (d u) i) u" using Poset.inf_smaller
          by (smt (verit, best) \<open>U \<subseteq> elems V\<close> \<open>i \<in> elems V\<close> calculation(1) calculation(2) calculation(6) ex_def prj_ext_adjunction_rhs_imp_lhs fst_conv gext_def i_def ll_def local_inclusion_domain pr_def subsetD V_valid)
        moreover have i_is_lb: "gle V i u"
          by (smt (verit, best) \<open>U \<subseteq> elems V\<close> \<open>i \<in> elems V\<close> calculation(1) calculation(2) calculation(7) elem_le_wrap fst_conv gl_def i_def ll_def pr_def subsetD V_valid)
        ultimately show "(Poset.le (OVA.poset V) i u)"
          by (simp add: gle_def)
      qed

       moreover have " (\<forall>z\<in>el (OVA.poset V). (\<forall>u\<in>U. Poset.le (OVA.poset V) z u) \<longrightarrow> Poset.le (OVA.poset V) z i)"
       proof auto
        fix a :: "'A set"
        fix b :: "'a"
        assume "(a,b) \<in>  el (OVA.poset V)"
        assume "\<forall>u\<in>U. Poset.le (OVA.poset V) (a,b) u"
        define "z" where "z = (a,b)"
        moreover have lb2: "\<forall> v \<in> U . d v \<subseteq> d z"
          by (metis  OVA.valid_welldefined \<open>\<forall>u\<in>U. Poset.le (OVA.poset V) (a, b) u\<close> d_antitone V_valid valid_gc_welldefined z_def)
        moreover have "\<forall> v \<in> U . local_le V (d v) (pr (d v) z) v"
          using U \<open>(a, b) \<in> el (Semigroup.poset (ordered_semigroup V))\<close> \<open>\<forall>u\<in>U. Poset.le (Semigroup.poset (ordered_semigroup V)) (a, b) u\<close> elem_le_unwrap ll_def pr_def V_valid z_def by blast
        moreover have "\<forall> v \<in> U . Poset.le (\<Phi> (d v)) (e (pr (d v) z)) (e v)"
          by (metis \<Phi>_def calculation(3) ll_def)
        moreover have "\<forall> v \<in> U . Poset.le (\<Phi> (d v)) (e (pr (d v) z)) (e v)"  using prj_ext_adjunction
          using calculation(4) by blast
        define "z_U" where "z_U = gprj V d_U z"
        moreover have "\<forall> v \<in> U . pr d_U (ex (d z) v) = ex d_U v" using up_and_down
          by (smt (verit) OVA.valid_welldefined U UN_subset_iff \<open>(a, b) \<in> el (Semigroup.poset (ordered_semigroup V))\<close> \<open>\<forall>u\<in>U. Poset.le (Semigroup.poset (ordered_semigroup V)) i u\<close> \<open>i \<in> el (Semigroup.poset (ordered_semigroup V))\<close> d_U_def d_antitone ex_def fst_conv i_def lb2 local_inclusion_domain pr_def subsetD V_valid z_def)
        moreover have "Poset.valid (\<Phi> d_U)"
          by (simp add: \<open>d_U \<in> Space.opens (Presheaf.space (presheaf V))\<close> local_completeness)
        moreover have "e z_U \<in> Poset.el (\<Phi> d_U)"
          by (metis UN_subset_iff \<Phi>_def \<open>(a, b) \<in> el (Semigroup.poset (ordered_semigroup V))\<close> \<open>d_U \<in> Space.opens (Presheaf.space (presheaf V))\<close> d_U_def e_gprj lb2 local_inclusion_domain V_valid z_U_def z_def)
        moreover have "\<forall> v \<in> U . local_le V d_U z_U (ex d_U v)" using calculation up_and_down
            moreover have "\<forall> v \<in> U . Poset.le (\<Phi> (d z)) (e z) (e (gext V (d z) v))"
              moreover have "\<Union> (d ` U) \<subseteq> d z"
          using lb2 by auto
        moreover have "d i \<subseteq> d z"
          by (simp add: \<open>d_U \<equiv> \<Union> (d ` U)\<close> calculation(11) i_def)
        define "i__Z" where "i__Z = gext V (d z) i"

        moreover have "Poset.le (\<Phi> d_U) (e ( gprj V d_U z)) e_U"  using inf_is_glb
        proof
          show "Poset.valid (\<Phi> d_U)"
            by (simp add: \<open>d_U \<in> OVA.opens V\<close> local_completeness)
          show "ex_U \<subseteq> el (\<Phi> d_U)"
            by (simp add: \<open>ex_U \<subseteq> el (\<Phi> d_U)\<close>)
          show "e (gprj V d_U z) \<in> el (\<Phi> d_U)"
            using calculation(8) z_U_def by blast
          show "e_U \<in> el (\<Phi> d_U)"
            by (simp add: \<open>e_U \<in> el (\<Phi> d_U)\<close>)
          show "is_inf (\<Phi> d_U) ex_U e_U"
            using \<open>Poset.valid (\<Phi> d_U)\<close> \<open>e_U \<in> el (\<Phi> d_U)\<close> \<open>ex_U \<subseteq> el (\<Phi> d_U)\<close> \<open>some_e_U = Some e_U\<close> some_e_U_def some_inf_is_inf by fastforce
          have z_U_is_lb : "\<forall> v \<in> U . Poset.le (\<Phi> d_U) (e (gprj V d_U z)) (e (ex d_U v))"
            using \<Phi>_def calculation(9) ll_def z_U_def by auto
          show "\<forall> u \<in> ex_U. Poset.le (\<Phi> d_U) (e (gprj V d_U z)) u"  using z_U_is_lb
            by (simp add: ex_U_def)
          show "le_rel (\<Phi> d_U) \<subseteq> le_rel (\<Phi> d_U)"
            by simp
        qed

        ultimately show "Poset.le ((Semigroup.poset (ordered_semigroup V))) (a, b) i"
          by (metis  \<Phi>_def \<open>(a, b) \<in> el (OVA.poset V)\<close> \<open>d i \<subseteq> d z\<close> \<open>i \<in> elems V\<close> elem_le_wrap fst_conv i_def snd_conv V_valid)
      qed
      moreover have "is_inf (OVA.poset V) U i"
        by (simp add: calculation(1) calculation(2) calculation(3) calculation(4) is_inf_def)

      ultimately show "U \<subseteq> el (poset V) \<and>
    i \<in> el (OVA.poset V) \<and>
    (\<forall>u\<in>U. Poset.le (OVA.poset V) i u) \<and> (\<forall>z\<in>el (OVA.poset V). (\<forall>u\<in>U. Poset.le (OVA.poset V) z u) \<longrightarrow> Poset.le (OVA.poset V) z i) "
        by blast
    qed

    thus "\<exists>a b. is_inf (OVA.poset V) U (a, b)"
      using i_def by auto
  qed
qed

end