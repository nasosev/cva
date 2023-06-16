theory OVA
  imports Main Presheaf OrderedSemigroup Grothendieck Poset
begin

type_synonym ('A, 'a) Valuation = "('A set \<times> 'a)"

record ('A, 'a) OVA =
  presheaf :: "('A, 'a) Presheaf"
  neutral :: "('A, unit, 'a) PresheafMap"
  ordered_semigroup :: "(('A, 'a) Valuation) OrderedSemigroup"

definition comb :: "('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"comb V a b =  (OrderedSemigroup.mult (ordered_semigroup V)) $$ (a, b)"

abbreviation "comb_V a V b \<equiv> comb V a b"

notation comb_V ("_ \<otimes>\<^sub>_ _")

term "A \<otimes>\<^sub>V B"

definition neut :: "('A, 'a) OVA \<Rightarrow> 'A set \<Rightarrow> ('A, 'a) Valuation" where
"neut V A = (A, (Presheaf.nat (neutral V) $ A) $$ ())"

definition space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space V = Presheaf.space (presheaf V)"

definition poset :: "('A,'a) OVA \<Rightarrow> (('A, 'a) Valuation) Poset" where
"poset V = OrderedSemigroup.poset (ordered_semigroup V)"

definition elems :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems V = Poset.el (OrderedSemigroup.poset (ordered_semigroup V))"

definition opens :: "('A,'a) OVA \<Rightarrow> 'A Open set" where
"opens V = Space.opens (space V)"

definition inclusions :: "('A,'a) OVA \<Rightarrow> 'A Inclusion set" where
"inclusions V = Space.inclusions (space V)"

definition local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems V A = Poset.el (Presheaf.ob (presheaf V) $ A)"

definition gle :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle V a b = Poset.le (OrderedSemigroup.poset (ordered_semigroup V)) a b"

definition le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"le V A a b = Poset.le (Presheaf.ob (presheaf V) $ A) a b"

definition gprj :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gprj V B a \<equiv> if B \<subseteq> d a \<and> B \<in> opens V then (B, Presheaf.ar (presheaf V) $ (Space.make_inclusion (space V) B (d a)) $$ (e a)) else undefined"

definition gext :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gext V A b \<equiv> if d b \<subseteq> A \<and> A \<in> opens V then (comb V (neut V A) b) else undefined"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid V \<equiv>
    let
        \<Phi> = presheaf V;
        E = neutral V;
        \<epsilon> = neut V;
        T = space V;
        S = ordered_semigroup V;
        mul = comb V;
        elems = elems V;
        pr = gprj V;

        welldefined = Presheaf.valid \<Phi>
                      \<and> OrderedSemigroup.valid S
                      \<and> Presheaf.valid_map E
                      \<and> T = Presheaf.map_space E
                      \<and> Presheaf.cod E = \<Phi>
                      \<and> Presheaf.dom E = Presheaf.terminal T
                      \<and> OrderedSemigroup.poset S = gc \<Phi>;

        domain_law = \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow> d (mul a b) = d a \<union> d b;
        neutral_law_left = (\<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> mul (\<epsilon> A) a = a);
        neutral_law_right = (\<forall>A a. A \<in> opens V \<and> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> mul a (\<epsilon> A) = a);
        comb_law_left = (\<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
             pr (d a) (mul a b) = mul a (pr (d a \<inter> d b) b));
        comb_law_right = (\<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
             pr (d b) (mul a b) = mul (pr (d a \<inter> d b) a) b)
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
  defines "mul \<equiv> comb V"
  defines "elem \<equiv> elems V"
  defines "pr \<equiv> gprj V"
  assumes welldefined : "Presheaf.valid \<Phi> \<and> OrderedSemigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> OrderedSemigroup.poset S = gc \<Phi>"
  assumes domain_law : " \<forall> a b . a \<in> elem \<longrightarrow> b \<in> elem \<longrightarrow> d (mul a b) = d a \<union> d b"
  assumes neutral_law_left : "( \<forall> A a . A \<in> opens V \<longrightarrow> a \<in> elem \<longrightarrow> d a = A \<longrightarrow> mul (\<epsilon> A) a = a)"
  assumes neutral_law_right : "(\<forall> A a .A \<in> opens V \<and> a \<in> elem \<longrightarrow> d a = A \<longrightarrow> mul a (\<epsilon> A) = a)"
  assumes comb_law_left : "(\<forall> a b . a \<in> elem \<longrightarrow> b \<in> elem \<longrightarrow>
             pr (d a) (mul a b) = mul a (pr (d a \<inter> d b) b))"
  assumes comb_law_right : "(\<forall> a b . a \<in> elem \<longrightarrow> b \<in> elem \<longrightarrow>
              pr (d b) (mul a b) = mul (pr (d a \<inter> d b) a) b)"
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
  using mul_def domain_law elem_def apply blast
  using mul_def domain_law elem_def apply blast
  using mul_def domain_law elem_def apply blast
  using T_def \<epsilon>_def mul_def elem_def neutral_law_left apply presburger
  using T_def \<epsilon>_def mul_def elem_def neutral_law_right apply blast
  using comb_law_left elem_def mul_def pr_def apply blast
  using comb_law_right elem_def mul_def pr_def by blast

lemma valid_welldefined  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<Phi> = presheaf V; E = neutral V; \<epsilon> = neut V; T = space V; S = ordered_semigroup V in
    Presheaf.valid \<Phi> \<and> OrderedSemigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> OrderedSemigroup.poset S = gc \<Phi>"
  by (simp add: valid_def Let_def)

lemma valid_gc_poset :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> OrderedSemigroup.poset (ordered_semigroup V) = gc (presheaf V)"
  by (meson OVA.valid_welldefined)

lemma valid_domain_law  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow>
    \<forall> a b. a \<in> elems V \<longrightarrow> b \<in> elems V \<longrightarrow> d (comb V a b) = d a \<union> d b"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_left  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<epsilon> = neut V; mul = comb V; elems = elems V in
    \<forall>A a. A \<in> opens V \<longrightarrow> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> mul (\<epsilon> A) a = a"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_right  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let  \<epsilon> = neut V; mul = comb V; elems = elems V in
    \<forall>A a. A \<in> opens V \<and> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> mul a (\<epsilon> A) = a"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_left  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<Phi> = presheaf V; T = space V; S = ordered_semigroup V; mul = comb V; elems = elems V; pr = gprj V in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
      pr (d a) (mul a b) = mul a (pr (d a \<inter> d b) b)"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_right  :
  fixes V :: "('A,'a) OVA"
  shows "valid V \<Longrightarrow> let \<Phi> = presheaf V; T = space V; S = ordered_semigroup V; mul = comb V; elems = elems V; pr = gprj V in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
      pr (d b) (mul a b) = mul (pr (d a \<inter> d b) a) b"
  by (simp add: valid_def Let_def)

lemma neutral_element : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> d (neut V A) = A "
  by (simp add: d_def neut_def)

lemma neutral_is_element :
fixes V :: "('A,'a) OVA" and A :: "'A Open"
defines "\<epsilon>A \<equiv> neut V A"
assumes "valid V" and "A \<in> opens V"
shows "neut V A \<in> elems V"
proof -
   have "Poset.valid_map  (PresheafMap.nat (neutral V) $ A)"
     by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined assms(2) assms(3))
    moreover have "Poset.cod (PresheafMap.nat (neutral V) $ A) = (Presheaf.ob (presheaf V)) $ A"
      by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined assms(2) assms(3))
  moreover have "Presheaf.dom (neutral V) = Presheaf.terminal (space V)"
    by (meson OVA.valid_welldefined assms(2))
moreover have "(Presheaf.ob ( Presheaf.terminal  (space V))) $ A = Poset.discrete"
  by (metis OVA.opens_def Presheaf.Presheaf.select_convs(2) UNIV_I assms(3) const_app terminal_def)
  moreover have "Poset.dom  (PresheafMap.nat (neutral V) $ A) = Poset.discrete"
    by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined assms(2) assms(3) calculation(4))
  moreover have "(PresheafMap.nat (neutral V) $ A $$ ()) \<in> Poset.el ((Presheaf.ob (presheaf V)) $ A)"
    by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined Poset.fun_app2 Presheaf.valid_welldefined UNIV_unit UNIV_witness assms(2) assms(3) calculation(1) calculation(2) calculation(4) calculation(5) singletonD terminal_value)
ultimately show ?thesis using neut_def elems_def
  by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined assms(2) assms(3) local_elem_gc)
qed

lemma neutral_local_element :
  fixes V :: "('A,'a) OVA" and A :: "'A Open"
  defines "\<epsilon>A \<equiv> neut V A"
  defines "\<epsilon> \<equiv> Presheaf.nat (neutral V)"
  defines "\<Phi>A \<equiv> Presheaf.ob (presheaf V) $ A"
  assumes valid_V : "valid V"
  and domain : "A \<in> opens V"
shows " e \<epsilon>A \<in> Poset.el \<Phi>A"
proof -
  have "Poset.valid_map (\<epsilon> $ A)"
    by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined \<epsilon>_def domain valid_V)
  moreover have "Poset.cod (\<epsilon> $ A) = \<Phi>A"
    by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined \<Phi>A_def \<epsilon>_def domain valid_V)
  moreover have "e \<epsilon>A =  (\<epsilon> $ A) $$ ()"
    by (simp add: \<epsilon>A_def \<epsilon>_def e_def neut_def)
  moreover have "Poset.dom  (\<epsilon> $ A) = Presheaf.ob (Presheaf.terminal (space V)) $ A"
    by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined \<epsilon>_def domain valid_V)
  moreover have "(Poset.dom (\<epsilon> $ A)) =  Poset.discrete" using Presheaf.terminal_def
    by (metis OVA.opens_def Presheaf.Presheaf.select_convs(2) UNIV_I calculation(4) const_app domain)
  moreover have "() \<in> Poset.el (Poset.dom (\<epsilon> $ A))"
    by (simp add: calculation(5) discrete_def)
    ultimately show ?thesis
      by (metis Poset.fun_app2)
  qed

lemma d_neut : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> \<epsilon>A = neut V A \<Longrightarrow> d \<epsilon>A = A"
  by (simp add: d_def neut_def)

lemma d_gprj : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow>  B \<in> opens V
\<Longrightarrow> A \<in> opens V\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d a = A \<Longrightarrow>  a_B = gprj V B a
\<Longrightarrow> d a_B = B"
  by (simp add: d_def gprj_def)

lemma d_gext : "valid V \<Longrightarrow>  b \<in> elems V \<Longrightarrow>  B \<in> opens V
\<Longrightarrow> A \<in> opens V\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d b = B \<Longrightarrow>  b__A = gext V A b
\<Longrightarrow> d b__A = A"
  by (simp add: d_neut gext_def neutral_is_element sup.order_iff valid_domain_law)

lemma local_inclusion_element : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> A = d a \<Longrightarrow> ea = e a
\<Longrightarrow> \<Phi> = (presheaf V) \<Longrightarrow> ob_A = ob \<Phi> $ A
\<Longrightarrow> ea \<in> el ob_A"
  by (metis OVA.valid_welldefined e_def elems_def gc_elem_local)

lemma global_inclusion_element : "valid V \<Longrightarrow> A \<in> opens V
\<Longrightarrow> \<Phi> = presheaf V \<Longrightarrow> \<Phi>A =(Presheaf.ob \<Phi>) $ A \<Longrightarrow> a \<in> Poset.el \<Phi>A
\<Longrightarrow>  (A, a) \<in> elems V"
  by (metis OVA.valid_welldefined d_neut elems_def local_dom local_elem_gc neutral_is_element)

lemma local_inclusion_domain : "valid V \<Longrightarrow> a \<in> elems V \<Longrightarrow> A = d a \<Longrightarrow> A \<in> opens V"
  by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined elems_def local_dom)




lemma gprj_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes valid_V : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A"
  and "d a = A"
  and "a \<in> elems V"
defines "pr \<equiv> gprj V"
and "l  \<equiv> (\<lambda> U a b . le V U (e a) (e b)) :: 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool"
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
    by (metis (no_types, lifting) \<Phi>1_def assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(2) d_gprj e_def g_def gprj_def i_CB_def pr_def snd_conv valid_V)
  moreover have "Presheaf.valid (presheaf V)"
    by (meson OVA.valid_welldefined valid_V)
  moreover have "Space.valid_inclusion i_CB \<and> Space.space i_CB = space V"
    by (metis Inclusion.select_convs(1) OVA.opens_def OVA.space_def assms(3) assms(4) assms(5) calculation(4) i_CB_def make_inclusion_def space_valid valid_make_inclusion)
  moreover have "i_CB \<in> inclusions V"
    by (simp add: OVA.inclusions_def Space.inclusions_def calculation(5))
  moreover have "Space.valid_inclusion i_BA \<and> Space.space i_BA = space V"
    by (metis Inclusion.select_convs(1) OVA.opens_def OVA.space_def assms(2) assms(3) assms(6) calculation(4) i_BA_def make_inclusion_def space_valid valid_make_inclusion)
    moreover have "i_BA \<in> inclusions V"
      using OVA.inclusions_def Space.inclusions_def calculation(7) by blast
moreover have "Space.valid_inclusion i_CA \<and> Space.space i_CA = space V"
  by (metis Inclusion.select_convs(1) OVA.opens_def OVA.space_def assms(2) assms(4) assms(5) assms(6) calculation(4) i_CA_def make_inclusion_def order.trans space_valid valid_make_inclusion)
  moreover have "i_CA = Space.compose i_BA i_CB" using Space.compose_def
    by (metis Inclusion.select_convs(2) Inclusion.select_convs(3) calculation(5) calculation(7) i_BA_def i_CA_def i_CB_def make_inclusion_def)
  moreover have "Poset.valid_map f \<and> Poset.valid_map g \<and> Poset.valid_map h"
    by (simp add: OVA.space_def Space.inclusions_def \<Phi>1_def calculation(4) calculation(5) calculation(7) calculation(9) f_def g_def h_def poset_maps_valid)
  moreover have "Space.cod i_BA = A \<and> Space.dom i_BA = B "
    by (simp add: i_BA_def make_inclusion_def)
  moreover have "Space.cod i_CB = B \<and> Space.dom i_CB = C "
    by (simp add: i_CB_def make_inclusion_def)
  moreover have "Space.cod i_CA = A \<and> Space.dom i_CA = C "
    by (simp add: i_CA_def make_inclusion_def)
  moreover have "Poset.dom f = Presheaf.ob (presheaf V) $ A"
    by (metis OVA.inclusions_def OVA.space_def \<Phi>1_def calculation(12) calculation(4) calculation(8) dom_proj f_def)
    moreover have "Poset.cod f  = Presheaf.ob (presheaf V) $ B \<and> Poset.dom g  = Presheaf.ob (presheaf V) $ B"
      by (metis OVA.inclusions_def OVA.space_def \<Phi>1_def calculation(12) calculation(13) calculation(4) calculation(6) calculation(8) cod_proj dom_proj f_def g_def)
    moreover have " (\<Phi>1 $ i_CB) $$ ((\<Phi>1 $ i_BA) $$ (e a)) =  (\<Phi>1 $ i_CA) $$ (e a)"  using Poset.compose_app
      by (metis OVA.inclusions_def OVA.space_def \<Phi>1_def assms(7) assms(8) calculation(10) calculation(11) calculation(12) calculation(13) calculation(15) calculation(16) calculation(4) calculation(6) calculation(8) f_def g_def local_inclusion_element valid_V valid_composition)
  ultimately show ?thesis
    by (metis f_def g_def)
qed

lemma combine_monotone : "valid V \<Longrightarrow>  a1 \<in> elems V \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> b1 \<in> elems V \<Longrightarrow> b2 \<in> elems V
\<Longrightarrow> gle V a1 a2 \<Longrightarrow> gle V b1 b2
\<Longrightarrow> gle V (comb V a1 b1) (comb V a2 b2)"
  unfolding gle_def comb_def
  by (metis OVA.valid_welldefined elems_def valid_monotone)

lemma le_imp_gle : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> local_elems V A
 \<Longrightarrow> a2 \<in> local_elems V A \<Longrightarrow> le V A a1 a2 \<Longrightarrow> gle V (A,a1) (A,a2)"
  unfolding local_elems_def le_def gle_def
  apply (frule valid_welldefined)
  apply (simp_all add: Let_def)
  apply safe
  apply auto
  apply (simp add: gc_def)
  apply (simp_all add: Let_def)
  apply safe
  apply (simp add: OVA.opens_def OVA.space_def)
  by (metis (no_types, lifting) OVA.opens_def OVA.space_def Poset.ident_app Presheaf.valid_welldefined make_inclusion_ident posets_valid valid_gc_1)

lemma le_imp_gle2 : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> elems V
 \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> d a1 = A \<Longrightarrow> d a2 = A \<Longrightarrow> le V A (e a1) (e a2) \<Longrightarrow> gle V a1 a2"
  by (metis d_def e_def le_imp_gle local_elems_def local_inclusion_element prod.collapse)

lemma gle_imp_le : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow> a1 \<in> elems V \<Longrightarrow> d a1 = A \<Longrightarrow> d a2 = A
 \<Longrightarrow> a2 \<in> elems V \<Longrightarrow> gle V a1 a2 \<Longrightarrow> le V A (e a1) (e a2)"
  unfolding local_elems_def le_def gle_def
  apply (frule valid_welldefined)
  apply (simp_all add: Let_def)
  apply safe
  apply auto
  apply (simp add: gc_def)
  apply (simp_all add: Let_def)
  apply safe
  by (simp add: d_def e_def make_inclusion_ident posets_valid space_valid)

lemma gprj_monotone :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a1 a2 :: "('A, 'a) Valuation"
  defines "pr \<equiv> gprj V"
  and "gl \<equiv> gle V"
  assumes valid_V: "valid V"
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
    using gle_imp_le
    by (metis \<Phi>A_def assms(10) assms(6) assms(7) assms(8) assms(9) le_def valid_V)
  moreover have "Poset.le \<Phi>A (e a1) (e a2)"
    using assms(11) calculation(2) by blast
  moreover have "i \<in> inclusions V \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) OVA.inclusions_def OVA.opens_def OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined Space.inclusions_def assms(4) assms(5) assms(6) assms(7) d_def i_def make_inclusion_def mem_Collect_eq valid_V valid_make_inclusion)
  moreover have "Poset.le \<Phi>B (\<Phi>i $$ (e a1)) (\<Phi>i $$ (e a2))" using Presheaf.prj_monotone
    by (metis OVA.inclusions_def OVA.space_def OVA.valid_welldefined \<Phi>A_def \<Phi>B_def \<Phi>i_def assms(10) assms(7) assms(9) calculation(3) calculation(4) local_inclusion_element valid_V)
  ultimately show ?thesis
    by (metis OVA.inclusions_def OVA.space_def OVA.valid_welldefined \<Phi>i_def assms(10) assms(4) assms(5) assms(7) assms(8) assms(9) d_def gprj_def i_def image gl_def le_def le_imp_gle local_elems_def local_inclusion_element pr_def valid_V)
qed





lemma stability:
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes valid_V: "valid V"
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
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.inclusions_def OVA.opens_def OVA.space_def OVA.valid_welldefined Space.inclusions_def assms(2) assms(3) assms(4) i_def make_inclusion_def mem_Collect_eq space_valid valid_V valid_make_inclusion)
    moreover have v1: "Poset.valid_map  (Presheaf.ar one $ i)" using Presheaf.poset_maps_valid
      by (metis OVA.inclusions_def OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined calculation(4) one_def terminal_def valid_V)
      moreover have v2: "Poset.valid_map (f $ B)"
        by (metis OVA.opens_def OVA.valid_welldefined Presheaf.valid_map_welldefined assms(3) f_def valid_V)
    moreover have "Presheaf.valid one"
      by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined one_def valid_V)
  moreover have "(Presheaf.ar one $ i ) $$ ()  = ()"
    by simp
moreover have "() \<in> Poset.el (Poset.dom  (ar one $ i))" using Presheaf.terminal_value
  by (metis (full_types) OVA.inclusions_def OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) UNIV_unit UNIV_witness calculation(1) calculation(4) calculation(7) dom_proj old.unit.exhaust space_valid terminal_def valid_V valid_inclusion_cod)
moreover have "((f $ B) \<cdot> (ar one $ i)) $$ () = ((f $ B) $$ ((ar one $ i)) $$ ())"
  by (metis OVA.inclusions_def OVA.opens_def OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined assms(3) calculation(3) calculation(4) calculation(9) cod_proj compose_app f_def one_def terminal_def v1 valid_V)
  moreover have "((Presheaf.ar (presheaf V) $ i) \<cdot> (f $ A)) $$ ()=  e \<epsilon>B"
    by (metis OVA.inclusions_def OVA.valid_welldefined \<epsilon>B_def calculation(10) calculation(3) calculation(4) calculation(8) e_def f_def neut_def one_def snd_conv valid_V valid_map_naturality)
  moreover have "e \<epsilon>A=   (f $ A) $$ ()"
    by (simp add: \<epsilon>A_def e_def f_def neut_def)
  ultimately show ?thesis
    by (smt (verit) OVA.inclusions_def OVA.opens_def OVA.space_def OVA.valid_welldefined Presheaf.valid_map_welldefined UNIV_unit UNIV_witness \<epsilon>A_def \<epsilon>B_def assms(2) assms(3) assms(4) compose_app dom_proj f_def gprj_def i_def neut_def neutral_element old.unit.exhaust poset_maps_valid terminal_value valid_V valid_map_naturality)
qed

(* [Remark 3 cont., CVA] *)
lemma local_mono_imp_global : "valid V \<Longrightarrow> A \<in> opens V \<Longrightarrow>  a1 \<in> local_elems V A \<Longrightarrow>  a1' \<in> local_elems V A
\<Longrightarrow>  a2' \<in> local_elems V A \<Longrightarrow>  a2' \<in> local_elems V A \<Longrightarrow> le V A a1 a2 \<Longrightarrow> le V A a1' a2'
 \<Longrightarrow> gle V (comb V (A,a1) (A,a1')) (comb V (A,a2) (A,a2'))"
  by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined Poset.valid_welldefined combine_monotone elems_def le_def le_imp_gle local_elem_gc local_elems_def posets_valid)

(* [Remark 3 cont., CVA] *)
lemma global_mono_imp_local : "valid V \<Longrightarrow> A \<in> opens V
\<Longrightarrow> a1 \<in> elems V \<Longrightarrow>  a1' \<in> elems V\<Longrightarrow>  a2' \<in> elems V \<Longrightarrow>  a2' \<in> elems V
\<Longrightarrow> d a1 = A \<Longrightarrow> d a1' = A \<Longrightarrow> d a2 = A \<Longrightarrow> d a2' = A
\<Longrightarrow> gle V a1 a2 \<Longrightarrow> gle V a1' a2'
\<Longrightarrow> le V A (e (comb V a1 a1')) (e (comb V a2 a2'))"
  by (smt (verit, ccfv_SIG) OVA.valid_welldefined comb_def d_neut e_def elems_def gle_def le_def local_le neutral_is_element valid_domain_law valid_gc_welldefined valid_monotone valid_neutral_law_right)

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
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.inclusions_def OVA.opens_def OVA.space_def OVA.valid_welldefined Space.inclusions_def assms(1) assms(2) assms(3) assms(4) assms(6) i_def make_inclusion_def mem_Collect_eq space_valid valid_make_inclusion)
  moreover have "gprj V B a = (B, a_B)"
    by (simp add: \<Phi>i_def a_B_def assms(3) assms(4) assms(6) gprj_def i_def)
    moreover have "Presheaf.valid (presheaf V)"
    by (meson OVA.valid_welldefined assms(1))
  moreover have "Poset.valid \<Phi>B"
    by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined \<Phi>B_def assms(1) assms(3) posets_valid)
  moreover have "Poset.valid_map \<Phi>i"  using Presheaf.poset_maps_valid
    by (metis OVA.inclusions_def OVA.space_def \<Phi>i_def calculation(1) calculation(3))
  moreover have "e a \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def assms(1) assms(5) assms(6) local_inclusion_element)
  moreover have "Space.cod i = A \<and> Space.dom i = B \<and> i \<in> inclusions V"
    by (metis Inclusion.select_convs(2) Inclusion.select_convs(3) assms(6) calculation(1) i_def make_inclusion_def)
  moreover have "a_B \<in> Poset.el \<Phi>B"
    by (metis OVA.inclusions_def OVA.space_def \<Phi>A_def \<Phi>B_def \<Phi>i_def a_B_def calculation(3) calculation(6) calculation(7) image)
    moreover have "Poset.le \<Phi>B a_B a_B "
      by (simp add: calculation(4) calculation(8) valid_reflexivity)
  moreover have "valid V" by fact
  ultimately show ?thesis apply (simp add: gle_def   )
    apply (frule valid_welldefined)
    apply (simp_all add: Let_def)
    apply (simp add: gc_def Let_def)
    apply auto
         apply (metis OVA.opens_def OVA.space_def assms(2) assms(6) d_def fst_conv)
    apply (metis OVA.opens_def OVA.space_def assms(3))
    apply (metis \<Phi>A_def assms(6) d_def e_def fst_eqD snd_eqD)
    using \<Phi>B_def apply force
    apply (metis assms(4) assms(6) d_def fst_conv subsetD)
    by (metis (mono_tags, opaque_lifting) OVA.space_def \<Phi>B_def \<Phi>i_def a_B_def d_def e_def fst_conv i_def snd_conv)
qed


lemma elem_le_wrap :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" and A B :: "('A Open)"
  assumes valid_V : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and dom_A : "d a = A" and dom_B : "d b = B"
  and b_subseteq_a : "B \<subseteq> A" and a_b_le_b : "le V B (e (gprj V B a)) (e b)"
shows "gle V a b"
proof -
  define "\<Phi>" where "\<Phi> = presheaf V"
  define "\<Phi>A" where "\<Phi>A = (Presheaf.ob \<Phi>) $ A"
  define "\<Phi>B" where "\<Phi>B = (Presheaf.ob \<Phi>) $ B"
  define "a_B" where "a_B = gprj V B a"

  have "d a_B = d b"
    by (metis a_B_def a_elem b_elem b_subseteq_a d_gprj dom_A dom_B local_inclusion_domain valid_V)

  moreover have "a_B \<in> elems V"
    by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined Poset.valid_welldefined a_B_def a_b_le_b b_elem b_subseteq_a dom_A dom_B e_def global_inclusion_element gprj_def le_def local_inclusion_domain posets_valid snd_conv valid_V) 
  moreover have "b \<in> elems V"
    by (simp add: b_elem)
  moreover have a1: "Presheaf.valid \<Phi>"
    by (metis OVA.valid_welldefined \<Phi>_def valid_V)
  moreover have a2: "A \<in> opens V"
    using a_elem  dom_A dom_B local_inclusion_domain valid_V by blast
  moreover have a3: "B \<in> opens V"
    using  b_elem dom_A dom_B local_inclusion_domain valid_V by blast
  moreover have a4: "e a \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def \<Phi>_def a_elem dom_A local_inclusion_element valid_V)
  moreover have a5: "e b \<in> Poset.el \<Phi>B"
    by (metis \<Phi>B_def \<Phi>_def b_elem dom_B local_inclusion_element valid_V)
  moreover have a6: "B \<subseteq> A"
    by (simp add: b_subseteq_a)
  moreover have a7: "le V B (e a_B) (e b)"
    by (simp add: a_B_def a_b_le_b)
  moreover have "Presheaf.space \<Phi> = space V"
    by (simp add: OVA.space_def \<Phi>_def) 
  ultimately show ?thesis 
    by (metis \<Phi>_def a_B_def a_elem dom_A dom_B elems_def gle_def id_le_gprj le_imp_gle2 valid_V valid_gc valid_gc_poset valid_transitivity) 
    qed

lemma gprj_elem : "valid V \<Longrightarrow>  a \<in> elems V \<Longrightarrow>  B \<in> opens V
\<Longrightarrow> A \<in> opens V\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d a = A \<Longrightarrow>  a_B = gprj V B a \<Longrightarrow> a_B \<in> elems V"
  by (metis OVA.valid_welldefined elems_def gle_def id_le_gprj valid_gc_welldefined)

lemma gext_elem :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes "valid V"
  and  "b \<in> elems V" and "B \<in> opens V" and "A \<in> opens V"
  and  "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V" and "d b = B"
defines "ex \<equiv> gext V"
and "b__A \<equiv> gext V A b"
and "mul \<equiv> comb V"
shows "b__A \<in> elems V "
proof -
  have "valid V"
    by (simp add: assms(1))
  moreover have "B \<subseteq> A \<and> B \<in> opens V \<and> A \<in> opens V \<and> d b = B"
    by (simp add: assms(3) assms(4) assms(5) assms(8))
  moreover have "b__A = mul (neut V A) b"
    by (simp add: b__A_def assms(4) assms(5) assms(8) gext_def mul_def)
  ultimately show ?thesis
    by (smt (verit) OVA.valid_welldefined OrderedSemigroup.valid_def Poset.valid_def assms(2) comb_def elems_def mul_def neutral_is_element valid_monotone)
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
proof -
  have "Poset.valid \<Phi>B"
    by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined \<Phi>B_def assms(4) assms(6) posets_valid)
  moreover have "d a_B = B"
    using a_B_def assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) d_gprj by blast
  define "i" where "i = Space.make_inclusion (space V) B A"
  define "\<Phi>i" where "\<Phi>i = Presheaf.ar (presheaf V) $ i"
  moreover have "i \<in> inclusions V"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.inclusions_def OVA.opens_def OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined Space.inclusions_def assms(4) assms(5) assms(6) assms(7) i_def make_inclusion_def mem_Collect_eq valid_make_inclusion)
  moreover have "Poset.valid_map \<Phi>i"
    by (metis OVA.inclusions_def OVA.space_def OVA.valid_welldefined \<Phi>i_def assms(4) calculation(3) poset_maps_valid)
  moreover have "a_B = (B, \<Phi>i $$ e a)"
    by (simp add: a_B_def \<Phi>i_def assms(5) assms(6) assms(8) gprj_def i_def)
  moreover have "Presheaf.valid (presheaf V)"
    by (meson OVA.valid_welldefined assms(4))
  moreover have "Space.dom i = B"
    by (simp add: i_def make_inclusion_def)
  moreover have "Poset.cod \<Phi>i = \<Phi>B"
    by (metis OVA.inclusions_def OVA.space_def \<Phi>B_def \<Phi>i_def calculation(3) calculation(6) calculation(7) cod_proj)
  moreover have "\<Phi>i $$ e a \<in> Poset.el \<Phi>B"
    by (metis OVA.valid_welldefined \<Phi>B_def \<open>d a_B = B\<close> a_B_def assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) calculation(5) elems_def gc_elem_local gprj_elem snd_conv)
  ultimately show ?thesis
    by (simp add: e_def)
qed

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
proof -
  have "valid V"
    by (simp add: assms(4))
  moreover have "Poset.valid \<Phi>A"
    by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined \<Phi>A_def assms(7) calculation posets_valid)
    moreover have "d b__A = A"
      using b__A_def assms(5) assms(6) assms(7) assms(8) assms(9) calculation(1) d_gext by blast
  define "i" where "i = Space.make_inclusion (space V) B A"
  define "\<Phi>i" where "\<Phi>i = Presheaf.ar (presheaf V) $ i"
  moreover have "i \<in> inclusions V"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.inclusions_def OVA.opens_def OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined Space.inclusions_def assms(5) assms(6) assms(7) calculation(1) i_def make_inclusion_def mem_Collect_eq valid_make_inclusion)
   moreover have "Poset.valid_map \<Phi>i"
     by (metis OVA.inclusions_def OVA.space_def OVA.valid_welldefined \<Phi>i_def calculation(1) calculation(4) poset_maps_valid)
  moreover have "b__A = comb V (neut V A) b"
    by (simp add: assms(5) assms(7) assms(8) b__A_def gext_def)
  moreover have "... = (A, e (comb V (neut V A) b))"
    by (metis \<open>d b__A = A\<close> calculation(6) d_def e_def prod.collapse)
  ultimately show ?thesis
    by (metis b__A_def \<Phi>A_def \<open>d b__A = A\<close> assms(5) assms(6) assms(7) assms(8) assms(9) gext_elem local_inclusion_element)
qed

lemma ext_prj_adjunction_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf V"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "mul \<equiv> comb V"
  defines "\<epsilon>A \<equiv> neut V (d a)"
  assumes valid_V : "valid V"
  and elems : "a \<in> elems V \<and> b \<in> elems V"
  and doms : "d a = A \<and> d b = B" and "B \<subseteq> A"
  and LHS: "le V (d b) (e (gprj V B a)) (e b)"
  shows "le V (d a) (e a) (e (mul \<epsilon>A b))"
proof -
  have "valid V \<and> le V (d b) (e (gprj V B a)) (e b)"
    by (simp add: LHS valid_V)
  define "a_B" where "a_B \<equiv> (gprj V B a)"
  define "ea_B" where "ea_B \<equiv> e a_B"
  define "eb" where "eb \<equiv> e b"
  define "A" where "A \<equiv> d a"
  define "B" where "B \<equiv> d b"
  moreover have "gle V a a_B"
    by (metis a_B_def assms(8) doms elems id_le_gprj local_inclusion_domain valid_V)
  moreover have "a = mul \<epsilon>A a"
    by (metis \<epsilon>A_def elems local_inclusion_domain mul_def valid_neutral_law_left valid_V)
  moreover have a_B_le_b : "le V B ea_B eb"
    by (simp add: a_B_def B_def LHS ea_B_def eb_def)
  moreover have "Poset.valid (\<Phi>0 A)"
    by (metis A_def OVA.valid_welldefined \<Phi>0_def \<Phi>_def elems elems_def local_dom posets_valid valid_V)
  moreover have "d \<epsilon>A = A"
    by (simp add: A_def \<epsilon>A_def d_def neut_def)
  moreover have "Poset.valid (\<Phi>0 A)"
    using calculation(5) by auto
  moreover have " e \<epsilon>A \<in> Poset.el (\<Phi>0 A)"  using neutral_local_element
    using A_def \<Phi>0_def \<Phi>_def \<epsilon>A_def elems local_inclusion_domain valid_V by blast
  moreover have "le V A (e \<epsilon>A) (e \<epsilon>A)"
    by (metis \<Phi>0_def \<Phi>_def calculation(5) calculation(8) le_def valid_reflexivity)
    define "gc_poset" where "gc_poset = (OrderedSemigroup.poset (ordered_semigroup V))"
  moreover have "Poset.valid gc_poset"
    by (metis OVA.valid_welldefined OrderedSemigroup.valid_welldefined gc_poset_def valid_V)
  moreover have "\<epsilon>A \<in> Poset.el gc_poset" using gc_poset_def   \<epsilon>A_def
    by (metis elems elems_def local_inclusion_domain neutral_is_element valid_V)
  moreover have "gle V \<epsilon>A \<epsilon>A" using gle_def
    by (metis calculation(10) calculation(11) gc_poset_def valid_reflexivity)
  moreover have "gle V (mul \<epsilon>A a) (mul \<epsilon>A a_B)"
    by (metis (no_types, lifting) OVA.valid_welldefined Poset.valid_welldefined calculation(10) calculation(12) calculation(2) comb_def gc_poset_def gle_def mul_def valid_monotone valid_V)
  moreover have "d a_B = B \<and> d b = B"
    by (metis a_B_def B_def assms(8) d_gprj doms elems local_inclusion_domain valid_V)
  moreover have "a_B = (B, ea_B) \<and> b = (B, eb)"
    by (metis calculation(14) d_def e_def ea_B_def eb_def prod.collapse)
  moreover have "gle V a_B b"  using  a_B_le_b
    by (metis a_B_def assms(8) calculation(14) doms ea_B_def eb_def elems gprj_elem le_imp_gle2 local_inclusion_domain valid_V)
  moreover have "gle V (mul \<epsilon>A a_B) (mul \<epsilon>A b)"
    by (metis OVA.valid_welldefined calculation(12) calculation(16) combine_monotone elems_def gle_def mul_def valid_gc_welldefined valid_V)
moreover have "gle V (mul \<epsilon>A a) (mul \<epsilon>A a_B)"
  by (simp add: calculation(13))
moreover have "gle V a (mul \<epsilon>A a_B)"
  using calculation(13) calculation(3) by auto
  moreover have "A \<union> B = A"
    by (simp add: A_def B_def Un_absorb2 assms(8) doms)
  moreover have "d (mul \<epsilon>A a_B) = A" using valid_domain_law
    by (metis Poset.valid_welldefined calculation(10) calculation(11) calculation(14) calculation(2) calculation(20) calculation(6) elems_def gc_poset_def gle_def mul_def valid_V)
  ultimately show ?thesis
    by (smt (verit) A_def Poset.valid_welldefined elems_def gle_def gle_imp_le local_inclusion_domain mul_def valid_domain_law valid_V valid_transitivity)
qed

lemma ext_prj_adjunction_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and a b :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf V"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "mul \<equiv> comb V"
  defines "\<epsilon>A \<equiv> neut V (d a)"
  assumes valid_V : "valid V"
  and elems : "a \<in> elems V \<and> b \<in> elems V"
  and doms : "d a = A \<and> d b = B"
  and "A \<in> opens V" and "B \<in> opens V" and "B \<subseteq> A"
  and RHS: "le V (d a) (e a) (e (mul \<epsilon>A b))"
shows "le V (d b) (e (gprj V B a)) (e b)"
proof -
  have "valid V" and "le V A (e a) (e (mul \<epsilon>A b))"
     apply (simp add: RHS valid_V)
    using RHS doms by blast
  moreover have "A \<union> B = A"
    using assms(10) by blast
    moreover have" d a = A"
      using doms by fastforce
    moreover have  "d  (mul \<epsilon>A b) = A"
      by (simp add: \<epsilon>A_def assms(8) calculation(3) doms elems mul_def neutral_element neutral_is_element valid_domain_law valid_V)
      moreover have "a \<in> elems V \<and> b \<in> elems V"
      by (simp add: elems)
    moreover have "(mul \<epsilon>A b) \<in> elems V"
      by (smt (verit) OVA.valid_welldefined OrderedSemigroup.valid_def Poset.valid_welldefined \<epsilon>A_def assms(8) comb_def doms elems elems_def mul_def neutral_is_element valid_monotone valid_V valid_reflexivity)
    moreover have "gle V a (mul \<epsilon>A b)" using le_imp_gle2
      using assms(8) calculation(2) calculation(4) calculation(5) calculation(7) elems valid_V by blast
    moreover have "gle V (gprj V B a) (gprj V B (mul \<epsilon>A b))"
      using assms(10) assms(8) assms(9) calculation(5) calculation(7) calculation(8) doms elems gprj_monotone valid_V by blast
    moreover have "gprj V B (mul \<epsilon>A b) = mul (gprj V (A \<inter> B) \<epsilon>A) b"  using valid_comb_law_right
      by (metis \<epsilon>A_def assms(8) doms elems mul_def neutral_element neutral_is_element valid_V)
    define "\<epsilon>B" where "\<epsilon>B \<equiv> neut V B"
    moreover have "gprj V (A \<inter> B) \<epsilon>A = \<epsilon>B"
      by (metis Un_Int_eq(2) \<epsilon>A_def \<epsilon>B_def assms(10) assms(8) assms(9) calculation(3) doms stability valid_V)
    moreover have "mul (gprj V (A \<inter> B) \<epsilon>A) b = b"
      by (metis \<epsilon>B_def assms(9) calculation(11) doms elems mul_def valid_neutral_law_left valid_V)
    ultimately show ?thesis
      by (metis (mono_tags, lifting) OVA.valid_welldefined \<open>gprj V B (mul \<epsilon>A b) = mul (gprj V (A \<inter> B) \<epsilon>A) b\<close> assms(10) assms(8) assms(9) d_gprj elems_def gle_def gle_imp_le valid_gc_welldefined)
  qed

(* [Remark 3, CVA] *)
lemma laxity :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a a' :: "('A, 'a) Valuation"
  assumes "valid V"
  and  "A \<in> opens V" and "B \<in> opens V"  and "B \<subseteq> A"
  and  "a \<in> elems V" and "d a = A" and  "a' \<in> elems V" and "d a' = A"
defines "pr \<equiv> gprj V" and "mul \<equiv> comb V" and "gl \<equiv> gle V"
shows "le V B (e (pr B (mul a a'))) (e (mul (pr B a) (pr B a')))"
proof -
   have "gl a (pr B a)"
     using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) id_le_gprj gl_def pr_def by blast
   moreover have "gl a' (pr B a')"
     using assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) id_le_gprj gl_def pr_def by blast
   define "m1" where "m1 = mul a a'"
   define "m2" where "m2 = mul (pr B a) (pr B a')"
   moreover have "d m1 = A"
     by (simp add: assms(1) assms(5) assms(6) assms(7) assms(8) m1_def mul_def valid_domain_law)
   moreover have "d m2 = B"
     by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gprj gprj_elem m2_def mul_def neutral_element neutral_is_element pr_def valid_domain_law valid_neutral_law_right)
   moreover have "gl m1 m2"
     by (metis \<open>gl a' (pr B a')\<close> assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(1) combine_monotone gprj_elem gl_def m1_def m2_def mul_def pr_def)
   define "\<Phi>B" where "\<Phi>B = (Presheaf.ob (presheaf V)) $ B"
    moreover have "e  m2 \<in> Poset.el \<Phi>B"
      by (metis OVA.valid_welldefined \<Phi>B_def \<open>gl m1 m2\<close> assms(1) calculation(4) elems_def gle_def gl_def local_inclusion_element valid_gc_welldefined)
   moreover have "e (pr B m1) \<in> Poset.el \<Phi>B"
     by (metis OVA.valid_welldefined \<Phi>B_def \<open>gl m1 m2\<close> assms(1) assms(2) assms(3) assms(4) calculation(3) e_gprj elems_def gle_def gl_def pr_def valid_gc_welldefined)
   ultimately show ?thesis
     by (smt (verit, del_insts) OVA.valid_welldefined \<open>gl m1 m2\<close> assms(1) assms(2) assms(3) assms(4) combine_monotone elems_def ext_prj_adjunction_rhs_imp_lhs gle_def gle_imp_le id_le_gprj gl_def m1_def neutral_element neutral_is_element pr_def stability sup.order_iff valid_domain_law valid_gc_welldefined valid_neutral_law_left)
 qed

(* THEOREMS *)

(* [Theorem 1, CVA] *)
theorem ext_prj_adjunction :
  fixes V :: "('A,'a) OVA" and  a b :: "('A, 'a) Valuation"
  defines "mul \<equiv> comb V"
  defines "\<epsilon>A \<equiv> neut V (d a)"
  defines "pr \<equiv> gprj V"
  assumes valid_V : "valid V"
  and elems : "a \<in> elems V \<and> b \<in> elems V"
  and doms : "d b \<subseteq> d a"
shows "le V (d b) (e (pr (d b) a)) (e b) \<longleftrightarrow> le V (d a) (e a) (e (mul \<epsilon>A b))"
  by (metis \<epsilon>A_def doms elems ext_prj_adjunction_lhs_imp_rhs ext_prj_adjunction_rhs_imp_lhs  local_inclusion_domain mul_def pr_def valid_V)

(* [Corollary 1, CVA] *)
theorem strongly_neutral_cVriance :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"
  assumes valid_V : "valid V"
  and strongly_neutral: "\<forall> A B . comb V (neut V A) (neut V B) = neut V (A \<union> B)"
  and  "B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
defines "ex \<equiv> gext V"
shows "ex A (neut V B) = neut V A "
by (metis assms(3) assms(4) assms(5) d_neut ex_def gext_def strongly_neutral sup.absorb_iff1 valid_V)

(* [Corollary 2, CVA] *)
theorem galois_insertion :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open" and b :: "('A, 'a) Valuation"
  assumes valid_V : "valid V" and "b \<in> elems V" and "d b = B"
  and " B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  defines "pr \<equiv> gprj V" and "ex \<equiv> gext V" and "mul \<equiv> comb V"
  shows "pr B (ex A b) = b"
proof -
  define \<epsilon>A where "\<epsilon>A \<equiv> neut V A"
  define \<epsilon>B where "\<epsilon>B \<equiv> neut V B"
  have "pr B (ex A b) = pr B (mul \<epsilon>A b)"
    by (simp add: \<epsilon>A_def assms(3) assms(4) assms(6) ex_def gext_def mul_def)
  moreover have "... =  mul (pr (A \<inter> B) \<epsilon>A) b"  using valid_comb_law_right pr_def mul_def ex_def
    by (metis \<epsilon>A_def assms(2) assms(3) assms(6) neutral_element neutral_is_element valid_V)
  moreover have "... =  mul \<epsilon>B b"
  by (simp add: \<epsilon>A_def \<epsilon>B_def assms(4) assms(5) assms(6) inf.absorb2 pr_def stability valid_V)
  ultimately show ?thesis
    by (metis \<epsilon>B_def \<open>pr B (ex A b) = pr B (mul \<epsilon>A b)\<close> assms(2) assms(3) assms(5) mul_def valid_neutral_law_left valid_V)
qed

(* [Corollary 2 cont., CVA] *)
theorem galois_closure_extensive :
  fixes V :: "('A,'a) OVA" and A B :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes valid_V : "valid V" and "a \<in> elems V" and "d a = A"
  and " B \<subseteq> A" and "B \<in> opens V" and "A \<in> opens V"
  defines "pr \<equiv> gprj V" and "ex \<equiv> gext V" and "mul \<equiv> comb V" and "ll \<equiv> le V"
  shows "ll A (e a) (e (ex A (pr B a)))"
proof -
  have "valid V" by fact
  moreover have "ll A (e a) (e a)"
    by (metis OVA.valid_welldefined OrderedSemigroup.valid_def assms(2) assms(3) e_def elems_def ll_def le_def local_le valid_V valid_reflexivity)
  moreover have "ll B (e (pr B a)) (e (pr B a))"
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) calculation(2) d_gprj gle_imp_le gprj_elem gprj_monotone ll_def le_imp_gle2 pr_def valid_V)
  ultimately show ?thesis
    by (metis (full_types) assms(2) assms(3) assms(4) assms(5) assms(6) d_gprj ex_def ext_prj_adjunction_lhs_imp_rhs gext_def gprj_elem ll_def pr_def)
qed

lemma ext_functorial_lhs_imp_rhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes valid_V : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
  and "ll  \<equiv> (\<lambda> A a b . le V A (e a) (e b)) :: 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool"
  shows "gle V (ex A c) (ex A (ex B c))"
proof -
  have "ll C c c"
    by (metis OVA.valid_welldefined OrderedSemigroup.valid_def assms(7) assms(8) e_def elems_def ll_def le_def local_le valid_V valid_reflexivity)
  moreover have "ll C (pr C (ex A c)) c"
    by (metis (no_types, opaque_lifting) assms(2) assms(5) assms(6) assms(7) assms(8) calculation dual_order.trans ex_def galois_insertion local_inclusion_domain pr_def valid_V)
  moreover have "pr C (pr B (ex A c)) = pr C (ex A c)"
    by (smt (verit, del_insts) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem gprj_functorial local_inclusion_domain pr_def valid_V)
  moreover have "ll C  (pr C (pr B (ex A c))) c"
    by (simp add: calculation(2) calculation(3))
  moreover have "ll B (pr B (ex A c)) (ex B c)"
    by (smt (verit, best) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(2) calculation(3) d_gext d_gprj dual_order.trans ex_def ext_prj_adjunction_lhs_imp_rhs gext_def gext_elem gprj_elem ll_def pr_def valid_V)
  moreover have "ll A (ex A c) (ex A (ex B c))"
    by (smt (verit, best) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(5) d_gext dual_order.trans ex_def ext_prj_adjunction_lhs_imp_rhs gext_def gext_elem ll_def pr_def valid_V)
  ultimately show ?thesis
    by (smt (verit, best) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.trans ex_def gext_elem ll_def le_imp_gle2 valid_V)
qed

lemma ext_functorial_rhs_imp_lhs :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes valid_V : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
  and "ll  \<equiv> (\<lambda> A a b . le V A (e a) (e b)) :: 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool"
  shows "gle V (ex A (ex B c)) (ex A c)"
proof -
  have "ll A (ex A (ex B c)) (ex A (ex B c))"
    by (metis (no_types, lifting) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_closure_extensive galois_insertion gext_elem ll_def valid_V)
  moreover have "ll B (pr B (ex A (ex B c))) (ex B c)"
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_closure_extensive galois_insertion gext_elem ll_def pr_def valid_V)
    moreover have "ll C (pr C (pr B (ex A (ex B c)))) c"
      by (smt (z3) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext dual_order.refl ex_def galois_closure_extensive galois_insertion gext_elem gprj_functorial ll_def local_inclusion_domain pr_def valid_V)
moreover have "ll C (pr C (ex A (ex B c))) c"
  by (metis (full_types) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) calculation(3) d_gext ex_def gext_elem gprj_functorial local_inclusion_domain pr_def valid_V)
  moreover have "ll A (ex A (ex B c)) (ex A c)"
    by (smt (verit, best) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(4) d_gext dual_order.trans ex_def ext_prj_adjunction_lhs_imp_rhs gext_def gext_elem ll_def pr_def valid_V)
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) assms(2) assms(3) assms(5) assms(6) assms(7) assms(8) d_gext ex_def gext_elem ll_def le_imp_gle2 local_inclusion_domain subset_trans valid_V)
qed

(* [Theorem 1 cont., CVA] *)
theorem ext_functorial :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes valid_V : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  shows "ex A (ex B c) = ex A c"
proof -
  have "gle V (ex A (ex B c)) (ex A c)"
    using assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def ext_functorial_rhs_imp_lhs valid_V by blast
  moreover have "gle V (ex A c)  (ex A (ex B c))"
    using assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def ext_functorial_lhs_imp_rhs valid_V by blast
  ultimately show ?thesis
    by (meson OVA.valid_welldefined OrderedSemigroup.valid_def Poset.valid_welldefined gle_def valid_V valid_antisymmetry)
qed

(* [Corollary 2 cont., CVA] *)
lemma galois_closure_idempotent :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and a :: "('A, 'a) Valuation"
  assumes valid_V : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d a = A" and "a \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
  shows "ex A (pr B (ex A (pr B a))) = ex A (pr B a)"
  by (metis assms(2) assms(3) assms(6) assms(7) assms(8) d_gprj ex_def galois_insertion gprj_elem pr_def valid_V)

lemma up_and_down :
  fixes V :: "('A,'a) OVA" and A B C :: "'A Open"  and c :: "('A, 'a) Valuation"
  assumes valid_V : "valid V"
  and "A \<in> opens V" and "B \<in> opens V" and "C \<in> opens V"
  and "C \<subseteq> B" and "B \<subseteq> A" and "d c = C" and "c \<in> elems V"
  defines "ex \<equiv> gext V"
  and "pr \<equiv> gprj V"
shows "pr B (ex A c) = ex B c"
proof -
  have "ex A c = ex A (ex B c)" using ext_functorial
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) ex_def valid_V)
  moreover have "pr B (ex A (ex B c)) = ex B c"
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gext ex_def galois_insertion gext_elem pr_def valid_V)
  ultimately show ?thesis
    by auto
qed

lemma elem_le_unwrap :
  fixes V :: "('A,'a) OVA" and a b :: "('A, 'a) Valuation" and A B :: "('A Open)"
  assumes valid_V : "valid V"
  and a_elem : "a \<in> elems V" and b_elem : "b \<in> elems V"
  and dom_A : "d a = A" and dom_B : "d b = B"
  assumes le_gc : "gle V a b"
  shows "le V B (e (gprj V B a)) (e b) \<and> B \<subseteq> A"
  using le_gc gle_def gprj_def valid_gc_le_unwrap
  apply clarsimp
  apply safe
  apply (smt (z3) OVA.valid_welldefined a_elem b_elem combine_monotone d_antitone d_gext d_gprj dom_A dom_B elems_def ext_prj_adjunction galois_closure_extensive galois_insertion gext_def gext_elem gle_def gle_imp_le gprj_elem id_le_gprj laxity le_gc le_imp_gle2 local_inclusion_domain neutral_element neutral_is_element stability up_and_down valid_V valid_comb_law_left valid_domain_law valid_gc_poset valid_neutral_law_left valid_neutral_law_right)
  by (smt (verit, best) OVA.valid_welldefined a_elem b_elem d_antitone dom_A dom_B elems_def gle_def subsetD valid_V)
  
(* [Corollary 3, CVA] *)
lemma locally_complete_imp_complete :
  fixes V :: "('A,'a) OVA"
  defines "\<Phi> A \<equiv> (Presheaf.ob (presheaf V)) $ A"
  and "pr \<equiv> gprj V" and "ex \<equiv> gext V"
  and "ll  \<equiv> (\<lambda> A a b . le V A (e a) (e b)) :: 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool"
  and "gl \<equiv> gle V"
  assumes valid_V: "valid V"
  assumes local_completeness: "\<And>A . A \<in> opens V \<Longrightarrow> Poset.is_complete (\<Phi> A)"
  shows "Poset.is_complete (poset V)"
proof
  show "Poset.valid (OVA.poset V)" 
    using valid_V by (metis OVA.poset_def OVA.valid_welldefined valid_gc)
next
  show "(\<forall> U \<subseteq> el (OVA.poset V). \<exists> i . is_inf (OVA.poset V) U i)"
  proof auto
    fix U :: "(('A,'a) Valuation) set"
    assume "U \<subseteq> elems V"

    define "d_U" where "d_U = \<Union> (d ` U)"
    define "ex_U" where "ex_U = ((e o ex d_U) ` U)"
    define "some_e_U" where "some_e_U = Poset.inf (\<Phi> (d_U)) ex_U"
  
    have "d_U \<in> opens V"
      by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined \<open>U \<subseteq> elems V\<close> d_U_def image_subsetI local_inclusion_domain space_valid subset_eq valid_V valid_union)
  
    moreover have "ex_U \<subseteq> Poset.el (\<Phi> (d_U))"
      by (smt (verit) Sup_upper UN_subset_iff Union_least \<Phi>_def \<open>U \<subseteq> elems V\<close> calculation comp_apply d_U_def e_gext ex_U_def ex_def image_subsetI in_mono local_inclusion_domain valid_V)
  
    moreover have "some_e_U \<noteq> None" using Poset.complete_inf_not_none
      using calculation(1) calculation(2) local_completeness some_e_U_def by fastforce 
  
    obtain e_U where "some_e_U = Some e_U" using \<open>some_e_U \<noteq> None\<close> by auto
  
    moreover have "e_U \<in> Poset.el (\<Phi> d_U)" 
      by (metis (mono_tags, lifting) \<open>some_e_U \<noteq> None\<close> calculation(3) inf_def option.inject someI_ex some_e_U_def)
  
    define "i" where "i = (d_U, e_U)"
    moreover have "i \<in> elems V"
      by (metis \<Phi>_def \<open>e_U \<in> el (\<Phi> d_U)\<close> calculation(1) global_inclusion_element i_def valid_V) 

    have "Poset.is_inf (poset V) U i" 
    proof (simp add: is_inf_def   )
      have "U \<subseteq> el (OVA.poset V)"
        by (metis OVA.poset_def \<open>U \<subseteq> elems V\<close> elems_def)
      moreover have "i \<in> el (OVA.poset V)"
        by (metis OVA.poset_def \<open>i \<in> elems V\<close> elems_def) 
      moreover have "(\<forall>u\<in>U. Poset.le (OVA.poset V) i u)"
        proof auto

        fix a :: "'A set"
        fix b :: "'a"
        define "u" where "u = (a,b)"
        assume "u \<in> U"
        moreover have "d u \<subseteq> d_U"
          using calculation(1) d_U_def by blast 
        moreover have "Poset.valid (\<Phi> (d_U))"
          by (metis OVA.opens_def OVA.space_def OVA.valid_welldefined \<Phi>_def \<open>d_U \<in> OVA.opens V\<close> posets_valid valid_V)
        moreover have "Poset.is_complete (\<Phi> (d_U))"
          by (simp add: \<open>d_U \<in> OVA.opens V\<close> local_completeness)
        moreover have "Poset.is_inf (\<Phi> (d_U)) ex_U e_U" using ex_U_def local_completeness
          by (metis \<open>e_U \<in> el (\<Phi> d_U)\<close> \<open>ex_U \<subseteq> el (\<Phi> d_U)\<close> \<open>some_e_U = Some e_U\<close> calculation(3) some_e_U_def some_inf_is_inf)
        moreover have "ll (d_U) i (ex d_U u)"
          by (metis \<Phi>_def calculation(1) calculation(5) comp_apply e_def ex_U_def i_def image_eqI is_inf_def le_def ll_def snd_conv) 
        moreover have "ll (d u) (pr (d u) i) u" using Poset.inf_smaller
          by (smt (verit, best) \<open>U \<subseteq> elems V\<close> \<open>i \<in> elems V\<close> calculation(1) calculation(2) calculation(6) d_def ex_def ext_prj_adjunction_rhs_imp_lhs fst_conv gext_def i_def ll_def local_inclusion_domain pr_def subsetD valid_V) 
        moreover have i_is_lb: "gl i u"
          by (smt (verit, best) \<open>U \<subseteq> elems V\<close> \<open>i \<in> elems V\<close> calculation(1) calculation(2) calculation(7) d_def elem_le_wrap fst_conv gl_def i_def ll_def pr_def subsetD valid_V) 
        ultimately show "(Poset.le (OVA.poset V) i u)"
          by (simp add: OVA.poset_def gl_def gle_def) 
         qed
       moreover have " (\<forall>z\<in>el (OVA.poset V). (\<forall>u\<in>U. Poset.le (OVA.poset V) z u) \<longrightarrow> Poset.le (OVA.poset V) z i)"
       proof auto   

        fix a :: "'A set"
        fix b :: "'a"
        define "z" where "z = (a,b)"
        assume "z \<in> elems V"
        assume "\<forall>u\<in>U. Poset.le (OVA.poset V) z u"
        moreover have lb2: "\<forall> v \<in> U . d v \<subseteq> d z"
          by (metis OVA.poset_def OVA.valid_welldefined calculation d_antitone valid_V valid_gc_welldefined) 
        moreover have "\<forall> v \<in> U . ll (d v) (pr (d v) z) v"
          by (metis OVA.poset_def OVA.valid_welldefined calculation(1) elem_le_unwrap elems_def gle_def ll_def pr_def valid_V valid_gc_welldefined)
        moreover have "\<forall> v \<in> U . Poset.le (\<Phi> (d v)) (e (pr (d v) z)) (e v)" 
          by (metis \<Phi>_def calculation(3) le_def ll_def)
        moreover have "\<forall> v \<in> U . Poset.le (\<Phi> (d v)) (e (pr (d v) z)) (e v)"  using ext_prj_adjunction
          using calculation(4) by blast 
        define "z_U" where "z_U = gprj V d_U z"
        moreover have "\<forall> v \<in> U . pr d_U (ex (d z) v) = ex d_U v" using up_and_down
          by (smt (verit) UN_subset_iff \<open>U \<subseteq> elems V\<close> \<open>d_U \<in> OVA.opens V\<close> \<open>z \<in> elems V\<close> d_U_def ex_def lb2 local_inclusion_domain pr_def subset_eq valid_V) 
        moreover have "\<forall> v \<in> U . ll d_U z_U (ex d_U v)"
          by (smt (z3) OVA.poset_def OVA.valid_welldefined \<open>U \<subseteq> elems V\<close> \<open>\<forall>u\<in>U. Poset.le (OVA.poset V) i u\<close> \<open>i \<in> elems V\<close> \<open>z \<in> elems V\<close> calculation(3) calculation(6) d_antitone d_def d_gext elems_def ex_def ext_functorial ext_prj_adjunction fst_conv galois_closure_extensive galois_insertion gext_def gext_elem gprj_def i_def lb2 ll_def local_inclusion_domain pr_def subsetD valid_V z_U_def) 
        moreover have "\<forall> v \<in> U . Poset.le (\<Phi> (d z)) (e z) (e (gext V (d z) v))"
          by (smt (verit, best) \<Phi>_def \<open>U \<subseteq> elems V\<close> \<open>z \<in> elems V\<close> calculation(3) ext_prj_adjunction gext_def in_mono lb2 le_def ll_def local_inclusion_domain pr_def valid_V)
        moreover have "\<Union> (d ` U) \<subseteq> d z"
          using lb2 by auto 
        moreover have "d i \<subseteq> d z"
          by (metis calculation(9) d_U_def d_def fst_conv i_def) 
        define "i__Z" where "i__Z = gext V (d z) i"


        moreover have "Poset.le (\<Phi> d_U) (e ( gprj V d_U z)) e_U"  using inf_is_glb
        proof 
          show "Poset.valid (\<Phi> d_U)"
            by (simp add: \<open>d_U \<in> OVA.opens V\<close> local_completeness)
          show "ex_U \<subseteq> el (\<Phi> d_U)"
            by (simp add: \<open>ex_U \<subseteq> el (\<Phi> d_U)\<close>) 
          show "e (gprj V d_U z) \<in> el (\<Phi> d_U)"
            by (metis \<Phi>_def \<open>d i \<subseteq> d z\<close> \<open>i \<in> elems V\<close> \<open>z \<in> elems V\<close> d_def e_gprj fst_conv i_def local_inclusion_domain valid_V)
          show "e_U \<in> el (\<Phi> d_U)"
            by (simp add: \<open>e_U \<in> el (\<Phi> d_U)\<close>)   
          show "is_inf (\<Phi> d_U) ex_U e_U"
            using \<open>Poset.valid (\<Phi> d_U)\<close> \<open>e_U \<in> el (\<Phi> d_U)\<close> \<open>ex_U \<subseteq> el (\<Phi> d_U)\<close> \<open>some_e_U = Some e_U\<close> some_e_U_def some_inf_is_inf by fastforce 
          have z_U_is_lb : "\<forall> v \<in> U . Poset.le (\<Phi> d_U) (e (gprj V d_U z)) (e (ex d_U v))"
            using \<Phi>_def calculation(7) le_def ll_def z_U_def by fastforce 
          show "\<forall> u \<in> ex_U. Poset.le (\<Phi> d_U) (e (gprj V d_U z)) u"  using z_U_is_lb
            by (simp add: ex_U_def) 
          show "le_rel (\<Phi> d_U) \<subseteq> le_rel (\<Phi> d_U)"
            by simp 
        qed

        ultimately have  "Poset.le (OVA.poset V) (a, b) i"
          by (metis OVA.poset_def \<Phi>_def \<open>d i \<subseteq> d z\<close> \<open>i \<in> elems V\<close> \<open>z \<in> elems V\<close> d_def e_def elem_le_wrap fst_conv gle_def i_def le_def snd_conv valid_V z_def) 
      qed
     


end