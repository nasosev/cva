theory OVA
  imports Main Presheaf OrderedSemigroup Grothendieck Poset
begin

type_synonym ('A, 'a) Valuation = "('A set \<times> 'a)"

record ('A, 'a) OVA =
  presheaf :: "('A, 'a) Presheaf"
  neutral :: "('A, unit, 'a) PresheafMap"
  ordered_semigroup :: "(('A, 'a) Valuation) OrderedSemigroup"

definition comb :: "('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"comb ova Aa Bb =  (OrderedSemigroup.mult (ordered_semigroup ova)) $$ (Aa, Bb)"

definition neut :: "('A, 'a) OVA \<Rightarrow> ('A set \<Rightarrow> ('A, 'a) Valuation)" where
"neut ova  = (\<lambda> A. (A, (Presheaf.nat (neutral ova) $ A) $$ ()))"

definition space :: "('A,'a) OVA \<Rightarrow> 'A Space" where
"space ova = Presheaf.space (presheaf ova)"

definition elems :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation set" where
"elems ova = Poset.el (OrderedSemigroup.poset (ordered_semigroup ova))"

definition local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems ova A = Poset.el (Presheaf.ob (presheaf ova) $ A)"

definition gle :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle ova Aa Bb = Poset.le (OrderedSemigroup.poset (ordered_semigroup ova)) Aa Bb"

definition le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"le ova A a b = Poset.le (Presheaf.ob (presheaf ova) $ A) a b"

definition gprj :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gprj ova B Aa \<equiv> if B \<subseteq> d Aa \<and> B \<in> opens (space ova) then (B, Presheaf.ar (presheaf ova) $ (Space.make_inclusion (space ova) B (d Aa)) $$ (e Aa)) else undefined"

definition gext :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gext ova A Bb \<equiv> if d Bb \<subseteq> A \<and> A \<in> opens (space ova) then (comb ova (neut ova A) Bb) else undefined"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid ova \<equiv>
    let
        \<Phi> = presheaf ova;
        E = neutral ova;
        \<epsilon> = neut ova;
        T = space ova;
        S = ordered_semigroup ova;
        mul = comb ova; 
        elems = elems ova;
        pr = gprj ova;

        welldefined = Presheaf.valid \<Phi>
                      \<and> OrderedSemigroup.valid S
                      \<and> Presheaf.valid_map E
                      \<and> T = Presheaf.map_space E
                      \<and> Presheaf.cod E = \<Phi>
                      \<and> Presheaf.dom E = Presheaf.terminal T
                      \<and> OrderedSemigroup.poset S = gc \<Phi>;

        domain_law = \<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow> d (mul Aa Bb) = d Aa \<union> d Bb;
        neutral_law_left = (\<forall>A Aa. A \<in> opens T \<longrightarrow> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> mul (\<epsilon> A) Aa = Aa);
        neutral_law_right = (\<forall>A Aa. A \<in> opens T \<and> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> mul Aa (\<epsilon> A) = Aa);
        comb_law_left = (\<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
             pr (d Aa) (mul Aa Bb) = mul Aa (pr (d Aa \<inter> d Bb) Bb));
        comb_law_right = (\<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
             pr (d Bb) (mul Aa Bb) = mul (pr (d Aa \<inter> d Bb) Aa) Bb)
    in
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"

(* LEMMAS *)

(* Todo: can we prove this and the below valid_... lemmas with meta implications? *)
lemma validI :
  fixes ova :: "('A,'a) OVA"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "E \<equiv> neutral ova"
  defines "\<epsilon> \<equiv> neut ova"
  defines "T \<equiv> space ova"
  defines "S \<equiv> ordered_semigroup ova"
  defines "mul \<equiv> comb ova"
  defines "elem \<equiv> elems ova"
  defines "pr \<equiv> gprj ova"
  assumes welldefined : "Presheaf.valid \<Phi> \<and> OrderedSemigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> OrderedSemigroup.poset S = gc \<Phi>"
  assumes domain_law : " \<forall> Aa Bb . Aa \<in> elem \<longrightarrow> Bb \<in> elem \<longrightarrow> d (mul Aa Bb) = d Aa \<union> d Bb"
  assumes neutral_law_left : "( \<forall> A Aa . A \<in> opens T \<longrightarrow> Aa \<in> elem \<longrightarrow> d Aa = A \<longrightarrow> mul (\<epsilon> A) Aa = Aa)"
  assumes neutral_law_right : "(\<forall> A Aa .A \<in> opens T \<and> Aa \<in> elem \<longrightarrow> d Aa = A \<longrightarrow> mul Aa (\<epsilon> A) = Aa)"
  assumes comb_law_left : "(\<forall> Aa Bb . Aa \<in> elem \<longrightarrow> Bb \<in> elem \<longrightarrow>
             pr (d Aa) (mul Aa Bb) = mul Aa (pr (d Aa \<inter> d Bb) Bb))"
  assumes comb_law_right : "(\<forall> Aa Bb . Aa \<in> elem \<longrightarrow> Bb \<in> elem \<longrightarrow>
              pr (d Bb) (mul Aa Bb) = mul (pr (d Aa \<inter> d Bb) Aa) Bb)"
  shows "valid ova"
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
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova in
    Presheaf.valid \<Phi> \<and> OrderedSemigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> OrderedSemigroup.poset S = gc \<Phi>"
  by (simp add: valid_def Let_def)

lemma valid_domain_law  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow>
    \<forall> Aa Bb. Aa \<in> elems ova \<longrightarrow> Bb \<in> elems ova \<longrightarrow> d (comb ova Aa Bb) = d Aa \<union> d Bb"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_left  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<epsilon> = neut ova; T = space ova; mul = comb ova; elems = elems ova in
    \<forall>A Aa. A \<in> opens T \<longrightarrow> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> mul (\<epsilon> A) Aa = Aa"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_right  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let  \<epsilon> = neut ova; T = space ova; mul = comb ova; elems = elems ova in
    \<forall>A Aa. A \<in> opens T \<and> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> mul Aa (\<epsilon> A) = Aa"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_left  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; T = space ova; S = ordered_semigroup ova; mul = comb ova; elems = elems ova; pr = gprj ova in
    \<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
      pr (d Aa) (mul Aa Bb) = mul Aa (pr (d Aa \<inter> d Bb) Bb)"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_right  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; T = space ova; S = ordered_semigroup ova; mul = comb ova; elems = elems ova; pr = gprj ova in
    \<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
      pr (d Bb) (mul Aa Bb) = mul (pr (d Aa \<inter> d Bb) Aa) Bb"
  by (simp add: valid_def Let_def)

lemma neutral_element : "valid ova \<Longrightarrow> A \<in> Space.opens (space ova) \<Longrightarrow> d (neut ova A) = A "
  by (simp add: d_def neut_def)

lemma neutral_is_element :
fixes ova :: "('A,'a) OVA" and A :: "'A Open"
defines "\<epsilon>A \<equiv> neut ova A"
assumes "valid ova" and "A \<in> Space.opens (space ova)"
shows "neut ova A \<in> elems ova"
proof -
  have "valid ova"
    using assms(2) by blast
  moreover have "A \<in> Space.opens (space ova)"
    by (simp add: assms(3))
  moreover have "Poset.valid_map  (PresheafMap.nat (neutral ova) $ A)"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined calculation(1) calculation(2))
  moreover have "Poset.cod (PresheafMap.nat (neutral ova) $ A) = (Presheaf.ob (presheaf ova)) $ A"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined calculation(1) calculation(2))
  moreover have "Presheaf.dom (neutral ova) = Presheaf.terminal (space ova)"
    by (meson OVA.valid_welldefined calculation(1))
  moreover have "Poset.dom  (PresheafMap.nat (neutral ova) $ A) = Poset.discrete"
    by (metis OVA.valid_welldefined Presheaf.Presheaf.select_convs(2) Presheaf.valid_map_welldefined UNIV_I calculation(1) calculation(2) const_app terminal_def)
  moreover have "(PresheafMap.nat (neutral ova) $ A $$ ()) \<in> Poset.el ((Presheaf.ob (presheaf ova)) $ A)"
    by (metis Poset.Poset.select_convs(1) Poset.fun_app2 UNIV_I calculation(3) calculation(4) calculation(6) discrete_def)
ultimately show ?thesis using neut_def elems_def
  by (metis OVA.space_def OVA.valid_welldefined local_elem_gc)
qed

lemma neutral_local_element :
  fixes ova :: "('A,'a) OVA" and A :: "'A Open"
  defines "\<epsilon>A \<equiv> neut ova A"
  defines "\<epsilon> \<equiv> Presheaf.nat (neutral ova)"
  defines "\<Phi>A \<equiv> Presheaf.ob (presheaf ova) $ A"
  assumes valid_ova : "valid ova"
  and domain : "A \<in> opens (space ova)"
shows " e \<epsilon>A \<in> Poset.el \<Phi>A"
proof -
  have "valid ova" by fact
  moreover have "A \<in> opens (space ova)" by fact
  moreover have "Poset.valid_map (\<epsilon> $ A)"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined \<epsilon>_def domain valid_ova)
  moreover have "Poset.cod (\<epsilon> $ A) = \<Phi>A"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined \<Phi>A_def \<epsilon>_def domain valid_ova)
  moreover have "e \<epsilon>A =  (\<epsilon> $ A) $$ ()"
    by (simp add: \<epsilon>A_def \<epsilon>_def e_def neut_def)
  moreover have "Poset.dom  (\<epsilon> $ A) = Presheaf.ob (Presheaf.terminal (space ova)) $ A"
    by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined \<epsilon>_def domain valid_ova)
  moreover have "(Poset.dom (\<epsilon> $ A)) =  Poset.discrete" using Presheaf.terminal_def
    by (metis Presheaf.Presheaf.select_convs(2) UNIV_I calculation(6) const_app domain)
  moreover have "() \<in> Poset.el (Poset.dom (\<epsilon> $ A))"
    by (simp add: calculation(7) discrete_def)
    ultimately show ?thesis
      by (metis Poset.fun_app2)
  qed

lemma d_neut : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow> \<epsilon>A = neut ova A \<Longrightarrow> d \<epsilon>A = A"
  by (simp add: d_def neut_def)

lemma d_gprj : "valid ova \<Longrightarrow>  Aa \<in> elems ova \<Longrightarrow>  B \<in> opens (space ova)
\<Longrightarrow> A \<in> opens (space ova)\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d Aa = A \<Longrightarrow>  Aa_B = gprj ova B Aa 
\<Longrightarrow> d Aa_B = B"
  by (simp add: d_def gprj_def)

lemma d_gext : "valid ova \<Longrightarrow>  Bb \<in> elems ova \<Longrightarrow>  B \<in> opens (space ova)
\<Longrightarrow> A \<in> opens (space ova)\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d Bb = B \<Longrightarrow>  Bb__A = gext ova A Bb 
\<Longrightarrow> d Bb__A = A"
  by (simp add: d_neut gext_def neutral_is_element sup.order_iff valid_domain_law)

lemma local_inclusion_element : "valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = d Aa \<Longrightarrow> a = e Aa
\<Longrightarrow> \<Phi> = (presheaf ova) \<Longrightarrow> ob_A = ob \<Phi> $ A 
\<Longrightarrow> a \<in> el ob_A"
  by (metis OVA.valid_welldefined e_def elems_def gc_elem_local)

lemma global_inclusion_element : "valid ova \<Longrightarrow> A \<in> Space.opens (space ova) 
\<Longrightarrow> \<Phi> = presheaf ova \<Longrightarrow> \<Phi>A =(Presheaf.ob \<Phi>) $ A \<Longrightarrow> a \<in> Poset.el \<Phi>A
\<Longrightarrow>  (A, a) \<in> elems ova"
  by (metis OVA.space_def OVA.valid_welldefined elems_def local_elem_gc)

lemma local_inclusion_domain  : "valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = d Aa \<Longrightarrow> T = space ova \<Longrightarrow> A \<in> opens T"
  by (metis OVA.space_def OVA.valid_welldefined elems_def local_dom)

lemma combine_monotone : "valid ova \<Longrightarrow>  Aa1 \<in> elems ova \<Longrightarrow> Aa2 \<in> elems ova \<Longrightarrow> Bb1 \<in> elems ova \<Longrightarrow> Bb2 \<in> elems ova
\<Longrightarrow> gle ova Aa1 Aa2 \<Longrightarrow> gle ova Bb1 Bb2 
\<Longrightarrow> gle ova (comb ova Aa1 Bb1) (comb ova Aa2 Bb2)"
  unfolding gle_def comb_def
  by (metis OVA.valid_welldefined elems_def valid_monotone)

lemma le_imp_gle : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow> a1 \<in> local_elems ova A
 \<Longrightarrow> a2 \<in> local_elems ova A \<Longrightarrow> le ova A a1 a2 \<Longrightarrow> gle ova (A,a1) (A,a2)"
  unfolding local_elems_def le_def gle_def
  apply (frule valid_welldefined)
  apply (simp_all add: Let_def)
  apply safe
  apply auto
  apply (simp add: gc_def)
  apply (simp_all add: Let_def)
  apply safe
   apply (metis OVA.space_def)
  by (metis (no_types, lifting) OVA.space_def Poset.ident_app Presheaf.valid_welldefined make_inclusion_ident posets_valid valid_gc_1)

lemma le_imp_gle2 : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow> Aa1 \<in> elems ova
 \<Longrightarrow> Aa2 \<in> elems ova \<Longrightarrow> d Aa1 = A \<Longrightarrow> d Aa2 = A \<Longrightarrow> le ova A (e Aa1) (e Aa2) \<Longrightarrow> gle ova Aa1 Aa2"
  by (metis d_def e_def le_imp_gle local_elems_def local_inclusion_element prod.collapse)

lemma gle_imp_le : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow> Aa1 \<in> elems ova \<Longrightarrow> d Aa1 = A \<Longrightarrow> d Aa2 = A
 \<Longrightarrow> Aa2 \<in> elems ova \<Longrightarrow> gle ova Aa1 Aa2 \<Longrightarrow> le ova A (e Aa1) (e Aa2)"
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
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"  and Aa1 Aa2 :: "('A, 'a) Valuation" 
  defines "pr \<equiv> gprj ova"
  and "l \<equiv> gle ova"
  assumes valid_ova: "valid ova"
  and "B \<subseteq> A" and "B \<in> opens (space ova)" and "A \<in> opens (space ova)"
  and "d Aa1 = A" and "d Aa2 = A" 
  and "Aa1 \<in> elems ova" and "Aa2 \<in> elems ova" and "l Aa1 Aa2"
shows "l (pr B Aa1) (pr B Aa2)"
proof -
  define "i" where "i = make_inclusion (OVA.space ova) B (fst Aa1)"
  define "\<Phi>i" where "\<Phi>i = (Presheaf.ar (presheaf ova)) $ i"
  define "\<Phi>A" where "\<Phi>A = (Presheaf.ob (presheaf ova)) $ A"
  define "\<Phi>B" where "\<Phi>B = (Presheaf.ob (presheaf ova)) $ B"
  moreover have "l Aa1 Aa2 \<longrightarrow> Poset.le \<Phi>A (e Aa1) (e Aa2)" 
    apply (simp add: l_def)
    using gle_imp_le
    by (metis \<Phi>A_def assms(10) assms(6) assms(7) assms(8) assms(9) le_def valid_ova)
  moreover have "Poset.le \<Phi>A (e Aa1) (e Aa2)"
    using assms(11) calculation(2) by blast
  moreover have "i \<in> inclusions (space ova) \<and> Space.dom i = B \<and> Space.cod i = A"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined assms(4) assms(5) assms(6) assms(7) d_def i_def inclusions_def make_inclusion_def mem_Collect_eq valid_make_inclusion valid_ova) 
  moreover have "Poset.le \<Phi>B (\<Phi>i $$ (e Aa1)) (\<Phi>i $$ (e Aa2))" using Presheaf.prj_monotone
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>A_def \<Phi>B_def \<Phi>i_def assms(10) assms(7) assms(9) calculation(3) calculation(4) local_inclusion_element valid_ova) 
  ultimately show ?thesis
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>i_def assms(10) assms(4) assms(5) assms(7) assms(8) assms(9) d_def gprj_def i_def image l_def le_def le_imp_gle local_elems_def local_inclusion_element pr_def valid_ova)
qed





lemma stability:
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"
  assumes valid_ova: "valid ova"
  assumes "B \<subseteq> A" and "B \<in> opens (space ova)" and "A \<in> opens (space ova)"
  defines \<epsilon>A_def: "\<epsilon>A \<equiv> neut ova A"
  defines \<epsilon>B_def: "\<epsilon>B \<equiv> neut ova B"
  defines \<epsilon>A_B_def: "\<epsilon>A_B \<equiv> gprj ova B \<epsilon>A"
  shows "\<epsilon>A_B = \<epsilon>B"
proof -
  define i where "i \<equiv> Space.make_inclusion (space ova) B A"
  define "f" where "f = nat (neutral ova)"
  define "one" where "one \<equiv> dom (neutral ova)"
  moreover have "\<epsilon>A_B = gprj ova B \<epsilon>A"
    by (simp add: \<epsilon>A_B_def) 
  moreover have "Space.cod i = A \<and> Space.dom i = B"
    by (simp add: i_def make_inclusion_def)
  moreover have "i \<in> Space.inclusions (space ova)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.space_def OVA.valid_welldefined assms(2) assms(3) assms(4) i_def inclusions_def make_inclusion_def mem_Collect_eq space_valid valid_make_inclusion valid_ova) 
    moreover have v1: "Poset.valid_map  (Presheaf.ar one $ i)" using Presheaf.poset_maps_valid
      by (metis OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined calculation(4) one_def terminal_def valid_ova) 
      moreover have v2: "Poset.valid_map (f $ B)"
        by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined assms(3) f_def valid_ova) 
    moreover have "Presheaf.valid one" 
      by (metis OVA.valid_welldefined Presheaf.valid_map_welldefined one_def valid_ova) 
  moreover have "(Presheaf.ar one $ i ) $$ ()  = ()"
    by simp
moreover have "() \<in> Poset.el (Poset.dom  (ar one $ i))" using Presheaf.terminal_value
  by (metis (full_types) OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined UNIV_unit UNIV_witness calculation(1) calculation(4) dom_proj old.unit.exhaust terminal_def valid_inclusion_cod valid_ova) 
moreover have "((f $ B) \<cdot> (ar one $ i)) $$ () = ((f $ B) $$ ((ar one $ i)) $$ ())"
  by (metis OVA.valid_welldefined Presheaf.Presheaf.select_convs(1) Presheaf.valid_map_welldefined assms(3) calculation(3) calculation(4) calculation(9) cod_proj compose_app f_def one_def terminal_def v1 valid_ova) 
  moreover have "((Presheaf.ar (presheaf ova) $ i) \<cdot> (f $ A)) $$ ()=  e \<epsilon>B"
    by (metis OVA.valid_welldefined \<epsilon>B_def calculation(10) calculation(3) calculation(4) calculation(8) e_def f_def neut_def one_def snd_conv valid_map_naturality valid_ova) 
  moreover have "e \<epsilon>A=   (f $ A) $$ ()"
    by (simp add: \<epsilon>A_def e_def f_def neut_def)  
  ultimately show ?thesis
    by (smt (verit) OVA.space_def OVA.valid_welldefined Presheaf.valid_map_welldefined UNIV_unit UNIV_witness \<epsilon>A_def \<epsilon>B_def assms(2) assms(3) assms(4) compose_app dom_proj f_def gprj_def i_def neut_def neutral_element old.unit.exhaust poset_maps_valid terminal_value valid_map_naturality valid_ova) 
  qed



(* [Remark 3 cont., CVA] *)
lemma local_mono_imp_global : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow>  a1 \<in> local_elems ova A \<Longrightarrow>  a1' \<in> local_elems ova A
\<Longrightarrow>  a2' \<in> local_elems ova A \<Longrightarrow>  a2' \<in> local_elems ova A \<Longrightarrow> le ova A a1 a2 \<Longrightarrow> le ova A a1' a2'
 \<Longrightarrow> gle ova (comb ova (A,a1) (A,a1')) (comb ova (A,a2) (A,a2'))"
  by (metis OVA.space_def OVA.valid_welldefined Poset.valid_welldefined combine_monotone elems_def le_def le_imp_gle local_elem_gc local_elems_def posets_valid)

(* [Remark 3 cont., CVA] *)
lemma global_mono_imp_local : "valid ova \<Longrightarrow> A \<in> opens (space ova) 
\<Longrightarrow> Aa1 \<in> elems ova \<Longrightarrow>  Aa1' \<in> elems ova\<Longrightarrow>  Aa2' \<in> elems ova \<Longrightarrow>  Aa2' \<in> elems ova 
\<Longrightarrow> d Aa1 = A \<Longrightarrow> d Aa1' = A \<Longrightarrow> d Aa2 = A \<Longrightarrow> d Aa2' = A 
\<Longrightarrow> gle ova Aa1 Aa2 \<Longrightarrow> gle ova Aa1' Aa2' 
\<Longrightarrow> le ova A (e (comb ova Aa1 Aa1')) (e (comb ova Aa2 Aa2'))"
  by (smt (verit, ccfv_SIG) OVA.valid_welldefined comb_def d_neut e_def elems_def gle_def le_def local_le neutral_is_element valid_domain_law valid_gc_welldefined valid_monotone valid_neutral_law_right)

(* [Remark 3 cont., CVA] *)
lemma id_le_gprj :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"  and Aa :: "('A, 'a) Valuation"
  assumes "valid ova"
  and  "A \<in> Space.opens (space ova)" and "B \<in> Space.opens (space ova)"  and "B \<subseteq> A"
  and  "Aa \<in> elems ova" and "d Aa = A"
shows " gle ova Aa (gprj ova B Aa)"
proof -
  define "i" where "i = Space.make_inclusion (space ova) B (d Aa)"
  define "\<Phi>i" where "\<Phi>i = Presheaf.ar (presheaf ova) $ i"
  define "\<Phi>A" where "\<Phi>A = Presheaf.ob (presheaf ova) $ A"
  define "\<Phi>B" where "\<Phi>B = Presheaf.ob (presheaf ova) $ B"
  define "a_B" where "a_B =  \<Phi>i $$ (e Aa)"
  have "Space.valid_inclusion i"
    by (metis OVA.space_def OVA.valid_welldefined assms(1) assms(2) assms(3) assms(4) assms(6) i_def space_valid valid_make_inclusion) 
  moreover have "gprj ova B Aa = (B, a_B)"
    by (simp add: \<Phi>i_def a_B_def assms(3) assms(4) assms(6) gprj_def i_def) 
  moreover have "Poset.valid \<Phi>B"
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>B_def assms(1) assms(3) posets_valid) 
  moreover have "Poset.valid_map \<Phi>i" 
    by (metis (mono_tags, lifting) Inclusion.simps(1) OVA.space_def OVA.valid_welldefined  \<Phi>i_def assms(1) calculation(1) i_def inclusions_def make_inclusion_def mem_Collect_eq poset_maps_valid ) 
  moreover have "e Aa \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def assms(1) assms(5) assms(6) local_inclusion_element) 
  moreover have "Space.cod i = A \<and> Space.dom i = B \<and> i \<in> Space.inclusions (space ova)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) assms(6) calculation(1) i_def inclusions_def make_inclusion_def mem_Collect_eq) 
  moreover have "a_B \<in> Poset.el \<Phi>B"
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>A_def \<Phi>B_def \<Phi>i_def a_B_def assms(1) calculation(5) calculation(6) image)  
  moreover have "Poset.le \<Phi>B a_B a_B "
    by (simp add: calculation(3) calculation(7) valid_reflexivity)
  moreover have "valid ova" by fact
  ultimately show ?thesis apply (simp add: gle_def   ) 
    apply (frule valid_welldefined)
    apply (simp_all add: Let_def)
    apply (simp add: gc_def Let_def)
    apply auto
    apply (metis OVA.space_def assms(2) assms(6) d_def fst_conv)
    apply (metis OVA.space_def assms(3))
    apply (metis \<Phi>A_def assms(6) d_def e_def fst_eqD snd_eqD)
    using \<Phi>B_def apply force
    apply (metis assms(4) assms(6) d_def fst_conv subsetD)
    by (metis (no_types, lifting) OVA.space_def \<Phi>B_def \<Phi>i_def a_B_def d_def e_def fst_conv i_def snd_conv)
qed

lemma gprj_elem : "valid ova \<Longrightarrow>  Aa \<in> elems ova \<Longrightarrow>  B \<in> opens (space ova)
\<Longrightarrow> A \<in> opens (space ova)\<Longrightarrow> B \<subseteq> A  \<Longrightarrow> d Aa = A \<Longrightarrow>  Aa_B = gprj ova B Aa \<Longrightarrow> Aa_B \<in> elems ova"
  by (metis OVA.valid_welldefined elems_def gle_def id_le_gprj valid_gc_welldefined)

lemma gext_elem :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open" and Bb :: "('A, 'a) Valuation"
  assumes "valid ova"
  and  "Bb \<in> elems ova" and "B \<in> Space.opens (space ova)" and "A \<in> Space.opens (space ova)"
  and  "B \<subseteq> A" and "B \<in> Space.opens (space ova)" and "A \<in> Space.opens (space ova)" and "d Bb = B"
defines "ex \<equiv> gext ova"
and "Bb__A \<equiv> gext ova A Bb"
and "mul \<equiv> comb ova"
shows "Bb__A \<in> elems ova "
proof -
  have "valid ova"
    by (simp add: assms(1)) 
  moreover have "B \<subseteq> A \<and> B \<in> Space.opens (space ova) \<and> A \<in> Space.opens (space ova) \<and> d Bb = B"
    by (simp add: assms(3) assms(4) assms(5) assms(8)) 
  moreover have "Bb__A = mul (neut ova A) Bb"
    by (simp add: Bb__A_def assms(4) assms(5) assms(8) gext_def mul_def)
  ultimately show ?thesis
    by (smt (verit) OVA.valid_welldefined OrderedSemigroup.valid_def Poset.valid_def assms(2) comb_def elems_def mul_def neutral_is_element valid_monotone) 
qed

lemma e_gprj : 
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"  and Aa :: "('A, 'a) Valuation" 
  defines "pr \<equiv> gprj ova"
  and "\<Phi>B \<equiv> Presheaf.ob (presheaf ova) $ B"
  and "Aa_B \<equiv> gprj ova B Aa"
  assumes "valid ova"
  and "B \<subseteq> A" and "B \<in> opens (space ova)" and "A \<in> opens (space ova)"
  and "d Aa = A"
  and "Aa \<in> elems ova"
shows " e (Aa_B) \<in> Poset.el \<Phi>B"
proof -
  have "valid ova"
    by (simp add: assms(4))  
  moreover have "Poset.valid \<Phi>B"
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>B_def assms(6) calculation posets_valid) 
  moreover have "d Aa_B = B"
    using Aa_B_def assms(5) assms(6) assms(7) assms(8) assms(9) calculation(1) d_gprj by blast
  define "i" where "i = Space.make_inclusion (space ova) B A" 
  define "\<Phi>i" where "\<Phi>i = Presheaf.ar (presheaf ova) $ i"
  moreover have "i \<in> Space.inclusions (space ova)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined assms(5) assms(6) assms(7) calculation(1) i_def inclusions_def make_inclusion_def mem_Collect_eq valid_make_inclusion)
  moreover have "Poset.valid_map \<Phi>i"
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>i_def calculation(1) calculation(4) poset_maps_valid) 
  moreover have "Aa_B = (B, \<Phi>i $$ e Aa)"
    by (simp add: Aa_B_def \<Phi>i_def assms(5) assms(6) assms(8) gprj_def i_def) 
  moreover have "Presheaf.valid (presheaf ova)"
    by (meson OVA.valid_welldefined calculation(1)) 
  moreover have "Poset.cod \<Phi>i = \<Phi>B"
    by (metis Inclusion.select_convs(2) OVA.space_def \<Phi>B_def \<Phi>i_def calculation(4) calculation(7) cod_proj i_def make_inclusion_def) 
  moreover have "\<Phi>i $$ e Aa \<in> Poset.el \<Phi>B"
    by (metis Inclusion.simps(2) Inclusion.simps(3) OVA.space_def OVA.valid_welldefined \<Phi>B_def assms(8) assms(9) calculation(1) calculation(3) calculation(4) e_def elems_def gc_elem_local i_def image make_inclusion_def) 
  ultimately show ?thesis
    by (simp add: e_def)  
qed

lemma e_gext : 
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"  and Bb :: "('A, 'a) Valuation" 
  defines "ex \<equiv> gext ova"
  and "\<Phi>A \<equiv> Presheaf.ob (presheaf ova) $ A"
  and "Bb__A \<equiv> gext ova A Bb"
  assumes "valid ova"
  and "B \<subseteq> A" and "B \<in> opens (space ova)" and "A \<in> opens (space ova)"
  and "d Bb = B"
  and "Bb \<in> elems ova"
shows " e (Bb__A) \<in> Poset.el \<Phi>A"
proof -
  have "valid ova"
    by (simp add: assms(4))  
  moreover have "Poset.valid \<Phi>A"
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>A_def assms(7) calculation posets_valid)
    moreover have "d Bb__A = A"
      using Bb__A_def assms(5) assms(6) assms(7) assms(8) assms(9) calculation(1) d_gext by blast 
  define "i" where "i = Space.make_inclusion (space ova) B A" 
  define "\<Phi>i" where "\<Phi>i = Presheaf.ar (presheaf ova) $ i"
  moreover have "i \<in> Space.inclusions (space ova)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined assms(5) assms(6) assms(7) calculation(1) i_def inclusions_def make_inclusion_def mem_Collect_eq valid_make_inclusion)
  moreover have "Poset.valid_map \<Phi>i"
    by (metis OVA.space_def OVA.valid_welldefined \<Phi>i_def calculation(1) calculation(4) poset_maps_valid) 
  moreover have "Bb__A = comb ova (neut ova A) Bb"
    by (simp add: Bb__A_def assms(5) assms(7) assms(8) gext_def) 
  moreover have "... = (A, e (comb ova (neut ova A) Bb))"
    by (metis \<open>d Bb__A = A\<close> calculation(6) d_def e_def prod.collapse) 
  ultimately show ?thesis
    by (metis Bb__A_def \<Phi>A_def \<open>d Bb__A = A\<close> assms(5) assms(6) assms(7) assms(8) assms(9) gext_elem local_inclusion_element)  
qed

lemma ext_prj_adjunction_lhs_imp_rhs :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon>A \<equiv> neut ova (d Aa)"
  assumes valid_ova : "valid ova"
  and elems : "Aa \<in> elems ova \<and> Bb \<in> elems ova"
  and doms : "d Aa = A \<and> d Bb = B" and "B \<subseteq> A"
  and LHS: "le ova (d Bb) (e (gprj ova B Aa)) (e Bb)"
  shows "le ova (d Aa) (e Aa) (e (mul \<epsilon>A Bb))"
proof -
  have "valid ova \<and> le ova (d Bb) (e (gprj ova B Aa)) (e Bb)"
    by (simp add: LHS valid_ova)
  define "Aa_B" where "Aa_B \<equiv> (gprj ova B Aa)"
  define "a_B" where "a_B \<equiv> e Aa_B"
  define "b" where "b \<equiv> e Bb"
  define "A" where "A \<equiv> d Aa"
  define "B" where "B \<equiv> d Bb"
  moreover have "gle ova Aa Aa_B"
    by (metis Aa_B_def assms(8) doms elems id_le_gprj local_inclusion_domain valid_ova) 
  moreover have "Aa = mul \<epsilon>A Aa"
    by (metis \<epsilon>A_def elems local_inclusion_domain mul_def valid_neutral_law_left valid_ova)
  moreover have a_B_le_b : "le ova B a_B b"
    by (simp add: Aa_B_def B_def LHS a_B_def b_def)
  moreover have "Poset.valid (\<Phi>0 A)"
    by (metis A_def OVA.space_def OVA.valid_welldefined \<Phi>0_def \<Phi>_def elems local_inclusion_domain posets_valid valid_ova)
  moreover have "d \<epsilon>A = A"
    by (simp add: A_def \<epsilon>A_def d_def neut_def)
  moreover have "Poset.valid (\<Phi>0 A)"
    using calculation(5) by auto
  moreover have " e \<epsilon>A \<in> Poset.el (\<Phi>0 A)"  using neutral_local_element
    using A_def \<Phi>0_def \<Phi>_def \<epsilon>A_def elems local_inclusion_domain valid_ova by blast
  moreover have "le ova A (e \<epsilon>A) (e \<epsilon>A)"
    by (metis \<Phi>0_def \<Phi>_def calculation(5) calculation(8) le_def valid_reflexivity)
    define "gc_poset" where "gc_poset = (OrderedSemigroup.poset (ordered_semigroup ova))"
  moreover have "Poset.valid gc_poset"
    by (metis OVA.valid_welldefined OrderedSemigroup.valid_welldefined gc_poset_def valid_ova)
  moreover have "\<epsilon>A \<in> Poset.el gc_poset" using gc_poset_def   \<epsilon>A_def
    by (metis elems elems_def local_inclusion_domain neutral_is_element valid_ova)
  moreover have "gle ova \<epsilon>A \<epsilon>A" using gle_def
    by (metis calculation(10) calculation(11) gc_poset_def valid_reflexivity)
  moreover have "gle ova (mul \<epsilon>A Aa) (mul \<epsilon>A Aa_B)"
    by (metis (no_types, lifting) OVA.valid_welldefined Poset.valid_welldefined calculation(10) calculation(12) calculation(2) comb_def gc_poset_def gle_def mul_def valid_monotone valid_ova)
  moreover have "d Aa_B = B \<and> d Bb = B"
    by (metis Aa_B_def B_def assms(8) d_gprj doms elems local_inclusion_domain valid_ova) 
  moreover have "Aa_B = (B, a_B) \<and> Bb = (B, b)"
    by (metis a_B_def b_def calculation(14) d_def e_def prod.collapse)
  moreover have "gle ova Aa_B Bb"  using  a_B_le_b
    by (metis Poset.valid_welldefined a_B_def b_def calculation(10) calculation(14) calculation(2) elems elems_def gc_poset_def gle_def le_imp_gle2 local_inclusion_domain valid_ova) 
  moreover have "gle ova (mul \<epsilon>A Aa_B) (mul \<epsilon>A Bb)"
    by (metis OVA.valid_welldefined calculation(12) calculation(16) combine_monotone elems_def gle_def mul_def valid_gc_welldefined valid_ova)
moreover have "gle ova (mul \<epsilon>A Aa) (mul \<epsilon>A Aa_B)"
  by (simp add: calculation(13))
moreover have "gle ova Aa (mul \<epsilon>A Aa_B)"
  using calculation(13) calculation(3) by auto
  moreover have "A \<union> B = A"
    by (simp add: A_def B_def Un_absorb2 assms(8) doms) 
  moreover have "d (mul \<epsilon>A Aa_B) = A" using valid_domain_law
    by (metis Poset.valid_welldefined calculation(10) calculation(11) calculation(14) calculation(2) calculation(20) calculation(6) elems_def gc_poset_def gle_def mul_def valid_ova)
  ultimately show ?thesis
    by (smt (verit) A_def Poset.valid_welldefined elems_def gle_def gle_imp_le local_inclusion_domain mul_def valid_domain_law valid_ova valid_transitivity) 
qed

lemma ext_prj_adjunction_rhs_imp_lhs :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon>A \<equiv> neut ova (d Aa)"
  assumes valid_ova : "valid ova"
  and elems : "Aa \<in> elems ova \<and> Bb \<in> elems ova"
  and doms : "d Aa = A \<and> d Bb = B" 
  and "A \<in> Space.opens (space ova)" and "B \<in> Space.opens (space ova)" and "B \<subseteq> A"
  and RHS: "le ova (d Aa) (e Aa) (e (mul \<epsilon>A Bb))"
shows "le ova (d Bb) (e (gprj ova B Aa)) (e Bb)"
proof -
  have "valid ova" and "le ova A (e Aa) (e (mul \<epsilon>A Bb))"
     apply (simp add: RHS valid_ova)
    using RHS doms by blast 
  moreover have "A \<union> B = A"
    using assms(10) by blast  
    moreover have" d Aa = A"
      using doms by fastforce 
    moreover have  "d  (mul \<epsilon>A Bb) = A"
      by (simp add: \<epsilon>A_def assms(8) calculation(3) doms elems mul_def neutral_element neutral_is_element valid_domain_law valid_ova) 
      moreover have "Aa \<in> elems ova \<and> Bb \<in> elems ova"
      by (simp add: elems)
    moreover have "(mul \<epsilon>A Bb) \<in> elems ova"
      by (smt (verit) OVA.valid_welldefined OrderedSemigroup.valid_def Poset.valid_welldefined \<epsilon>A_def assms(8) comb_def doms elems elems_def mul_def neutral_is_element valid_monotone valid_ova valid_reflexivity) 
    moreover have "gle ova Aa (mul \<epsilon>A Bb)" using le_imp_gle2
      using assms(8) calculation(2) calculation(4) calculation(5) calculation(7) elems valid_ova by blast 
    moreover have "gle ova (gprj ova B Aa) (gprj ova B (mul \<epsilon>A Bb))"
      using assms(10) assms(8) assms(9) calculation(5) calculation(7) calculation(8) doms elems gprj_monotone valid_ova by blast 
    moreover have "gprj ova B (mul \<epsilon>A Bb) = mul (gprj ova (A \<inter> B) \<epsilon>A) Bb"  using valid_comb_law_right
      by (metis \<epsilon>A_def assms(8) doms elems mul_def neutral_element neutral_is_element valid_ova) 
    define "\<epsilon>B" where "\<epsilon>B \<equiv> neut ova B"
    moreover have "gprj ova (A \<inter> B) \<epsilon>A = \<epsilon>B"
      by (metis Un_Int_eq(2) \<epsilon>A_def \<epsilon>B_def assms(10) assms(8) assms(9) calculation(3) doms stability valid_ova) 
    moreover have "mul (gprj ova (A \<inter> B) \<epsilon>A) Bb = Bb"
      by (metis \<epsilon>B_def assms(9) calculation(11) doms elems mul_def valid_neutral_law_left valid_ova) 
    ultimately show ?thesis
      by (metis (mono_tags, lifting) OVA.valid_welldefined \<open>gprj ova B (mul \<epsilon>A Bb) = mul (gprj ova (A \<inter> B) \<epsilon>A) Bb\<close> assms(10) assms(8) assms(9) d_gprj elems_def gle_def gle_imp_le valid_gc_welldefined)
  qed

(* [Remark 3, CVA] *)
lemma laxity :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"  and Aa Aa' :: "('A, 'a) Valuation"
  assumes "valid ova"
  and  "A \<in> Space.opens (space ova)" and "B \<in> Space.opens (space ova)"  and "B \<subseteq> A"
  and  "Aa \<in> elems ova" and "d Aa = A" and  "Aa' \<in> elems ova" and "d Aa' = A"
defines "pr \<equiv> gprj ova" and "mul \<equiv> comb ova" and "l \<equiv> gle ova"
shows "le ova B (e (pr B (mul Aa Aa'))) (e (mul (pr B Aa) (pr B Aa')))"
proof -
   have "l Aa (pr B Aa)"
     using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) id_le_gprj l_def pr_def by blast
   moreover have "l Aa' (pr B Aa')"
     using assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) id_le_gprj l_def pr_def by blast
   define "m1" where "m1 = mul Aa Aa'"
   define "m2" where "m2 = mul (pr B Aa) (pr B Aa')"
   moreover have "d m1 = A"
     by (simp add: assms(1) assms(5) assms(6) assms(7) assms(8) m1_def mul_def valid_domain_law)
   moreover have "d m2 = B"
     by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) d_gprj gprj_elem m2_def mul_def neutral_element neutral_is_element pr_def valid_domain_law valid_neutral_law_right)
   moreover have "l m1 m2"
     by (metis \<open>l Aa' (pr B Aa')\<close> assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) calculation(1) combine_monotone gprj_elem l_def m1_def m2_def mul_def pr_def) 
   define "\<Phi>B" where "\<Phi>B = (Presheaf.ob (presheaf ova)) $ B"
    moreover have "e  m2 \<in> Poset.el \<Phi>B"
      by (metis OVA.valid_welldefined \<Phi>B_def \<open>l m1 m2\<close> assms(1) calculation(4) elems_def gle_def l_def local_inclusion_element valid_gc_welldefined)
   moreover have "e (pr B m1) \<in> Poset.el \<Phi>B"
     by (metis OVA.valid_welldefined \<Phi>B_def \<open>l m1 m2\<close> assms(1) assms(2) assms(3) assms(4) calculation(3) e_gprj elems_def gle_def l_def pr_def valid_gc_welldefined) 
   ultimately show ?thesis
     by (smt (z3) OVA.valid_welldefined \<open>l m1 m2\<close> assms(1) assms(2) assms(3) assms(4) combine_monotone elems_def ext_prj_adjunction_rhs_imp_lhs gle_def gle_imp_le id_le_gprj l_def m1_def neutral_element neutral_is_element pr_def stability sup.order_iff valid_domain_law valid_gc_welldefined valid_neutral_law_left)
 qed

(* THEOREMS *)

(* [Theorem 1, CVA] *)
theorem ext_prj_adjunction :
  fixes ova :: "('A,'a) OVA" and  Aa Bb :: "('A, 'a) Valuation"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon>A \<equiv> neut ova (d Aa)"
  defines "l \<equiv> le ova" 
  defines "pr \<equiv> gprj ova"
  assumes valid_ova : "valid ova"
  and elems : "Aa \<in> elems ova \<and> Bb \<in> elems ova"
  and doms : "d Bb \<subseteq> d Aa"
shows "l (d Bb) (e (pr (d Bb) Aa)) (e Bb) \<longleftrightarrow> l (d Aa) (e Aa) (e (mul \<epsilon>A Bb))"
  by (metis \<epsilon>A_def doms elems ext_prj_adjunction_lhs_imp_rhs ext_prj_adjunction_rhs_imp_lhs l_def local_inclusion_domain mul_def pr_def valid_ova)

(* [Corollary 1, CVA] *)
theorem strongly_neutral_covariance :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"
  assumes valid_ova : "valid ova"
  and strongly_neutral: "\<forall> A B . comb ova (neut ova A) (neut ova B) = neut ova (A \<union> B)"
  and  "B \<subseteq> A" and "B \<in> Space.opens (space ova)" and "A \<in> Space.opens (space ova)"
defines "ex \<equiv> gext ova"
shows "ex A (neut ova B) = neut ova A "
by (metis assms(3) assms(4) assms(5) d_neut ex_def gext_def strongly_neutral sup.absorb_iff1 valid_ova)

(* [Corollary 2, CVA] *)
theorem ext_prj_eq_id :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open" and Bb :: "('A, 'a) Valuation"
  assumes valid_ova : "valid ova" and "Bb \<in> elems ova" and "d Bb = B"
  and " B \<subseteq> A" and "B \<in> opens (space ova)" and "A \<in> opens (space ova)"
  defines "pr \<equiv> gprj ova" and "ex \<equiv> gext ova" and "mul \<equiv> comb ova"
  shows "pr B (ex A Bb) = Bb"
proof -
  define \<epsilon>A where "\<epsilon>A \<equiv> neut ova A"
  define \<epsilon>B where "\<epsilon>B \<equiv> neut ova B"
  have "pr B (ex A Bb) = pr B (mul \<epsilon>A Bb)"
    by (simp add: \<epsilon>A_def assms(3) assms(4) assms(6) ex_def gext_def mul_def)
  moreover have "... =  mul (pr (A \<inter> B) \<epsilon>A) Bb"  using valid_comb_law_right pr_def mul_def ex_def
    by (metis \<epsilon>A_def assms(2) assms(3) assms(6) neutral_element neutral_is_element valid_ova)
  moreover have "... =  mul \<epsilon>B Bb"
  by (simp add: \<epsilon>A_def \<epsilon>B_def assms(4) assms(5) assms(6) inf.absorb2 pr_def stability valid_ova)
  ultimately show ?thesis
    by (metis \<epsilon>B_def \<open>pr B (ex A Bb) = pr B (mul \<epsilon>A Bb)\<close> assms(2) assms(3) assms(5) mul_def valid_neutral_law_left valid_ova)
qed

(* [Corollary 2 cont., CVA] *)
theorem id_le_prj_ext :
  fixes ova :: "('A,'a) OVA" and A B :: "'A Open"  and Aa :: "('A, 'a) Valuation"
  assumes valid_ova : "valid ova" and "Aa \<in> elems ova" and "d Aa = A"
  and " B \<subseteq> A" and "B \<in> opens (space ova)" and "A \<in> opens (space ova)"
  defines "pr \<equiv> gprj ova" and "ex \<equiv> gext ova" and "mul \<equiv> comb ova" and "l \<equiv> le ova"
  shows "l A (e Aa) (e (ex A (pr B Aa)))"
proof -
  have "valid ova" by fact
  moreover have "l A (e Aa) (e Aa)"
    by (metis OVA.valid_welldefined OrderedSemigroup.valid_def assms(2) assms(3) e_def elems_def l_def le_def local_le valid_ova valid_reflexivity) 
  moreover have "l B (e (pr B Aa)) (e (pr B Aa))"
    by (metis assms(2) assms(3) assms(4) assms(5) assms(6) calculation(2) d_gprj gle_imp_le gprj_elem gprj_monotone l_def le_imp_gle2 pr_def valid_ova) 
  ultimately show ?thesis
    by (metis (full_types) assms(2) assms(3) assms(4) assms(5) assms(6) d_gprj ex_def ext_prj_adjunction_lhs_imp_rhs gext_def gprj_elem l_def pr_def) 
qed

(* [Theorem 1 cont., CVA] *)
theorem ext_functorial :
  fixes ova :: "('A,'a) OVA" and A B C :: "'A Open"  and Cc :: "('A, 'a) Valuation"
  assumes valid_ova : "valid ova"
  and "A \<in> Space.opens (space ova)" and "B \<in> Space.opens (space ova)" and "C \<in> Space.opens (space ova)"
  and "C \<subseteq> B" and "B \<subseteq> A"
  and "d Cc = C"
  defines "ex \<equiv> gext ova"
  shows "ex A (ex B Cc) = ex A Cc"
  oops



