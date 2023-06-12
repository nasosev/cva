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
"elems ova = Poset.el (poset (ordered_semigroup ova))"

definition local_elems :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a set" where
"local_elems ova A = Poset.el (Presheaf.ob (presheaf ova) $ A)"

definition gle :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle ova Aa Bb = Poset.le (OrderedSemigroup.poset (ordered_semigroup ova)) Aa Bb"

definition le :: "('A,'a) OVA \<Rightarrow> 'A Open \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"le ova A Aa Ab = Poset.le (Presheaf.ob (presheaf ova) $ A) Aa Ab"

definition gprj :: "('A,'a) OVA \<Rightarrow> 'A Inclusion =>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gprj ova i Aa \<equiv> if Space.cod i = d Aa then (Space.dom i, Presheaf.ar (presheaf ova) $ i $$ (e Aa)) else undefined"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid ova \<equiv>
    let
        \<Phi> = presheaf ova;
        E = neutral ova;
        \<epsilon> = neut ova;
        T = space ova;
        S = ordered_semigroup ova;
        comb = comb ova;
        elems = elems ova;
        gprj = gprj ova;
        inc = Space.make_inclusion T;

        welldefined = Presheaf.valid \<Phi>
                      \<and> OrderedSemigroup.valid S
                      \<and> Presheaf.valid_map E
                      \<and> T = Presheaf.map_space E
                      \<and> Presheaf.cod E = \<Phi>
                      \<and> Presheaf.dom E = Presheaf.terminal T
                      \<and> OrderedSemigroup.poset S = gc \<Phi>;

        domain_law = \<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow> d (comb Aa Bb) = d Aa \<union> d Bb;
        neutral_law_left = (\<forall>A Aa. A \<in> opens T \<longrightarrow> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> comb (\<epsilon> A) Aa = Aa);
        neutral_law_right = (\<forall>A Aa. A \<in> opens T \<and> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> comb Aa (\<epsilon> A) = Aa);
        comb_law_left = (\<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
             gprj (inc (d Aa) (d Aa \<union> d Bb)) (comb Aa Bb) = comb Aa (gprj (inc (d Aa \<inter> d Bb) (d Aa)) Bb));
        comb_law_right = (\<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
             gprj (inc (d Bb) (d Aa \<union> d Bb)) (comb Aa Bb) = comb (gprj (inc (d Aa \<inter> d Bb) (d Bb)) Aa) Bb)
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
  defines "com \<equiv> comb ova"
  defines "elem \<equiv> elems ova"
  defines "gp \<equiv> gprj ova"
  defines "inc \<equiv> Space.make_inclusion T"
  assumes welldefined : "Presheaf.valid \<Phi> \<and> OrderedSemigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> OrderedSemigroup.poset S = gc \<Phi>"
  assumes domain_law : " \<forall> Aa Bb . Aa \<in> elem \<longrightarrow> Bb \<in> elem \<longrightarrow> d (com Aa Bb) = d Aa \<union> d Bb"
  assumes neutral_law_left : "( \<forall> A Aa . A \<in> opens T \<longrightarrow> Aa \<in> elem \<longrightarrow> d Aa = A \<longrightarrow> com (\<epsilon> A) Aa = Aa)"
  assumes neutral_law_right : "(\<forall> A Aa .A \<in> opens T \<and> Aa \<in> elem \<longrightarrow> d Aa = A \<longrightarrow> com Aa (\<epsilon> A) = Aa)"
  assumes comb_law_left : "(\<forall> Aa Bb . Aa \<in> elem \<longrightarrow> Bb \<in> elem \<longrightarrow>
             gp (inc (d Aa) (d Aa \<union> d Bb)) (com Aa Bb) = com Aa (gp (inc (d Aa \<inter> d Bb) (d Aa)) Bb))"
  assumes comb_law_right : "(\<forall> Aa Bb . Aa \<in> elem \<longrightarrow> Bb \<in> elem \<longrightarrow>
              gp (inc (d Bb) (d Aa \<union> d Bb)) (com Aa Bb) = com (gp (inc (d Aa \<inter> d Bb) (d Bb)) Aa) Bb)"
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
  using com_def domain_law elem_def apply blast
  using com_def domain_law elem_def apply blast
  using com_def domain_law elem_def apply blast
  using T_def \<epsilon>_def com_def elem_def neutral_law_left apply presburger
  using T_def \<epsilon>_def com_def elem_def neutral_law_right apply blast
  using T_def com_def comb_law_left elem_def gp_def local.inc_def apply blast
  using T_def com_def comb_law_right elem_def gp_def local.inc_def by blast

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
  shows "valid ova \<Longrightarrow> let \<epsilon> = neut ova; T = space ova; comb = comb ova; elems = elems ova in
    \<forall>A Aa. A \<in> opens T \<longrightarrow> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> comb (\<epsilon> A) Aa = Aa"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_right  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let  \<epsilon> = neut ova; T = space ova; comb = comb ova; elems = elems ova in
    \<forall>A Aa. A \<in> opens T \<and> Aa \<in> elems \<longrightarrow> d Aa = A \<longrightarrow> comb Aa (\<epsilon> A) = Aa"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_left  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova; gprj = gprj ova in
    \<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
      gprj (Space.make_inclusion T (d Aa) (d Aa \<union> d Bb)) (comb Aa Bb) = comb Aa (gprj (Space.make_inclusion T (d Aa \<inter> d Bb) (d Aa)) Bb)"
  apply (simp add: valid_def Let_def)
  apply safe
  by presburger

lemma valid_comb_law_right  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova; gprj = gprj ova in
    \<forall> Aa Bb. Aa \<in> elems \<longrightarrow> Bb \<in> elems \<longrightarrow>
      gprj (Space.make_inclusion T (d Bb) (d Aa \<union> d Bb)) (comb Aa Bb) = comb (gprj (Space.make_inclusion T (d Aa \<inter> d Bb) (d Bb)) Aa) Bb"
  apply (simp add: valid_def Let_def)
  apply safe
  by presburger

lemma d_gprj : "valid ova \<Longrightarrow> i \<in> Space.inclusions (space ova) \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i \<Longrightarrow>
 d Aa = A \<Longrightarrow>  Aa_B = gprj ova i Aa \<Longrightarrow> d Aa_B = B"
  by (simp add: d_def gprj_def)

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
  have "valid ova"
    by (simp add: valid_ova)
  moreover have "A \<in> opens (space ova)"
    using domain by blast
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

lemma local_inclusion_element : "valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = d Aa \<Longrightarrow> a = e Aa
\<Longrightarrow> \<Phi> = (presheaf ova) \<Longrightarrow> ob_A = ob \<Phi> $ A \<Longrightarrow> a \<in> el ob_A"
  by (metis OVA.valid_welldefined e_def elems_def gc_elem_local)

lemma local_inclusion_domain  : "valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = d Aa \<Longrightarrow> T = space ova \<Longrightarrow> A \<in> opens T"
  by (metis OVA.space_def OVA.valid_welldefined elems_def local_dom)

lemma combine_monotone : "valid ova \<Longrightarrow>  Aa1 \<in> elems ova \<Longrightarrow> Aa2 \<in> elems ova \<Longrightarrow> Bb1 \<in> elems ova \<Longrightarrow> Bb2 \<in> elems ova
\<Longrightarrow>  gle ova Aa1 Aa2 \<Longrightarrow> gle ova Bb1 Bb2 \<Longrightarrow> gle ova (comb ova Aa1 Bb1) (comb ova Aa2 Bb2)"
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

lemma gprj_monotone : "valid ova \<Longrightarrow> i \<in> inclusions (space ova) \<Longrightarrow> A = Space.cod i \<Longrightarrow> B = Space.dom i
\<Longrightarrow> False"
  oops

(* [Remark 3, CVA] *)
lemma laxity : "todo"
  oops

(* [Remark 3, CVA] *)
lemma local_mono_imp_global : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow>  a1 \<in> local_elems ova A \<Longrightarrow>  a1' \<in> local_elems ova A
\<Longrightarrow>  a2' \<in> local_elems ova A \<Longrightarrow>  a2' \<in> local_elems ova A \<Longrightarrow> le ova A a1 a2 \<Longrightarrow> le ova A a1' a2'
 \<Longrightarrow> gle ova (comb ova (A,a1) (A,a1')) (comb ova (A,a2) (A,a2'))"
  oops


(* [Remark 3, CVA] *)
lemma global_mono_imp_local : "valid ova \<Longrightarrow> A \<in> opens (space ova) \<Longrightarrow>  Aa1 \<in> elems ova \<Longrightarrow>  Aa1' \<in> elems ova
\<Longrightarrow>  Aa2' \<in> elems ova \<Longrightarrow>  Aa2' \<in> elems ova \<Longrightarrow> d Aa1 = A \<Longrightarrow> d Aa1' = A \<Longrightarrow> d Aa2 = A \<Longrightarrow> d Aa2' = A \<Longrightarrow>
gle ova Aa1 Aa2 \<Longrightarrow> gle ova Aa1' Aa2' \<Longrightarrow> le ova A (e (comb ova (A,a1) (A,a1'))) (e (comb ova (A,a2) (A,a2')))"
  oops

(* [Remark 3, CVA] *)
lemma id_le_gprj :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa :: "('A, 'a) Valuation"
  shows " valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> i \<in> inclusions (space ova) \<Longrightarrow> d Aa = Space.cod i \<Longrightarrow> Aa_B = (gprj ova i Aa)
\<Longrightarrow> gle ova Aa Aa_B"
  unfolding gprj_def gle_def gc_def
  apply clarsimp
  apply (frule valid_welldefined)
  apply (simp_all add: Let_def d_def gc_def gle_def gprj_def)
  apply clarsimp
  apply safe
  apply (metis OVA.space_def space_valid valid_inclusion_cod)
      apply (metis OVA.space_def space_valid valid_inclusion_dom)
     apply (simp add: elems_def)
    apply (simp add: OVA.space_def elems_def image)
  apply (simp add: e_def image)
  apply (meson Presheaf.valid_map_welldefined in_mono valid_inclusion_def valid_inclusions)
  by (smt (verit, ccfv_SIG) Inclusion.surjective OVA.space_def Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD e_def elems_def fst_conv image inclusions_def make_inclusion_def mem_Collect_eq old.unit.exhaust posets_valid snd_conv space_valid valid_inclusion_dom valid_reflexivity)

lemma extension_left :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon>A \<equiv> neut ova (d Aa)"
  assumes valid_ova : "valid ova"
  and inclusion : "i \<in> inclusions (space ova)"
  and elems : "Aa \<in> elems ova \<and> Bb \<in> elems ova"
  and doms : "d Aa = Space.cod i \<and> d Bb = Space.dom i"
  and LHS: "le ova (d Bb) (e (gprj ova i Aa)) (e Bb)"
  shows "le ova (d Aa) (e Aa) (e (mul \<epsilon>A Bb))"
proof -
  have "valid ova \<and> le ova (d Bb) (e (gprj ova i Aa)) (e Bb)"
    by (simp add: LHS valid_ova)
  define "Aa_B" where "Aa_B \<equiv> (gprj ova i Aa)"
  define "a_B" where "a_B \<equiv> e Aa_B"
  define "b" where "b \<equiv> e Bb"
  define "A" where "A \<equiv> d Aa"
  define "B" where "B \<equiv> d Bb"
  moreover have "gle ova Aa Aa_B"
    using Aa_B_def doms elems id_le_gprj inclusion valid_ova by blast
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
    by (metis Aa_B_def B_def d_gprj doms elems inclusion valid_ova) 
  moreover have "Aa_B = (B, a_B) \<and> Bb = (B, b)"
    by (metis a_B_def b_def calculation(14) d_def e_def prod.collapse) 
  moreover have "gle ova Aa_B Bb"  using le_imp_gle a_B_le_b
    by (metis Aa_B_def B_def OVA.space_def OVA.valid_welldefined calculation(15) doms e_def elems gprj_def image inclusion local_elems_def local_inclusion_domain local_inclusion_element snd_conv valid_ova) 
  moreover have "gle ova (mul \<epsilon>A Aa_B) (mul \<epsilon>A Bb)"
    by (metis OVA.valid_welldefined calculation(12) calculation(16) combine_monotone elems_def gle_def mul_def valid_gc_welldefined valid_ova) 
moreover have "gle ova (mul \<epsilon>A Aa) (mul \<epsilon>A Aa_B)"
  by (simp add: calculation(13)) 
moreover have "gle ova Aa (mul \<epsilon>A Aa_B)"
  using calculation(13) calculation(3) by auto
  moreover have "A \<union> B = A"
    by (metis A_def B_def OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined Un_absorb2 doms inclusion valid_inclusion_def valid_inclusions valid_ova) 
  moreover have "d (mul \<epsilon>A Aa_B) = A" using valid_domain_law
    by (metis Poset.valid_welldefined calculation(10) calculation(11) calculation(14) calculation(2) calculation(20) calculation(6) elems_def gc_poset_def gle_def mul_def valid_ova) 
  ultimately show ?thesis
    by (metis (no_types, lifting) A_def Poset.valid_welldefined elems_def gle_def gle_imp_le local_inclusion_domain mul_def valid_domain_law valid_ova valid_transitivity)
qed

lemma extension_right :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon>A \<equiv> neut ova (d Aa)"
  assumes valid_ova : "valid ova"
  and inclusion : "i \<in> inclusions (space ova)"
  and elems : "Aa \<in> elems ova \<and> Bb \<in> elems ova"
  and doms : "d Aa = Space.cod i \<and> d Bb = Space.dom i"
  and RHS: "le ova (d Aa) (e Aa) (e (mul \<epsilon>A Bb))"
shows "le ova (d Bb) (e (gprj ova i Aa)) (e Bb)" 
proof -
  define "A" where "A \<equiv> d Aa"
  define "B" where "B \<equiv> d Bb"
  have "valid ova" and "le ova A (e Aa) (e (mul \<epsilon>A Bb))"
     apply (simp add: RHS valid_ova)
    by (simp add: A_def RHS) 
  moreover have "A \<union> B = A"
    by (metis A_def B_def OVA.space_def OVA.valid_welldefined Presheaf.valid_welldefined Un_absorb2 doms inclusion valid_inclusion_def valid_inclusions valid_ova) 
  moreover have" d Aa = A" 
    by (simp add: A_def)
    moreover have  "d  (mul \<epsilon>A Bb) = A"
      by (metis A_def B_def \<epsilon>A_def calculation(3) elems local_inclusion_domain mul_def neutral_element neutral_is_element valid_domain_law valid_ova) 
    moreover have "Aa \<in> elems ova \<and> Bb \<in> elems ova"
      by (simp add: elems) 
    moreover have "(mul \<epsilon>A Bb) \<in> elems ova"
      by (metis A_def OVA.space_def OVA.valid_welldefined Poset.valid_welldefined RHS calculation(5) d_def e_def elems elems_def le_def local_elem_gc local_inclusion_domain posets_valid prod.collapse valid_ova) 
    moreover have "gle ova Aa (mul \<epsilon>A Bb)" using le_imp_gle2
      by (metis A_def RHS calculation(5) calculation(7) elems local_inclusion_domain valid_ova)
    moreover have "gle ova (gprj ova i Aa) (gprj ova i (mul \<epsilon>A Bb))" 
      oops

(* THEOREMS *)
(*
(* [Theorem 1, CVA] *)
theorem extension :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "prj \<equiv> (\<lambda> i Aa. (Space.cod i, Presheaf.ar \<Phi> $ i $$ (e Aa)))"
  defines "lessEq \<equiv> (\<lambda> A Aa Ab . le (\<Phi>0 A) (e Aa) (e Ab))"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon> \<equiv> neut ova"
  assumes "d Aa = Space.cod i \<and> d Bb = Space.dom i"
  assumes "valid ova" and "i \<in> inclusions (space ova)"
  shows "lessEq (d Bb) (prj i Aa) Bb = lessEq (d Aa) Aa (mul (\<epsilon> A) Bb)"
proof -
  oops
*)
(* theorem extension_functorial *)

end