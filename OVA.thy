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

definition gle :: "('A,'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> bool" where
"gle ova Aa Bb = Poset.le (OrderedSemigroup.poset (ordered_semigroup ova)) Aa Bb"

definition gprj :: "('A,'a) OVA \<Rightarrow> 'A Inclusion =>  ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"gprj ova i Aa \<equiv> if Space.cod i = d Aa then (d Aa, Presheaf.ar (presheaf ova) $ i $$ (snd Aa)) else undefined"

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
        inc = \<lambda> B A . \<lparr> Space.Inclusion.space = T, dom = B, cod = A \<rparr>;
        gprj = gprj ova;

        welldefined = Presheaf.valid \<Phi>
                      \<and> OrderedSemigroup.valid S
                      \<and> Presheaf.valid_map E
                      \<and> T = Presheaf.map_space E
                      \<and> Presheaf.cod E = \<Phi>
                      \<and> Presheaf.dom E = Presheaf.terminal T
                      \<and> OrderedSemigroup.poset S = gc \<Phi>;

        domain_law = \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow> d (comb a b) = d a \<union> d b;
        neutral_law_left = (\<forall>A a. A \<in> opens T \<longrightarrow> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> comb (\<epsilon> A) a = a);
        neutral_law_right = (\<forall>A a. A \<in> opens T \<and> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> comb a (\<epsilon> A) = a);
        comb_law_left = (\<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
             gprj (inc (d a) (d a \<union> d b)) (comb a b) = comb a (gprj (inc (d a \<inter> d b) (d a)) b));
        comb_law_right = (\<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
             gprj (inc (d b) (d a \<union> d b)) (comb a b) = comb (gprj (inc (d a \<inter> d b) (d b)) a) b)
    in
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"

(* LEMMAS *)

lemma valid_welldefined  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova in
    Presheaf.valid \<Phi> \<and> OrderedSemigroup.valid S \<and> Presheaf.valid_map E \<and> T = Presheaf.map_space E \<and>
    Presheaf.cod E = \<Phi> \<and> Presheaf.dom E = Presheaf.terminal T \<and> OrderedSemigroup.poset S = gc \<Phi>"
  by (simp add: valid_def Let_def)

lemma valid_domain_law  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow> d (comb a b) = d a \<union> d b"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_left  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova in
    \<forall>A a. A \<in> opens T \<longrightarrow> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> comb (\<epsilon> A) a = a"
  by (simp add: valid_def Let_def)

lemma valid_neutral_law_right  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova in
    \<forall>A a. A \<in> opens T \<and> a \<in> elems \<longrightarrow> d a = A \<longrightarrow> comb a (\<epsilon> A) = a"
  by (simp add: valid_def Let_def)

lemma valid_comb_law_left  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova; inc = \<lambda> B A . \<lparr> Space.Inclusion.space = T, dom = B, cod = A \<rparr>; gprj = gprj ova in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
      gprj (inc (d a) (d a \<union> d b)) (comb a b) = comb a (gprj (inc (d a \<inter> d b) (d a)) b)"
  apply (simp add: valid_def Let_def)
  apply safe
  by presburger

lemma valid_comb_law_right  :
  fixes ova :: "('A,'a) OVA"
  shows "valid ova \<Longrightarrow> let \<Phi> = presheaf ova; E = neutral ova; \<epsilon> = neut ova; T = space ova; S = ordered_semigroup ova; comb = comb ova; elems = elems ova; inc = \<lambda> B A . \<lparr> Space.Inclusion.space = T, dom = B, cod = A \<rparr>; gprj = gprj ova in
    \<forall> a b. a \<in> elems \<longrightarrow> b \<in> elems \<longrightarrow>
      gprj (inc (d b) (d a \<union> d b)) (comb a b) = comb (gprj (inc (d a \<inter> d b) (d b)) a) b"
  apply (simp add: valid_def Let_def)
  apply safe
  by presburger

lemma local_inclusion_element : "valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = d Aa \<Longrightarrow> a = snd Aa 
\<Longrightarrow> \<Phi> = (presheaf ova) \<Longrightarrow> ob_A = ob \<Phi> $ A \<Longrightarrow> a \<in> el ob_A"
  by (metis OVA.valid_welldefined elems_def local_elem)

lemma local_inclusion_domain  : "valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> A = d Aa \<Longrightarrow> T = space ova \<Longrightarrow> A \<in> opens T"
  by (metis OVA.space_def OVA.valid_welldefined elems_def local_dom)
 
lemma id_le_gprj :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa :: "('A, 'a) Valuation"
  shows " valid ova \<Longrightarrow> Aa \<in> elems ova \<Longrightarrow> i \<in> inclusions (space ova) \<Longrightarrow> d Aa = Space.cod i \<Longrightarrow> Aa_B = (gprj ova i Aa) 
\<Longrightarrow> gle ova Aa Aa_B"
  unfolding gprj_def gle_def gc_def
  apply clarsimp
  apply (frule valid_welldefined)
  apply (simp_all add: Let_def d_def gc_def gle_def gprj_def)
  apply clarsimp
  apply (simp add: Space.ident_def[symmetric])
  oops
  

  
 
    
   

 

 

  

lemma extension_left :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "l \<equiv> (\<lambda> A Aa Ab . Poset.le (\<Phi>0 A) (snd Aa) (snd Ab))"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon> \<equiv> neut ova"
  shows "d Aa = Space.cod i \<and> d Bb = Space.dom i \<Longrightarrow> valid ova \<Longrightarrow> i \<in> inclusions (space ova) \<Longrightarrow>
    l (d Bb) (prj ova i Aa) Bb \<Longrightarrow> l (d Aa) Aa (mul (\<epsilon> A) Bb)"
  apply clarsimp
  apply (simp add: mul_def)
  oops


(* THEOREMS *)
(*
theorem extension :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)"
  defines "prj \<equiv> (\<lambda> i Aa. (Space.cod i, Presheaf.ar \<Phi> $ i $$ (snd Aa)))"
  defines "lessEq \<equiv> (\<lambda> A Aa Ab . le (\<Phi>0 A) (snd Aa) (snd Ab))"
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
