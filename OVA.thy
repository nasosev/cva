theory OVA
imports Main Presheaf OrderedSemigroup Grothendieck Poset
begin
declare [[show_types]]

type_synonym ('A, 'a) Valuation = "('A set \<times> 'a)"

record ('A, 'a) OVA =
  presheaf :: "('A, 'a) Presheaf"
  neutral :: "('A, unit, 'a) PresheafMap"
  ordered_semigroup :: "(('A, 'a) Valuation) OrderedSemigroup"

definition comb :: "('A, 'a) OVA \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation \<Rightarrow> ('A, 'a) Valuation" where
"comb ova Aa Bb =  (OrderedSemigroup.mult (ordered_semigroup ova)) $$ (Aa, Bb)"

definition neut :: "('A, 'a) OVA \<Rightarrow> ('A set \<Rightarrow> ('A, 'a) Valuation)" where
"neut ova  = (\<lambda> A. (A, (Presheaf.nat (neutral ova) $ A) $$ ()))"

definition d :: "('A, 'a) Valuation \<Rightarrow> 'A set" where
"d Aa = fst Aa"

definition space :: "('A,'a) OVA \<Rightarrow> 'A Space" where 
"space ova = Presheaf.space (presheaf ova)"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid ova \<equiv>
    let 
        \<Phi> = presheaf ova;
        E = neutral ova;
        \<epsilon> = neut ova;
        T = space ova;
        S = ordered_semigroup ova;
        comb = comb ova;
        elements = Poset.el (gc \<Phi>);
        inc = \<lambda> B A . \<lparr> Space.Inclusion.space = T, dom = B, cod = A \<rparr>;
        prj = \<lambda> i Aa. (Space.cod i, Presheaf.ar \<Phi> $ i $$ (snd Aa));

        welldefined = Presheaf.valid \<Phi>
                      \<and> OrderedSemigroup.valid S
                      \<and> Presheaf.valid_map E
                      \<and> T = Presheaf.map_space E
                      \<and> Presheaf.cod E = \<Phi>
                      \<and> Presheaf.dom E = Presheaf.terminal T
                      \<and> OrderedSemigroup.poset S = gc \<Phi>;

        domain_law = \<forall> a b. a \<in> elements \<longrightarrow> b \<in> elements \<longrightarrow> d (comb a b) = d a \<union> d b;
        neutral_law_left = (\<forall>A a. A \<in> opens T \<longrightarrow> a \<in> elements \<longrightarrow> d a = A \<longrightarrow> comb (\<epsilon> A) a = a);
        neutral_law_right = (\<forall>A a. A \<in> opens T \<and> a \<in> elements \<longrightarrow> d a = A \<longrightarrow> comb a (\<epsilon> A) = a);
        comb_law_left = (\<forall> a b. a \<in> elements \<longrightarrow> b \<in> elements \<longrightarrow>
             prj (inc (d a) (d a \<union> d b)) (comb a b) = comb a (prj (inc (d a \<inter> d b) (d a)) b));
        comb_law_right = (\<forall> a b. a \<in> elements \<longrightarrow> b \<in> elements \<longrightarrow>
             prj (inc (d b) (d a \<union> d b)) (comb a b) = comb (prj (inc (d a \<inter> d b) (d b)) a) b)
    in 
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"

(* Doesnt show functoriality of extension *)
theorem extension :
  fixes ova :: "('A,'a) OVA" and i :: "'A Inclusion" and Aa Bb :: "('A, 'a) Valuation"
  defines "\<Phi> \<equiv> presheaf ova"
  defines "\<Phi>0 \<equiv> (\<lambda> A . (ob \<Phi>) $ A)" 
  defines "prj \<equiv> (\<lambda> i Aa. (Space.cod i, Presheaf.ar \<Phi> $ i $$ (snd Aa)))"
  defines "lessEq \<equiv> (\<lambda> A Aa Ab . le (\<Phi>0 A) (snd Aa) (snd Ab))"
  defines "mul \<equiv> comb ova"
  defines "\<epsilon> \<equiv> neut ova"
  assumes "d a = Space.cod i \<and> d B = Space.dom i"
  assumes "valid ova" and "i \<in> inclusions (space ova)"
  shows "lessEq (d Bb) (prj i Aa) b \<longleftrightarrow> lessEq (d Aa) Aa (mul (\<epsilon> A) Bb)"
proof -



end
