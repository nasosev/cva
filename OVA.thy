theory OVA
imports Main Presheaf OrderedSemigroup Grothendieck Poset
begin
declare [[show_types]]

record ('A, 'a) OVA =
  presheaf :: "('A, 'a) Presheaf"
  neutral :: "('A, unit, 'a) PresheafMap"
  ordered_semigroup :: "('A set \<times> 'a) OrderedSemigroup"

definition comb :: "('A, 'a) OVA \<Rightarrow> ('A set \<times> 'a) \<Rightarrow> ('A set \<times> 'a) \<Rightarrow> ('A set \<times> 'a)" where
"comb ova Aa Bb =  (OrderedSemigroup.mult (ordered_semigroup ova)) $$ (Aa, Bb)"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid ova \<equiv>
    let 
        \<Phi> = presheaf ova;
        E = neutral ova;
        \<epsilon>  = \<lambda> A. (A, (Presheaf.nat (neutral ova) $ A) $$ ());
        T = Presheaf.space \<Phi>;
        S = ordered_semigroup ova;
        comb = comb ova;
        elements = Poset.el (gc \<Phi>);
        inc = \<lambda> B A . \<lparr> Space.Inclusion.space = T, dom = B, cod = A \<rparr>;
        prj = \<lambda> i Aa. (Space.cod i, Presheaf.ar \<Phi> $ i $$ (snd Aa));
        d = fst;

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
             prj (inc (d a) ((d a) \<union> d b)) (comb a b) = comb a (prj (inc ((d a) \<inter> d b) (d a)) b));
        comb_law_right = (\<forall> a b. a \<in> elements \<longrightarrow> b \<in> elements \<longrightarrow>
             prj (inc (d b) ((d a) \<union> d b)) (comb a b) = comb (prj (inc ((d a) \<inter> d b) (d b)) a) b)
    in 
      welldefined \<and> domain_law \<and> neutral_law_left \<and> neutral_law_right \<and> comb_law_left \<and> comb_law_right"





end
