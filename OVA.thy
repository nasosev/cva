theory OVA
imports Main Presheaf OrderedSemigroup Grothendieck
begin

record ('A, 'a) OVA =
  presheaf :: "('A, 'a) Presheaf"
  neutral :: "('A, unit, 'a) PresheafMap"
  ordered_semigroup :: "('A set \<times> 'a) OrderedSemigroup"


definition mult :: "('A, 'a) OVA \<Rightarrow> (('A set \<times> 'a) \<times> ('A set \<times> 'a) , ('A set \<times> 'a)) PosetMap" where
"mult ova = OrderedSemigroup.mult (ordered_semigroup ova)"

definition valid :: "('A, 'a) OVA \<Rightarrow> bool" where
  "valid ova \<equiv>
    let 
        \<Phi> = presheaf ova;
        \<epsilon> = neutral ova;
        T = Presheaf.space \<Phi>;
        S = ordered_semigroup ova;

        welldefined = Presheaf.valid \<Phi>
                      \<and> OrderedSemigroup.valid S
                      \<and> Presheaf.valid_map \<epsilon>
                      \<and> T = Presheaf.map_space \<epsilon>
                      \<and> Presheaf.cod \<epsilon> = \<Phi>
                      \<and> Presheaf.dom \<epsilon> = Presheaf.terminal T
                      \<and> OrderedSemigroup.poset S = gc \<Phi>;

        neutral_law = undefined;
        domain_law = undefined;
        comb_law = undefined
    in 
      welldefined"





end
