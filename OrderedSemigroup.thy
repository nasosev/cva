theory OrderedSemigroup
  imports Main  Poset
begin
declare [[show_types]]

record 'a OrderedSemigroup =
  poset :: "'a Poset"
  mult :: "('a \<times> 'a,'a) PosetMap"


definition valid :: "'a OrderedSemigroup \<Rightarrow> bool" where
"valid S \<equiv> 
  let 
    welldefined = (Poset.valid (poset S)) 
                  \<and> (Poset.valid_map (mult S))
                  \<and> (dom (mult S)) = (poset S) \<times>\<times> (poset S)
                  \<and> cod (mult S) = (poset S);
    associative = undefined
  in 
    (welldefined \<and> associative)
"

end