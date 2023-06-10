theory OrderedSemigroup
  imports Main  Poset
begin

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

    mul = \<lambda> a b . (mult S) $$ (a,b);
    associative = \<forall> a b c . mul (mul a b) c = mul a (mul b c)
  in 
    (welldefined \<and> associative)"

end