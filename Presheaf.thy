theory Presheaf
imports Main Poset Space Function
begin


record ('A, 'a) Presheaf =
  space :: "'A Space"
  ob :: "('A Open, 'a Poset) Function "
  ar :: "('A Inclusion, ('a, 'a) PosetMap) Function"

definition isValid :: "('A, 'a) Presheaf \<Rightarrow> bool" where
  "isValid \<Phi> \<equiv> 
    let 
      space = (space \<Phi>);
      \<Phi>0 = ob \<Phi>;
      \<Phi>1 = ar \<Phi>;
      welldefined = Space.isValid space \<and> (\<forall>x. x \<in> opens space \<longrightarrow> Poset.isValid (\<Phi>0 $ x))
                    \<and> (\<forall>i. i \<in> inclusions space \<longrightarrow> Poset.isValidMap (\<Phi>1 $ i)
                           \<and>  Poset.dom (\<Phi>1 $ i) = (\<Phi>0 $ (Space.dom i)));
      identity = (\<forall>a. a \<in> opens space \<longrightarrow> (\<Phi>1 $ (Space.ident space a)) = Poset.ident (\<Phi>0 $ a));
      composition = (\<forall>j i. j \<in> inclusions space \<longrightarrow> i \<in> inclusions space \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow>  (\<Phi>1 $ (Space.compose j i )) = (\<Phi>1 $ i) \<circ> (\<Phi>1 $ j))     
    in
    (welldefined )" 




end