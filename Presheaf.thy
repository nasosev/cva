theory Presheaf
imports Main Poset Space Function
begin


record ('t, 'a) Presheaf =
  space :: "'t Space"
  ob :: "('t Open, 'a Poset) Function "
  ar :: "('t Inclusion, ('a, 'a) PosetMap) Function"

definition isValid :: "('t, 'a) Presheaf \<Rightarrow> bool" where
  "isValid f \<equiv> 
    let 
      welldefined = Space.isValid (space f) \<and> (\<forall>x. x \<in> opens (space f) \<longrightarrow> Poset.isValid ((ob f) $ x))
                    \<and> (\<forall>i. i \<in> inclusions (space f) \<longrightarrow> Poset.isValidMap ((ar f) $ i)
                       \<and>  Poset.dom ((ar f) $ i) = ((ob f) $ (Space.dom i)));
      identity = (\<forall>a. a \<in> opens (space f) \<longrightarrow> ((ar f) $ (Space.ident (space f) a)) = Poset.ident ((ob f) $ a));
      composition = (\<forall>j i. j \<in> inclusions (space f) \<longrightarrow> i \<in> inclusions (space f) \<longrightarrow>
        Space.dom j = Space.cod i \<longrightarrow>  ((ar f) $ (Space.compose j i )) = ((ar f) $ i) \<circ> ((ar f) $ j))     
    in
    (welldefined )" 




end