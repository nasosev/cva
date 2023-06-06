theory GC
imports Main Presheaf Poset
begin

(* covariant Grothendieck construction *)

definition gc :: "('A, 'a) Presheaf \<Rightarrow> ('A set \<times> 'a) Poset" where
  "gc \<Phi> \<equiv> 
    let 
        \<Phi>0 = Presheaf.ob \<Phi>;
        \<Phi>1 = Presheaf.ar \<Phi>;
        space  = Presheaf.space \<Phi>;
        opens = Space.opens space;
        elements = { (A, a) .  A \<in> opens \<and> a \<in> Poset.elements (\<Phi>0 $ A) };
        le  =  \<lambda>(A,a) (B,b) .
            let 
              i = \<lparr> Space.Inclusion.space = space, dom = B, cod = A \<rparr>;
              a_B = (\<Phi>1 $ i) $$ a;
              le_B = Poset.le (\<Phi>0 $ B)     
            in  B \<subseteq> A \<and> le_B a_B b
    in
    \<lparr> Poset.elements = elements, Poset.le = le \<rparr>"


lemma isValidGcPoset:  "\<forall> \<Phi> . Presheaf.isValid \<Phi> \<longrightarrow> Poset.isValid (gc \<Phi>)"









end 


