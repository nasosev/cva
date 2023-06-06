theory GC
imports Main Presheaf Poset
begin

(* covariant Grothendieck construction *)

definition gc :: "('t, 'a) Presheaf \<Rightarrow> ('t set \<times> 'a) Poset" where
  "gc \<Phi> \<equiv> 
    let 
        ob = Presheaf.ob \<Phi>;
        ar = Presheaf.ar \<Phi>;
        space  = Presheaf.space \<Phi>;
        opens = Space.opens space;
        elements = { (A, a) .  A \<in> opens \<and> a \<in> Poset.elements (ob $ A) };
        le  =  \<lambda>(A,a) (B,b) .
            let 
              i = \<lparr> Space.Inclusion.space = space, dom = B, cod = A \<rparr>;
              a_B = (ar $ i) $$ a;
              leB = Poset.le (ob $ B)     
            in  B \<subseteq> A \<and> leB a_B b
    in
    \<lparr> Poset.elements = elements, Poset.le = le \<rparr>"

lemma isValidGcPoset:  "\<forall> \<Phi> . Presheaf.isValid \<Phi> \<longrightarrow> Poset.isValid (gc \<Phi>)"
  by simp
  






end 


