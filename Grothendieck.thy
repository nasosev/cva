section \<open> Grothendieck.thy \<close>


text \<open>
   Theory      :  Grothendieck.thy

   This theory formalizes the covariant Grothendieck construction, which is a fundamental
   construction in category theory. The main goal of this theory is to define and prove
   properties of the Grothendieck construction for a given presheaf.

   The covariant Grothendieck construction takes a presheaf @{term \<Phi>} and constructs a poset P,
   where the elements of P are pairs (A, a), where A is an open set in the space of @{term \<Phi>} and
   a is an element in the presheaf value at A. The ordering relation in P is determined by
   the inclusion relations between open sets and the ordering relation in the presheaf.
--------------------------------------------------------------------------------
\<close>

theory Grothendieck
imports Main Prealgebra Poset
begin

text \<open>
   The function d takes a pair (A, a) and returns the first component A.
   It extracts the open set from the pair.
\<close>
abbreviation d :: "('A set \<times> 'a)  \<Rightarrow> 'A set" where
"d Aa \<equiv> fst Aa"

text \<open>
   The function e takes a pair (A, a) and returns the second component a.
   It extracts the element from the pair.
\<close>
abbreviation e :: "('A set \<times> 'a)  \<Rightarrow> 'a" where
"e Aa \<equiv> snd Aa"

text \<open>
   The function gc takes a presheaf @{term \<Phi>} and constructs a poset P, which represents
   the covariant Grothendieck construction for @{term \<Phi>}. The elements of P are pairs (A, a),
   where A is an open set in the space of @{term \<Phi>} and a is an element in the presheaf value at A.
   The construction involves defining a set el of pairs (A, a), where \<cdot>\<cdot>A \in opens\<cdot>\<cdot> and
   \<cdot>\<cdot>a \in Poset.el \Phi 0 \\<cdot>\<cdot> A)\<cdot>\<cdot>, and a relation le\_rel that defines the ordering relation
   between elements in P based on the inclusion relations between open sets and the
   ordering relation in the presheaf.
\<close>
definition gc :: "('A, 'a) Prealgebra \<Rightarrow> ('A set \<times> 'a) Poset" where
  "gc \<Phi> \<equiv>
    let
        \<Phi>0 = Prealgebra.ob \<Phi>;
        \<Phi>1 = Prealgebra.ar \<Phi>;
        T = Prealgebra.space \<Phi>;
        opens = Space.opens T;
        el = { (A, a) .  A \<in> opens \<and> a \<in> Poset.el (\<Phi>0 \<cdot>\<cdot> A) };
        inc = Space.make_inclusion T;
        le_rel  = { ((A, a), (B, b)) . A \<in> opens \<and> B \<in> opens \<and> a \<in> Poset.el ((\<Phi>0 \<cdot>\<cdot> A)) \<and> b \<in> Poset.el ((\<Phi>0 \<cdot>\<cdot> B))
                     \<and> B \<subseteq> A \<and> Poset.le (\<Phi>0 \<cdot>\<cdot> B) ((\<Phi>1 \<cdot>\<cdot> (inc B A)) \<cdot> a) b }
    in
    \<lparr> Poset.el = el, Poset.le_rel = le_rel \<rparr>"

text \<open> LEMMAS \<close>

text \<open>
   The lemma local\_dom states that if @{term \<Phi>} is a valid presheaf, P = gc @{term \<Phi>}, and Aa is an element in Poset.el P,
   then A = d Aa is an open set in the space of @{term \<Phi>}.
\<close>
lemma local_dom : "Prealgebra.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> A = d Aa
\<Longrightarrow> T = Prealgebra.space \<Phi>  \<Longrightarrow>  A \<in> opens T"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD gc_def)

text \<open>
   The lemma gc\_elem\_local states that if @{term \<Phi>} is a valid presheaf, P = gc @{term \<Phi>}, and Aa is an element in Poset.el P,
   then A = d Aa and \<cdot>\<cdot>P\_A = Prealgebra.ob \Phi \\<cdot>\<cdot> A\<cdot>\<cdot>, then \<cdot>\<cdot>a = snd Aa \in Poset.el P\_A\<cdot>\<cdot>.
\<close>
lemma gc_elem_local : "Prealgebra.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> A = d Aa
\<Longrightarrow> P_A = Prealgebra.ob \<Phi> \<cdot>\<cdot> A \<Longrightarrow> a = snd Aa \<Longrightarrow> a \<in> Poset.el P_A"
  by (metis (no_types, lifting) Poset.Poset.select_convs(1) Product_Type.Collect_case_prodD gc_def)

text \<open>
   The lemma local\_elem\_gc states that if @{term \<Phi>} is a valid presheaf, P = gc @{term \<Phi>}, A is an open set in the space of @{term \<Phi>},
   and \<cdot>\<cdot>P\_A = Prealgebra.ob \Phi \\<cdot>\<cdot> A\<cdot>\<cdot>, and a is an element in Poset.el P\_A, then \<cdot>\<cdot>(A, a) \in Poset.el P\<cdot>\<cdot>.
\<close>
lemma local_elem_gc : "Prealgebra.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> A \<in> opens (Prealgebra.space \<Phi>)
\<Longrightarrow> P_A = Prealgebra.ob \<Phi> \<cdot>\<cdot> A \<Longrightarrow> a \<in> Poset.el P_A \<Longrightarrow> (A,a) \<in> Poset.el P"
  unfolding gc_def
  by (simp add: Let_def)

text \<open>
   The lemma d\_antitone states that if @{term \<Phi>} is a valid presheaf, P = gc @{term \<Phi>},
   and Aa and Bb are elements in Poset.el P, and Poset.le P Aa Bb, then \<cdot>\<cdot>d Bb \subseteq d Aa\<cdot>\<cdot>.
\<close>
lemma d_antitone : "Prealgebra.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> Bb \<in> Poset.el P \<Longrightarrow>
Poset.le P Aa Bb \<Longrightarrow> d Bb \<subseteq> d Aa"
  unfolding gc_def
  by (smt (verit) Poset.Poset.select_convs(2) case_prod_conv case_prod_unfold mem_Collect_eq)

text \<open>
   The lemma local\_le states that if @{term \<Phi>} is a valid presheaf, P = gc @{term \<Phi>}, Aa and Aa' are elements in Poset.el P,
   and d Aa = d Aa', and Poset.le P Aa Aa', then A = d Aa, \<cdot>\<cdot>P\_A = Prealgebra.ob @{term \<Phi>} \\<cdot>\<cdot> A\<cdot>\<cdot>, a = snd Aa,
   a' = snd Aa', then Poset.le P\_A a a'.
\<close>
lemma local_le : "Prealgebra.valid \<Phi> \<Longrightarrow> P = gc \<Phi> \<Longrightarrow> Aa \<in> Poset.el P \<Longrightarrow> Aa' \<in> Poset.el P \<Longrightarrow>
d Aa = d Aa' \<Longrightarrow> Poset.le P Aa Aa' \<Longrightarrow> A = d Aa \<Longrightarrow> P_A = Prealgebra.ob \<Phi> \<cdot>\<cdot> A \<Longrightarrow> a = e Aa \<Longrightarrow> a' = e Aa' \<Longrightarrow>
 Poset.le P_A a a' "
  unfolding gc_def
  by (smt (verit) Poset.Poset.select_convs(2) Poset.ident_app Prealgebra.valid_welldefined Product_Type.Collect_case_prodD case_prod_conv make_inclusion_ident prod.collapse valid_identity)

text \<open>
   The lemma valid\_gc\_1 states that if @{term \<Phi>} is a valid presheaf and A is an open set in the space of @{term \<Phi>},
   then (ar @{term \<Phi>} \<cdot>\<cdot> (Space.ident (space @{term \<Phi>}) A)) = (Poset.ident (ob @{term \<Phi>} \<cdot>\<cdot> A)).
\<close>
lemma valid_gc_1 :
  fixes \<Phi> :: "('A,'a) Prealgebra" and A :: "'A Open"
  assumes "valid \<Phi>" and "A \<in> opens (space \<Phi>)"
  shows "(ar \<Phi> \<cdot>\<cdot> (Space.ident (space \<Phi>) A)) = (Poset.ident (ob \<Phi> \<cdot>\<cdot> A))"
  by (simp add: assms(1) assms(2) valid_identity)

text \<open>
   The lemma valid\_gc\_transitive states that if @{term \<Phi>} is a valid presheaf and A, B, C are open sets in the space of @{term \<Phi>},
   and a, b, c are elements in the presheaf values at A, B, C respectively, then if \<cdot>\<cdot>C \subseteq B\<cdot>\<cdot>, \<cdot>\<cdot>B \subseteq  A\<cdot>\<cdot>,
   \<cdot>\<cdot>A \in Space.opens T\<cdot>\<cdot>, \<cdot>\<cdot>B \in Space.opens T\<cdot>\<cdot>, \<cdot>\<cdot>C \in Space.opens T\<cdot>\<cdot>, \<cdot>\<cdot>a \in el \Phi\_A, b \in el \Phi\_B\<cdot>\<cdot>, \<cdot>\<cdot>c \in el \Phi\_C\<cdot>\<cdot>,
   \<cdot>\<cdot>le \Phi\_B (prj\_AB \\<cdot>\<cdot>\\<cdot>\<cdot> a) b\<cdot>\<cdot>, and \<cdot>\<cdot>le \Phi\_C (prj\_BC \\<cdot>\<cdot>\\<cdot>\<cdot> b) c\<cdot>\<cdot>, then \<cdot>\<cdot>le \Phi\_C (prj\_AC \\<cdot>\<cdot>\\<cdot>\<cdot> a) c\<cdot>\<cdot>.
\<close>
lemma valid_gc_transitive :
  fixes \<Phi> :: "('A,'a) Prealgebra" and A B C :: "'A Open" and a b c :: "'a"
  defines "\<Phi>0 \<equiv> (ob \<Phi>)"
  defines "\<Phi>1 \<equiv> (ar \<Phi>)"
  defines "T \<equiv> Prealgebra.space \<Phi>"
  defines "\<Phi>_A \<equiv> \<Phi>0 \<cdot>\<cdot> A"
  defines "\<Phi>_B \<equiv> \<Phi>0 \<cdot>\<cdot> B"
  defines "\<Phi>_C \<equiv> \<Phi>0 \<cdot>\<cdot> C"
  defines "i_BA \<equiv> \<lparr>Inclusion.space = T, dom = B, cod = A\<rparr>"
  defines "i_CB \<equiv> \<lparr>Inclusion.space = T, dom = C, cod = B\<rparr>"
  defines "i_CA \<equiv> \<lparr>Inclusion.space = T, dom = C, cod = A\<rparr>"
  defines "prj_AB \<equiv> (\<Phi>1 \<cdot>\<cdot> i_BA)"
  defines "prj_BC \<equiv> (\<Phi>1 \<cdot>\<cdot> i_CB)"
  defines "prj_AC \<equiv> (\<Phi>1 \<cdot>\<cdot> i_CA)"
  assumes "valid \<Phi>" and "C \<subseteq> B" and "B \<subseteq> A"
  and "A \<in> Space.opens T" and "B \<in> Space.opens T" and "C \<in> Space.opens T"
  and "a \<in> el \<Phi>_A" and "b \<in> el \<Phi>_B" and "c \<in> el \<Phi>_C"
  and "le \<Phi>_B (prj_AB \<cdot> a) b"
  and "le \<Phi>_C (prj_BC \<cdot> b) c"
shows "le \<Phi>_C (prj_AC \<cdot> a) c"
proof -
  have "valid \<Phi> "
    by (simp add: assms(13))
 moreover have "le \<Phi>_B (prj_AB \<cdot> a) b"
   by (simp add: assms(22))
   moreover have "a \<in> el \<Phi>_A"
     by (simp add: assms(19))
  moreover have "b \<in> el \<Phi>_B"
    using assms(20) by blast
  moreover have "Space.valid T"
    using T_def calculation(1) valid_space by blast 
  moreover have "Space.valid_inclusion i_BA"
    by (simp add: assms(15) assms(16) assms(17) calculation(5) i_BA_def valid_inclusion_def)
  moreover have "Poset.valid_map prj_AB"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Prealgebra.valid_welldefined T_def \<Phi>1_def calculation(1) calculation(6) i_BA_def inclusions_def mem_Collect_eq prj_AB_def) 
  moreover have "Poset.cod prj_AB = \<Phi>_B"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) T_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def calculation(1) calculation(6) cod_proj i_BA_def inclusions_def mem_Collect_eq prj_AB_def)
    moreover have "(prj_AB \<cdot> a) \<in> el \<Phi>_B"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.simps(3) T_def \<Phi>0_def \<Phi>1_def \<Phi>_A_def \<Phi>_B_def calculation(1) calculation(3) calculation(6) i_BA_def image inclusions_def mem_Collect_eq prj_AB_def)
  moreover have "Space.valid_inclusion i_CB"
    by (simp add: assms(14) assms(17) assms(18) calculation(5) i_CB_def valid_inclusion_def)
moreover have "Poset.valid_map prj_BC"
  by (metis (mono_tags, lifting) Inclusion.select_convs(1) Prealgebra.valid_welldefined T_def \<Phi>1_def calculation(1) calculation(10) i_CB_def inclusions_def mem_Collect_eq prj_BC_def) 
  moreover have "le \<Phi>_C (prj_BC \<cdot> (prj_AB \<cdot>  a)) (prj_BC \<cdot>  b)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) T_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def \<Phi>_C_def calculation(1) calculation(10) calculation(11) calculation(2) calculation(4) calculation(9) cod_proj dom_proj i_CB_def inclusions_def mem_Collect_eq prj_BC_def valid_map_monotone)
   moreover have "le \<Phi>_C (prj_BC \<cdot> b) c"
     by (simp add: assms(23))
   moreover have "le \<Phi>_C (prj_BC \<cdot> (prj_AB \<cdot> a)) c"
     by (smt (verit, best) Inclusion.simps(1) Inclusion.simps(2) Inclusion.simps(3) T_def \<Phi>0_def \<Phi>1_def \<Phi>_B_def \<Phi>_C_def assms(18) assms(21) calculation(1) calculation(10) calculation(12) calculation(13) calculation(4) calculation(9) i_CB_def image inclusions_def mem_Collect_eq prj_BC_def valid_ob valid_transitivity) 
    ultimately show ?thesis
      by (smt (z3) Inclusion.select_convs(1) Inclusion.select_convs(2) Inclusion.select_convs(3) Prealgebra.valid_welldefined Space.compose_def T_def \<Phi>0_def \<Phi>1_def \<Phi>_A_def compose_app i_BA_def i_CA_def i_CB_def inclusions_def mem_Collect_eq prj_AB_def prj_AC_def prj_BC_def valid_composition) 
  qed

text \<open> THEOREM \<close>

text \<open>
   The theorem valid\_gc states that if @{term \<Phi>} is a valid presheaf, then (gc @{term \<Phi>}) is a valid poset.
\<close>

proposition valid_gc:  
  fixes \<Phi> :: "('A, 'a) Prealgebra"
  assumes valid_\<Phi> : "valid \<Phi>"
  shows "Poset.valid (gc \<Phi>)"
proof (intro Poset.validI)
  fix x y
  assume a1: "(x, y) \<in> le_rel (gc \<Phi>)" 

   show "x \<in> el (gc \<Phi>) \<and> y \<in> el (gc \<Phi>)" using assms a1 gc_def [where ?\<Phi>=\<Phi>]
     by (smt (verit, best) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) case_prod_unfold fst_conv mem_Collect_eq snd_conv) 
next 
  fix x
  assume "x \<in> el (gc \<Phi>)"
  define "T" where "T = Prealgebra.space \<Phi>" 
  define "i" where "i = Space.ident T (d x)"
  have "e x = ((Prealgebra.ar \<Phi>) \<cdot>\<cdot> i) \<cdot> (e x)"
    by (metis Poset.ident_app T_def \<open>x \<in> el (gc \<Phi>)\<close> gc_elem_local i_def local_dom valid_\<Phi> valid_identity valid_ob) 
  moreover have "d x \<in> opens (Prealgebra.space \<Phi>)"
    using \<open>x \<in> el (gc \<Phi>)\<close> local_dom valid_\<Phi> by blast 

  moreover have "e x \<in> Poset.el ((Prealgebra.ob \<Phi>) \<cdot>\<cdot> (d x))"
    by (meson \<open>x \<in> el (gc \<Phi>)\<close> gc_elem_local valid_\<Phi>) 
  moreover have "Poset.le ((Prealgebra.ob \<Phi>) \<cdot>\<cdot> (d x)) (((Prealgebra.ar \<Phi>) \<cdot>\<cdot> i) \<cdot> (e x)) (e x)"
    by (metis calculation(1) calculation(2) calculation(3) valid_\<Phi> valid_ob valid_reflexivity) 

  moreover have "(x,x) \<in> le_rel (gc \<Phi>)"  using  calculation i_def T_def gc_def [where ?\<Phi> = \<Phi>]
    by (smt (verit, best) Poset.Poset.select_convs(2) case_prodI case_prod_unfold dual_order.refl make_inclusion_ident mem_Collect_eq valid_\<Phi> valid_space) 
    
  show "le (gc \<Phi>) x x"
    by (simp add: \<open>(x, x) \<in> le_rel (gc \<Phi>)\<close> \<open>x \<in> el (gc \<Phi>)\<close>)
next
  fix x y
  assume a1: "x \<in> el (gc \<Phi>)"
  assume a2: "y \<in> el (gc \<Phi>)"
  assume a3: "le (gc \<Phi>) x y"
  assume a4: "le (gc \<Phi>) y x "
  show "x = y" using gc_def  [where ?\<Phi> = \<Phi>] assms  a1 a2 a3 a4
    by (smt (z3) Poset.Poset.select_convs(2) Poset.ident_app Product_Type.Collect_case_prodD case_prodD case_prodE' fst_conv make_inclusion_ident snd_conv subset_antisym valid_antisymmetry valid_identity valid_ob valid_space)
next
  fix x y z
  assume a1: "x \<in> el (gc \<Phi>)"
  assume a2: "y \<in> el (gc \<Phi>)"
  assume a3: "z \<in> el (gc \<Phi>)"
  assume a4: "le (gc \<Phi>) x y"
  assume a5: "le (gc \<Phi>) y z "
  show "le (gc \<Phi>) x z" using gc_def [where ?\<Phi> = \<Phi>] assms a1 a2 a3 a4 a5 
valid_gc_transitive [where ?\<Phi> = \<Phi> and ?a="e x" and ?b="e y" and ?c="e z" and ?A="d x" and ?B="d y"
  and ?C="d z"]
    by (smt (verit, del_insts) Poset.Poset.select_convs(2) case_prod_conv make_inclusion_def mem_Collect_eq prod.collapse subset_trans) 
qed

text \<open>
   The lemma valid\_gc\_le\_wrap states that if @{term \<Phi>} is a valid presheaf, Aa and Bb are pairs of the form (A, a),
   where A is an open set in the space of @{term \<Phi>} and a is an element in the presheaf value at A, and
   i is the inclusion map from B to A, pr is the map from @{term \<Phi>}1 i to @{term \<Phi>}0 B, @{term \<Phi>}A is the presheaf value at A,
   and @{term \<Phi>}B is the presheaf value at B, and \<cdot>\<cdot>d Bb \subseteq d Aa\<cdot>\<cdot>, and \<cdot>\<cdot>le \Phi B (pr \\<cdot>\<cdot>\\<cdot>\<cdot> (e Aa)) (e Bb)\<cdot>\<cdot>,
   then Aa is less than or equal to Bb in the poset gc @{term \<Phi>}.
\<close>
lemma valid_gc_le_wrap :
  fixes \<Phi> :: "('A, 'a) Prealgebra" and Aa Bb :: "('A set \<times> 'a)"

  defines "i \<equiv> Space.make_inclusion (Prealgebra.space \<Phi>) (d Bb) (d Aa)"
  defines "pr \<equiv>  (Prealgebra.ar \<Phi>) \<cdot>\<cdot> i"
  defines "\<Phi>A \<equiv>  (Prealgebra.ob \<Phi>) \<cdot>\<cdot> (d Aa)"
  defines "\<Phi>B \<equiv>  (Prealgebra.ob \<Phi>) \<cdot>\<cdot> (d Bb)"

  assumes  "Prealgebra.valid \<Phi>"
  assumes "d Aa \<in> Space.opens (Prealgebra.space \<Phi>)"
  assumes "d Bb \<in> Space.opens (Prealgebra.space \<Phi>)"
  assumes "e Aa \<in> Poset.el \<Phi>A"
  assumes "e Bb \<in> Poset.el \<Phi>B"
  assumes "d Bb \<subseteq> d Aa"

  assumes "Poset.le \<Phi>B (pr \<cdot> (e Aa)) (e Bb) "
  shows "le (gc \<Phi>) Aa (Bb)"
  unfolding gc_def
  by (smt (verit) Poset.Poset.select_convs(1) Poset.Poset.select_convs(2) \<Phi>A_def \<Phi>B_def assms(10) assms(11) assms(6) assms(7) assms(8) assms(9) case_prod_conv i_def mem_Collect_eq pr_def prod.collapse)

  
text \<open>
   The lemma valid\_gc\_le\_unwrap states that if @{term \<Phi>} is a valid presheaf, Aa and Bb are pairs of the form (A, a),
   where A is an open set in the space of @{term \<Phi>} and a is an element in the presheaf value at A, and
   i is the inclusion map from B to A, pr is the map from @{term \<Phi>}1 i to @{term \<Phi>}0 B, @{term \<Phi>}A is the presheaf value at A,
   and @{term \<Phi>}B is the presheaf value at B, and gc@{term \<Phi>} is the poset gc @{term \<Phi>},
   and Aa is less than or equal to Bb in gc@{term \<Phi>}, then @{term \<Phi>}B is less than or equal to \<cdot>\<cdot>(pr \\<cdot>\<cdot>\\<cdot>\<cdot> (e Aa)) \in \Phi B\<cdot>\<cdot>,
   d Bb is a subset of d Aa, e Bb is an element in @{term \<Phi>}B, and e Aa is an element in @{term \<Phi>}A.
\<close>
lemma valid_gc_le_unwrap :
  fixes \<Phi> :: "('A, 'a) Prealgebra" and Aa Bb :: "('A set \<times> 'a)"

  defines "i \<equiv> Space.make_inclusion (Prealgebra.space \<Phi>) (d Bb) (d Aa)"
  defines "pr \<equiv>  (Prealgebra.ar \<Phi>) \<cdot>\<cdot> i"
  defines "\<Phi>A \<equiv>  (Prealgebra.ob \<Phi>) \<cdot>\<cdot> (d Aa)"
  defines "\<Phi>B \<equiv>  (Prealgebra.ob \<Phi>) \<cdot>\<cdot> (d Bb)"
  defines "gc\<Phi> \<equiv> gc \<Phi>"

assumes  valid: "Prealgebra.valid \<Phi>"
and "Aa \<in> Poset.el gc\<Phi> " and "Bb \<in> Poset.el (gc \<Phi>)"
and le_gc: "le gc\<Phi> Aa Bb"

shows "Poset.le \<Phi>B (pr \<cdot> (e Aa)) (e Bb) \<and> d Bb \<subseteq> d Aa \<and> e Bb \<in> Poset.el \<Phi>B \<and> e Aa \<in> Poset.el \<Phi>A"
proof -
  have a1: "le gc\<Phi> Aa Bb"
    by (simp add: le_gc)
  moreover have "d Bb \<subseteq> d Aa"
    using assms(7) assms(8) d_antitone gc\<Phi>_def le_gc valid by blast
  moreover have "e Bb \<in> Poset.el \<Phi>B \<and> e Aa \<in> Poset.el \<Phi>A"
    by (metis \<Phi>A_def \<Phi>B_def assms(7) assms(8) gc\<Phi>_def gc_elem_local valid)
  moreover have "Space.valid_inclusion i"
    by (metis assms(7) assms(8) calculation(2) gc\<Phi>_def i_def local_dom valid valid_make_inclusion valid_space) 
  moreover have "Prealgebra.valid \<Phi>"
    by (simp add: valid)
  moreover have "i \<in> Space.inclusions (space \<Phi>)"
    by (metis (mono_tags, lifting) Inclusion.select_convs(1) calculation(4) i_def inclusions_def make_inclusion_def mem_Collect_eq)
  moreover have "Poset.valid_map pr"
    using calculation(6) pr_def valid valid_ar by auto  
  define "a_B" where "a_B = (pr \<cdot> (e Aa))"
  moreover have "Poset.dom pr = \<Phi>A \<and> Poset.cod pr = \<Phi>B"
    by (metis Inclusion.simps(2) Inclusion.simps(3) \<Phi>A_def \<Phi>B_def calculation(6) cod_proj dom_proj i_def make_inclusion_def pr_def valid)
  moreover have "a_B \<in> Poset.el \<Phi>B"
    using Poset.fun_app2 \<open>Poset.valid_map pr\<close> a_B_def calculation(3) calculation(8) by fastforce
  moreover have " Poset.valid gc\<Phi>"
    by (simp add: gc\<Phi>_def valid valid_gc)
  moreover have "Poset.valid \<Phi>B"
    using Poset.valid_cod \<open>Poset.valid_map pr\<close> calculation(8) by blast 
  moreover have "Poset.le \<Phi>B a_B (e Bb)" using gc_def a1
    apply (simp_all add: Let_def)
    unfolding gc\<Phi>_def gc_def
    apply auto
      apply (simp_all add: Let_def)
    apply (smt (verit) Poset.Poset.select_convs(2) Product_Type.Collect_case_prodD \<Phi>A_def \<Phi>B_def a_B_def assms(7) assms(8) calculation(3) case_prod_conv case_prod_unfold gc\<Phi>_def i_def local_dom pr_def valid)
    using calculation(9) apply force
    using calculation(3) by blast
  ultimately show ?thesis                                                                      
    by blast
qed

end
