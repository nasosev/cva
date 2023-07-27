theory Poset_Types
imports Main "HOL-Eisbach.Eisbach"

begin


locale carrier =
  fixes carrier :: "'a set"
begin

definition "member_of x \<equiv> x \<in> carrier"

end

locale poset = carrier +
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes p_refl: "x \<in> carrier \<Longrightarrow> le x x" and
          p_trans: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> z \<in> carrier \<Longrightarrow> le x y \<Longrightarrow> le y z \<Longrightarrow> le x z" and
          p_antisym: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> le x y \<Longrightarrow> le y x \<Longrightarrow> x = y"


typedef (overloaded) ('a) poset = " {(x, y). poset x y} :: ('a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> bool)) set  "
  apply (rule_tac x="({}, undefined)" in exI)
  apply (clarsimp)
  by (standard; clarsimp)

setup_lifting type_definition_poset


lift_definition leq :: "'a poset \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" is
    "\<lambda>P :: ('a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> bool)) . snd P" done

notation leq ("_ \<Ztypecolon> _ \<sqsubseteq> _" 50)

lift_definition el :: "'a poset \<Rightarrow> ('a set)" is
    "\<lambda>P :: ('a set \<times> ('a \<Rightarrow> 'a \<Rightarrow> bool)) . fst P" done

interpretation poset "(el x)" "(leq x)"
  apply (standard; transfer, clarsimp elim:  poset.p_refl  poset.p_trans  poset.p_antisym)
    apply (transfer)
    apply (simp add: poset.p_refl)
   apply (metis  poset.p_trans)
  by (metis  poset.p_antisym)

definition to_poset :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a poset"
  where "to_poset A f = Abs_poset (A, f)"

definition (in poset) witness :: "'a poset" where 
  "witness \<equiv> (to_poset carrier le)"

interpretation empty: poset "{}" "f"
  apply (standard; clarsimp)
  done

interpretation nat_pos: poset "UNIV :: nat set" "(\<le>)"
  apply (standard; clarsimp)
  done

interpretation discrete: poset "UNIV :: 'a set" "(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"
  apply (standard)
    apply (clarsimp)
   apply (clarsimp)
  apply (erule sym)
  done

context poset begin


lemma leq_valid[simp]: "leq witness = le "
  unfolding witness_def
  using poset_axioms 
  by (simp add: Abs_poset_inverse leq.rep_eq to_poset_def)

lemma el_valid[simp]: "el witness = carrier "
  unfolding witness_def
  using poset_axioms 
  by (simp add: Abs_poset_inverse el.rep_eq to_poset_def)

sublocale op_poset: poset carrier "\<lambda>y x. le x y"
  apply (standard)
    apply (simp add: local.p_refl)
   apply (erule (4) local.p_trans)
  apply (erule (3) local.p_antisym)
  done

end

lemma discrete_leq_iff: "(discrete.witness \<Ztypecolon> x \<sqsubseteq> x) \<longleftrightarrow> x = x"
  apply (safe, rule p_refl, clarsimp)
  done

lemma "nat_pos.witness \<Ztypecolon> x \<sqsubseteq> x"
  by (clarsimp)

locale morphism = fr: carrier S + to: carrier S'  for S :: "'a set" and S' :: "'b set" +
  fixes f :: "'a \<Rightarrow> 'b" 
  assumes well_formed: "f ` S \<subseteq> S'"

begin

lemma maps_betw: "x \<in> S \<Longrightarrow> f x \<in> S'"
  using well_formed  by blast

definition "morphism_witness g P P' \<equiv> g = f \<and> P = S \<and> P' = S'"

end

locale poset_morphism = morphism "el P" "el P'" f for P P' f +
  assumes mono_ord: "x \<in> el P \<Longrightarrow> y \<in> el P \<Longrightarrow> leq P x y \<Longrightarrow> leq P' (f x) (f y)"

begin

sublocale is_morphism: morphism "(el P)" \<open>el P'\<close> f
  using morphism_axioms by blast

end


typedef (overloaded) ('a, 'b) poset_morphism = " {(p, f, p'). poset_morphism p p' f} :: ('a poset \<times> ('a \<Rightarrow> 'b) \<times> 'b poset) set"
  apply (clarsimp)
  apply (rule_tac x="discrete.witness" in exI)
  apply (rule_tac x="\<lambda>_. undefined" in exI)
  apply (rule_tac x="discrete.witness" in exI)
  apply (standard)
   apply (clarsimp)
  apply (clarsimp)
  done

setup_lifting type_definition_poset_morphism


lift_definition left :: "('a, 'b) poset_morphism \<Rightarrow> 'a poset" is
    "\<lambda>f :: ('a poset \<times> ('a \<Rightarrow> 'b) \<times> 'b poset) . fst f" done


lift_definition right :: "('a, 'b) poset_morphism \<Rightarrow> 'b poset" is
    "\<lambda>f :: ('a poset \<times> ('a \<Rightarrow> 'b) \<times> 'b poset) . snd (snd f)" done


lift_definition func :: "('a, 'b) poset_morphism \<Rightarrow> 'a \<Rightarrow> 'b" is
    "\<lambda>f :: ('a poset \<times> ('a \<Rightarrow> 'b) \<times> 'b poset) . fst (snd f)" done

interpretation poset_morphism "(left x)" "(right x)" "func x" 
  apply (standard; transfer; clarsimp)
   apply (meson morphism.maps_betw poset_morphism.axioms(1))
  by (simp add:  poset_morphism.mono_ord)

interpretation id_morphism: poset_morphism P P id
  by (standard; clarsimp)


lift_definition lift_poset_morphism :: "'a poset \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b poset \<Rightarrow> ('a, 'b) poset_morphism" 
           is "\<lambda>a f b. if poset_morphism a b f then (a, f, b) else Rep_poset_morphism (undefined)"
  apply (clarsimp)
  by (metis fst_conv func.rep_eq left.rep_eq poset_morphism_axioms right.rep_eq snd_conv)

definition "compose_poset f g = lift_poset_morphism (left f) (func g o func f) (right g)"


notation compose_poset (infixl "\<cdot>"  55)

definition "compatible f g \<equiv> right f = left g"

definition "mono_betw m P f P' \<equiv> left m = P \<and> right m = P' \<and> func m = f"

notation mono_betw ("_ \<Ztypecolon> _ \<longrightarrow>\<^sub>_ _")

lemma mono_betw_left[dest]: "mono_betw m P f P'  \<Longrightarrow> left m = P"
                                        unfolding mono_betw_def by simp

lemma mono_betw_right[dest]: "mono_betw m P f P' \<Longrightarrow> right m = P'"
                                        unfolding mono_betw_def by simp

lemma mono_betw_func[dest]: "mono_betw m P f P'  \<Longrightarrow> func m = f" 
                                        unfolding mono_betw_def by simp


lemma poset_morphism_compose: "poset_morphism a b f \<Longrightarrow> poset_morphism b c g 
                                                    \<Longrightarrow> poset_morphism a c (g \<circ> f)"
  apply (standard; clarsimp)
   apply (meson morphism.maps_betw poset_morphism.axioms(1))
  by (meson morphism.maps_betw poset_morphism.axioms(1)
             poset_morphism.axioms(2) poset_morphism_axioms_def)
  

lemma left_comp_iff[dest]: "compatible m m' \<Longrightarrow> mono_betw (m \<cdot> m') P f P' \<Longrightarrow> left m = P"
  apply (clarsimp simp:  mono_betw_def)
  apply (clarsimp simp: compatible_def compose_poset_def, transfer)
  by (clarsimp simp:poset_morphism_compose )

lemma right_comp_iff[dest]: "compatible m m' \<Longrightarrow> mono_betw (m \<cdot> m') P f P' \<Longrightarrow> right m' = P'"
  apply (clarsimp simp:  mono_betw_def)
  by (clarsimp simp: compatible_def compose_poset_def, transfer, 
      clarsimp simp: poset_morphism_compose)

lemma func_comp_iff[dest]: "compatible m m' \<Longrightarrow> mono_betw (m \<cdot> m') P f P' \<Longrightarrow> f = func m' o func m"
  apply (clarsimp simp:  mono_betw_def)
  by (clarsimp simp: compatible_def compose_poset_def, transfer, 
      clarsimp simp: poset_morphism_compose)


lemma "morphism_witness m f P P' \<Longrightarrow> x \<in> P \<Longrightarrow> f x \<in>  P'"
  apply (clarsimp simp: morphism_witness_def)
  by (simp add: maps_betw morphism_witness_def)

locale two_posets = A: poset S le + B: poset S' le' for S S' le le'
begin

sublocale product_poset: poset "S \<times> S'" "(\<lambda>x y. le (fst x) (fst y) \<and> le' (snd x) (snd y))"
  apply (standard)
    apply (simp add: A.p_refl B.p_refl mem_Times_iff)
   apply (metis A.p_trans B.p_trans mem_Times_iff)
  using A.op_poset.p_antisym B.op_poset.p_antisym by force
  
end


interpretation two_posets "el P" "el P'" "leq P" "leq P'"
  by (standard)

notation product_poset.witness (infixl \<open>\<times>\<^sub>P\<close> 50)

term "nat_pos.witness \<times>\<^sub>P discrete.witness"



end