section \<open> Conditional.thy \<close>

(* This file must be in the same directory as http://github.com/nasosev/cva *)

theory Conditional
  imports Main OVA
begin

record ('A, 'a) Conditional =
  ova :: "('A, 'a) OVA"
  src :: "'A Open"
  el :: "('A, 'a) Valuation"

definition valid :: "('A, 'a) Conditional \<Rightarrow> bool" where
  "valid f \<equiv> OVA.valid (ova f) 
     \<and> src f \<in> opens (space (ova f))
     \<and> el f \<in> elems (ova f)
     \<and> src f \<subseteq> d (el f)
     \<and> OVA.is_commutative (ova f) 
     \<and> OVA.is_strongly_neutral (ova f)
     \<and> space (ova f) = Space.discrete" (* todo: is commutativity here needed ? *)

abbreviation valid2 :: "('A, 'a) Conditional \<Rightarrow> ('A, 'a) Conditional \<Rightarrow> bool" where
  "valid2 g f \<equiv> valid g \<and> valid f \<and> ova g = ova f"

abbreviation valid3 :: "('A, 'a) Conditional \<Rightarrow> ('A, 'a) Conditional \<Rightarrow> ('A, 'a) Conditional \<Rightarrow> bool" where
  "valid3 h g f \<equiv> valid h \<and> valid g \<and> valid f \<and> ova h = ova g \<and> ova g = ova f"

definition dom :: "('A, 'a) Conditional \<Rightarrow> 'A Open" where
"dom f \<equiv> d (el f)"

abbreviation tgt :: "('A, 'a) Conditional \<Rightarrow> 'A Open" where
"tgt f \<equiv> dom f - src f"

lemma valid_ova :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "OVA.valid (ova f)"
  using Conditional.valid_def f_valid by blast 

lemma valid_src :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "src f \<in> opens (space (ova f))"
  using Conditional.valid_def f_valid by blast 

lemma valid_el :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "el f \<in> elems (ova f)"
  using Conditional.valid_def f_valid by blast 

lemma valid_domain :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "src f \<subseteq> d (el f)"
  by (meson Conditional.valid_def f_valid) 

lemma valid_comm :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "OVA.is_commutative (ova f)"
  by (meson Conditional.valid_def f_valid) 

lemma valid_is_strongly_neutral :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "OVA.is_strongly_neutral (ova f)"
  by (meson Conditional.valid_def f_valid) 

lemma valid_discrete :
  fixes f :: "('A,'a) Conditional"
  assumes f_valid : "valid f"
  shows "space (ova f) = Space.discrete"
  by (meson Conditional.valid_def f_valid) 

lemma validI [intro] :
  fixes f :: "('A,'a) Conditional"
  assumes valid_ova : "OVA.valid (ova f)"
  assumes valid_src : "src f \<in> opens (space (ova f))"
  assumes valid_el : "el f \<in> elems (ova f)"
  assumes valid_domain : "src f \<subseteq> d (el f)"
  assumes valid_comm : "is_commutative (ova f)"
  assumes valid_strongly_neutral : "is_strongly_neutral (ova f)"
  assumes valid_discrete : "space (ova f) = Space.discrete"
  shows "valid f"
  using Conditional.valid_def local.valid_comm local.valid_discrete local.valid_domain local.valid_el local.valid_ova valid_src valid_strongly_neutral by blast

definition unit :: "('A, 'a) OVA \<Rightarrow> 'A Open \<Rightarrow> ('A, 'a) Conditional" where
  "unit V A =
     \<lparr>
      ova = V,
      src = A,
      el = OVA.neut V A \<rparr>"

lemma "OVA.valid V 
     \<and> OVA.is_commutative V
     \<and> OVA.is_strongly_neutral V \<and> space V = Space.discrete \<Longrightarrow> A \<in> opens (space V) \<Longrightarrow> valid (unit V A)"
  by (metis Conditional.select_convs(1) Conditional.select_convs(2) Conditional.select_convs(3) Conditional.valid_def d_neut dual_order.refl neutral_is_element unit_def)

lemma "valid f \<Longrightarrow> d (el f) \<in> opens (space (ova f))"
  using d_elem_is_open valid_el valid_ova by blast

lemma discrete :
  fixes f :: "('A,'a) Conditional"
  assumes "valid f"
  shows "A \<in> opens (space (ova f)) \<Longrightarrow> B \<in> opens (space (ova f)) \<Longrightarrow> A - B \<in> opens (space (ova f))"
proof -
  have "space (ova f) = Space.discrete"
    by (simp add: Conditional.valid_discrete assms) 
  then show ?thesis using  assms unfolding Space.discrete_def 
    by simp
qed

(* COMPOSE *)

definition compose :: "('A, 'a) Conditional \<Rightarrow> ('A, 'a) Conditional \<Rightarrow> ('A, 'a) Conditional" where
  "compose g f =
     \<lparr>
      ova = ova f,
      src = ((src g - src f) \<union> (src f - src g)) - (tgt f \<inter> src g),
      el = OVA.res (ova f) ((dom f \<union> dom g) - (tgt f \<inter> src g)) (OVA.comb (ova f) (el g) (el f)) \<rparr>"

lemma domain :
  fixes g f :: "('A,'a) Conditional"
  assumes "valid2 g f"
shows "d (el (compose g f)) = (dom f \<union> dom g) - (tgt f \<inter> src g)"
  by (metis (no_types, lifting) Conditional.compose_def Conditional.dom_def Conditional.select_convs(3) Conditional.valid_discrete Diff_subset Pow_UNIV Space.Space.simps(1) Space.discrete_def UNIV_I assms comb_is_element d_comb d_res sup_commute valid_el valid_ova)

lemma source :
  fixes g f :: "('A,'a) Conditional"
  assumes "valid2 g f"
shows "src (compose g f) = ((src g - src f) \<union> (src f - src g)) - (tgt f \<inter> src g)"
  by (simp add: Conditional.compose_def)

lemma target :
  fixes g f :: "('A,'a) Conditional"
  assumes "valid2 g f"
  shows "tgt (compose g f) = ((dom f \<union> dom g) - (tgt f \<inter> src g)) - (((src g - src f) \<union> (src f - src g)) - (tgt f \<inter> src g))"
  by (simp add: Conditional.dom_def assms domain source)

lemma validity :
  fixes g f :: "('A,'a) Conditional"
  assumes "valid2 g f" 
shows "valid (compose g f)"
proof (intro validI, goal_cases)
  case 1
  then show ?case
    by (simp add: Conditional.compose_def assms(1) valid_ova) 
next
  case 2
  then show ?case
    by (simp add: Conditional.compose_def Conditional.valid_discrete Space.discrete_def assms(1)) 
next
  case 3
  then show ?case 
    unfolding compose_def
    apply clarsimp
    by (smt (verit, best) Conditional.discrete Conditional.dom_def Diff_subset OVA.valid_welldefined Prealgebra.valid_space assms comb_is_element comp_apply d_comb d_elem_is_open res_elem sup_commute valid_el valid_inter valid_ova valid_src)
next
  case 4
  then show ?case     unfolding compose_def using assms
    by (smt (verit) Conditional.compose_def Conditional.dom_def Conditional.select_convs(2) Conditional.valid_domain Diff_subset_conv Un_Diff_cancel Un_assoc Un_commute Un_subset_iff domain sup.absorb_iff1)
next
  case 5
  then show ?case
    by (simp add: Conditional.compose_def assms valid_comm) 
next
  case 6
  then show ?case
    by (simp add: Conditional.compose_def assms valid_is_strongly_neutral) 
next
  case 7
  then show ?case
    by (
simp add: Conditional.compose_def Conditional.valid_discrete assms) 
qed

(*
lemma unit_left :
  fixes f :: "('A,'a) Conditional"
  assumes "valid f"  
  shows "compose (unit (ova f) (tgt f)) f = f"
  oops

lemma unit_right :
  fixes f :: "('A,'a) Conditional"
  assumes "valid f"  
  shows "compose f (unit (ova f) (src f)) = f"
  unfolding compose_def unit_def
  apply clarsimp
  oops
 This is clearly false as src = {} *)

definition acyclic2 :: "('A,'a) Conditional \<Rightarrow> ('A,'a) Conditional \<Rightarrow> bool " where
"acyclic2 g f \<equiv>
    dom f \<inter> tgt g = {}
  \<and> dom g \<inter> src f = {}"

definition acyclic3 :: "('A,'a) Conditional \<Rightarrow> ('A,'a) Conditional \<Rightarrow> ('A,'a) Conditional \<Rightarrow> bool " where
"acyclic3 h g f \<equiv>
    (dom f \<inter> tgt h = {})
  \<and> (dom f \<inter> tgt g = {})
  \<and> (dom g \<inter> src f = {})
  \<and> (dom g \<inter> tgt h = {})
  \<and> (dom h \<inter> src g = {})
  \<and> (dom h \<inter> src f= {})"

lemma acyclic3gf : "acyclic3 h g f \<Longrightarrow> acyclic2 g f"
  by (simp add: acyclic2_def acyclic3_def) 

lemma acyclic3hg : "acyclic3 h g f \<Longrightarrow> acyclic2 h g"
  by (simp add: acyclic2_def acyclic3_def)

lemma acyclic2to3 : "(acyclic2 g f \<and> acyclic2 h g \<and> dom h \<inter> src f = {} \<and> dom f \<inter> tgt h = {}) = acyclic3 h g f"
  by (meson acyclic2_def acyclic3_def)

lemma acyclic_domain_interaction :
  fixes g f :: "('A,'a) Conditional"
  assumes "valid2 g f"
  and acyclic2 : "acyclic2 g f"
shows "tgt f \<inter> src g = dom f \<inter> dom g"
  by (smt (verit, ccfv_SIG) Conditional.dom_def Conditional.valid_domain Diff_Diff_Int Diff_triv Int_Diff acyclic2 acyclic2_def assms(1) inf.orderE inf_commute)

lemma acyclic3_compose_left : 
  fixes h g f :: "('A, 'a) Conditional"
  assumes "valid3 h g f" and "acyclic3 h g f"
  shows "acyclic2 (compose h g) f"
proof - 
  have "src (compose h g) = ((src h - src g) \<union> (src g - src h)) - (tgt g \<inter> src h)"
    by (simp add: assms(1) source) 
  moreover have "tgt (compose h g) = ((dom g \<union> dom h) - (tgt g \<inter> src h)) - (((src h - src g) \<union> (src g - src h)) - (tgt g \<inter> src h))"
    by (simp add: assms(1) target) 
  moreover have "dom f \<inter> tgt (compose h g) = {}" using assms calculation valid_def acyclic3_def
    apply clarsimp
    by (smt (z3) Conditional.dom_def Conditional.valid_domain Diff_disjoint Diff_eq_empty_iff Diff_iff Un_iff acyclic3_def disjoint_iff)
  moreover have "dom (compose h g) \<inter> src f = {}" using assms calculation  acyclic3_def
    by (smt (verit) Conditional.dom_def Diff_iff Un_iff disjoint_iff domain)
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) Conditional.dom_def Diff_iff Un_iff acyclic2_def acyclic3_def assms(1) assms(2) disjoint_iff domain) 
qed    

lemma acyclic3_compose_right : 
  fixes h g f :: "('A, 'a) Conditional"
  assumes "valid3 h g f" and "acyclic3 h g f"
  shows "acyclic2 h (compose g f)"
proof - 
  have "src (compose g f) = ((src g - src f) \<union> (src f - src g)) - (tgt f \<inter> src g)"
    by (simp add: assms(1) source) 
  moreover have "tgt (compose g f) = ((dom f \<union> dom g) - (tgt f \<inter> src g)) - (((src g - src f) \<union> (src f - src g)) - (tgt f \<inter> src g))"
    by (simp add: assms(1) target) 
  moreover have "dom (compose g f) \<inter> tgt h = {}" using assms calculation valid_def acyclic3_def
    apply clarsimp
    by (smt (verit) Conditional.dom_def Diff_Int_distrib2 Diff_cancel Int_Diff Int_Un_distrib2 Int_commute acyclic3_def domain)
  moreover have "dom h \<inter> src (compose g f) = {}" using assms calculation  acyclic3_def
    by (smt (verit) Diff_iff Un_iff disjoint_iff)
  ultimately show ?thesis
    by (simp add: acyclic2_def)
qed   

lemma src_compose_acyclic :
  fixes g f :: "('A, 'a) Conditional"
  assumes "valid2 g f"
  and acyclic2 : "acyclic2 g f"
shows  "src (compose g f) = src f \<union> (src g - tgt f)"
  unfolding compose_def res_def  
  apply clarsimp
  apply safe
  apply (metis Conditional.dom_def Conditional.valid_domain IntI acyclic2 acyclic2_def assms(1) empty_iff subset_iff)
  using Conditional.dom_def Conditional.valid_domain assms(2)
  apply (metis assms(1) subsetD) 
  by (metis Conditional.dom_def Conditional.valid_domain IntI acyclic2 acyclic2_def assms(1) empty_iff subset_iff)

lemma tgt_compose_acyclic :
  fixes g f :: "('A, 'a) Conditional"
  assumes "valid2 g f"
  and acyclic2 : "acyclic2 g f"
shows  "tgt (compose g f) = tgt g \<union> (tgt f - src g)"
  using assms unfolding   valid_def 
  apply clarsimp
  apply safe
  apply (simp add: Conditional.dom_def assms(1) domain)
  apply (simp add: assms(1) src_compose_acyclic)
  apply (simp add: assms(1) src_compose_acyclic)
  apply (simp add: assms(1) src_compose_acyclic)
  apply (metis Conditional.dom_def subset_iff)
  apply (simp add: Conditional.dom_def assms(1) domain src_compose_acyclic)
  apply (simp add: Conditional.dom_def assms(1) domain)
  apply (simp add: Conditional.dom_def assms(1) domain)
  apply (simp add: acyclic2_def assms(1) disjoint_iff src_compose_acyclic)
  by (simp add: assms(1) src_compose_acyclic)

lemma dom_compose_acyclic :
  fixes g f :: "('A, 'a) Conditional"
  assumes "valid2 g f"
  and acyclic2 : "acyclic2 g f"
shows  "dom (compose g f) = src f \<union> (src g - tgt f) \<union> tgt g \<union> (tgt f - src g)"
  by (metis (no_types, lifting) Conditional.dom_def Conditional.valid_domain Diff_partition acyclic2 assms(1) src_compose_acyclic sup_assoc tgt_compose_acyclic validity)

lemma src_compose_acyclic_assoc :
  fixes h g f :: "('A, 'a) Conditional"
  assumes "valid3 h g f"
  and "acyclic3 h g f"
shows "src (compose h (compose g f)) = src (compose (compose h g) f)"
proof -
  let ?gf = "compose g f"
  have "acyclic2 h ?gf"
    using acyclic3_compose_right assms by blast
  moreover have l1: "src (compose h ?gf) = src ?gf \<union> (src h - tgt ?gf)"
    by (metis Conditional.compose_def Conditional.select_convs(1) assms(1) calculation src_compose_acyclic validity)
  moreover have l2: "... = src f \<union> (src g - tgt f) \<union> (src h - (tgt g \<union> (tgt f - src g)))"
    by (metis acyclic3gf assms src_compose_acyclic tgt_compose_acyclic) 

  let ?hg = "compose h g"
  have "acyclic2 ?hg f"
    using acyclic3_compose_left assms by blast
  moreover have r1: "src (compose ?hg f) = src f \<union> (src ?hg - tgt f)"
    by (metis Conditional.compose_def Conditional.select_convs(1) assms(1) calculation(3) src_compose_acyclic validity)
  moreover have r2: "... = src f \<union> ((src g \<union> (src h - tgt g)) - tgt f)"
    using acyclic3hg assms src_compose_acyclic by blast

  ultimately show ?thesis using assms unfolding valid_def
    apply safe
    apply (metis Diff_iff Un_iff acyclic3hg assms(1) l2 source src_compose_acyclic)
    using l2 by fastforce
  qed

lemma dom_compose_acyclic_assoc :
  fixes h g f :: "('A, 'a) Conditional"
  assumes "valid3 h g f"
  and acyclic: "acyclic3 h g f"
shows "dom (compose h (compose g f)) = dom (compose (compose h g) f)"
proof -
  let ?gf = "compose g f"
  have "acyclic2 h ?gf"
    by (simp add: acyclic acyclic3_compose_right assms(1))
  moreover have l1: "dom (compose h ?gf) = src ?gf \<union> (src h - tgt ?gf) \<union> tgt h \<union> (tgt ?gf - src h)"
    by (metis Conditional.compose_def Conditional.select_convs(1) assms(1) calculation dom_compose_acyclic validity)
  moreover have l2: "... = src f \<union> (src g - tgt f) \<union> (src h - (tgt g \<union> (tgt f - src g))) \<union> tgt h \<union> (tgt g \<union> (tgt f - src g) - src h)"
    by (metis acyclic acyclic2to3 assms(1) src_compose_acyclic tgt_compose_acyclic)

  let ?hg = "compose h g"
  have "acyclic2 ?hg f"
    using acyclic acyclic3_compose_left assms(1) assms(2) by blast
  moreover have r1 : "dom (compose ?hg f) = src f \<union> (src ?hg - tgt f) \<union> tgt ?hg \<union> (tgt f - src ?hg)"
    by (metis Conditional.compose_def Conditional.select_convs(1) assms(1) calculation(3) dom_compose_acyclic validity)
  moreover have r2 : "... = src f \<union> ((src g \<union> (src h - tgt g)) - tgt f) \<union> (tgt h \<union> (tgt g - src h)) \<union> (tgt f - (src g \<union> (src h - tgt g)))"
    by (metis acyclic acyclic3hg assms(1) src_compose_acyclic tgt_compose_acyclic)

  ultimately show ?thesis using assms unfolding valid_def
    apply safe
    apply clarsimp
    apply (smt (verit) Conditional.dom_def Diff_iff Diff_partition Int_Diff Int_iff Un_iff acyclic3_def acyclic3gf assms(1) domain src_compose_acyclic)
    by (smt (z3) Diff_iff Un_iff acyclic3_def disjoint_iff l2)
qed

lemma tgt_compose_acyclic_assoc :
  fixes h g f :: "('A, 'a) Conditional"
  assumes "valid3 h g f"
  and "acyclic3 h g f"
shows "tgt (compose h (compose g f)) = tgt (compose (compose h g) f)"
  by (simp add: assms(1) assms(2) dom_compose_acyclic_assoc src_compose_acyclic_assoc) 

lemma el_acyclic_assoc :
  fixes h g f :: "('A,'a) Conditional"
  assumes "valid3 h g f"
  and acyclic: "acyclic3 h g f"
shows "el (compose h (compose g f)) = el (compose (compose h g) f)"
proof -
  let ?V = "ova f"
  let ?hg = "compose h g"
  let ?gf = "compose g f"

  have "el (compose ?hg f) 
    = res ?V ((dom h \<union> dom g \<union> dom f) - ((src h \<inter> tgt g) \<union> (src g \<inter> tgt f)))
      (comb ?V (comb ?V (el h) (el g)) (el f))" 
    sorry
(*
  proof -
    let ?d = "((((dom h \<union> dom g) - (src h \<inter> tgt g)) \<union> dom f) - ((src g \<union> (src h - tgt g)) \<inter> tgt f))"


    have "?d = (dom h \<union> dom g \<union> dom f) - ((src h \<inter> tgt g) \<union> (src g \<inter> tgt f))" 
      using acyclic unfolding acyclic3_def 
      apply clarsimp
      oops

    have "el (compose ?hg f)  =
      res ?V ?d (comb ?V (res ?V ((dom h \<union> dom g) - (src h \<inter> tgt g)) (comb ?V (el h) (el g))) (el f))"
      by (smt (verit) Conditional.compose_def Conditional.dom_def Conditional.select_convs(3) acyclic acyclic3hg assms(1) domain inf_commute src_compose_acyclic sup_commute)
*)
 
  moreover have "el (compose h ?gf) 
    = res ?V ((dom h \<union> dom g \<union> dom f) - ((src h \<inter> tgt g) \<union> (src g \<inter> tgt f)))
      (comb ?V (el h) (comb ?V  (el g) (el f)))" 
    sorry

  ultimately show ?thesis
    by (metis assms(1) valid_associative valid_el valid_ova valid_semigroup)
qed

lemma acyclic_assoc :
  fixes h g f :: "('A,'a) Conditional"
  assumes "valid3 h g f"
  and acyclic: "acyclic3 h g f"
shows "compose h (compose g f) = compose (compose h g) f"
  by (smt (verit, del_insts) Conditional.compose_def Conditional.select_convs(1) Conditional.select_convs(3) acyclic assms(1) el_acyclic_assoc source src_compose_acyclic_assoc validity)

(*
lemma acyclic_assoc :
  fixes h g f :: "('A,'a) Conditional"
  assumes "valid h" and  "valid g" and "valid f"
  and "ova h = ova g" and "ova g = ova f"
  and "src h = tgt g" and "src g = tgt f" 
  and "src h \<inter> tgt h = {}" and "src g \<inter> tgt g = {}" and "src f \<inter> tgt f = {}"  
  and "tgt h \<inter> src g = {}" and "tgt g \<inter> src f = {}"
  and "tgt h \<inter> src f = {}" 
shows "compose h (compose g f) = compose (compose h g) f"
proof -
  let ?V = "ova f"

  have "el (compose (compose h g) f) = res ?V (tgt h \<union> src f) (comb ?V (comb ?V (el h) (el g)) (el f))" 
  proof -
    have "tgt h \<union> tgt f = (dom h \<union> dom g) \<inter> (tgt h \<union> dom f)"
      by (metis (no_types, lifting) Conditional.dom_def assms(12) assms(6) assms(7) assms(9) inf_sup_absorb sup.idem sup_assoc sup_commute sup_inf_distrib1) 
    moreover have "dom f \<subseteq> tgt h \<union> dom f \<and> tgt h \<union> tgt f \<subseteq> dom h \<union> dom g \<union> dom f"
      by (simp add: calculation le_infI1) 
    moreover have "res ?V (tgt h \<union> dom f) (comb ?V (comb ?V (el h) (el g)) (el f))
       = comb ?V (res ?V ((dom h \<union> dom g) \<inter> (tgt h \<union> dom f)) (comb ?V (el h) (el g))) (el f)"
      by (smt (verit, ccfv_threshold) Conditional.dom_def Conditional.valid_def OVA.valid_welldefined Prealgebra.valid_space Un_mono assms(1) assms(2) assms(3) assms(4) assms(5) calculation(1) comb_is_element d_comb inf_le1 inf_left_commute inf_sup_absorb sup.idem sup_ge2 valid_ova valid_union2 weak_comb_law_right)
    moreover have "... =  comb ?V (res ?V (tgt h \<union> src g) (comb ?V (el h) (el g))) (el f)"
      using assms(7) calculation(1) by auto
    moreover have "el (compose (compose h g) f) = res ?V (tgt h \<union> src f) ..."
      by (simp add: Conditional.compose_def assms(5))
    moreover have "... = res ?V (tgt h \<union> src f) (res ?V (tgt h \<union> dom f) (comb ?V (comb ?V (el h) (el g)) (el f)))"
      using calculation(3) calculation(4) by presburger
    moreover have "... = res ?V (tgt h \<union> src f) (comb ?V (comb ?V (el h) (el g)) (el f))"
      by (smt (verit, del_insts) Conditional.dom_def Conditional.valid_def OVA.valid_welldefined Prealgebra.valid_space assms(1) assms(2) assms(3) assms(4) assms(5) comb_is_element d_comb res_functorial_trans sup_assoc sup_commute sup_ge1 valid_union2)
    ultimately show ?thesis
      by (simp add: sup_commute)
  qed

  moreover have "el (compose h (compose g f)) = res ?V (tgt h \<union> src f) (comb ?V (el h) (comb ?V (el g) (el f)))"
  proof -
    have "src h \<union> src f = (dom g \<union> dom f) \<inter> (dom h \<union> src f)"
      by (metis (no_types, lifting) Conditional.dom_def Int_Un_eq(4) assms(11) assms(6) assms(7) assms(9) inf_commute sup_assoc sup_commute sup_inf_distrib1)
    moreover have "dom h \<subseteq> dom h \<union> src f \<and> dom h \<union> src f \<subseteq> dom h \<union> dom g \<union> dom f"
      using Conditional.dom_def by fastforce
    moreover have "res ?V (dom h \<union> src f) (comb ?V (el h) (comb ?V (el g) (el f)))
       = comb ?V (el h) (res ?V ((dom g \<union> dom f) \<inter> (dom h \<union> src f)) (comb ?V (el g) (el f)))"
      by (smt (verit, del_insts) Conditional.dom_def Conditional.valid_def OVA.valid_welldefined Prealgebra.valid_space assms(1) assms(2) assms(3) assms(4) assms(5) calculation(2) comb_is_element d_comb sup_assoc valid_union2 weak_comb_law_left)
    moreover have "... =  comb ?V (el h) (res ?V (src h \<union> src f) (comb ?V (el g) (el f)))"
      using assms(7) calculation(1) by auto
    moreover have "el (compose h (compose g f)) = res ?V (tgt h \<union> src f) ..."
      by (simp add: Conditional.compose_def assms(6))
    moreover have "... = res ?V (tgt h \<union> src f) (res ?V (dom h \<union> src f) (comb ?V (el h) (comb ?V (el g) (el f))))"
      using calculation(3) calculation(4) by presburger
    moreover have "... = res ?V (tgt h \<union> src f) (comb ?V (el h) (comb ?V (el g) (el f)))"
      by (smt (verit, del_insts) Conditional.dom_def Conditional.valid_def OVA.valid_welldefined Prealgebra.valid_space assms(1) assms(2) assms(3) assms(4) assms(5) comb_is_element d_comb res_functorial_trans sup_assoc sup_commute sup_ge1 valid_union2)
    ultimately show ?thesis
      by (simp add: sup_commute)
  qed

  ultimately show ?thesis
    by (metis Conditional.compose_def Conditional.select_convs(1) Conditional.select_convs(2) Conditional.select_convs(3) Conditional.select_convs(4) assms(1) assms(2) assms(3) assms(4) assms(5) valid_associative valid_el valid_ova valid_semigroup)
qed

*)

end