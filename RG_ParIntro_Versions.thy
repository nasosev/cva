section \<open> RG_ParIntro_Versions.thy \<close>

theory RG_ParIntro_Versions
  imports Logic
begin

(*
Attempts at deriving another form of the parallel-introduction law:

{p,r or g2}c1{g1,q1}
{p,r or g1}c2{g2,q2}
======================
{p,r}c1||c2{g1 or g2, q1 and q2}
*)

(* Using join for combining r with g1 (and r with g2) *)
proposition rg_concurrency_rule_explicit :
  fixes V :: "('A, 'a) CVA" and r p a1 q1 g1  a2 q2 :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and V_complete : "is_complete V"
  and "r \<in> elems V" and "p \<in> elems V" and "a1 \<in> elems V" and "q1 \<in> elems V" and "g1 \<in> elems V"
  and                                      "a2 \<in> elems V" and "q2 \<in> elems V" and "g2 \<in> elems V" 
  and rg1 : "rg V p (join V r g2) a1 g1 q1" and rg2 : "rg V p (join V r g1) a2 g2 q2"
  and inv_r : "invariant V r" and inv_g1 : "invariant V g1"  and inv_g2 : "invariant V g2"
(* Extra assumptions needed: *)
and inv_rg2: "invariant V (join V r g2)" and inv_rg1: "invariant V (join V r g1)"

shows "rg V (CVA.meet V p p) (meet V (join V r g2) (join V r g1)) (par V a1 a2) (par V g1 g2) (meet V q1 q2)"

  apply(rule  rg_concurrency_rule[of V "join V r g2" "p" a1 q1 g1 "join V r g1" p a2 q2 g2] )
   apply ( simp add: assms  )
  using V_complete apply auto[1]
  using V_complete assms(10) assms(3) join_elem apply blast
  using assms(4) apply force
  using assms(5) apply auto[1]
  using assms(6) apply force
  using assms(7) apply blast
  using V_complete assms(3) assms(7) join_elem apply blast
  using assms(4) apply blast
  using assms(8) apply fastforce
  using assms(9) apply auto[1]
  using assms(10) apply force
  using rg1 apply force
  using rg2 apply blast
  using inv_rg2 apply auto[1]  
  using inv_g1 apply auto[1]
  using inv_rg1 apply blast  
  using inv_g2 apply fastforce
  apply (metis V_complete assms(3) assms(7) complete_equiv_cocomplete join_greater)
  apply (metis V_complete assms(10) assms(3) complete_equiv_cocomplete join_greater)

  done

(* Using par for combining r with g1 (and r with g2) *)
proposition rg_concurrency_rule_explicit_par :
  fixes V :: "('A, 'a) CVA" and r p a1 q1 g1  a2 q2 :: "('A,'a) Valuation"
  assumes V_valid : "valid V"
  and V_complete : "is_complete V"
  and "r \<in> elems V" and "p \<in> elems V" and "a1 \<in> elems V" and "q1 \<in> elems V" and "g1 \<in> elems V"
  and                                      "a2 \<in> elems V" and "q2 \<in> elems V" and "g2 \<in> elems V" 
  and rg1 : "rg V p (par V r g2) a1 g1 q1" and rg2 : "rg V p (par V r g1) a2 g2 q2"
  and inv_r : "invariant V r" and inv_g1 : "invariant V g1"  and inv_g2 : "invariant V g2"
(* Extra assumptions needed: *)
and inv_rg2: "invariant V (par V r g2)" and inv_rg1: "invariant V (par V r g1)"
and "le V g1 (par V r g1)" and "le V g2 (par V r g2)"

shows "rg V (CVA.meet V p p) (meet V (par V r g2) (par V r g1)) (par V a1 a2) (par V g1 g2) (meet V q1 q2)"

  apply(rule  rg_concurrency_rule[of V "par V r g2" "p" a1 q1 g1 "par V r g1" p a2 q2 g2] )
   apply ( simp add: assms  )
  using V_complete apply auto[1]
  using V_valid assms(10) assms(3) valid_par_elem apply blast
  using assms(4) apply force
  using assms(5) apply auto[1]
  using assms(6) apply force
  using assms(7) apply blast
  using V_valid assms(3) assms(7) valid_par_elem apply blast
  using assms(4) apply blast
  using assms(8) apply fastforce
  using assms(9) apply auto[1]
  using assms(10) apply force
  using rg1 apply force
  using rg2 apply blast
  using inv_rg2 apply auto[1]  
  using inv_g1 apply auto[1]
  using inv_rg1 apply blast  
  using inv_g2 apply fastforce
  using assms(18) apply fastforce
  using assms(19) apply fastforce
  done




end