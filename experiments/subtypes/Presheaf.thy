section \<open> Presheaf.thy \<close>

theory Presheaf
imports Main Space Function
begin

record ('A, 'x) RawPresheaf =
  prim_space :: "'A Space"
  prim_ob :: "('A Open, 'x set) Function"
  prim_ar :: "('A Inclusion, ('x, 'x) Function) Function"

definition valid :: "('A, 'x) RawPresheaf \<Rightarrow> bool" where
  "valid F \<equiv>
    let
      T = prim_space F;
      F0 = prim_ob F;
      F1 = prim_ar F;

      welldefined =  (\<forall>i. i \<in> inclusions T \<longrightarrow>
                     Function.dom (F1 \<cdot> i) = F0 \<cdot> (Space.cod i)
                   \<and> Function.cod (F1 \<cdot> i) = F0 \<cdot> (Space.dom i));
      identity = (\<forall>A. A \<in> opens T \<longrightarrow> (F1 \<cdot> (Space.ident A)) = Function.ident (F0 \<cdot> A));
      composition = (\<forall>j i. j \<in> inclusions T \<longrightarrow> i \<in> inclusions T \<longrightarrow> Space.dom j = Space.cod i
        \<longrightarrow>  F1 \<cdot> (j \<propto> i) = (F1 \<cdot> i) \<bullet> (F1 \<cdot> j))
    in
    welldefined \<and> identity \<and> composition"


typedef ('A, 'x) Presheaf = "{ rF :: ('A, 'x) RawPresheaf . valid rF}"
proof
  define "empty_presheaf" where "empty_presheaf =  
    \<lparr> prim_space = Space.discrete,
      prim_ob = Function.const (opens Space.discrete) UNIV {},
      prim_ar = Function.const (inclusions Space.discrete) UNIV (Function.ident {})
   \<rparr>"
  have "valid empty_presheaf"  
    unfolding valid_def empty_presheaf_def 
    apply (simp add: Let_def)
    apply safe
    apply (metis (no_types, lifting) UNIV_I const_app const_dom deterministic empty_iff fun_app ident_dom mem_Collect_eq the_equality)
    apply (metis (no_types, lifting) UNIV_I const_app const_dom deterministic empty_def fun_app mem_Collect_eq the_equality)
       apply (simp_all add: const_func)
    apply (metis (no_types, lifting) CollectI UNIV_I const_app valid_ident_inc valid_inc_cod valid_inc_dom)
    by (metis compose_ident_left ident_cod)
  thus "empty_presheaf \<in> {rF. valid rF}" by auto
qed

setup_lifting type_definition_Presheaf

lift_definition space :: "('A, 'x) Presheaf \<Rightarrow> 'A Space" is "prim_space" done

lift_definition ob :: "('A, 'x) Presheaf \<Rightarrow> ('A Open, 'x set) Function" is "prim_ob" done

lift_definition ar :: "('A, 'x) Presheaf \<Rightarrow> ('A Inclusion, ('x, 'x) Function) Function" is "prim_ar" done

(* Validity *)

lemma welldefined_dom : 
  fixes F :: "('A, 'x) Presheaf" and i :: "'A Inclusion"
  assumes "i \<in> inclusions (space F)" 
  shows "Function.dom (ar F \<cdot> i) = ob F \<cdot> (Space.cod i)"
  apply transfer
  oops
end