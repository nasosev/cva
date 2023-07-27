theory Category
imports Dependent_Function 
begin

(* Probably a terser way of stating all this *)



locale category =
  fixes objects :: "'a set"   and 
        arrows  :: "'b set"   and 
            to  ::  "'b \<rightharpoondown> 'a" and 
        "from"  ::  "'b \<rightharpoondown> 'a" and
           comp :: "'b \<times> 'b \<rightharpoondown> 'b" and
       id_arrow :: "'a \<rightharpoondown> 'b" 
     assumes     to_type[types]:   "to   : arrows \<rightarrow> objects" and
                 from_type[types]: "from : arrows \<rightarrow> objects" and
                 comp_type[types]:  "comp : \<Pi> (x,y)\<in>{(x,y). x \<in> arrows \<and> y \<in> arrows \<and> to $ x = from $ y} \<rightarrow> {f. to $ f = to $ y \<and> from $ f = from $ x} : arrows" and
                 id_type_inner: "id_arrow : \<Pi> x\<in>objects \<rightarrow> {f. to $ f = x \<and> from $ f = x} : arrows" and
                 to_id[simp]:   "a \<in> objects \<Longrightarrow> to $ (id_arrow $ a) =  a" and
                 from_id[simp]: "a \<in> objects \<Longrightarrow> from $ (id_arrow $ a) = a" and
                 lid[simp]: "g \<in> arrows \<Longrightarrow> from $ g = a \<Longrightarrow> comp $ (id_arrow $ a, g ) = g" and
                 rid[simp]: "g \<in> arrows \<Longrightarrow> to $ g = b \<Longrightarrow> comp $ (g, (id_arrow $ b) ) =  g" and
                 composable_assoc[simp]: "(g, h) \<in> dom (comp) \<Longrightarrow> (f, (comp $ (g, h))) \<in> dom (comp) \<longleftrightarrow>  (f, g) \<in> dom comp" and
                 composable_assoc'[simp]: "(f, g) \<in> dom (comp) \<Longrightarrow> ((comp $ (f, g), h )) \<in> dom (comp) \<longleftrightarrow>  (g, h) \<in> dom comp" and
                 comp_assoc: "(f, g) \<in> dom (comp) \<Longrightarrow> (g, h) \<in> dom (comp) \<Longrightarrow> comp $ (f, (comp $ (g,h))) =  comp $ (comp $ (f, g), h)"


begin

lemma dom_to[simp]: "dom to = arrows"
  using to_type by auto

lemma cod_to[simp]: "codomain to = objects"
  using to_type by auto

lemma dom_from[simp]: "dom from = arrows"
  using from_type by auto

lemma cod_from[simp]: "codomain from = objects"
  using from_type by auto

definition in_hom :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "in_hom f a b \<equiv> to $$ f = Some b \<and> from $$ f = Some a"

definition "homs a b = {f. in_hom f a b}"

lemma id_type[types]: "id_arrow : \<Pi> x\<in>objects \<rightarrow> homs x x : arrows" 
  apply (simp add: homs_def)
  by (smt (verit, ccfv_SIG) Collect_cong category.in_hom_def category_axioms cod_cong cod_of_typ_iff codomain_typ_iff
                            dom_cod_of_codomain dom_from dom_to dom_typ_iff id_type_inner mem_Collect_eq safe_app_Some_iff)


definition "arr_composable (f :: 'b) (g :: 'b) \<equiv> (f \<in> arrows \<and> g \<in> arrows \<and> to $ f = from $ g)" 

lemma dom_composition[simp]:
 "dom comp = {(f, g). f \<in> arrows \<and> g \<in> arrows \<and> to $ f = from $ g}"
  using comp_type by auto


lemma cod_of_composition[simp]: " b \<in> arrows \<Longrightarrow> a \<in> arrows \<Longrightarrow> to $ b = from $ a \<Longrightarrow> c \<in> cod_of comp (b, a) \<longleftrightarrow> from $ c = from $ b \<and> to $ c = to $ a"
  using comp_type by auto


lemma cod_composition[simp]: " b \<in> arrows \<Longrightarrow> a \<in> arrows \<Longrightarrow> to $ b = from $ a \<Longrightarrow> ((b,a), c) \<in> cod comp  \<longleftrightarrow> from $ c = from $ b \<and> to $ c = to $ a"
  using comp_type by auto



lemma dom_id[simp]:
 "dom id_arrow = objects"
  using id_type by auto


lemma to_left[simp]: "in_hom f A B \<Longrightarrow> to $$ f = Some B"
  by (clarsimp simp: in_hom_def)

lemma from_right[simp]: "in_hom f A B \<Longrightarrow> from $$ f = Some A"
  by (unfold in_hom_def, elim conjE, assumption)

lemma arr_composableI: "in_hom f A B \<Longrightarrow> in_hom g B C \<Longrightarrow> arr_composable f g"
  by (metis category.arr_composable_def category.from_right category.to_left category_axioms dom_from safe_app_Some_iff)

lemma arr_composableD: "arr_composable f g \<Longrightarrow> f \<in> arrows \<and> g \<in> arrows \<and> to $ f = from $ g"
  by (clarsimp simp: arr_composable_def)

definition "homset = {(f, a, b). f \<in> arrows \<and> a \<in> objects \<and> b \<in> objects \<and> from $ f = a \<and> to $ f = b}"   

lemma fst_in_times[intro]: "x \<in> (S \<times> S') \<Longrightarrow> fst x \<in> S"
  by (clarsimp)

lemma snd_in_times[intro]: "x \<in> (S' \<times> S) \<Longrightarrow> snd x \<in> S"
  by (clarsimp)

lemma f_app_in_helper: "x \<in> dom f \<Longrightarrow> g ` codomain f \<subseteq> S \<Longrightarrow> g (f $ x) \<in> S"
  by (simp add: image_subset_iff)

lemma in_hom_in_homset:"in_hom f A B \<longleftrightarrow> (f, A, B) \<in> homset"
  apply (subst in_hom_def)
  apply (safe; clarsimp simp: homset_def)
    apply (metis cod_from cod_to dom_to in_dom_in_codomain safe_app_Some_iff)
  apply (metis  dom_to  safe_app_Some_iff)
  by (simp add: safe_app_Some_iff)

lemma in_hom_iff: "in_hom f a b \<longleftrightarrow> f \<in> arrows \<and> a \<in> objects \<and> b \<in> objects \<and> from $ f = a \<and> to $ f = b"
  by (clarsimp simp: in_hom_in_homset homset_def)
end

(*
locale category = pre_category + 
  fixes id_arrow :: "'a \<rightharpoondown> 'b"
  assumes id_dom[simp]:  "dom (id_arrow) = objects " and
          cod_id[simp]:  "cod (id_arrow) = {f. \<exists>x. in_hom f x x}" and
          to_id[simp]:   "id_arrow $$ A = Some f \<Longrightarrow> to $ f =  A" and
          from_id[simp]: "id_arrow $$ A = Some f \<Longrightarrow> from $ f =  A" and
          lid[simp]: "in_hom g A B \<Longrightarrow> comp $$ (id_arrow $ A, g ) = Some g" and
          rid[simp]: "in_hom g A B \<Longrightarrow> comp $$ (g, (id_arrow $ B) ) = Some g" and
          domain_comp[simp]: "dom (comp) = {(x,y). arr_composable x y}" and
          composable_assoc[simp]: "arr_composable g h \<Longrightarrow> arr_composable f (comp $ (g, h)) \<longleftrightarrow>  arr_composable f g" and
          composable_assoc'[simp]: "arr_composable f g \<Longrightarrow> arr_composable (comp $ (f, g)) h \<longleftrightarrow>  arr_composable g h" and
          comp_assoc: "arr_composable f g \<Longrightarrow> arr_composable g h \<Longrightarrow> comp $ (f, (comp $ (g,h))) =  comp $ (comp $ (f, g), h)"
begin

end

*)



interpretation empty_category: category "{}" "{}" "\<lambda>x\<in>{} \<rightarrow> {}. undefined" "\<lambda>x\<in>{} \<rightarrow> {}. undefined" "\<lambda>x\<in>{} \<rightarrow> {}. undefined" "\<lambda>x\<in>{} \<rightarrow> {}. undefined"
  by (standard; (clarsimp | intro typ_judgI)+)

datatype ('a, 'b) raw_category = 
   Category (r_ob : "'a set") (r_ar : "'b set") (r_to : "('b \<rightharpoondown> 'a)") (r_from : "('b \<rightharpoondown> 'a)") (r_comp : "('b \<times> 'b \<rightharpoondown> 'b)") (r_id : "('a \<rightharpoondown> 'b)")

typedef ('a, 'b) category = "{c :: ('a, 'b) raw_category. category (r_ob c) (r_ar c) (r_to c) (r_from c) (r_comp c) (r_id c)}"
  apply (rule_tac x="Category {} {} (\<lambda>x\<in>{} \<rightarrow> {}. undefined) (\<lambda>x\<in>{} \<rightarrow> {}. undefined) (\<lambda>x\<in>{} \<rightarrow> {}. undefined) (\<lambda>x\<in>{} \<rightarrow> {}. undefined)" in exI, clarsimp)
  by (simp add: empty_category.category_axioms)

definition "ob = r_ob o Rep_category"

definition "ar = r_ar o Rep_category"

definition "src = r_from o Rep_category"

definition "target = r_to o Rep_category"

definition "ccmp = r_comp o Rep_category"

definition "ids = r_id o Rep_category"

 
interpretation category "ob c" "ar c" "target c" "src c"  "ccmp c" "ids c"
  apply (insert Rep_category[where x=c], clarsimp) 
  by (simp add: ar_def ccmp_def src_def target_def ids_def ob_def) 

context category begin

definition "witness = Abs_category (Category objects arrows to from comp id_arrow)"

lemma ob_witness[simp]: "ob (local.witness) = objects"
  using local.category_axioms
  by (clarsimp simp: ob_def local.witness_def Abs_category_inverse)

lemma ar_witness[simp]: "ar (local.witness) = arrows"
  using local.category_axioms
  by (clarsimp simp: ar_def local.witness_def Abs_category_inverse)

lemma src_witness[simp]: "src (local.witness) = from"
  using local.category_axioms
  by (clarsimp simp: src_def local.witness_def Abs_category_inverse)

lemma target_witness[simp]: "target (local.witness) = to"
  using local.category_axioms
  by (clarsimp simp: target_def local.witness_def Abs_category_inverse)

lemma ccmp_witness[simp]: "ccmp (local.witness) = comp"
  using local.category_axioms
  by (clarsimp simp: ccmp_def local.witness_def Abs_category_inverse)

lemma ids_witness[simp]: "ids (local.witness) = id_arrow"
  using local.category_axioms
  by (clarsimp simp: ids_def local.witness_def Abs_category_inverse)

lemma in_hom_in_objects[simp]: "in_hom f a b \<Longrightarrow> a \<in> objects"
  by (clarsimp simp: in_hom_in_homset, clarsimp simp: homset_def)


lemma in_hom_in_arrows[simp]: "in_hom f a b \<Longrightarrow> f \<in> arrows"
  by (clarsimp simp: in_hom_in_homset, clarsimp simp: homset_def)

lemma in_hom_in_objects'[simp]: "in_hom f a b \<Longrightarrow> b \<in> objects"
  by (clarsimp simp: in_hom_in_homset, clarsimp simp: homset_def)


lemma comp_in_arrows[simp]: "arr_composable f g \<Longrightarrow> f \<in> arrows"
  by (clarsimp simp: arr_composable_def)


lemma comp_in_arrows'[simp]: "arr_composable f g \<Longrightarrow> g \<in> arrows"
  by (subst (asm) arr_composable_def, clarsimp )



lemma id_arrow_in_arrows[simp, intro]: "A \<in> objects \<Longrightarrow> id_arrow $ A \<in> arrows"
  apply (rule total_ind, assumption; clarsimp?)
  using id_type 
  by (meson cod_of_typ_codomain in_mono)

lemma from_left[simp]: "in_hom f a b \<Longrightarrow> from $ f = a"
  by (metis local.from_right safe_app_Some_iff)


lemma id_in_hom[simp]: "a \<in> objects \<Longrightarrow> in_hom (id_arrow $ a) a a"
  using id_arrow_in_arrows local.from_id local.in_hom_iff local.to_id by presburger

lemma to_right[simp]: "in_hom f a b \<Longrightarrow> to $ f = b"
  by (metis local.to_left safe_app_Some_iff)


lemma swap_prod[simp]: "(h, g) \<in> converse S \<Longrightarrow> swap S $ (g, h) = (h, g)"
  by (clarsimp simp: swap_def)

lemma composable_id_r[simp]: "in_hom f a b \<Longrightarrow> arr_composable f (id_arrow $ b)"
  by (meson id_in_hom in_hom_in_objects' local.arr_composableI)


lemma composable_id_l[simp]: "in_hom f a b \<Longrightarrow> arr_composable (id_arrow $ a) f "
  by (meson id_in_hom in_hom_in_objects local.arr_composableI)



lemma from_comp_pres[simp]: "g \<in> arrows \<Longrightarrow> f \<in> arrows \<Longrightarrow> to $ g = from $ f \<Longrightarrow>
                                                from $ (comp $ (g, f)) = from $ g "
  using composable_assoc[simplified dom_composition, simplified] 
  by (metis id_arrow_in_arrows in_dom_in_codomain local.cod_from local.dom_from local.to_id)



lemma to_comp_pres[simp]: "g \<in> arrows \<Longrightarrow> f \<in> arrows \<Longrightarrow> to $ g = from $ f \<Longrightarrow>
                                                to $ (comp $ (g, f)) = to $ f "
  using composable_assoc'[simplified dom_composition, simplified] 
  by (metis id_arrow_in_arrows in_dom_in_codomain local.cod_to local.dom_to local.from_id)


lemma from_arrow_in_objects[simp]: "g \<in> arrows \<Longrightarrow> from $ g \<in> objects"
  by (metis in_dom_in_codomain local.cod_from local.dom_from)


lemma to_arrow_in_objects[simp]: "g \<in> arrows \<Longrightarrow> to $ g \<in> objects"
  by (metis in_dom_in_codomain local.cod_to local.dom_to)


lemma matching_arrows_comp_in_arrows[simp]: "g \<in> arrows \<Longrightarrow> h \<in> arrows \<Longrightarrow> to $ h = from $ g \<Longrightarrow> comp $ (h, g) \<in> arrows"
  using in_dom_in_codomain local.comp_type mem_Collect_eq typ_judg_def by auto

end


locale op_category = category
begin


sublocale op_cat: category objects arrows "from" "to" "swap (converse (dom comp)) \<cdot> comp"  id_arrow 
  apply (standard; (clarsimp | intro typ_judgI)+)
  using local.from_type apply auto[1]
  using to_type apply auto[1]
       apply (safe; clarsimp)
  apply (clarsimp)
  using comp_type apply force
  apply (clarsimp)
           apply (clarsimp simp: swap_def)
         apply (safe; clarsimp?)
  using id_type apply force
  using id_type apply force
  using local.id_type 
  apply (metis (no_types, lifting) Collect_cong Sigma_cong cod_typ_iff local.id_type_inner)
  by (simp add: local.comp_assoc)

end


interpretation op_category "ob c" "ar c" "target c" "src c"  "ccmp c" "ids c"
  apply (insert Rep_category[where x=c], clarsimp) 
  apply (clarsimp simp: op_category_def)
  by (simp add: ar_def ccmp_def src_def target_def  ids_def ob_def) 

interpretation set_category: category "UNIV :: 'a set set" "UNIV :: ('a \<rightharpoondown> 'a) set" "(\<lambda>x!. codomain x )" "(\<lambda>x!. dom x )" 
  "\<Pi> (f, g)\<in>{(f,g). codomain f = dom g} \<rightarrow> {h. codomain h = codomain g  \<and> Dependent_Function.dom h = Dependent_Function.dom f } : UNIV. f \<cdot> g"
  "(\<Pi> x\<in>UNIV \<rightarrow> {f. dom f = x  \<and> codomain f = x} : UNIV. (\<lambda> y\<in>x \<rightarrow> x. y))"
  apply (standard;  (clarsimp  |(intro typ_judgI) | typesimp)+)
    apply (rule extensionality'; clarsimp)
    apply (rule extensionality'; clarsimp)
  apply (rule extensionality; clarsimp)
   apply (safe; clarsimp?)
    apply blast
   apply (metis Image_iff SigmaI dom_cod_of_codomain)
  by (typesimp)


locale "functor" = 
  fixes A :: "('a, 'b) category" and B :: "('c, 'd) category" and
        obj_map :: "'a \<rightharpoondown> 'c" and 
        arr_map :: "'b \<rightharpoondown> 'd" 
      assumes obj_map_dom[simp]: "dom obj_map = ob A" and
              obj_map_cod[simp]: "codomain obj_map = ob B" and
              arr_map_typ[simp, types]: "arr_map : \<Pi> a\<in>(ar A) \<rightarrow> homs B (a |> src A \<cdot> obj_map) (a |> target A \<cdot> obj_map) : (ar B)" and
              distrib: "in_hom A f a b \<Longrightarrow>
                        in_hom A g b c \<Longrightarrow>  
                        arr_map $ (ccmp A $ (f, g)) = (ccmp B $ (arr_map $ f, arr_map $ g))" and
              id_map : " ids A \<cdot> arr_map  =  obj_map \<cdot> ids B"

begin

abbreviation "acomp f g \<equiv> ccmp A $ (f, g)"
abbreviation "bcomp f g \<equiv> ccmp B $ (f, g)"

notation acomp (infixr "o\<^sub>A" 54)

notation bcomp (infixr "o\<^sub>B" 54)

lemma id_map_app: "a \<in> ob A \<Longrightarrow> a |> ids A \<cdot> arr_map = a |> obj_map \<cdot> ids B"
  using id_map by presburger

declare types[THEN dep_appI, intro] 

thm types[THEN dep_appI, intro]

lemma in_hom_in_hom: "in_hom A f a b \<Longrightarrow> in_hom B (arr_map $ f) (obj_map $ a) (obj_map $ b)"
  apply (standard; clarsimp simp: homs_def)
  done

end


lemma (in category) in_hom_from_to[simp]:  "a \<in> arrows \<Longrightarrow> in_hom a (a |> from) (a |> to)"
  using local.from_arrow_in_objects local.in_hom_iff local.to_arrow_in_objects by presburger

lemma (in category) codomain_id_arrow[simp]: "codomain id_arrow = arrows"
  by (metis (no_types, lifting) codomain_typ_iff id_type)

lemma (in category) in_hom_comp[simp]: "in_hom f a b \<Longrightarrow> in_hom g b c \<Longrightarrow> in_hom ((f, g) |> comp) a c"
  by (metis local.from_comp_pres local.from_left local.in_hom_from_to local.in_hom_in_arrows
            local.matching_arrows_comp_in_arrows local.to_comp_pres local.to_right)

lemma (in category) hom_is_ar[simp]: "{x. in_hom x (x |> from) (x |> to )} = arrows"
  by (safe; clarsimp)


lemma (in category) in_arrows_in_homs[simp]:  "x \<in> arrows \<Longrightarrow> x \<in> homs (x |> from) (x |> to)"
  by (simp add: homs_def)


lemma (in category) homs_subset_arrows[simp]:  "homs x y \<subseteq> arrows"
  by (simp add: homs_def, safe; clarsimp)


lemma (in category) homs_objects: "x \<in> objects \<Longrightarrow> {f. f |> from = x \<and> f |> to = x} = homs x x"
  apply (clarsimp simp: homs_def; safe; clarsimp?)
  by (smt (verit, best) cod_of_typ_iff dom_cod_of_codomain 
                        local.codomain_id_arrow local.dom_id 
                        local.id_type_inner local.in_hom_from_to mem_Collect_eq)

lemma  (in category) homs_iff[simp]: "y \<in> arrows \<Longrightarrow> y \<in> homs a b \<longleftrightarrow> y |> from = a \<and> y |> to = b"
  by (safe; clarsimp simp: homs_def)

definition id_on :: "'a set \<rightharpoondown> 'a \<rightharpoondown> 'a" where
  "id_on = ids (set_category.witness)"

interpretation identity_functor: "functor" A A "(ob A) |> id_on" " \<Pi> a\<in>(ar A) \<rightarrow> homs A (a |> src A) (a |> target A) : (ar A). a"
  apply (standard; clarsimp simp: id_on_def)
    apply (rule typ_judgI; (clarsimp cong: Sigma_cong |typesimp)+ )
  apply (rule extensionality'; (clarsimp?, (solves \<open>auto\<close>)?))
  by (typesimp)

lemma not_in_hom_empty_category[simp]: "empty_category.in_hom f a b \<Longrightarrow> False"
  by (drule empty_category.in_hom_in_objects, clarsimp)

interpretation empty_functor: "functor"  "empty_category.witness :: ('a, 'b) category" "empty_category.witness :: ('c, 'd) category" "(\<lambda>x\<in>{} \<rightarrow> {}. undefined)" "(\<lambda>x\<in>{} \<rightarrow> {}. undefined)"
  apply (subst functor_def; clarsimp?)
  apply (intro conjI)
    apply (rule typ_judgI; (clarsimp cong: Sigma_cong |typesimp)+ )
   apply (clarsimp)
  apply (drule not_in_hom_empty_category, clarsimp)
  by (rule extensionality'; (clarsimp?, (solves \<open>auto\<close>)?))


datatype ('a, 'b, 'c , 'd) raw_functor = 
   Functor (r_from_cat : "('a, 'b) category") (r_to_cat : "('c, 'd) category") (r_obj_map : "'a \<rightharpoondown> 'c")  (r_arrow_map : "'b \<rightharpoondown> 'd")

term "functor"

typedef ('a, 'b, 'c , 'd) "functor" = "{c :: ('a, 'b, 'c , 'd) raw_functor. functor (r_from_cat c) (r_to_cat c) (r_obj_map c) (r_arrow_map c) }"
  apply (rule_tac x="Functor empty_category.witness empty_category.witness (\<lambda>x\<in>{} \<rightarrow> {}. undefined) (\<lambda>x\<in>{} \<rightarrow> {}. undefined)" in exI, clarsimp)
  by (simp add: empty_functor.functor_axioms)

definition "ob_map = r_obj_map o Rep_functor"

definition "ar_map = r_arrow_map o Rep_functor"

definition "to_cat = r_to_cat o Rep_functor"

definition "from_cat = r_from_cat o Rep_functor"

interpretation "functor" "from_cat c" "to_cat c" "ob_map c" "ar_map c"
  apply (insert Rep_functor[where x=c], clarsimp) 
  by (simp add: ob_map_def ar_map_def to_cat_def from_cat_def ids_def ob_def) 

context "functor"
begin

definition "f_witness = Abs_functor (Functor A B obj_map arr_map)"

lemma A_witness[simp]: "from_cat (local.f_witness) = A"
  using local.functor_axioms
  by (clarsimp simp: from_cat_def local.f_witness_def Abs_functor_inverse)

lemma B_witness[simp]: "to_cat (local.f_witness) = B"
  using local.functor_axioms
  by (clarsimp simp: to_cat_def local.f_witness_def Abs_functor_inverse)

lemma ar_map_witness[simp]: "ar_map (local.f_witness) = arr_map"
  using local.functor_axioms
  by (clarsimp simp: ar_map_def local.f_witness_def Abs_functor_inverse)


lemma ob_map_witness[simp]: "ob_map (local.f_witness) = obj_map"
  using local.functor_axioms
  by (clarsimp simp: ob_map_def local.f_witness_def Abs_functor_inverse)

end


locale functor_composition = f: "functor" A B obj_map arr_map + g: "functor" B C obj_map' arr_map' for A B C obj_map arr_map obj_map' arr_map' 
begin


sublocale "functor" A C "obj_map \<Zcomp> obj_map'" "arr_map \<Zcomp> arr_map'"
  apply (unfold_locales; clarsimp?)
    apply (rule typ_judgI; (clarsimp cong: Sigma_cong)? )
  sorry
end

interpretation functor_composition "from_cat A" "to_cat A" "to_cat B" "ob_map A" "ar_map A" "ob_map B" "ar_map B"
  apply (unfold_locales)


interpretation cat: category "UNIV :: ('a, 'b) category set" "UNIV :: ('a, 'b, 'a ,'b) functor set" "(\<lambda>x!. from_cat x)" "(\<lambda>x!. to_cat x)" _ "(\<lambda>x!. identity_functor.f_witness x) "
  
  

end