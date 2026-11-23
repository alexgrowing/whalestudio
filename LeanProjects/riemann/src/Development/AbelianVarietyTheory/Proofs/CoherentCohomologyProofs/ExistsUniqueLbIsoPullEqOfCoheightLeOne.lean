import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

section Functions

variable {X Y : Scheme.{u}}

theorem ringKrullDim_stalk_le_one_iff (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 ↔ Order.coheight x ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Iff.rfl

theorem coheight_apply_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    Order.coheight (f y) = Order.coheight y := by
  have := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
  exact_mod_cast this

theorem genericPoint_mem_opens [IsIntegral X] (W : X.Opens) [h : Nonempty W] :
    genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)

theorem coheight_genericPoint [IsIntegral X] : Order.coheight (genericPoint X) = 0 := by
  have := ringKrullDim_eq_zero_of_isField (Field.toIsField X.functionField)
  rw [Scheme.functionField, ringKrullDim_stalk_eq_coheight] at this
  exact_mod_cast this

theorem germToFunctionField_mem_range_stalk [IsIntegral X] (V : X.Opens) [Nonempty V]
    (s : Γ(X, V)) {x : X} (hx : x ∈ V) :
    X.germToFunctionField V s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  ⟨X.presheaf.germ V x hx s, X.presheaf.germ_stalkSpecializes_apply hx _ s⟩

theorem germToFunctionField_res [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    X.germToFunctionField W (X.presheaf.map (homOfLE h).op s) = X.germToFunctionField V s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

theorem exists_germToFunctionField_eq_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (V : X.Opens) [Nonempty V] (t : X.functionField)
    (h : ∀ x ∈ V, Order.coheight x = 1 →
      t ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx ↦ ?_
  obtain ⟨_, ⟨(W : X.Opens), hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  obtain ⟨s, hs⟩ : t ∈ (algebraMap Γ(X, W) X.functionField).range := by
    refine (mem_range_algebraMap_iff_forall_height_eq_one t).mpr fun p hp h1 ↦ ?_
    have hy : hW.fromSpec ⟨p, hp⟩ ∈ W := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨_, rfl⟩
    let y : W := ⟨_, hy⟩
    let : Algebra Γ(X, W) (X.presheaf.stalk y.1) := X.presheaf.algebra_section_stalk y
    have : IsLocalization.AtPrime (X.presheaf.stalk y.1) p := hW.isLocalization_stalk' ⟨p, hp⟩ hy
    have := functionField_isScalarTower X W y
    refine (mem_range_algebraMap_iff_mem_primeLocalSubalgebra p (X.presheaf.stalk y.1) t).mp
      (h _ (hWV hy) ?_)
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk y.1)
    rw [ringKrullDim_stalk_eq_coheight, h1] at e
    exact_mod_cast e
  exact ⟨W, inferInstance, s, hxW, hWV, hs⟩

theorem exists_germToFunctionField_eq_iff_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (V : X.Opens) [Nonempty V] (t : X.functionField) :
    (∃ s : Γ(X, V), X.germToFunctionField V s = t) ↔ ∀ x ∈ V, Order.coheight x = 1 →
      t ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  ⟨fun ⟨s, hs⟩ _ hx _ ↦ hs ▸ germToFunctionField_mem_range_stalk V s hx,
    exists_germToFunctionField_eq_of_coheight_eq_one V t⟩

theorem bijective_res_of_eq_bot {V W : X.Opens} (h : W ≤ V) (hV : V = ⊥) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  obtain rfl : W = V := le_antisymm h (hV ▸ bot_le)
  rw [show (homOfLE h).op = 𝟙 _ from rfl, X.presheaf.map_id]
  exact Function.bijective_id

theorem bijective_res_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] {V W : X.Opens} (h : W ≤ V) [Nonempty W]
    (hW : ∀ x ∈ V, Order.coheight x = 1 → x ∈ W) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  have : Nonempty V := ⟨⟨_, h (genericPoint_mem_opens W)⟩⟩
  refine ⟨map_injective_of_isIntegral X (homOfLE h), fun s ↦ ?_⟩
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V
    (X.germToFunctionField W s) fun x hx h1 ↦ germToFunctionField_mem_range_stalk W s (hW x hx h1)
  exact ⟨t, X.germToFunctionField_injective W ((germToFunctionField_res h t).trans ht)⟩

theorem bijective_app_iff_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) :
    Function.Bijective (f.app V).hom ↔
      Function.Bijective (X.presheaf.map
        (homOfLE (inf_le_left : V ⊓ f.opensRange ≤ V)).op).hom := by
  have := f.isIso_app (V ⊓ f.opensRange) inf_le_right
  have hb : Function.Bijective (f.app (V ⊓ f.opensRange)).hom :=
    ConcreteCategory.bijective_of_isIso _
  have he : f ⁻¹ᵁ (V ⊓ f.opensRange) = f ⁻¹ᵁ V :=
    le_antisymm (fun _ h ↦ h.1) fun y h ↦ ⟨h, y, rfl⟩
  have hb' : Function.Bijective (Y.presheaf.map (eqToHom he).op).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [← hb.of_comp_iff', ← hb'.of_comp_iff', ← RingHom.coe_comp, ← RingHom.coe_comp,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, f.naturality]
  rfl

theorem bijective_app_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (hf : ∀ x : X, Order.coheight x = 1 → x ∈ Set.range f) (V : X.Opens) :
    Function.Bijective (f.app V).hom := by
  rw [bijective_app_iff_of_isOpenImmersion]
  by_cases hV : V = ⊥
  · exact bijective_res_of_eq_bot _ hV
  have : Nonempty V := ((Opens.ne_bot_iff_nonempty _).mp hV).to_subtype
  have : Nonempty f.opensRange := ⟨⟨f (Nonempty.some inferInstance), _, rfl⟩⟩
  have : Nonempty (V ⊓ f.opensRange : X.Opens) :=
    ⟨⟨_, genericPoint_mem_opens V, genericPoint_mem_opens f.opensRange⟩⟩
  exact bijective_res_of_coheight_eq_one _ fun x hx h1 ↦ ⟨hx, hf x h1⟩

theorem bijective_app_of_coheight_le_one [IsLocallyNoetherian X] [IsNormalScheme X]
    (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) (V : X.Opens) :
    Function.Bijective (f.app V).hom := by
  let B : (Σ Z : irreducibleComponents X, (IsNormalScheme.component Z).toScheme.Opens) → X.Opens :=
    fun p ↦ (IsNormalScheme.component p.1).ι ''ᵁ p.2
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro O x hx
    let Z : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
    refine ⟨_, ⟨⟨Z, (IsNormalScheme.component Z).ι ⁻¹ᵁ O⟩, rfl⟩,
      ⟨⟨x, mem_irreducibleComponent⟩, hx, rfl⟩, Scheme.Hom.image_preimage_le _ _⟩
  let φ : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj Y.sheaf := ⟨f.c⟩
  have hφ : IsIso φ := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis hB fun ⟨Z, O⟩ ↦ ?_
    have hf' : ∀ x : (IsNormalScheme.component Z).toScheme, Order.coheight x ≤ 1 →
        x ∈ Set.range (f ∣_ IsNormalScheme.component Z) := fun x hx ↦ by
      obtain ⟨y, hy⟩ := hf ((IsNormalScheme.component Z).ι x)
        (by rwa [coheight_apply_of_isOpenImmersion])
      refine ⟨⟨y, ?_⟩, Subtype.ext ?_⟩
      · change f y ∈ IsNormalScheme.component Z
        rw [hy]
        exact x.2
      · exact (morphismRestrict_base_coe f _ _).trans hy
    have : Nonempty (f ⁻¹ᵁ IsNormalScheme.component Z).toScheme := by
      obtain ⟨y, -⟩ := hf' (genericPoint _) (by simp [coheight_genericPoint])
      exact ⟨y⟩
    have hb := bijective_app_of_coheight_eq_one (f ∣_ IsNormalScheme.component Z)
      (fun x hx ↦ hf' x hx.le) O
    have : IsIso ((f ∣_ IsNormalScheme.component Z).app O) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hb
    rw [morphismRestrict_app] at this
    exact (@isIso_comp_right_iff _ _ _ _ _ (f.app _) _ (Functor.map_isIso Y.presheaf _)).mp this
  have : IsIso f.c := @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) φ hφ
  exact ConcreteCategory.bijective_of_isIso (f.c.app (op V))

theorem bijective_res_inf_of_coheight_le_one [IsLocallyNoetherian X] [IsNormalScheme X]
    {U : X.Opens} (hU : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U) (V : X.Opens) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op).hom := by
  have := (bijective_app_iff_of_isOpenImmersion U.ι V).mp
    (bijective_app_of_coheight_le_one U.ι (fun x hx ↦ by simpa using hU x hx) V)
  have key : ∀ U' : X.Opens, U' = U → Function.Bijective
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U' ≤ V)).op).hom → Function.Bijective
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op).hom := by
    rintro _ rfl h
    exact h
  exact key _ U.opensRange_ι this

end Functions

section Charts

open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y : Scheme.{u}}

theorem res_appLE_apply (f : Y ⟶ X) {V : X.Opens} {W W' : Y.Opens} (e : W ≤ f ⁻¹ᵁ V) (h : W' ≤ W)
    (s : Γ(X, V)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE V W e).hom s) =
      (f.appLE V W' (h.trans e)).hom s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res_apply (f : Y ⟶ X) {V V' : X.Opens} {W : Y.Opens} (h : V' ≤ V)
    (e : W ≤ f ⁻¹ᵁ V') (s : Γ(X, V)) :
    (f.appLE V' W e).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (f.appLE V W (e.trans (f.preimage_mono h))).hom s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem bijective_appLE_of_eq (f : Y ⟶ X) {V : X.Opens} {W : Y.Opens} (h : W = f ⁻¹ᵁ V)
    (hf : Function.Bijective (f.app V).hom) : Function.Bijective (f.appLE V W h.le).hom := by
  subst h
  rwa [← Scheme.Hom.app_eq_appLE]

theorem injective_appLE_of_eq (f : Y ⟶ X) {V : X.Opens} {W : Y.Opens} (h : W = f ⁻¹ᵁ V)
    (hf : Function.Injective (f.app V).hom) : Function.Injective (f.appLE V W h.le).hom := by
  subst h
  rwa [← Scheme.Hom.app_eq_appLE]

theorem existsUnique_sec_of_charts (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    {L : LB X} {L' : LB Y} (e : L'.ι ≃ L.ι) (hU : ∀ j, L'.U j = f ⁻¹ᵁ L.U (e j))
    (hg : ∀ i j, (L'.g i j).val = (f.appLE (L.U (e i) ⊓ L.U (e j)) (L'.U i ⊓ L'.U j)
      (inf_le_inf (hU i).le (hU j).le)).hom (L.g (e i) (e j)).val) (s : L'.Sec) :
    ∃! t : L.Sec, ∀ j, (f.appLE (L.U (e j)) (L'.U j) (hU j).le).hom (t.f (e j)) = s.f j := by
  have hb (j) := bijective_appLE_of_eq f (hU j) (hf _)
  choose a ha using fun j ↦ (hb j).2 (s.f j)
  let t : ∀ i, Γ(X, L.U i) := e.piCongrLeft (fun i ↦ Γ(X, L.U i)) a
  have ht (j) : t (e j) = a j := e.piCongrLeft_apply_apply (fun i ↦ Γ(X, L.U i)) a j
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun j ↦ by rw [← ha, ← ht], fun t' ht' ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    apply (bijective_appLE_of_eq f (V := L.U (e i) ⊓ L.U (e j)) (W := L'.U i ⊓ L'.U j)
      (by rw [hU, hU]; rfl) (hf _)).1
    have := s.compat i j
    rw [← ha, ← ha, res_appLE_apply, res_appLE_apply, hg] at this
    rw [map_mul, appLE_res_apply, appLE_res_apply, ht, ht]
    exact this
  · cases t' with | mk t' _ => ?_
    congr 1
    funext i
    obtain ⟨i, rfl⟩ := e.surjective i
    exact (hb i).1 ((ht' i).trans (by rw [ht, ha]))

theorem existsUnique_gen_of_charts (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    {L : LB X} {L' : LB Y} (e : L'.ι ≃ L.ι) (hU : ∀ j, L'.U j = f ⁻¹ᵁ L.U (e j))
    (hg : ∀ i j, (L'.g i j).val = (f.appLE (L.U (e i) ⊓ L.U (e j)) (L'.U i ⊓ L'.U j)
      (inf_le_inf (hU i).le (hU j).le)).hom (L.g (e i) (e j)).val) (s : L'.Gen) (hs : s.IsGen) :
    ∃! t : L.Gen, t.IsGen ∧
      ∀ j, (f.appLE (L.U (e j)) (L'.U j) (hU j).le).hom (t.s (e j)).val = (s.s j).val := by
  obtain ⟨t, ht, hu⟩ := existsUnique_sec_of_charts f hf e hU hg
    ⟨fun j ↦ (s.s j).val, fun i j ↦ congrArg Units.val (hs i j)⟩
  have hunit (i) : IsUnit (t.f i) := by
    obtain ⟨i, rfl⟩ := e.surjective i
    have hb := bijective_appLE_of_eq f (hU i) (hf _)
    refine (MulEquiv.isUnit_map (RingEquiv.ofBijective _ hb)).mp ?_
    rw [RingEquiv.ofBijective_apply, ht]
    exact (s.s i).isUnit
  refine ⟨⟨fun i ↦ (hunit i).unit⟩, ⟨fun i j ↦ Units.ext (t.compat i j), ht⟩, ?_⟩
  rintro ⟨t'⟩ ⟨h1, h2⟩
  have := hu ⟨fun j ↦ (t' j).val, fun i j ↦ congrArg Units.val (h1 i j)⟩ h2
  congr 1
  funext i
  exact Units.ext (congrArg (fun z : L.Sec ↦ z.f i) this)

theorem lb_pull_U (L : LB X) (f : Y ⟶ X) (j : PUnit.{u + 1} → L.ι) :
    (L.pull f).U j = f ⁻¹ᵁ L.U (j PUnit.unit) :=
  le_antisymm (LB.wchart_le L (K := PUnit) (fun _ ↦ f) j PUnit.unit)
    fun _ hy ↦ Set.mem_iInter.mpr fun _ ↦ hy

theorem lb_pull_g (L : LB X) (f : Y ⟶ X) (i j : PUnit.{u + 1} → L.ι) :
    ((L.pull f).g i j).val =
      (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ((L.pull f).U i ⊓ (L.pull f).U j)
        (inf_le_inf (lb_pull_U L f i).le (lb_pull_U L f j).le)).hom
        (L.g (i PUnit.unit) (j PUnit.unit)).val :=
  congrArg Units.val (LB.lcg_pull L f i j)

noncomputable def lbSecPull (L : LB X) (s : L.Sec) (f : Y ⟶ X) : (L.pull f).Sec where
  f j := (f.appLE (L.U (j PUnit.unit)) ((L.pull f).U j) (lb_pull_U L f j).le).hom
    (s.f (j PUnit.unit))
  compat i j := by
    rw [res_appLE_apply, res_appLE_apply, lb_pull_g L f i j]
    have := congrArg (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
      ((L.pull f).U i ⊓ (L.pull f).U j)
      (inf_le_inf (lb_pull_U L f i).le (lb_pull_U L f j).le)).hom
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at this
    exact (appLE_res_apply f _ _ _).symm.trans
      (this.trans (congrArg (_ * ·) (appLE_res_apply f _ _ _)))

theorem lbSecPull_f (L : LB X) (s : L.Sec) (f : Y ⟶ X) (j : PUnit.{u + 1} → L.ι) :
    (lbSecPull L s f).f j =
      (f.appLE (L.U (j PUnit.unit)) ((L.pull f).U j) (lb_pull_U L f j).le).hom
        (s.f (j PUnit.unit)) := rfl

theorem lbSec_ext {L : LB X} {s t : L.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s
  cases t
  congr 1
  exact funext h

theorem lbGen_ext {L : LB X} {s t : L.Gen} (h : ∀ i, (s.s i).val = (t.s i).val) : s = t := by
  cases s
  cases t
  congr 1
  exact funext fun i ↦ Units.ext (h i)

theorem genPull_s_val (L : LB X) (c : L.Gen) (f : Y ⟶ X) (j : PUnit.{u + 1} → L.ι) :
    ((L.genPull c f).s j).val =
      (f.appLE (L.U (j PUnit.unit)) ((L.pull f).U j) (lb_pull_U L f j).le).hom
        (c.s (j PUnit.unit)).val := rfl

theorem bijective_lbSecPull (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom) (L : LB X) :
    Function.Bijective fun s : L.Sec ↦ lbSecPull L s f := by
  refine (Function.bijective_iff_existsUnique _).mpr fun s ↦ ?_
  refine (existsUnique_congr fun t ↦ ?_).mp (existsUnique_sec_of_charts f hf (L := L)
    (L' := L.pull f) (Equiv.funUnique PUnit L.ι) (lb_pull_U L f) (lb_pull_g L f) s)
  exact ⟨fun h ↦ lbSec_ext h, fun h j ↦ congrArg (fun z : (L.pull f).Sec ↦ z.f j) h⟩

theorem existsUnique_genPull_eq (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    (L : LB X) (r : (L.pull f).Gen) (hr : r.IsGen) :
    ∃! t : L.Gen, t.IsGen ∧ L.genPull t f = r := by
  refine (existsUnique_congr fun t ↦ and_congr_right fun _ ↦ ?_).mp
    (existsUnique_gen_of_charts f hf (L := L)
      (L' := L.pull f) (Equiv.funUnique PUnit L.ι) (lb_pull_U L f) (lb_pull_g L f) r hr)
  exact ⟨fun h ↦ lbGen_ext h, fun h j ↦ congrArg (fun z : (L.pull f).Gen ↦ (z.s j).val) h⟩

noncomputable abbrev lbIsoPull {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X) :
    LB.Iso (L.pull f) (M.pull f) :=
  LB.linCombIso w (K := PUnit) (fun _ ↦ f) (fun _ ↦ 1)

theorem lb_div_pull_U (L M : LB X) (f : Y ⟶ X)
    (p : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((M.pull f).div (L.pull f)).U p = f ⁻¹ᵁ (M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit) :=
  congrArg₂ (· ⊓ ·) (lb_pull_U M f p.1) (lb_pull_U L f p.2)

theorem lb_div_pull_g (L M : LB X) (f : Y ⟶ X)
    (p q : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((M.pull f).div (L.pull f)).g p q =
      res (inf_le_inf (lb_div_pull_U L M f p).le (lb_div_pull_U L M f q).le)
        (pullU f ((M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit) ⊓
            (M.div L).U (q.1 PUnit.unit, q.2 PUnit.unit))
          ((M.div L).g (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit))) := by
  have key : ∀ {a b a' b' : X.Opens} {c d c' d' : Y.Opens}
      (h₁ : c ⊓ c' ≤ f ⁻¹ᵁ (a ⊓ a')) (h₂ : d ⊓ d' ≤ f ⁻¹ᵁ (b ⊓ b'))
      (h₃ : c ⊓ d ⊓ (c' ⊓ d') ≤ f ⁻¹ᵁ (a ⊓ b ⊓ (a' ⊓ b'))) (x : Γ(X, a ⊓ a')ˣ) (y : Γ(X, b ⊓ b')ˣ)
      (x' : Γ(Y, c ⊓ c')ˣ) (y' : Γ(Y, d ⊓ d')ˣ),
      x' = res h₁ (pullU f _ x) →
      y' = res h₂ (pullU f _ y) →
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          c ⊓ d ⊓ (c' ⊓ d') ≤ c ⊓ c') x' *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          c ⊓ d ⊓ (c' ⊓ d') ≤ d ⊓ d') y')⁻¹ =
      res h₃ (pullU f _
        (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          a ⊓ b ⊓ (a' ⊓ b') ≤ a ⊓ a') x *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          a ⊓ b ⊓ (a' ⊓ b') ≤ b ⊓ b') y)⁻¹)) := by
    rintro a b a' b' c d c' d' h₁ h₂ h₃ x y _ _ rfl rfl
    simp only [map_mul, map_inv, LB.pullU_res, LB.res_res]
  exact key _ _ _ _ _ _ _ (LB.lcg_pull M f p.1 q.1) (LB.lcg_pull L f p.2 q.2)

theorem lbIsoPull_s_val {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X)
    (p : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((lbIsoPull w f).s p).val =
      (f.appLE ((M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit)) (((M.pull f).div (L.pull f)).U p)
        (lb_div_pull_U L M f p).le).hom (w.s (p.1 PUnit.unit, p.2 PUnit.unit)).val := by
  simp only [lbIsoPull, LB.linCombIso, zpow_one]
  exact congrArg Units.val (Fintype.prod_unique _)

theorem existsUnique_lbIsoPull_eq (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    (L M : LB X) (w : LB.Iso (L.pull f) (M.pull f)) (hw : w.IsGen) :
    ∃! v : LB.Iso L M, v.IsGen ∧ lbIsoPull v f = w := by
  refine (existsUnique_congr fun t ↦ and_congr_right fun _ ↦ ?_).mp
    (existsUnique_gen_of_charts f hf (L := M.div L) (L' := (M.pull f).div (L.pull f))
      ((Equiv.funUnique PUnit M.ι).prodCongr (Equiv.funUnique PUnit L.ι)) (lb_div_pull_U L M f)
      (fun p q ↦ congrArg Units.val (lb_div_pull_g L M f p q)) w hw)
  exact ⟨fun h ↦ lbGen_ext fun p ↦ (lbIsoPull_s_val t f p).trans (h p),
    fun h p ↦ (lbIsoPull_s_val t f p).symm.trans
      (congrArg (fun z : LB.Iso (L.pull f) (M.pull f) ↦ (z.s p).val) h)⟩

end Charts

section SectionsOnOpens

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y : Scheme.{0}}

theorem resG_resG {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_refl {U : X.Opens} (s : Γ(X, U)) : resG X le_rfl s = s := by
  rw [resG, show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, X.presheaf.map_id]
  rfl

theorem resG_eq_mul_of_injective {A B G T A' B' T' : X.Opens} (hA : T ≤ A) (hB : T ≤ B)
    (hG : T ≤ G) (hA' : A' ≤ A) (hB' : B' ≤ B) (hT : T' ≤ T) (kA : T' ≤ A') (kB : T' ≤ B')
    (hi : Function.Injective (resG X hT)) {a : Γ(X, A)} {b : Γ(X, B)} {g : Γ(X, G)}
    (h : resG X kA (resG X hA' a) = resG X (hT.trans hG) g * resG X kB (resG X hB' b)) :
    resG X hA a = resG X hG g * resG X hB b := by
  apply hi
  simpa only [map_mul, resG_resG] using h

theorem res_mem_secOn {L : LB X} {V W : X.Opens} (h : W ≤ V) {s : ∀ i, Γ(X, V ⊓ L.U i)}
    (hs : s ∈ secOn L V) : (fun i ↦ resG X (inf_le_inf_right _ h) (s i)) ∈ secOn L W := by
  intro i j
  have := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    W ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hs i j)
  simpa only [map_mul, resG_resG] using this

theorem res_sec_mem_secOn {L : LB X} (W : X.Opens) (s : L.Sec) :
    (fun i ↦ resG X inf_le_right (s.f i)) ∈ secOn L W := by
  intro i j
  have := congrArg (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j)) (s.compat i j)
  simpa only [map_mul, resG_resG] using this

theorem bijective_resG_of_coheight_le_one [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {V W : X.Opens} (h : W ≤ V) (hW : ∀ x ∈ V, Order.coheight x ≤ 1 → x ∈ W) :
    Function.Bijective (resG X h) := by
  have hb := bijective_res_inf_of_coheight_le_one (X := V) (U := V.ι ⁻¹ᵁ W)
    (fun x hx ↦ hW _ x.2 (by rwa [← coheight_apply_of_isOpenImmersion V.ι] at hx)) (V.ι ⁻¹ᵁ V)
  have h1 : Function.Bijective (V.ι.app V).hom :=
    have := V.ι.isIso_app V (by simp)
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective (V.ι.appLE W (V.ι ⁻¹ᵁ V ⊓ V.ι ⁻¹ᵁ W) inf_le_right).hom :=
    have := V.ι.isIso_app W (by simpa)
    bijective_appLE_of_eq V.ι (inf_eq_right.mpr (V.ι.preimage_mono h))
      (ConcreteCategory.bijective_of_isIso _)
  rw [← h2.of_comp_iff']
  convert hb.comp h1 using 1
  funext s
  exact appLE_res_apply V.ι h _ s

theorem existsUnique_secOn_of_coheight_le_one [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (L : LB X) {V W : X.Opens} (h : W ≤ V) (hW : ∀ x ∈ V, Order.coheight x ≤ 1 → x ∈ W)
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    ∃! t : ∀ i, Γ(X, V ⊓ L.U i),
      t ∈ secOn L V ∧ ∀ i, resG X (inf_le_inf_right _ h) (t i) = s i := by
  have hb (i) : Function.Bijective (resG X (inf_le_inf_right (L.U i) h)) :=
    bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ⟨hW x hx.1 h1, hx.2⟩
  choose t ht using fun i ↦ (hb i).2 (s i)
  refine ⟨t, ⟨fun i j ↦ ?_, ht⟩, fun t' ht' ↦ funext fun i ↦ (hb i).1 ((ht'.2 i).trans (ht i).symm)⟩
  refine resG_eq_mul_of_injective _ _ _ (inf_le_inf_right _ h) (inf_le_inf_right _ h)
    (inf_le_inf_right _ (inf_le_inf_right _ h) : W ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ?_).1 ?_
  · exact ⟨⟨hW x hx.1.1 h1, hx.1.2⟩, hx.2⟩
  · rw [ht, ht]
    exact hs i j

theorem existsUnique_sec_res_eq_of_coheight_le_one [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (L : LB X) {U : X.Opens} (hU : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U)
    {s : ∀ i, Γ(X, U ⊓ L.U i)} (hs : s ∈ secOn L U) :
    ∃! t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i := by
  have hb (i) : Function.Bijective (resG X (inf_le_right : U ⊓ L.U i ≤ L.U i)) :=
    bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ⟨hU x h1, hx⟩
  choose t ht using fun i ↦ (hb i).2 (s i)
  refine ⟨⟨t, fun i j ↦ ?_⟩, ht, fun t' ht' ↦ lbSec_ext fun i ↦
    (hb i).1 ((ht' i).trans (ht i).symm)⟩
  refine Eq.trans ?_ (congrArg (· * _) (resG_refl _))
  refine resG_eq_mul_of_injective _ _ _ inf_le_right inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (bijective_resG_of_coheight_le_one _ fun x hx h1 ↦ ?_).1 ?_
  · exact ⟨⟨hU x h1, hx.1⟩, hx.2⟩
  · rw [ht, ht]
    exact hs i j

section Integral

variable [IsIntegral X]

theorem nonempty_inf_of_isIntegral (V W : X.Opens) [Nonempty V] [Nonempty W] :
    Nonempty (V ⊓ W : X.Opens) :=
  ⟨⟨_, genericPoint_mem_opens V, genericPoint_mem_opens W⟩⟩

theorem injective_resG_of_inf_le (W : X.Opens) [Nonempty W] {T T' : X.Opens} (h : T' ≤ T)
    (hW : W ⊓ T ≤ T') : Function.Injective (resG X h) := by
  by_cases hT : T = ⊥
  · exact (bijective_res_of_eq_bot h hT).1
  have : Nonempty T := ((Opens.ne_bot_iff_nonempty _).mp hT).to_subtype
  have : Nonempty T' := ⟨⟨_, hW ⟨genericPoint_mem_opens W, genericPoint_mem_opens T⟩⟩⟩
  exact map_injective_of_isIntegral X (homOfLE h)

theorem germToFunctionField_mem_range_stalk_of_secOn {L : LB X} {W : X.Opens}
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) {x : X} {i j : L.ι} (hi : x ∈ L.U i)
    (hj : x ∈ L.U j) [Nonempty (W ⊓ L.U i : X.Opens)] [Nonempty (W ⊓ L.U j : X.Opens)]
    (h : X.germToFunctionField _ (s j) ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    X.germToFunctionField _ (s i) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have : Nonempty (L.U j) := ⟨⟨x, hj⟩⟩
  have : Nonempty (L.U i ⊓ L.U j : X.Opens) := ⟨⟨x, hi, hj⟩⟩
  have := nonempty_inf_of_isIntegral (W ⊓ L.U i) (L.U j)
  have e := congrArg (X.germToFunctionField (W ⊓ L.U i ⊓ L.U j)) (hs i j)
  rw [map_mul] at e
  erw [germToFunctionField_res, germToFunctionField_res, germToFunctionField_res] at e
  rw [e]
  exact mul_mem (germToFunctionField_mem_range_stalk _ _ ⟨hi, hj⟩) h

variable [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]

theorem exists_resG_eq_of_secOn {L : LB X} {W : X.Opens} [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) (i : L.ι) {O : X.Opens} (h : W ⊓ L.U i ≤ O)
    (hO : O ≤ L.U i)
    (H : ∀ x ∈ O, Order.coheight x = 1 → x ∉ W → ∃ (j : L.ι) (_ : Nonempty (W ⊓ L.U j : X.Opens)),
      x ∈ L.U j ∧ X.germToFunctionField (W ⊓ L.U j) (s j) ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ t : Γ(X, O), resG X h t = s i := by
  by_cases hT : O = ⊥
  · exact (bijective_res_of_eq_bot h hT).2 _
  have : Nonempty O := ((Opens.ne_bot_iff_nonempty _).mp hT).to_subtype
  have : Nonempty (W ⊓ L.U i : X.Opens) :=
    ⟨⟨_, genericPoint_mem_opens W, hO (genericPoint_mem_opens O)⟩⟩
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_coheight_eq_one O
    (X.germToFunctionField _ (s i)) fun x hx h1 ↦ by
      by_cases hxW : x ∈ W
      · exact germToFunctionField_mem_range_stalk _ _ ⟨hxW, hO hx⟩
      · obtain ⟨j, _, hj, h⟩ := H x hx h1 hxW
        exact germToFunctionField_mem_range_stalk_of_secOn hs (hO hx) hj h
  exact ⟨t, X.germToFunctionField_injective _ ((germToFunctionField_res h t).trans ht)⟩

theorem exists_secOn_res_eq_iff {L : LB X} (hL : L.IsLB) {V W : X.Opens} (h : W ≤ V) [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    (∃ t ∈ secOn L V, ∀ i, resG X (inf_le_inf_right _ h) (t i) = s i) ↔
      ∀ x ∈ V, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
          X.germToFunctionField (W ⊓ L.U i) (s i) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · rintro ⟨t, -, ht⟩ x hx - -
    obtain ⟨i, hi⟩ := LB.mem_of_cover hL x
    have : Nonempty (L.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (V ⊓ L.U i : X.Opens) := ⟨⟨x, hx, hi⟩⟩
    have := nonempty_inf_of_isIntegral W (L.U i)
    refine ⟨i, this, hi, ?_⟩
    rw [← ht]
    erw [germToFunctionField_res]
    exact germToFunctionField_mem_range_stalk _ _ ⟨hx, hi⟩
  · intro H
    choose t ht using fun i ↦ exists_resG_eq_of_secOn hs i (inf_le_inf_right _ h) inf_le_right
      fun x hx ↦ H x hx.1
    refine ⟨t, fun i j ↦ ?_, ht⟩
    refine resG_eq_mul_of_injective _ _ _ (inf_le_inf_right _ h) (inf_le_inf_right _ h)
      (inf_le_inf_right _ (inf_le_inf_right _ h) : W ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (injective_resG_of_inf_le W _ fun x hx ↦ ⟨⟨hx.1, hx.2.1.2⟩, hx.2.2⟩) ?_
    rw [ht, ht]
    exact hs i j

theorem exists_sec_res_eq_iff {L : LB X} (hL : L.IsLB) {W : X.Opens} [Nonempty W]
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) :
    (∃ t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i) ↔
      ∀ x : X, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
          X.germToFunctionField (W ⊓ L.U i) (s i) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · rintro ⟨t, ht⟩
    exact fun x ↦ (exists_secOn_res_eq_iff hL le_top hs).mp
      ⟨_, res_sec_mem_secOn ⊤ t, fun i ↦ (resG_resG _ _ _).trans (ht i)⟩ x trivial
  · intro H
    choose t ht using fun i ↦ exists_resG_eq_of_secOn hs i inf_le_right le_rfl fun x _ ↦ H x
    refine ⟨⟨t, fun i j ↦ ?_⟩, ht⟩
    refine Eq.trans ?_ (congrArg (· * _) (resG_refl _))
    refine resG_eq_mul_of_injective _ _ _ inf_le_right inf_le_right
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ⊓ L.U i ⊓ L.U j ≤ _) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (injective_resG_of_inf_le W _ fun x hx ↦ ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩) ?_
    rw [ht, ht]
    exact hs i j

omit [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] in

theorem lbSec_eq_of_res_eq {L : LB X} (W : X.Opens) [Nonempty W] {t t' : L.Sec}
    (h : ∀ i, resG X (inf_le_right : W ⊓ L.U i ≤ L.U i) (t.f i) = resG X inf_le_right (t'.f i)) :
    t = t' :=
  lbSec_ext fun i ↦ injective_resG_of_inf_le W _ le_rfl (h i)

end Integral

theorem lb_pull_ι_U (L : LB X) (W : X.Opens) (j : PUnit.{1} → L.ι) :
    (L.pull W.ι).U j = W.ι ⁻¹ᵁ (W ⊓ L.U (j PUnit.unit)) :=
  (lb_pull_U L W.ι j).trans (le_antisymm (fun y hy ↦ ⟨y.2, hy⟩) fun _ hy ↦ hy.2)

theorem bijective_ι_appLE (W : X.Opens) {V : X.Opens} (hV : V ≤ W) {T : W.toScheme.Opens}
    (h : T = W.ι ⁻¹ᵁ V) : Function.Bijective (W.ι.appLE V T h.le).hom :=
  have := W.ι.isIso_app V (by simpa)
  bijective_appLE_of_eq W.ι h (ConcreteCategory.bijective_of_isIso _)

theorem existsUnique_secOn_of_pull (L : LB X) (W : X.Opens) (r : (L.pull W.ι).Sec) :
    ∃! s : ∀ i, Γ(X, W ⊓ L.U i), s ∈ secOn L W ∧ ∀ j : PUnit.{1} → L.ι,
      (W.ι.appLE (W ⊓ L.U (j PUnit.unit)) _ (lb_pull_ι_U L W j).le).hom (s (j PUnit.unit)) =
        r.f j := by
  have hb (j : PUnit.{1} → L.ι) := bijective_ι_appLE W inf_le_left (lb_pull_ι_U L W j)
  choose s hs using fun i : L.ι ↦ (hb fun _ ↦ i).2 (r.f fun _ ↦ i)
  refine ⟨s, ⟨fun i j ↦ ?_, fun j ↦ hs (j PUnit.unit)⟩,
    fun t ht ↦ funext fun i ↦ (hb fun _ ↦ i).1 ((ht.2 fun _ ↦ i).trans (hs i).symm)⟩
  apply (bijective_ι_appLE W (V := W ⊓ L.U i ⊓ L.U j) (inf_le_left.trans inf_le_left)
    (T := (L.pull W.ι).U (fun _ ↦ i) ⊓ (L.pull W.ι).U (fun _ ↦ j))
    (congrArg₂ (· ⊓ ·) (lb_pull_ι_U L W fun _ ↦ i) (lb_pull_U L W.ι fun _ ↦ j))).1
  have := r.compat (fun _ ↦ i) (fun _ ↦ j)
  rw [← hs, ← hs, lb_pull_g L W.ι (fun _ ↦ i) (fun _ ↦ j)] at this
  erw [res_appLE_apply, res_appLE_apply] at this
  rw [map_mul]
  erw [appLE_res_apply, appLE_res_apply, appLE_res_apply]
  exact this

theorem exists_lbSecPull_eq_iff [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {L : LB X} (hL : L.IsLB) {W : X.Opens} [Nonempty W] (r : (L.pull W.ι).Sec) :
    (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
      ∀ x : X, Order.coheight x = 1 → x ∉ W →
        ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)) (a : Γ(X, W ⊓ L.U i)), x ∈ L.U i ∧
          (W.ι.appLE (W ⊓ L.U i) _ (lb_pull_ι_U L W fun _ ↦ i).le).hom a = r.f (fun _ ↦ i) ∧
          X.germToFunctionField (W ⊓ L.U i) a ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have hb (j : PUnit.{1} → L.ι) := bijective_ι_appLE W inf_le_left (lb_pull_ι_U L W j)
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull L W r
  have h1 : (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
      ∃ t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i := by
    refine exists_congr fun t ↦ ⟨fun h i ↦ (hb fun _ ↦ i).1 ?_, fun h ↦ lbSec_ext fun j ↦ ?_⟩
    · refine (appLE_res_apply W.ι _ _ _).trans (Eq.trans ?_ (hr fun _ ↦ i).symm)
      rw [← h]
      rfl
    · refine Eq.trans ?_ (hr j)
      rw [← h]
      exact (appLE_res_apply W.ι _ _ _).symm
  rw [h1, exists_sec_res_eq_iff hL hs]
  refine forall₃_congr fun x _ _ ↦ exists₂_congr fun i _ ↦
    ⟨fun h ↦ ⟨s i, h.1, hr fun _ ↦ i, h.2⟩, fun ⟨a, h1, h2, h3⟩ ↦ ⟨h1, ?_⟩⟩
  rwa [← (hb fun _ ↦ i).1 (h2.trans (hr fun _ ↦ i).symm)]

end SectionsOnOpens

section Main

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem bijective_lbSecPull_of_coheight_le_one {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) (L : LB X) :
    Function.Bijective fun s : L.Sec ↦ lbSecPull L s f :=
  bijective_lbSecPull f (bijective_app_of_coheight_le_one f hf) L

theorem existsUnique_genPull_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) (L : LB X) (r : (L.pull f).Gen)
    (hr : r.IsGen) : ∃! t : L.Gen, t.IsGen ∧ L.genPull t f = r :=
  existsUnique_genPull_eq f (bijective_app_of_coheight_le_one f hf) L r hr

theorem existsUnique_lbIsoPull_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) (L M : LB X)
    (w : LB.Iso (L.pull f) (M.pull f)) (hw : w.IsGen) :
    ∃! v : LB.Iso L M, v.IsGen ∧ lbIsoPull v f = w :=
  existsUnique_lbIsoPull_eq f (bijective_app_of_coheight_le_one f hf) L M w hw

theorem lbIso_pull_iff {X Y : Scheme.{0}} (f : Y ⟶ X) (hf : ∀ V, Function.Bijective (f.app V).hom)
    (L M : LB X) : LBIso (L.pull f) (M.pull f) ↔ LBIso L M :=
  ⟨fun ⟨w, hw⟩ ↦ let ⟨v, hv, _⟩ := existsUnique_lbIsoPull_eq f hf L M w hw; ⟨v, hv.1⟩,
    fun ⟨v, hv⟩ ↦ ⟨lbIsoPull v f, DVR.linCombIso_isGen v hv _ _⟩⟩

theorem extension_over_codim_two (X : Scheme.{0}) [IsLocallyNoetherian X]
    (hX : Geo.Tor.IsNormalScheme X) :
    (∀ U : X.Opens, (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U) →
      (∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ U ≤ V))) ∧
      (∀ (L : LB X) (r : (L.pull U.ι).Sec), ∃! t : L.Sec, lbSecPull L t U.ι = r) ∧
      (∀ (L : LB X) (V : X.Opens), ∀ s ∈ secOn L (V ⊓ U), ∃! t : ∀ i, Γ(X, V ⊓ L.U i),
        t ∈ secOn L V ∧ ∀ i, resG X (inf_le_inf_right _ inf_le_left) (t i) = s i) ∧
      (∀ (L : LB X) (r : (L.pull U.ι).Gen), r.IsGen →
        ∃! t : L.Gen, t.IsGen ∧ L.genPull t U.ι = r) ∧
      (∀ (L M : LB X) (w : LB.Iso (L.pull U.ι) (M.pull U.ι)), w.IsGen →
        ∃! v : LB.Iso L M, v.IsGen ∧
          LB.linCombIso v (K := PUnit) (fun _ ↦ U.ι) (fun _ ↦ 1) = w) ∧
      (∀ L M : LB X, LBIso (L.pull U.ι) (M.pull U.ι) ↔ LBIso L M)) ∧
    (∀ x : X, Order.coheight x = 1 →
      ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x)) ∧
    (∀ [IsIntegral X] (L : LB X), L.IsLB → ∀ (W : X.Opens) [Nonempty W],
      (∀ s ∈ secOn L W, (∃! t : L.Sec, ∀ i, resG X inf_le_right (t.f i) = s i) ↔
        ∀ x : X, Order.coheight x = 1 → x ∉ W →
          ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)), x ∈ L.U i ∧
            X.germToFunctionField (W ⊓ L.U i) (s i) ∈
              (algebraMap (X.presheaf.stalk x) X.functionField).range) ∧
      (∀ r : (L.pull W.ι).Sec, (∃ t : L.Sec, lbSecPull L t W.ι = r) ↔
        ∀ x : X, Order.coheight x = 1 → x ∉ W →
          ∃ (i : L.ι) (_ : Nonempty (W ⊓ L.U i : X.Opens)) (a : Γ(X, W ⊓ L.U i)), x ∈ L.U i ∧
            (W.ι.appLE (W ⊓ L.U i) _ (lb_pull_ι_U L W fun _ ↦ i).le).hom a = r.f (fun _ ↦ i) ∧
            X.germToFunctionField (W ⊓ L.U i) a ∈
              (algebraMap (X.presheaf.stalk x) X.functionField).range)) := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine ⟨fun U hU ↦ ?_, fun x hx ↦ ⟨inferInstance,
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hx⟩,
    fun L hL W _ ↦ ⟨fun s hs ↦ ?_, exists_lbSecPull_eq_iff hL⟩⟩
  · have hU' : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U := fun x hx ↦
      hU x ((ringKrullDim_stalk_le_one_iff x).mpr hx)
    have hf := bijective_app_of_coheight_le_one U.ι fun x hx ↦ by simpa using hU' x hx
    exact ⟨bijective_res_inf_of_coheight_le_one hU',
      fun L ↦ (Function.bijective_iff_existsUnique _).mp (bijective_lbSecPull U.ι hf L),
      fun L V s hs ↦ existsUnique_secOn_of_coheight_le_one L inf_le_left
        (fun x hx h1 ↦ ⟨hx, hU' x h1⟩) hs,
      existsUnique_genPull_eq U.ι hf, existsUnique_lbIsoPull_eq U.ι hf, lbIso_pull_iff U.ι hf⟩
  · rw [← exists_sec_res_eq_iff hL hs]
    exact ⟨ExistsUnique.exists, fun ⟨t, ht⟩ ↦ ⟨t, ht, fun t' ht' ↦
      lbSec_eq_of_res_eq W fun i ↦ (ht' i).trans (ht i).symm⟩⟩

example : ∃ (X : Scheme.{0}) (_ : IsIntegral X) (_ : IsLocallyNoetherian X)
    (_ : Geo.Tor.IsNormalScheme X) (U : X.Opens), U ≠ ⊤ ∧
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U := by
  obtain ⟨m, hm, h1⟩ : ∃ m : Ideal (Polynomial ℤ), m.IsMaximal ∧ ¬ m.height ≤ 1 := by
    by_contra! H
    have h := (ringKrullDim_le_iff_isMaximal_height_le (R := Polynomial ℤ) 1).mpr
      fun m hm ↦ by exact_mod_cast H m hm
    rw [Polynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at h
    exact absurd h (by decide)
  let x : Spec (.of (Polynomial ℤ)) := ⟨m, hm.isPrime⟩
  have hc : IsClosed {x} := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr hm
  refine ⟨Spec (.of (Polynomial ℤ)), inferInstance, inferInstance, GlobalTheory.IsNormalScheme.pred _,
    ⟨{x}ᶜ, hc.isOpen_compl⟩, fun h ↦ ?_, fun y hy hyx ↦ h1 ?_⟩
  · have : x ∈ (⟨{x}ᶜ, hc.isOpen_compl⟩ : (Spec (.of (Polynomial ℤ))).Opens) := h ▸ trivial
    exact this rfl
  · rw [show y = x from hyx, ringKrullDim_stalk_le_one_iff, ← idealHeight_eq_coheight] at hy
    exact hy

end Main

end GlobalTheory
