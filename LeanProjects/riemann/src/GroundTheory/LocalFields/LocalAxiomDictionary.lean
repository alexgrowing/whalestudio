import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.LocalAxiomTransport

namespace GroundTheory.LocalField

open Abstract IntermediateField

section Embeddings

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem algebraMap_norm_eq_prod_embeddings_of_splits
    (hL : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits) (x : L) :
    haveI : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
    algebraMap K Ω (Algebra.norm K x) = ∏ τ : L →ₐ[K] Ω, τ x := by
  classical
  let _ : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
  let ι : Ω →ₐ[K] AlgebraicClosure Ω := IsScalarTower.toAlgHom K Ω (AlgebraicClosure Ω)
  let c : (L →ₐ[K] Ω) → (L →ₐ[K] AlgebraicClosure Ω) := fun τ => ι.comp τ
  have hc : Function.Injective c := fun τ τ' h =>
    AlgHom.ext fun y => ι.toRingHom.injective (AlgHom.congr_fun h y)
  have hcard : Nat.card (L →ₐ[K] Ω) = Nat.card (L →ₐ[K] AlgebraicClosure Ω) := by
    rw [AlgHom.natCard_of_splits K L Ω hL, AlgHom.natCard_of_splits K L _
      (fun _ => IsAlgClosed.splits _)]
  have hbij : Function.Bijective c := by
    refine (Function.Injective.bijective_of_nat_card_le hc hcard.ge)
  apply ι.toRingHom.injective
  change ι (algebraMap K Ω _) = ι (∏ τ : L →ₐ[K] Ω, τ x)
  rw [AlgHom.commutes, map_prod, Algebra.norm_eq_prod_embeddings K (AlgebraicClosure Ω) x]
  exact (Fintype.prod_bijective c hbij _ _ fun τ => rfl).symm

end Embeddings

section Fields

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

local notation "G" => Ω ≃ₐ[K] Ω

def fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] : OpenSubgroup G :=
  ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen⟩

@[simp]
theorem coe_fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (fixingOpenSubgroup L : Subgroup G) = L.fixingSubgroup :=
  rfl

variable [IsGalois K Ω]

theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup G) :
    (fixedField (U : Subgroup G)).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField (⟨(U : Subgroup G), U.isClosed⟩ : ClosedSubgroup G)

instance finiteDimensional_fixedField_openSubgroup (U : OpenSubgroup G) :
    FiniteDimensional K (fixedField (U : Subgroup G)) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)

theorem fixedField_fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    fixedField (fixingOpenSubgroup L : Subgroup G) = L :=
  InfiniteGalois.fixedField_fixingSubgroup L

theorem fixingOpenSubgroup_fixedField (U : OpenSubgroup G) :
    fixingOpenSubgroup (fixedField (U : Subgroup G)) = U :=
  OpenSubgroup.ext fun σ => by
    rw [← OpenSubgroup.mem_toSubgroup, coe_fixingOpenSubgroup,
      fixingSubgroup_fixedField_openSubgroup]
    rfl

theorem fixingSubgroup_le_fixingSubgroup_iff {L L' : IntermediateField K Ω} :
    L.fixingSubgroup ≤ L'.fixingSubgroup ↔ L' ≤ L := by
  constructor
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, ← InfiniteGalois.fixedField_fixingSubgroup L']
    exact IntermediateField.fixedField_antitone h
  · intro h
    exact IntermediateField.fixingSubgroup_antitone h

theorem mem_iff_forall_fixingSubgroup (L : IntermediateField K Ω) (x : Ω) :
    x ∈ L ↔ ∀ σ ∈ L.fixingSubgroup, σ x = x := by
  conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  rw [IntermediateField.mem_fixedField_iff]

end Fields

section Units

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω

omit [IsGalois K Ω] in

theorem mem_fixedModule_units_iff' (H : Subgroup G) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ H ↔ ∀ σ ∈ H, σ (a : Ω) = a := by
  rw [mem_fixedModule]
  refine forall₂_congr fun σ _ => ?_
  rw [Units.ext_iff]
  rfl

def unitsEquivOfForall {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) :
    fixedModule Ωˣ H ≃* Fˣ where
  toFun a :=
    ⟨⟨((a : Ωˣ) : Ω), (hF _).2 ((mem_fixedModule_units_iff' H a).1 a.2)⟩,
      ⟨((a⁻¹ : fixedModule Ωˣ H) : Ωˣ), (hF _).2 ((mem_fixedModule_units_iff' H _).1 (a⁻¹).2)⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  invFun u := ⟨Units.map (algebraMap F Ω : F →* Ω) u,
    (mem_fixedModule_units_iff' H _).2 ((hF _).1 (by simp))⟩
  left_inv a := by
    ext
    rfl
  right_inv u := by
    ext
    rfl
  map_mul' a b := by
    ext
    rfl

omit [IsGalois K Ω] in
@[simp]
theorem coe_unitsEquivOfForall {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) (a : fixedModule Ωˣ H) :
    (((unitsEquivOfForall H F hF a : Fˣ) : F) : Ω) = ((a : Ωˣ) : Ω) :=
  rfl

omit [IsGalois K Ω] in
@[simp]
theorem coe_unitsEquivOfForall_symm {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) (u : Fˣ) :
    ((((unitsEquivOfForall H F hF).symm u : fixedModule Ωˣ H) : Ωˣ) : Ω) = ((u : F) : Ω) :=
  rfl

theorem mem_fixedModule_units_iff (L : IntermediateField K Ω) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ L.fixingSubgroup ↔ (a : Ω) ∈ L := by
  rw [mem_iff_forall_fixingSubgroup, mem_fixedModule]
  refine forall₂_congr fun σ _ => ?_
  rw [Units.ext_iff]
  rfl

def fixedModuleUnitsEquiv (L : IntermediateField K Ω) : fixedModule Ωˣ L.fixingSubgroup ≃* Lˣ :=
  unitsEquivOfForall L.fixingSubgroup L (mem_iff_forall_fixingSubgroup L)

@[simp]
theorem coe_fixedModuleUnitsEquiv (L : IntermediateField K Ω)
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((fixedModuleUnitsEquiv L a : Lˣ) : L) : Ω) = ((a : Ωˣ) : Ω) :=
  rfl

@[simp]
theorem coe_fixedModuleUnitsEquiv_symm (L : IntermediateField K Ω) (u : Lˣ) :
    ((((fixedModuleUnitsEquiv L).symm u : fixedModule Ωˣ L.fixingSubgroup) : Ωˣ) : Ω) =
      ((u : L) : Ω) :=
  rfl

noncomputable def baseUnitsEquiv : fixedModule Ωˣ (⊤ : Subgroup G) ≃* Kˣ :=
  (MulEquiv.subgroupCongr (by rw [IntermediateField.fixingSubgroup_bot])).trans <|
    (fixedModuleUnitsEquiv (⊥ : IntermediateField K Ω)).trans
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).toMulEquiv)

omit [IsGalois K Ω] in
theorem algebraMap_botEquiv (y : (⊥ : IntermediateField K Ω)) :
    algebraMap K Ω (IntermediateField.botEquiv K Ω y) = (y : Ω) := by
  conv_rhs => rw [← (IntermediateField.botEquiv K Ω).symm_apply_apply y]
  rw [IntermediateField.botEquiv_symm]
  rfl

@[simp]
theorem algebraMap_baseUnitsEquiv (a : fixedModule Ωˣ (⊤ : Subgroup G)) :
    algebraMap K Ω (baseUnitsEquiv a : Kˣ) = ((a : Ωˣ) : Ω) := by
  simp only [baseUnitsEquiv, MulEquiv.trans_apply, Units.coe_mapEquiv]
  exact algebraMap_botEquiv _

theorem isDiscreteModule_units : IsDiscreteModule G Ωˣ := by
  rw [isDiscreteModule_iff]
  intro a
  have : FiniteDimensional K (IntermediateField.adjoin K {(a : Ω)}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  exact ⟨fixingOpenSubgroup (IntermediateField.adjoin K {(a : Ω)}),
    (mem_fixedModule_units_iff _ a).2 (IntermediateField.subset_adjoin K _ rfl)⟩

end Units

section Norm

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω

variable (L : IntermediateField K Ω)

def restrictEmbedding (σ : G) : L →ₐ[K] Ω :=
  (σ : Ω →ₐ[K] Ω).comp L.val

omit [IsGalois K Ω] in
@[simp]
theorem restrictEmbedding_apply (σ : G) (x : L) : restrictEmbedding L σ x = σ x :=
  rfl

omit [IsGalois K Ω] in

theorem restrictEmbedding_eq_iff (σ τ : G) :
    restrictEmbedding L σ = restrictEmbedding L τ ↔ σ⁻¹ * τ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : σ x = τ x := AlgHom.congr_fun h ⟨x, hx⟩
    rw [AlgEquiv.mul_apply, ← h', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro h
    ext x
    have h' := h x x.2
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h'
    exact h'.symm

theorem restrictEmbedding_surjective : Function.Surjective (restrictEmbedding L) := by
  intro τ
  let σ₀ : Ω →ₐ[K] Ω := τ.liftNormal Ω
  refine ⟨AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀), ?_⟩
  ext x
  simp only [restrictEmbedding_apply, AlgEquiv.coe_ofBijective]
  exact τ.liftNormal_commutes Ω x

noncomputable def cosetEmbeddingEquiv :
    (⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤ ≃ (L →ₐ[K] Ω) :=
  Equiv.ofBijective
    (Quotient.lift (fun σ : (⊤ : Subgroup G) => restrictEmbedding L σ) fun σ τ h => by
      have h' : σ⁻¹ * τ ∈ L.fixingSubgroup.subgroupOf ⊤ := QuotientGroup.leftRel_apply.mp h
      rw [Subgroup.mem_subgroupOf] at h'
      exact (restrictEmbedding_eq_iff L σ τ).2 (by simpa using h'))
    ⟨fun p q h => by
      induction p using QuotientGroup.induction_on with
      | H σ =>
      induction q using QuotientGroup.induction_on with
      | H τ =>
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (restrictEmbedding_eq_iff L σ τ).1 h,
     fun τ => by
      obtain ⟨σ, rfl⟩ := restrictEmbedding_surjective L τ
      exact ⟨((⟨σ, Subgroup.mem_top σ⟩ : (⊤ : Subgroup G)) : _ ⧸ _), rfl⟩⟩

@[simp]
theorem cosetEmbeddingEquiv_mk (σ : (⊤ : Subgroup G)) :
    cosetEmbeddingEquiv L (σ : (⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤) =
      restrictEmbedding L σ :=
  rfl

variable [FiniteDimensional K L]

theorem coe_norm_top [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((norm Ωˣ ⊤ L.fixingSubgroup a : fixedModule Ωˣ (⊤ : Subgroup G)) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K ((fixedModuleUnitsEquiv L a : Lˣ) : L)) := by
  classical
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  let _ := Fintype.ofFinite ((⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤)
  let _ : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
  have hsplit : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits := fun x => by
    rw [← minpoly.algebraMap_eq (algebraMap L Ω).injective x]
    exact Normal.splits inferInstance _
  rw [algebraMap_norm_eq_prod_embeddings_of_splits K L Ω hsplit, coe_norm,
    finprod_eq_prod_of_fintype, Units.coe_prod]
  refine Fintype.prod_equiv (cosetEmbeddingEquiv L) _ _ fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H σ => rfl

theorem baseUnitsEquiv_norm [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    baseUnitsEquiv (norm Ωˣ ⊤ L.fixingSubgroup a) = normUnits K L (fixedModuleUnitsEquiv L a) := by
  ext
  apply (algebraMap K Ω).injective
  rw [algebraMap_baseUnitsEquiv, coe_norm_top, coe_normUnits]

end Norm

section Normal

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')

include hK hL in

theorem normal_extendScalars [(L'.subgroupOf K').Normal] :
    Normal E (extendScalars hEF) := by
  subst hK hL
  refine IntermediateField.normal_iff_forall_map_le'.2 fun σ' => ?_
  rintro _ ⟨x, hx, rfl⟩
  replace hx : ∀ τ ∈ F.fixingSubgroup, τ x = x := (mem_iff_forall_fixingSubgroup F x).1 hx
  show σ' x ∈ F
  rw [mem_iff_forall_fixingSubgroup]
  let σ : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm σ'
  have hσ : ∀ y, (σ : Ω ≃ₐ[K] Ω) y = σ' y := fun _ => rfl
  intro τ hτ
  have hc : (σ : Ω ≃ₐ[K] Ω)⁻¹ * τ * σ ∈ F.fixingSubgroup := by
    have hτE : τ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hEF hτ
    have := (inferInstance : (F.fixingSubgroup.subgroupOf E.fixingSubgroup).Normal).conj_mem
      ⟨τ, hτE⟩ (by simpa [Subgroup.mem_subgroupOf] using hτ) σ⁻¹
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have h1 := hx _ hc
  simp only [AlgEquiv.mul_apply] at h1
  change τ (σ' x) = σ' x
  have h2 := congrArg (σ : Ω ≃ₐ[K] Ω) h1
  rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2

instance isSeparable_extendScalars : Algebra.IsSeparable E (extendScalars hEF) :=
  have : Algebra.IsSeparable E Ω := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  Algebra.isSeparable_tower_bot_of_isSeparable E (extendScalars hEF) Ω

omit [IsGalois K Ω] in

theorem finiteDimensional_extendScalars [FiniteDimensional K F] :
    FiniteDimensional E (extendScalars hEF) :=
  have : FiniteDimensional K (extendScalars hEF) := inferInstanceAs (FiniteDimensional K F)
  Module.Finite.of_restrictScalars_finite K E (extendScalars hEF)

include hL in
theorem mem_extendScalars_iff_forall (x : Ω) : x ∈ extendScalars hEF ↔ ∀ σ ∈ L', σ x = x := by
  rw [IntermediateField.mem_extendScalars, mem_iff_forall_fixingSubgroup, hL]

variable [Normal E (extendScalars hEF)]

noncomputable def restrictHom : K' →* (extendScalars hEF ≃ₐ[E] extendScalars hEF) :=
  (AlgEquiv.restrictNormalHom (extendScalars hEF)).comp
    ((IntermediateField.fixingSubgroupEquiv E).toMonoidHom.comp
      (MulEquiv.subgroupCongr hK.symm).toMonoidHom)

omit [IsGalois K Ω] in
theorem coe_restrictHom_apply (σ : K') (x : extendScalars hEF) :
    ((restrictHom K' hEF hK σ x : extendScalars hEF) : Ω) = (σ : Ω ≃ₐ[K] Ω) x :=
  AlgEquiv.restrictNormal_commutes _ _ x

omit [IsGalois K Ω] in
include hL in
theorem ker_restrictHom : (restrictHom K' hEF hK).ker = L'.subgroupOf K' := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hL, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := congrArg
      (fun τ : (extendScalars hEF ≃ₐ[E] extendScalars hEF) =>
        ((τ ⟨x, hx⟩ : extendScalars hEF) : Ω)) h
    simpa [coe_restrictHom_apply] using this
  · intro h
    ext x
    rw [coe_restrictHom_apply]
    exact h x x.2

theorem restrictHom_surjective : Function.Surjective (restrictHom K' hEF hK) := by
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  refine (AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := extendScalars hEF) (E := Ω)).comp ?_
  exact (IntermediateField.fixingSubgroupEquiv E).surjective.comp
    (MulEquiv.subgroupCongr hK.symm).surjective

noncomputable def galoisTateModel :
    TateModel Ωˣ K' L' (extendScalars hEF ≃ₐ[E] extendScalars hEF) (extendScalars hEF)ˣ where
  le := hK ▸ hL ▸ IntermediateField.fixingSubgroup_antitone hEF
  hom := restrictHom K' hEF hK
  surjective_hom := restrictHom_surjective K' hEF hK
  ker_hom := ker_restrictHom K' L' hEF hK hL
  equiv := unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL)
  coe_equiv_symm_smul σ a := by
    ext
    rw [coe_unitsEquivOfForall_symm]
    change ((restrictHom K' hEF hK σ _ : extendScalars hEF) : Ω) = _
    rw [coe_restrictHom_apply]
    rfl

@[simp]
theorem coe_galoisTateModel_equiv (a : fixedModule Ωˣ L') :
    ((((galoisTateModel K' L' hEF hK hL).equiv a : (extendScalars hEF)ˣ) : extendScalars hEF) : Ω) =
      ((a : Ωˣ) : Ω) :=
  rfl

end Normal

section Relative

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')

include hK in
theorem mem_iff_forall_of_fixingSubgroup_eq (x : Ω) : x ∈ E ↔ ∀ σ ∈ K', σ x = x := by
  rw [mem_iff_forall_fixingSubgroup, hK]

def restrictEmbeddingRel (σ : K') : extendScalars hEF →ₐ[E] Ω :=
  ((IntermediateField.fixingSubgroupEquiv E ⟨σ, hK ▸ σ.2⟩ : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω).comp
    (extendScalars hEF).val

omit [IsGalois K Ω] in
@[simp]
theorem restrictEmbeddingRel_apply (σ : K') (x : extendScalars hEF) :
    restrictEmbeddingRel K' hEF hK σ x = (σ : Ω ≃ₐ[K] Ω) x :=
  rfl

omit [IsGalois K Ω] in
include hL in
theorem restrictEmbeddingRel_eq_iff (σ τ : K') :
    restrictEmbeddingRel K' hEF hK σ = restrictEmbeddingRel K' hEF hK τ ↔
      σ⁻¹ * τ ∈ L'.subgroupOf K' := by
  rw [Subgroup.mem_subgroupOf, ← hL, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : (σ : Ω ≃ₐ[K] Ω) x = (τ : Ω ≃ₐ[K] Ω) x := AlgHom.congr_fun h ⟨x, hx⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h', AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply]
  · intro h
    ext x
    have h' := h x x.2
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_eq] at h'
    exact h'.symm

theorem restrictEmbeddingRel_surjective : Function.Surjective (restrictEmbeddingRel K' hEF hK) := by
  intro τ
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  let σ₀ : Ω →ₐ[E] Ω := τ.liftNormal Ω
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  let σ : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm σ'
  refine ⟨⟨σ, hK ▸ σ.2⟩, ?_⟩
  ext x
  exact τ.liftNormal_commutes Ω x

noncomputable def cosetEmbeddingEquivRel : K' ⧸ L'.subgroupOf K' ≃ (extendScalars hEF →ₐ[E] Ω) :=
  Equiv.ofBijective
    (Quotient.lift (restrictEmbeddingRel K' hEF hK) fun σ τ h =>
      (restrictEmbeddingRel_eq_iff K' L' hEF hK hL σ τ).2 (QuotientGroup.leftRel_apply.mp h))
    ⟨fun p q h => by
      induction p using QuotientGroup.induction_on with
      | H σ =>
      induction q using QuotientGroup.induction_on with
      | H τ =>
        exact QuotientGroup.eq.2 ((restrictEmbeddingRel_eq_iff K' L' hEF hK hL σ τ).1 h),
     fun τ => by
      obtain ⟨σ, rfl⟩ := restrictEmbeddingRel_surjective K' hEF hK τ
      exact ⟨(σ : K' ⧸ L'.subgroupOf K'), rfl⟩⟩

include hK in

theorem coe_norm_eq_algebraMap_norm [FiniteDimensional K F] [(L'.subgroupOf K').FiniteIndex]
    (a : fixedModule Ωˣ L') :
    (((norm Ωˣ K' L' a : fixedModule Ωˣ K') : Ωˣ) : Ω) =
      algebraMap E Ω (Algebra.norm E
        ((unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL) a :
          (extendScalars hEF)ˣ) : extendScalars hEF)) := by
  classical
  have := finiteDimensional_extendScalars hEF
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  let _ := Fintype.ofFinite (K' ⧸ L'.subgroupOf K')
  let _ : Fintype (extendScalars hEF →ₐ[E] Ω) := Fintype.ofFinite _
  have hsplit : ∀ x : extendScalars hEF, ((minpoly E x).map (algebraMap E Ω)).Splits := fun x => by
    rw [← minpoly.algebraMap_eq (algebraMap (extendScalars hEF) Ω).injective x]
    exact Normal.splits inferInstance _
  rw [algebraMap_norm_eq_prod_embeddings_of_splits E (extendScalars hEF) Ω hsplit, coe_norm,
    finprod_eq_prod_of_fintype, Units.coe_prod]
  refine Fintype.prod_equiv (cosetEmbeddingEquivRel K' L' hEF hK hL) _ _ fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H σ => rfl

theorem unitsEquivOfForall_norm [FiniteDimensional K F] [(L'.subgroupOf K').FiniteIndex]
    (a : fixedModule Ωˣ L') :
    unitsEquivOfForall K' E (mem_iff_forall_of_fixingSubgroup_eq K' hK) (norm Ωˣ K' L' a) =
      normUnits E (extendScalars hEF)
        (unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL) a) := by
  ext
  change _ = algebraMap E Ω ((normUnits E (extendScalars hEF) _ : Eˣ) : E)
  rw [coe_normUnits, ← coe_norm_eq_algebraMap_norm K' L' hEF hK hL a]
  rfl

end Relative

end GroundTheory.LocalField
