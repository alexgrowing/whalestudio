import Mathlib
import GroundTheory.LocalFields.LocalArtinMap
import GroundTheory.LocalFields.KroneckerWeber

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel GroundTheory.LocalField.FormalGroup

section Galois

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem apply_eq_self_of_mem_sup {τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    {E₁ E₂ : IntermediateField F Ω} (h₁ : E₁ ≤ maximalAbelianExtension F Ω)
    (h₂ : E₂ ≤ maximalAbelianExtension F Ω)
    (hτ₁ : ∀ (y : Ω) (hy : y ∈ E₁), ((τ ⟨y, h₁ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y)
    (hτ₂ : ∀ (y : Ω) (hy : y ∈ E₂), ((τ ⟨y, h₂ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y)
    (y : Ω) (hy : y ∈ E₁ ⊔ E₂) :
    ((τ ⟨y, sup_le h₁ h₂ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm τ)
  have hτ : τ = topologicalAbelianizationEquiv F Ω (g : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hg, ContinuousMulEquiv.apply_symm_apply]
  subst hτ
  have hg : g ∈ (E₁ ⊔ E₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_,
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_⟩
    · have := hτ₁ z hz
      rwa [topologicalAbelianizationEquiv_mk_apply] at this
    · have := hτ₂ z hz
      rwa [topologicalAbelianizationEquiv_mk_apply] at this
  rw [topologicalAbelianizationEquiv_mk_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy

end Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Uniqueness

theorem monoidHom_ext_uniformizer {M : Type*} [Group M] {f g : Kˣ →* M}
    (h : ∀ {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ), f (uniformizerUnit hϖ) = g (uniformizerUnit hϖ)) :
    f = g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hunit : ∀ u : 𝒪[K]ˣ, f (unitsIncl K u) = g (unitsIncl K u) := by
    intro u
    have huϖ : Irreducible ((u : 𝒪[K]) * ϖ) := (irreducible_units_mul u).2 hϖ
    have he : unitsIncl K u = uniformizerUnit huϖ * (uniformizerUnit hϖ)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      ext
      simp [coe_uniformizerUnit]
    rw [he, map_mul, map_mul, map_inv, map_inv, h huϖ, h hϖ]
  ext x
  set e := unitsEquivIntProd hϖ
  have hx : x = uniformizerUnit hϖ ^ Multiplicative.toAdd (e x).1 * unitsIncl K (e x).2 := by
    apply e.injective
    rw [map_mul, map_zpow, unitsEquivIntProd_uniformizer, unitsEquivIntProd_unitsIncl]
    ext
    · simp [← ofAdd_zsmul]
    · simp
  rw [hx, map_mul, map_mul, map_zpow, map_zpow, h hϖ, hunit]

theorem eq_localArtinMap_of
    {ψ : Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)}
    (hFrob : ∀ π : Kˣ, ord (π : K) = 1 →
      restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
        (ψ π) = maximalUnramifiedExtensionFrobenius K Ω)
    (hnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      ∀ x ∈ (normUnits K L).range, restrictAb L (le_maximalAbelianExtension L) (ψ x) = 1) :
    ψ = localArtinMap K Ω := by
  refine monoidHom_ext_uniformizer fun {ϖ} hϖ => ?_
  set π := uniformizerUnit hϖ
  have hπ : ord (π : K) = 1 := ord_uniformizer hϖ
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf := isLubinTateSeries_ltPoly ϖ

  have hLT : ∀ (χ : Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω))
      (hχ : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        ∀ x ∈ (normUnits K L).range, restrictAb L (le_maximalAbelianExtension L) (χ x) = 1)
      (n : ℕ) (y : Ω) (hy : y ∈ lubinTateField Ω hϖ hf (n + 1)),
      ∃ hy' : y ∈ maximalAbelianExtension K Ω, ((χ π ⟨y, hy'⟩ : maximalAbelianExtension K Ω) : Ω) = y := by
    intro χ hχ n y hy
    have : IsAbelianGalois K (lubinTateField Ω hϖ hf (n + 1)) :=
      isAbelianGalois_of_mul_comm _ (lubinTateField_mul_comm hϖ hf (n + 1))
    refine ⟨le_maximalAbelianExtension _ hy, ?_⟩
    obtain ⟨z, hz⟩ := exists_norm_eq_uniformizer (Ω := Ω) hϖ hf n.succ_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hz
      exact coe_ne_zero_of_irreducible hϖ hz.symm
    have hmem : π ∈ (normUnits K (lubinTateField Ω hϖ hf (n + 1))).range :=
      ⟨Units.mk0 z hz0, Units.ext (by simpa [π, coe_uniformizerUnit] using hz)⟩
    have := congrArg (fun ρ : lubinTateField Ω hϖ hf (n + 1) ≃ₐ[K] lubinTateField Ω hϖ hf (n + 1) =>
      ((ρ ⟨y, hy⟩ : lubinTateField Ω hϖ hf (n + 1)) : Ω)) (hχ _ π hmem)
    simpa only [restrictAb_apply, AlgEquiv.one_apply] using this
  have hφnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      ∀ x ∈ (normUnits K L).range,
        restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) = 1 := by
    intro L _ _ x hx
    rw [← MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_restrictAb_localArtinMap]
    exact hx
  have hur : ∀ (y : Ω) (hy : y ∈ maximalUnramifiedExtension K Ω),
      ((ψ π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
        maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
        maximalAbelianExtension K Ω) : Ω) := by
    intro y hy
    have h1 := congrArg (fun ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω =>
      ((ρ ⟨y, hy⟩ : maximalUnramifiedExtension K Ω) : Ω)) (hFrob π hπ)
    have h2 := congrArg (fun ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω =>
      ((ρ ⟨y, hy⟩ : maximalUnramifiedExtension K Ω) : Ω)) (restrictAb_localArtinMap_uniformizer (Ω := Ω) hπ)
    simp only [restrictAb_apply] at h1 h2
    rw [h1, h2]

  set τ := (ψ π)⁻¹ * localArtinMap K Ω π
  have hτ1 : τ = 1 := by
    refine ext_restrictAb fun L _ _ => ?_
    obtain ⟨n, m, hLM⟩ := exists_le_lubinTateField_sup_unramifiedTower hϖ hf L
    have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
    have hM := isAbelianGalois_lubinTateField_sup hϖ hf n.succ_pos hE
    have h₁ : lubinTateField Ω hϖ hf (n + 1) ≤ maximalAbelianExtension K Ω :=
      (le_sup_left : lubinTateField Ω hϖ hf (n + 1) ≤
        lubinTateField Ω hϖ hf (n + 1) ⊔ unramifiedTower K Ω m).trans (le_maximalAbelianExtension _)
    have h₂ : unramifiedTower K Ω m ≤ maximalAbelianExtension K Ω :=
      (le_sup_right : unramifiedTower K Ω m ≤ lubinTateField Ω hϖ hf (n + 1) ⊔ _).trans
        (le_maximalAbelianExtension _)
    have hfix := apply_eq_self_of_mem_sup (τ := τ) h₁ h₂ (fun y hy => ?_) (fun y hy => ?_)
    · ext y
      rw [restrictAb_apply, map_one, AlgEquiv.one_apply]
      exact hfix y (hLM y.2)
    · obtain ⟨hy₁, hψ⟩ := hLT ψ hnorm n y hy
      obtain ⟨hy₂, hφ⟩ := hLT (localArtinMap K Ω) hφnorm n y hy
      simp only [τ, AlgEquiv.mul_apply]
      have : (localArtinMap K Ω π ⟨y, h₁ hy⟩) = ⟨y, h₁ hy⟩ := Subtype.ext hφ
      have h1 : (ψ π).symm ⟨y, h₁ hy⟩ = ⟨y, h₁ hy⟩ :=
        (AlgEquiv.symm_apply_eq _).2 (Subtype.ext hψ).symm
      rw [this, AlgEquiv.aut_inv, h1]
    · have hyur : y ∈ maximalUnramifiedExtension K Ω := unramifiedTower_le_maximalUnramifiedExtension m hy
      have h := hur y hyur
      simp only [τ, AlgEquiv.mul_apply]
      have h1 : (ψ π).symm (localArtinMap K Ω π ⟨y, h₂ hy⟩) = ⟨y, h₂ hy⟩ :=
        (AlgEquiv.symm_apply_eq _).2 (Subtype.ext h).symm
      rw [AlgEquiv.aut_inv, h1]
  rw [← inv_mul_eq_one]
  exact hτ1

end Uniqueness

end GroundTheory.LocalField
