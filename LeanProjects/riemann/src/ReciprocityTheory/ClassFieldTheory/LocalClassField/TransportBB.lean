import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

theorem continuous_gal_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  refine Filter.tendsto_def.2 fun s hs => ?_
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  let b := Module.finBasis k' E
  choose c hc using h
  have hopen : IsOpen (⋂ i, {σ : F ≃ₐ[k] F | σ (c (b i : F')) = c (b i : F')}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := k) (c (b i : F'))
  refine Filter.mem_of_superset (hopen.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun σ hσ => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : F') := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    exact this.symm
  rw [hx']
  show φ σ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact congrArg _ (hc _ σ (Set.mem_iInter.1 hσ i))

theorem exists_topAb_iso {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  have hc : (commutator G).map (φ : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]
    exact (hφ.homeomorph φ).image_closure _
  let ψ := QuotientGroup.congr _ _ φ hmap
  have h1 : Continuous ψ :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hφ.continuous)
  have hs : Continuous φ.symm :=
    (φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous
  have h2 : Continuous ψ.symm :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hs)
  exact ⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

theorem Model.E_symm_coe (x : m.K') :
    m.E.symm (x : PadicAlgCl p) = algebraMap K (AlgebraicClosure K) (m.e.symm x) := by
  rw [RingEquiv.symm_apply_eq, m.comm, RingEquiv.apply_symm_apply]

include m in
theorem Model.charZero : CharZero K :=
  charZero_of_injective_ringHom (f := (m.e.symm : m.K' →+* K)) m.e.symm.injective

noncomputable def Model.galIso : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃* GK p m.K' where
  toFun σ :=
    { m.E.symm.trans (σ.toRingEquiv.trans m.E) with
      commutes' := fun x => by
        show m.E (σ (m.E.symm (x : PadicAlgCl p))) = (x : PadicAlgCl p)
        rw [m.E_symm_coe, AlgEquiv.commutes, m.comm, RingEquiv.apply_symm_apply] }
  invFun τ :=
    { m.E.trans (τ.toRingEquiv.trans m.E.symm) with
      commutes' := fun x => by
        show m.E.symm (τ (m.E (algebraMap K (AlgebraicClosure K) x))) = algebraMap K (AlgebraicClosure K) x
        rw [m.comm, show τ ((m.e x : m.K') : PadicAlgCl p) = _ from τ.commutes (m.e x)]
        show m.E.symm ((m.e x : m.K') : PadicAlgCl p) = _
        rw [m.E_symm_coe, RingEquiv.symm_apply_apply] }
  left_inv σ := by
    ext x
    show m.E.symm (m.E (σ (m.E.symm (m.E x)))) = σ x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  right_inv τ := by
    ext x
    show m.E (m.E.symm (τ (m.E (m.E.symm x)))) = τ x
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  map_mul' σ τ := by
    ext x
    show m.E (σ (τ (m.E.symm x))) = m.E (σ (m.E.symm (m.E (τ (m.E.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem Model.isGalIso_galIso : m.IsGalIso m.galIso := fun σ x => by
  show m.E (σ (m.E.symm (m.E x))) = m.E (σ x)
  rw [RingEquiv.symm_apply_apply]

variable {m}

theorem Model.IsGalIso.symm_apply {φ} (hφ : m.IsGalIso φ) (τ : GK p m.K') (x : AlgebraicClosure K) :
    m.E (φ.symm τ x) = τ (m.E x) := by
  rw [← hφ, MulEquiv.apply_symm_apply]

theorem Model.IsGalIso.galois_iso_isHomeomorph {φ} (hφ : m.IsGalIso φ) : IsHomeomorph φ := by
  have hint : Algebra.IsIntegral m.K' (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have h1 : Continuous φ.toMonoidHom := continuous_gal_of_fix φ.toMonoidHom fun y => ⟨m.E.symm y, fun σ hσ => by
    show φ σ y = y
    have := hφ σ (m.E.symm y)
    rwa [hσ, RingEquiv.apply_symm_apply] at this⟩
  have h2 : Continuous φ.symm.toMonoidHom := continuous_gal_of_fix φ.symm.toMonoidHom fun y => ⟨m.E y, fun τ hτ => by
    show φ.symm τ y = y
    apply m.E.injective
    rw [hφ.symm_apply, hτ]⟩
  exact (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph

theorem Model.isFrobeniusLift_iff_model [IsNonarchimedeanLocalField K] {φ} (hφ : m.IsGalIso φ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : IsFrobeniusLift K g ↔ IsFrob p m.K' (φ g) := by
  constructor
  · intro h y hy
    have h1 := h (m.E.symm y) ((m.mem_integral_closure_iff_norm _).2 (by rwa [RingEquiv.apply_symm_apply]))
    rw [m.mem_maximal_ideal_closure_iff_norm, map_sub, map_pow, ← hφ, RingEquiv.apply_symm_apply, m.card_residue_field_model] at h1
    exact h1
  · intro h x hx
    have h1 := h (m.E x) ((m.mem_integral_closure_iff_norm _).1 hx)
    rw [m.mem_maximal_ideal_closure_iff_norm, map_sub, map_pow, ← hφ, m.card_residue_field_model]
    exact h1

theorem Model.exists_abelianization_iso {φ} (hφ : m.IsGalIso φ) :
    ∃ ψ : Field.absoluteGaloisGroupAbelianization K ≃* GKab p m.K', IsHomeomorph ψ ∧
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ψ (toAb K g) = toAbK p m.K' (φ g) :=
  exists_topAb_iso φ hφ.galois_iso_isHomeomorph

end ReciprocityTheory.DiscreteGroups.LocalClassField
