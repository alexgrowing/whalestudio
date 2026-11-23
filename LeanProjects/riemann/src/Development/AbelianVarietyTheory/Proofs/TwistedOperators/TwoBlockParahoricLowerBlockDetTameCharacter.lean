import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
  GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricLowerBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem lower_block_det (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (j : GL (A ⊕ D) k) (hj : j ∈ parahoric k A D) :
    ∃ a b : 𝒪[k], (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k a ∧
      ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k b ∧
      IsLocalRing.residue 𝒪[k] (a * b) = 1 := by
  obtain ⟨⟨h, rfl⟩, hlow⟩ := mem_parahoric.1 hj
  set f := IsLocalRing.residue 𝒪[k]
  set Hb := f.mapMatrix h.val
  set Gb := f.mapMatrix (h⁻¹).val
  have hz : Hb.toBlocks₂₁ = 0 := by
    ext i j'
    exact (residue_eq_zero_iff_val _).2 (hlow i j')
  have hHG : Hb * Gb = 1 := by
    simp only [Hb, Gb, ← map_mul, Units.mul_inv, map_one]
  have h22 : Hb.toBlocks₂₂ * Gb.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hHG
    rw [← fromBlocks_toBlocks Hb, ← fromBlocks_toBlocks Gb, fromBlocks_multiply, hz] at this
    have e : (1 : Matrix (A ⊕ D) (A ⊕ D) 𝓀[k]).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, Matrix.one_apply]
    simpa [e] using this
  refine ⟨h.val.toBlocks₂₂.det, (h⁻¹).val.toBlocks₂₂.det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det]; rfl
  · rw [RingHom.map_det, ← map_inv]; rfl
  · rw [map_mul, RingHom.map_det, RingHom.map_det, ← det_mul]
    exact (congrArg det h22).trans det_one

end GlobalTheory.ParahoricLowerBlock

namespace GlobalTheory.ParahoricLowerBlock

theorem lower_block_tame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξ j hj
  obtain ⟨a, b, ha, hb, hab⟩ := lower_block_det A D j hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul, map_zero] at hab
    exact zero_ne_one hab
  refine ⟨?_, fun d d' hd hd' => ?_⟩
  · rw [ha]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[k] k)).2 ha0
  · have hv : valuation k (((d * d' : kˣ) : k) - 1) < 1 := by
      have e : ((d * d' : kˣ) : k) - 1 = algebraMap 𝒪[k] k (a * b - 1) := by
        rw [Units.val_mul, hd, hd', ha, hb, map_sub, map_mul, map_one]
      rw [e, ← residue_eq_zero_iff_val, map_sub, hab, map_one, sub_self]
    have := hξ (d * d') hv
    rw [map_mul] at this
    have := congrArg Units.val this
    simpa using this

end GlobalTheory.ParahoricLowerBlock
