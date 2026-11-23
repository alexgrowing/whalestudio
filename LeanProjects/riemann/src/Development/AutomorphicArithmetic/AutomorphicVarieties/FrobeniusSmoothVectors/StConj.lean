import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

theorem UpperTheory.V.Fr.st_conj :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (κ : G ℚ Ω →* kˣ) (y : G ℚ Ω → k), (∀ s t, y (s * t) = y s + κ s * y t) → ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → (∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b) → ∃ b, ∀ s ∈ Dec (F := ℚ) A', y s = κ s * b - b := by
  intro Ω _ _ _ k _ κ y hy v A A' hA hA' ⟨b, hb⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hA hA'
  refine ⟨(κ σ : k) * b - y σ, fun s hs => ?_⟩
  have hs' : s • A' = A' := mem_Dec.mp hs
  have ht : σ⁻¹ * s * σ ∈ Dec (F := ℚ) A := by
    rw [mem_Dec, mul_smul, mul_smul, hσ, hs', ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
  have hbt := hb _ ht
  have hκ : κ (σ⁻¹ * s * σ) = κ s := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hκ' : ((κ (σ⁻¹ * s * σ) : kˣ) : k) = κ s := congrArg Units.val hκ
  have h1 := hy s σ
  have h2 := hy σ (σ⁻¹ * s * σ)
  have h3 : σ * (σ⁻¹ * s * σ) = s * σ := by group
  rw [h3] at h2
  linear_combination -h1 + h2 + (κ σ : k) * hbt + (κ σ : k) * b * hκ'
