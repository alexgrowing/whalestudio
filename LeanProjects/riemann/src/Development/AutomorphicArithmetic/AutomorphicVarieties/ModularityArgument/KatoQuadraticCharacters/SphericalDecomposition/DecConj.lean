import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

private theorem gap_pow {C : Type} [CommGroup C] (x : C) (a b : ℤ) (m : ℕ)
    (h : (x ^ a) ^ m = (x ^ b * x) ^ m) : x ^ ((m : ℤ) * (a - b - 1)) = 1 := by
  have h' : x ^ (a * m) = x ^ ((b + 1) * m) := by
    rw [zpow_mul, zpow_mul, zpow_add_one, zpow_natCast, zpow_natCast, h]
  have hc : (m : ℤ) * (a - b - 1) = a * m - (b + 1) * m := by ring
  rw [hc, zpow_sub, h', mul_inv_cancel]

private theorem exp_ne (e : ℕ) (he : 1 ≤ e) (m : ℕ) (hm : 1 ≤ m) (i j : Fin 2) :
    (m : ℤ) * ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i - (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j - 1) ≠ 0 := by
  refine mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) ?_
  fin_cases i <;> fin_cases j <;> simp <;> omega

private def decConj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.potOf :
    PotOf := by
  intro F Ω _ _ _ _ _ l _ e he r w A κ hl hA hE
  obtain ⟨⟨g, hg⟩, hI⟩ := hE
  have hvA : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa using h1
  have hv : ∀ (t : Dec (F := F) A), (t : G F Ω) ∈ Ine A → ∀ i : Fin 2,
      κ i t = cycBar F Ω l ↑t ^ ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i) := by
    intro t ht i
    fin_cases i
    · exact (hI t ht).1
    · exact (hI t ht).2
  intro A' hA'
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  refine ⟨fun i => (κ i).comp (decConj A A' σ hσ), ?_, ?_⟩
  · refine ⟨g * r σ⁻¹, fun s => ?_⟩
    have hc : ((decConj A A' σ hσ s : Dec (F := F) A) : G F Ω) = σ⁻¹ * ↑s * σ := rfl
    have key : g * r σ⁻¹ * r ↑s * (g * r σ⁻¹)⁻¹ = g * r ↑(decConj A A' σ hσ s) * g⁻¹ := by
      rw [hc, map_mul, map_mul, map_inv]
      group
    rw [key]
    exact hg _
  · intro i j m hm heq
    obtain ⟨g0, hg0, hn⟩ := Ws.Pt.cycIne F Ω l A hvA _ (exp_ne e he m hm i j)
    have hA'σ : σ⁻¹ • A' = A := by rw [← hσ, inv_smul_smul]
    have hg1 : σ * g0 * σ⁻¹ ∈ Ine A' := by
      have h2 := (Two.ineConj F Ω σ⁻¹).1 A' g0 (by rw [hA'σ]; exact hg0)
      rwa [inv_inv] at h2
    have ht : decConj A A' σ hσ ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩ = ⟨g0, Ine_le_Dec A hg0⟩ :=
      Subtype.ext (by
        show σ⁻¹ * (σ * g0 * σ⁻¹) * σ = g0
        group)
    have hcyc : cycBar F Ω l (σ * g0 * σ⁻¹) = cycBar F Ω l g0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 := DFunLike.congr_fun heq ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩
    simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype] at h3
    rw [ht, hv _ hg0 i, hv _ hg0 j, hcyc] at h3
    exact hn (gap_pow (cycBar F Ω l g0) _ _ m h3)
