import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondIffRhoOfGoodPoint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem unramified_of_levelAway : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (M : ℕ), 1 ≤ M → LevelAway l M W → ∃ S : Finset Pl, ContainsAbove S l ∧ ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker := by
  intro l _ Ω _ _ _ W M hM hL
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hne : Ideal.span {((l * M : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hl0 (by omega))
  have hfin := Ideal.finite_factors hne
  have hmem : ∀ v : Pl, v ∈ hfin.toFinset ↔ ((l * M : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro v hv
    rw [hmem, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv
  · intro w hw B hB s hs
    rw [hmem, Nat.cast_mul] at hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (w.asIdeal.mul_mem_right _ h)
    have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (w.asIdeal.mul_mem_left _ h)
    obtain ⟨A, hA, χ, hχ, g, hg⟩ := hL w hlw
    have hMA : ¬ A.valuation (M : Ω) < 1 := by
      intro h
      apply hMw
      apply (hA (M : 𝓞 ℚ)).1
      simpa using h
    have key : ∀ u ∈ Ine (F := ℚ) A, W u = 1 := by
      intro u hu
      have h1 : ∀ i, χ i u = 1 := fun i => hχ i u fun ζ hζ => GlobalTheory.TameTau.ine_fix_root hu M hMA hζ
      have h2 := hg u hu
      have h3 : g * W u * g⁻¹ = 1 := by
        apply Units.ext
        rw [h2]
        simp [h1]
      have h4 : W u = g⁻¹ * (g * W u * g⁻¹) * g := by group
      rw [h4, h3]; group
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
    have h5 := key _ (GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq hσ hs)
    have h6 : s = σ * (σ⁻¹ * s * σ) * σ⁻¹ := by group
    rw [MonoidHom.mem_ker, h6, map_mul, map_mul, h5, mul_one, ← map_mul, mul_inv_cancel, map_one]

end GlobalTheory.Ord2
