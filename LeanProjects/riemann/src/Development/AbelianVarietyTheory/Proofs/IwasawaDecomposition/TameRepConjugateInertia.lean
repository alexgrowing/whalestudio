import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
open scoped Pointwise

namespace GlobalTheory.TameTauConj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem conj_mem_Ine_of_mem_Ine_smul [IsAlgClosure E Ω] {A : ValuationSubring Ω} {g σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) (g • A)) : g⁻¹ * σ * g ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        AlgEquiv.smul_def]
      have : (g⁻¹ : G E Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (smul_valuation_lt_one_iff g A _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G E Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ : G E Ω) (g x) = x
      show (g⁻¹ * g) x = x
      simp
    rw [e] at h
    exact h

end GlobalTheory.TameTauConj

open GlobalTheory.TameTauConj in

theorem GlobalTheory.TameTauConj.tameRep_conj : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A₀ : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A₀ P → ∀ (e : ℤ) (σ : G E Ω) (u : 𝓞 E), NX.TameRep P e σ u → ∃ ρ : G E Ω, ρ⁻¹ * σ * ρ ∈ Ine (F := E) A₀ ∧ ∃ (ϖ : 𝓞 E) (π : Ω), ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ π ^ (normV P - 1) = algebraMap E Ω (ϖ : E) ∧ A₀.valuation ((ρ⁻¹ * σ * ρ) π / π - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ A₀ P hA₀ e σ u hT
  obtain ⟨A, hA, hσ, ϖ, π, h1, h2, h3, h4⟩ := hT
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  subst hρ
  refine ⟨ρ, conj_mem_Ine_of_mem_Ine_smul hσ, ϖ, (ρ⁻¹ : G E Ω) π, h1, h2, ?_, ?_⟩
  · rw [← map_pow, h3, AlgEquiv.commutes]
  · have e1 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) = (ρ⁻¹ : G E Ω) (σ π) := by
      show (ρ⁻¹ * σ * ρ * ρ⁻¹) π = (ρ⁻¹ * σ) π
      rw [show ρ⁻¹ * σ * ρ * ρ⁻¹ = ρ⁻¹ * σ by group]
    have e2 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) / (ρ⁻¹ : G E Ω) π - (algebraMap E Ω (u : E)) ^ e
        = (ρ⁻¹ : G E Ω) (σ π / π - (algebraMap E Ω (u : E)) ^ e) := by
      rw [e1, map_sub, map_div₀, map_zpow₀, AlgEquiv.commutes]
    rw [e2]
    exact (smul_valuation_lt_one_iff ρ A₀ _).1 h4
