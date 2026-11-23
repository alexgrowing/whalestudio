import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

open Complex Matrix

namespace GlobalTheory.CompanionTheory.Metric

theorem mean_sq_fixes_norm_const :
    ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (Λ : Submodule ℤ (Fin g → ℂ))
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) (b : ℝ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, c i = 0 ∨ c i = 1 / 2) →
    (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ, h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z)) →
    (∀ l ∈ Λ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z, θ (z + l) = ε *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z) →
    0 < b →
    (∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
      b ^ 2 = (∫ w in Fd, (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm w w).re)) ^ 2) / (volume Fd).toReal) →
    b ^ 2 = ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h Hm a c Λ θ κ b hs hp hh ha hc hΛ hH hθ hper hb hmean
  have h₁ : ∀ i, (fun i => (a i : ℂ)) i = 0 ∨ (fun i => (a i : ℂ)) i = 1 / 2 := fun i => by
    rcases ha i with e | e <;> simp [e]
  have h₂ : ∀ i, (fun i => (c i : ℂ)) i = 0 ∨ (fun i => (c i : ℂ)) i = 1 / 2 := fun i => by
    rcases hc i with e | e <;> simp [e]
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨Fd, hFd, -⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) Λ.toAddSubgroup hs hp hh h₁ h₂ hΛ
  have hFdΛ : IsAddFundamentalDomain Λ Fd volume := hFd
  have hb2 := hmean Fd hFdΛ
  have hsq := GlobalTheory.Dict.VacNorm.norm_sq_of_mean (τ := τ) (h := h) (A := Λ.toAddSubgroup)
    (H := hermForm Hm) (θ := fun z => θ z / b) (a := κ / b) ⟨hs, hp⟩ hh h₁ h₂ hΛ
    (fun z w => by
      rw [hH]
      rfl)
    (fun z => by
      simp only [hθ, GlobalTheory.CanTh.canTh, GlobalTheory.CanTh.imInv]
      ring)
    (fun p hp' => by
      obtain ⟨ε, hε, hz⟩ := hper p hp'
      have hε0 : ε ≠ 0 := by
        intro e
        simp [e] at hε
      refine ⟨ε⁻¹, by simp [hε], fun z => ?_⟩
      have e2 : hermForm Hm (z + (1 / 2 : ℂ) • p) p = hermForm Hm z p + 1 / 2 * hermForm Hm p p := by
        simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul]
      simp only [hz, e2]
      have e3 : Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
          Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p) = 1 := by
        rw [← Complex.exp_add]
        simp only [Nat.cast_one]
        ring_nf
        simp
      have e1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
      linear_combination (θ z / b * Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
        Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p)) * e1 + (θ z / b) * e3)
    hFd
    (by
      have hint : ∀ z, ‖θ z / (b : ℂ)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) = (b ^ 2)⁻¹ *
          (‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re)) ^ 2 := by
        intro z
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, mul_pow, div_pow,
          ← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) =
            -Real.pi * (hermForm Hm z z).re := by
          push_cast
          ring
        rw [this]
        ring
      simp only [hint]
      rw [MeasureTheory.integral_const_mul, mul_div_assoc, ← hb2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hb.ne'))
  have hD : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hp.det_pos)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, div_pow,
    div_eq_iff (pow_ne_zero _ hb.ne')] at hsq
  rw [hsq]
  field_simp

end GlobalTheory.CompanionTheory.Metric
