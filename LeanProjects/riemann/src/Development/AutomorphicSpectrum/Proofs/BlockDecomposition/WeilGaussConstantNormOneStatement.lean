import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantNormOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_constant_norm_one : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∫ a, g a * (nsg E a * (((modulus a : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) ∂selfDualMeasure χ = ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.Right.avg_fubini | exact GlobalTheory.CompanionTheory.GaussLam.Right.avg_fubini | (intros; apply GlobalTheory.CompanionTheory.GaussLam.Right.avg_fubini <;> assumption)
