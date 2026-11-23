import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_constant_square : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ ∂selfDualMeasure χ = ∫ z, Φ z * localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) (σ.symm z) ∂muE E χ := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.Left.left_average | exact GlobalTheory.CompanionTheory.GaussLam.Left.left_average | (intros; apply GlobalTheory.CompanionTheory.GaussLam.Left.left_average <;> assumption)
