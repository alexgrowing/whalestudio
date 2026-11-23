import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerIntegralEqLeftPartialFourier
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_integral_eq_left_partial_fourier : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), ∀ (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (y h : GL (Fin 2) F), LFS.inn ψ Φ y⁻¹ (w3 * tinv (em h)) = Lpart ψ (Pf Φ h y) := by
  first | exact @GlobalTheory.CompanionTheory.InnerIntegralLongWeyl.inner_integral_long_weyl_transpose_inv | exact GlobalTheory.CompanionTheory.InnerIntegralLongWeyl.inner_integral_long_weyl_transpose_inv | (intros; apply GlobalTheory.CompanionTheory.InnerIntegralLongWeyl.inner_integral_long_weyl_transpose_inv <;> assumption)
