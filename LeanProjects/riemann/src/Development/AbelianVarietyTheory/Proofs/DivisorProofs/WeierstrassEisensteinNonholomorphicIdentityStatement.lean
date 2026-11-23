import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  first | exact @GlobalTheory.wB_nonhol_correction | exact GlobalTheory.wB_nonhol_correction | (intros; apply GlobalTheory.wB_nonhol_correction <;> assumption)
