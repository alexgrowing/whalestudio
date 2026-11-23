import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubst
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst : ∀ (E : Subring ℂ) (N w a d : ℕ) (b : ℤ) (φ : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N (fun τ => DD τ ^ w * φ τ) → QAll (· ∈ E) (N * (a * d)) fun τ => DD τ ^ (w * (a * d)) * up φ (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNPole.qAll_pole_affine | exact GlobalTheory.FNPole.qAll_pole_affine | (intros; apply GlobalTheory.FNPole.qAll_pole_affine <;> assumption)
