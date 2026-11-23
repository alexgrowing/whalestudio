import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLocalGaussSumNormSqEqAbsNormPow
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ), a ≠ 0 → ExpAt χ w a → IsUnitary χ → w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) → ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  first | exact @GlobalTheory.GaussMod.gaussSumAt_normSq | exact GlobalTheory.GaussMod.gaussSumAt_normSq | (intros; apply GlobalTheory.GaussMod.gaussSumAt_normSq <;> assumption)
