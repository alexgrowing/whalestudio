import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParameterInequalitiesGood
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_inequalities_good : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ n L₂ : ℕ, s.x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + 1) * ((6 * Formalism.MainNotions.G.rG s + 1) * Formalism.MainNotions.G.goodU s.delta1) ≤ n ∧ (n : ℝ) * (L₂.choose (Formalism.MainNotions.G.KG s) : ℝ) * s.delta1 ^ Formalism.MainNotions.G.KG s + n * (1 - Formalism.G0.markedBound s.delta1 (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + n * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) s.delta1 (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x - 1) ≤ Cb * s.x ^ (-2 : ℝ) := by
  first | exact @GlobalTheory.OrbitTerms.orbit_terms_le | exact GlobalTheory.OrbitTerms.orbit_terms_le | (intros; apply GlobalTheory.OrbitTerms.orbit_terms_le <;> assumption)
