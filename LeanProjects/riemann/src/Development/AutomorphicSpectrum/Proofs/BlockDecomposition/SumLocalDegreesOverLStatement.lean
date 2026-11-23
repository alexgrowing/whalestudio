import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumLocalDegreesOverL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_local_degrees_over_l : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) → ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank | exact GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank <;> assumption)
