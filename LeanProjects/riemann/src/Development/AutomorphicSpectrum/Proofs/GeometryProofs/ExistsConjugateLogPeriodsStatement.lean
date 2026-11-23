import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_log_periods : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) → ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1, HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u = (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram | exact GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram <;> assumption)
