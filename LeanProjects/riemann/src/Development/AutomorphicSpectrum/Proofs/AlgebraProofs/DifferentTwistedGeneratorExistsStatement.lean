import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_twisted_generator_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes), ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧ Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator | exact GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.RelDiff.exists_local_generator <;> assumption)
