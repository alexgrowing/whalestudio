import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferent
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_determinant_log_different : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ = -(Fintype.card I : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE | exact GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE <;> assumption)
