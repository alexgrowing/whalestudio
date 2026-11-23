import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicNormTransitionDetOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | exact GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one | (intros; apply GlobalTheory.CompanionTheory.Relay.padic_norm_transition_det_one <;> assumption)
