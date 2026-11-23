import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_ideal_power_le_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs | exact GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs | (intros; apply GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs <;> assumption)
