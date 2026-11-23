import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_blowup_of_smooth : ∀ {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k) (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁), IsIntegral X₁ → FinalTheorems.Blowup π Z → Smooth (π ≫ g) → Nonempty X₂ → IsIntegral X₂ := by
  first | exact @GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup | exact GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup | (intros; apply GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup <;> assumption)
