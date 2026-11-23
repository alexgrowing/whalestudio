import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancel
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_cancel : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q → LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) → LocallyOfFinitePresentation f := by
  first | exact @GlobalTheory.CompanionTheory.LfpDescent.descends | exact GlobalTheory.CompanionTheory.LfpDescent.descends | (intros; apply GlobalTheory.CompanionTheory.LfpDescent.descends <;> assumption)
