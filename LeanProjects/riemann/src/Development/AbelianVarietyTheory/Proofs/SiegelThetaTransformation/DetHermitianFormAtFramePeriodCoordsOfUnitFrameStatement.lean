import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetHermitianFormAtFramePeriodCoordsOfUnitFrame
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_hermitianFormAtFramePeriodCoords_of_unitFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, IsUnitFr X x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z w, hermForm Hm z w = hx X bas idx x z w) → Hm.det = ((∏ τ : X.Ψ, X.c τ ^ r : ℝ) : ℂ) := by
  first | exact @GlobalTheory.Dict.det_hx_of_isUnitFr | exact GlobalTheory.Dict.det_hx_of_isUnitFr | (intros; apply GlobalTheory.Dict.det_hx_of_isUnitFr <;> assumption)
