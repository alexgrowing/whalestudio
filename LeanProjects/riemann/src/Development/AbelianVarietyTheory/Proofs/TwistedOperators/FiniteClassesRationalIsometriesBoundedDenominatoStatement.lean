import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominato
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧ ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  first | exact @GlobalTheory.HeckeEx.QFin.finite_reps | exact GlobalTheory.HeckeEx.QFin.finite_reps | (intros; apply GlobalTheory.HeckeEx.QFin.finite_reps <;> assumption)
