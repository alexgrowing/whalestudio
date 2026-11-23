import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_coordinates_frame_rational_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ), Formalism.L2.PjFree.perFr X' (lact a (castFr h.psi x)) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = Formalism.L2.PjFree.perFr X x v τ i := by
  first | exact @GlobalTheory.GeoLevel.perFr_lact_of_isMatch | exact GlobalTheory.GeoLevel.perFr_lact_of_isMatch | (intros; apply GlobalTheory.GeoLevel.perFr_lact_of_isMatch <;> assumption)
