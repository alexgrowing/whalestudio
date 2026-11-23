import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_determinant_nonneg_curve_degree : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)) (Z : Scheme.{0}) (i : Z ⟶ Fl ι N) [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 → ∃ (r : ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B r), 0 ≤ ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).curveDeg hr := by
  first | exact @GlobalTheory.FlagZ.curveDeg_restr_flDet_nonneg | exact GlobalTheory.FlagZ.curveDeg_restr_flDet_nonneg | (intros; apply GlobalTheory.FlagZ.curveDeg_restr_flDet_nonneg <;> assumption)
