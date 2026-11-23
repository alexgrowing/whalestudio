import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  first | exact @GlobalTheory.Desc.OpenChart.nonempty_chart | exact GlobalTheory.Desc.OpenChart.nonempty_chart | (intros; apply GlobalTheory.Desc.OpenChart.nonempty_chart <;> assumption)
