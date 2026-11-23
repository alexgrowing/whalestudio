import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.USt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_pelUniformisation_of_norm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) [inst : Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)), (letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), P.D = D ∧ HEq P.mod inst ∧ HEq P.oD oD := by
  first | exact @GlobalTheory.UChart.exists_sab_pelUnif_of_norm | exact GlobalTheory.UChart.exists_sab_pelUnif_of_norm | (intros; apply GlobalTheory.UChart.exists_sab_pelUnif_of_norm <;> assumption)
