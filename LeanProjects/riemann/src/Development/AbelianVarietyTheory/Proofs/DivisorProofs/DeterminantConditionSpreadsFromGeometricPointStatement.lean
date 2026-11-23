import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantConditionSpreadsFromGeometricPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantCondition_spreads_from_geometricPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : A), IsAbelianScheme G → ρ ^ 2 = -(H.d : A) → Nonempty (ℚ →+* A) → ∀ (K₀ : Type) [Field K₀] [IsAlgClosed K₀] (g₀ : A →+* K₀), DetCond D act (spMap g₀) (g₀ ρ) → ∀ (K : Type) [Field K] [IsAlgClosed K] (g : A →+* K), DetCond D act (spMap g) (g ρ) := by
  first | exact @GlobalTheory.SpreadOnePoint.detCond_of_point | exact GlobalTheory.SpreadOnePoint.detCond_of_point | (intros; apply GlobalTheory.SpreadOnePoint.detCond_of_point <;> assumption)
