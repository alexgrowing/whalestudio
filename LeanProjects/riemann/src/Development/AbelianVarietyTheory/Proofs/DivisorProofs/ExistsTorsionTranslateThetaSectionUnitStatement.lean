import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTranslate_thetaSection_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_unitAt_mul | exact GlobalTheory.Poinc.IntTerm.exists_unitAt_mul | (intros; apply GlobalTheory.Poinc.IntTerm.exists_unitAt_mul <;> assumption)
