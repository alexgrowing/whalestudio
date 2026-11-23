import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePrimeToCharTorsionRational
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_primeToChar_torsion_rational : ∀ (K₀ K : Type) [Field K₀] [IsAlgClosed K₀] [Field K] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y],
  IsAbelianScheme Y → ∀ n : ℕ, IsUnit (n : K₀) → ∀ y : Over.mk (spMap e) ⟶ Y, y ^ n = 1 →
  ∃ y₀ : Sp K₀ ⟶ Y.left, y.left = spMap e ≫ y₀ := by
  first | exact @GlobalTheory.TorsRat.torsion_point_rational | exact GlobalTheory.TorsRat.torsion_point_rational | (intros; apply GlobalTheory.TorsRat.torsion_point_rational <;> assumption)
