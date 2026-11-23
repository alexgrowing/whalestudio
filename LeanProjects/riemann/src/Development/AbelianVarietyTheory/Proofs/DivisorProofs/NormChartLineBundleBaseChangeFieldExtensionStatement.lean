import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtension
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normChartLineBundle_baseChange_field_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ → NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A) (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  first | exact @GlobalTheory.ProjField.normChart_baseChange | exact GlobalTheory.ProjField.normChart_baseChange | (intros; apply GlobalTheory.ProjField.normChart_baseChange <;> assumption)
