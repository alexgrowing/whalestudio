import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame <;> assumption)
