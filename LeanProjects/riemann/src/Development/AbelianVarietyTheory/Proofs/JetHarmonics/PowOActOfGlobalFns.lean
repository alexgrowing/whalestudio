import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowDegDiagonalAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem powOAct_of_globalFns : GlobalFnsSt → PowOActSt := by
  intro hG E _ _ _ H V _ _ _ t P n D' pD
  letI := H.starRing
  letI M : Module (𝓞 E) D'.toPre.X := pD.xe.module (𝓞 E)
  have h : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := by
    intro a x
    exact pD.xe.apply_symm_apply _
  obtain ⟨oa', hoa'⟩ := powDeg_diagonal_action hG V n P.D.toPre D'.toPre pD (𝓞 E) h P.oD
  exact ⟨M, oa', fun a x i => by rw [h]; rfl, hoa'⟩

end GlobalTheory
