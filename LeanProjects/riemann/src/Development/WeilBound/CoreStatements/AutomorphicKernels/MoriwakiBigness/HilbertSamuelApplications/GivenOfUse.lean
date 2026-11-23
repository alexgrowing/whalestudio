import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.InputsOfUse
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.ProvHSOfUse
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.NineFreeOfUse
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GivenOfAllInputs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem given_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → Top.Given := by
  intro hAI hU hBig hRes hSA hHT hGaga hLine
  exact GlobalTheory.T.final_theorem_of_inputs_left GlobalTheory.CompanionTheory.Ar.Top.modelClause_holds GlobalTheory.KeyFam.keyFormula_holds hSA
    GlobalTheory.CompanionTheory.Segre.numericalSegre_closed hRes hHT hGaga hLine
    (GlobalTheory.CompanionTheory.Ar.Giv.inputs_of_use hAI hU hBig hRes) (provHS_of_use hAI hU hBig hRes) GlobalTheory.T.analytic_provision_holds
    (nineFree_of_use hAI hU hBig hRes)

end GlobalTheory.CompanionTheory.Ar.Link
