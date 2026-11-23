import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxRosati
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTauBalOfLinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem powerRosati_tauBal_action : BoxRosatiSt ∧ BoxTauBalSt ∧ PowOActSt :=
  ⟨boxRosati, BoxTauLin.boxTauBal_of_linear allSixLaws.1.globalFns,
    powOAct_of_globalFns allSixLaws.1.globalFns⟩

end GlobalTheory
