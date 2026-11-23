import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspCoefficient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivCover

variable {D : D7}

def delDet (V : HSp D) {C : Type} [AddCommGroup C] (u : GlobalTheory.ExportSeries.UnivTwist D C) (Q : Finset (Pl D.host.E))
    (g : GA D V) : ↥Q → C :=
  Multiplicative.toAdd (GlobalTheory.ExportSeries.detChar V (u.delQ Q) g)

example (V : HSp D) {C : Type} [AddCommGroup C] (Q : Finset (Pl D.host.E)) (g : GA D V) :
    delDet V (⟨fun _ => 1, fun _ => 1⟩ : GlobalTheory.ExportSeries.UnivTwist D C) Q g = 0 := by
  funext q
  rfl

end GlobalTheory.UnivCover
