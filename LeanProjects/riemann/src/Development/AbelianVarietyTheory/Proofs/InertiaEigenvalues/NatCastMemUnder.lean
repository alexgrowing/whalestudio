import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.CloseUnitNorms.TestVectorMemSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie.PlaceChoice

variable {D : D7}

abbrev under (P : Pl D.host.E) : Ideal (𝓞 D.host.K) := P.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def choice (D : D7) : Set (Pl D.host.E) :=
  {P | ∃ P', IsConjPl D.host P P' ∧
    (WellOrderingRel (under P) (under P') ∨ (under P = under P' ∧ WellOrderingRel P P'))}

end GlobalTheory.SeriesTie.PlaceChoice

end
