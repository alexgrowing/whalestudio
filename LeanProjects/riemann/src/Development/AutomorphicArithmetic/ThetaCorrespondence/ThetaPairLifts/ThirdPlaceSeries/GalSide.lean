import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.TwInputs
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
structure GalSideAlt (D : D7) : Type 1 where
  wd : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : GlobalTheory.HeightCounting.LabTrue D wd
  cf : CharFrame D
  chr : GlobalTheory.HeightCounting.CharSide D cf
  triple : _root_.GlobalTheory.Triple.IsGaloisTriple D
  lam : GlobalTheory.LamTie.LamDat D
  lamOk : lam.Ok
  lamTie : GlobalTheory.LamTie.IsLamTie D.ntw lam
  rank : 100 ≤ D.R.r
  primes : ∀ k, 2 * D.R.r ≤ D.host.g k
section Abstract
end Abstract
end GlobalTheory.TwInputs
end
end
