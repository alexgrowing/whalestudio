import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWPairProof

variable {D : D7}

def dbl (V W : HSp D) (f₁ f₂ : WO V W → ℂ) : WO (GlobalTheory.Doubling.dblSp W) V → ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁)

theorem dbl_apply (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (x : WO (GlobalTheory.Doubling.dblSp W) V) :
    dbl V W f₁ f₂ x = starRingEnd ℂ (f₂ (GlobalTheory.PairLift.adjO V W (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL W V x))) *
      f₁ (GlobalTheory.PairLift.adjO V W (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR W V x)) := by
  simp only [dbl, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, GlobalTheory.PairLift.dag, Complex.conj_conj]

end GlobalTheory.SWPairProof

end
