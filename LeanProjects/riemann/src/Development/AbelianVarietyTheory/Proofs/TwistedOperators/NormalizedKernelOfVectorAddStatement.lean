import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedKernelOfVector_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  first | exact @GlobalTheory.TopZeroInv.kkVec_add | exact GlobalTheory.TopZeroInv.kkVec_add | (intros; apply GlobalTheory.TopZeroInv.kkVec_add <;> assumption)
