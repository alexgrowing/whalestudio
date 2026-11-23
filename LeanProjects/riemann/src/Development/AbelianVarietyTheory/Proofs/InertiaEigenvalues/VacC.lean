import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGoodStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.DualType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.StepLaw (ResAt UnrOff)

variable {D : D7} {S T : HSp D}

open Classical in

def allP (B : Base S T) (Q : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := B.G.Pg ∪ (B.de.Q ∪ Q)

open Classical in

def resP (B : Base S T) (ν : Twist D Circle) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  (if PP ∈ B.G.Pg then B.G.muC PP else 1) * B.de.locC PP * ν.locC PP

def vacC (B : Base S T) (ν : Twist D Circle) (g : GA D S) (h : GA D T) : ℂˣ :=
  ∏ PP ∈ allP B ν.Q, (resP B ν PP (GeneralLinearGroup.det (redFn B.F.βS PP (Lev.finE S g))))⁻¹ *
    resP B ν PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T h)))

end GlobalTheory.ExportSeries.DualType
end
