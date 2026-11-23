import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberIntegralFrameEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirstMember_integralFrame_eq : ∀ {D : D7} (S T : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) (β : GL (Fin S.rank) (EAf D)),
  IsIntM β.val → IsIntM (β⁻¹).val → ∀ t : WO S T, stdFst ν e 𝔪 S T β 1 t =
    if IsHalf e t ∧ (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
        ∀ i j, S.rank ≤ i.1 → InId 𝔪 (toEAf D (t i j)) then
      unitChar ν e (HMul.hMul (topL S.rank (Matrix.of fun i j => toEAf D (t i j))) β.val) else 0 := by
  first | exact @GlobalTheory.StdReadFrame.stdFst_frame | exact GlobalTheory.StdReadFrame.stdFst_frame | (intros; apply GlobalTheory.StdReadFrame.stdFst_frame <;> assumption)
