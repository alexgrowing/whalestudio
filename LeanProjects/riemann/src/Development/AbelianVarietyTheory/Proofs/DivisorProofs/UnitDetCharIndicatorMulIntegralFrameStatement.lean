import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorMulIntegralFrame
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
theorem _root_.GlobalTheory.T.unitDetCharIndicator_mul_integralFrame : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D), e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
  ∀ {k : ℕ} (N : Matrix (Fin k) (Fin k) (EAf D)) (β : GL (Fin k) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
  unitChar ν e (HMul.hMul N β.val) = unitChar ν e N * unitChar ν e β.val := by
  first | exact @GlobalTheory.StdRead.CharMul.unitChar_mul | exact GlobalTheory.StdRead.CharMul.unitChar_mul | (intros; apply GlobalTheory.StdRead.CharMul.unitChar_mul <;> assumption)
