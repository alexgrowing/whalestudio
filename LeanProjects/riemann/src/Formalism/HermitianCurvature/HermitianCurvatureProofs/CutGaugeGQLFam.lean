import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem quadratic_local_family_holds : GQLFam := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Dc Φ hF Y a b
  obtain ⟨hO, hD, hM, hS, hFF⟩ := hF
  refine ⟨hO, hD, hM, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.transfer_joint_smooth _ _ _ _ _ _ _ Φ (Y : ℂ) a b hO hS
  · intro c hc
    exact Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ _ _ _ _ _ _ _ _ (Y : ℂ) a b Bs.z_mem Bs.z'_mem (hD c hc) _ (hFF c hc)

end Formalism.FourierDecayAlt.P.CutMP.Gauge
