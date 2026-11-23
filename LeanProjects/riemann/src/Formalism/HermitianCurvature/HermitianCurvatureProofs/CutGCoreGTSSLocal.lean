import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceDZ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTSSLocal_of_radT : GTCLRadT → GTSSLocal := by
  intro hT Wp Wq _ _ _ _ _ _ P Bs X d hG e he _
  obtain ⟨hP, hk, hC, -⟩ := id hG
  have hX : ∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b) := fun Y a b =>
    second_shift_slice_derivative Wp Wq P Bs hP _ (hT Wp Wq P Bs hP hk hC X Y a b)
  exact second_shift_matrix_form Wp Wq P Bs X d hG e he
    (second_shift_slice_operator Wp Wq P Bs X d hG hX)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
