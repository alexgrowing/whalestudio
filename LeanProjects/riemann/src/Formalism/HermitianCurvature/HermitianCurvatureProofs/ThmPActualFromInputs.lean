import Formalism.HermitianCurvature.HermitianCurvatureProofs.EqOfContinuousOffZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopIdentFromParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem thmPActualFromInputs : ThmPActualFromInputs := by
  intro hHer hWC hWS hFA hOW hPW Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, hAdj, hTD, hTT, hSl, hSD, hWK, hFS, hCor, hJ⟩ :=
    hHer Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  refine ⟨K, ?_, hSl, hCor, hJ⟩
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD hFA hOW hAdj
  have hST := stepTwistFromParts (S := S) P z z' π π' X μ L st K l0 hD hPW (hWS Wp Wq P z z' π π' X L)
    (hWC Wp Wq P z z' π π' X μ L st l0 hD) hWK
  exact thmPFromStepsAll Wp Wq S P z z' π π' μ L st K l0 hTI hTD hTT hSl hSD hST hFS

theorem thmPActualFromHer : ThmPActualFromHer := fun hHer hWC =>
  thmPActualFromInputs hHer hWC waveSiteAll Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR Formalism.FourierDecayAlt.P.plane_wave_vector_identity

end Formalism.FourierDecayAlt.P5
