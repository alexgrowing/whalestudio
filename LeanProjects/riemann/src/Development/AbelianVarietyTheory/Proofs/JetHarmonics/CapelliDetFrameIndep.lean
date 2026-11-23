import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

theorem capelli_det_frame_indep : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B B' : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsFrameOf k r [z] B → IsFrameOf k r [z] B' → ∀ w : ℂ, qdet (EB π B) w = qdet (EB π B') w :=
  fun _ _ _ _ _ _ _ _ _ _ hz hT hπ hB hB' w => Formalism.FourierDecayAlt.P.QrCap.capChange hz hT hπ hB hB' w

end GlobalTheory
