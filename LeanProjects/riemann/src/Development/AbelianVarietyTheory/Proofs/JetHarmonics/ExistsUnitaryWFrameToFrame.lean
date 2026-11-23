import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P

namespace GlobalTheory.FrameTrans

variable {k r : ℕ}

noncomputable def swapMat (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  1 + Matrix.of fun p q => ∑ c, (B' c p - B c p) * herm H (bvec q) (B c)

end GlobalTheory.FrameTrans

namespace GlobalTheory

end GlobalTheory
