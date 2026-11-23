import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasSgsPow

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

def psiMaj (a : ℝ) (γ : Mx k r) (q : B.SS k r × Mt k r) : ℝ :=
  B.gN ((Matrix.of q.1.1.1)⁻¹ * (Matrix.of q.1.1.2)⁻¹ * Matrix.of q.2) ^ (-a) *
    B.gN ((Matrix.of q.2)⁻¹ * γ * Matrix.of q.1.2.2 * Matrix.of q.1.2.1) ^ (-a)

def gFib (a : ℝ) (G0 : Mx k r) (t : Mt k r) : ℝ :=
  B.gN (Matrix.of t) ^ (-a) * B.gN ((Matrix.of t)⁻¹ * G0) ^ (-a)

theorem gN_nonneg (g : Mx k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

end Formalism.FourierDecayAlt.P.S3dx6
