import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Kr (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p : Mt k r × Mt k r, star (psi k r Bs.z' cStd (Matrix.of p.2)) •
    (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹) ∂(Bs.μW'.prod Bs.μN)

end Formalism.FourierDecayAlt.P.PBG
