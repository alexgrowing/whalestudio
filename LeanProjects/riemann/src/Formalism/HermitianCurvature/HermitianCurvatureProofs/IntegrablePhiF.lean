import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiMajNonneg

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def phiF (D : B.RealPlaceData k r Wp Wq) (σ : Mx k r → (H →L[ℂ] H)) (w0 x y : H) (X0 : Wq →L[ℂ] Wp) (γ : Mx k r)
    (q : B.SS k r × Mt k r) : Wq →L[ℂ] Wp :=
  (aInt D.z cStd D.π σ w0 x (Matrix.of q.2) q.1.1).comp
    (X0.comp (bInt D.z' cStd D.π' σ w0 y (Matrix.of q.2) γ q.1.2))

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun g : Mt k r => psi k r z c (Matrix.of g) := by
  have hl := B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

attribute [local instance] B7.properFD

end Formalism.FourierDecayAlt.P.S3dx6
