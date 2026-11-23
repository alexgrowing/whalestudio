import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsCombineMk

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem mulOp_comm_fn (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π'))
    (m : (Fin r → ℂ) → Mx k r → ℂ) (hW : multiplicationOperator W m) (j : Fin 6) : W * X.fn j = X.fn j * W := by
  have hW1 : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      m c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g := hW
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  simp only [Module.End.mul_apply]
  rw [hW1]
  by_cases hp : (c, g) ∈ DomR k r z z'
  · have h1 := X.fn_apply j Φ (c, g) hp
    have h2 := X.fn_apply j (W Φ) (c, g) hp
    simp only at h1 h2
    rw [h1, h2, hW1, smul_comm]
  · have h1 := (X.fn j Φ).2.1 (c, g) hp
    have h2 := (X.fn j (W Φ)).2.1 (c, g) hp
    simp only at h1 h2
    rw [h1, h2, smul_zero]

end Actual

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
