import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem gf_castPt {k a b : ℕ} (h : a = b) (z z' : Fin (2 * a + k + 1) → ℂ) (A M C : B.Mat k a) :
    Gf k b (D.castV h z) (D.castV h z') ((D.castM h A)⁻¹ * D.castM h M * D.castM h C) =
      Gf k a z z' (A⁻¹ * M * C) := by
  subst h
  have h1 : ∀ v : Fin (2 * a + k + 1) → ℂ, D.castV rfl v = v := fun v => by
    funext i
    simp [D.castV]
  have h2 : ∀ X : B.Mat k a, D.castM rfl X = X := fun X => by
    ext i j
    simp [D.castM]
  rw [h1, h1, h2, h2, h2]

theorem gram_function_induction : GfStep := by
  intro k ρ m e z z' hz hz' t _ γ xx
  have h1 : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ
  show Gf k m (D.castV e (D.castV h1 (liftVec k 1 ρ z))) (D.castV e (D.castV h1 (liftVec k 1 ρ z')))
      ((D.castM e (D.castM h1 (U.Rn k 1 ρ xx.1)))⁻¹ *
        D.castM e (D.castM h1 (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) *
        D.castM e (D.castM h1 (U.Rn k 1 ρ xx.2))) = _
  rw [gf_castPt e, gf_castPt h1,
    level_function_slice k 1 ρ _ _ (Qx4.lift_inWb hz) (Qx4.lift_inWb hz'), lowV_lift, lowV_lift]
  simp [Matrix.det_unique, Complex.normSq_eq_norm_sq]

end Formalism.FourierDecayAlt.P.CutSH.SFG
