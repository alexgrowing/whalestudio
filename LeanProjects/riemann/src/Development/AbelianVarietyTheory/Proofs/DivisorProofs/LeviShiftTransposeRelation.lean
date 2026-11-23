import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LeviShift

theorem shiftA_mul_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ d d₁ : ℕ)
    (W : Spc F E d) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J)
    (m : UA σ W.J), IsLevi H' t h₁ m → ∀ l : (AE F E)ˣ,
      shiftA H H' (l * Units.map (cA σ : AE F E →* AE F E) t) * (mat m)ᵀ = shiftA H H' l := by
  intro F E _ _ _ _ _ σ n n₁ d d₁ W W₁ H H' t h₁ m h l
  have hv : Matrix.vecMulVec (incV F H.x) (incV F H'.y) * (mat m)ᵀ = cA σ (t⁻¹).1 • Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h.2.1]
    ext i j
    simp [Matrix.vecMulVec_apply, mul_left_comm]
  have hc : cA σ t.1 * cA σ (t⁻¹).1 = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [shiftA, shiftA, Matrix.smul_mul, hv, smul_smul]
  congr 1
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  rw [mul_assoc, hc, mul_one]

end GlobalTheory.ThK.LeviShift
