import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight

noncomputable section

namespace GlobalTheory.ArchSchA

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def lagSetA (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) :
    Set ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
  {l | ∃ (y : Fin n → AE F E) (c : Fin d₁ → AE F E) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)),
    At (evI F) y ∧ At (evI F) c ∧ At (evI F) z ∧ arch F (M₁.co.e z).1 = 0 ∧
    l = (arch F (M.co.e (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) +
        incM F H.ι * z * (incM F H'.ι)ᵀ)).1,
      arch F (M.co.e (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) +
        incM F H.ι * z * (incM F H'.ι)ᵀ)).2)}

theorem zero_vecMulVec' {m k : ℕ} (x : Fin k → AE F E) : Matrix.vecMulVec (0 : Fin m → AE F E) x = 0 := by
  ext i j; simp [Matrix.vecMulVec_apply]

section Mem

variable (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)

theorem mem_lagSetA_y {y : Fin n → AE F E} (hy : At (evI F) y) :
    (arch F (M.co.e (Matrix.vecMulVec y (incV F H'.x))).1, arch F (M.co.e (Matrix.vecMulVec y (incV F H'.x))).2) ∈
      lagSetA M M₁ H H' := by
  refine ⟨y, 0, 0, hy, fun _ _ => smul_zero _, fun _ _ => smul_zero _, by simp [arch_zero'], ?_⟩
  simp only [Matrix.mulVec_zero, vecMulVec_zero', Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem mem_lagSetA_cz {c : Fin d₁ → AE F E} {z : Matrix (Fin n₁) (Fin d₁) (AE F E)} (hc : At (evI F) c)
    (hz : At (evI F) z) (hz1 : arch F (M₁.co.e z).1 = 0) :
    (arch F (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) + incM F H.ι * z * (incM F H'.ι)ᵀ)).1,
      arch F (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) + incM F H.ι * z * (incM F H'.ι)ᵀ)).2) ∈
      lagSetA M M₁ H H' := by
  refine ⟨0, c, z, fun _ _ => smul_zero _, hc, hz, hz1, ?_⟩
  simp only [zero_vecMulVec', zero_add]

theorem mem_lagSetA_c {c : Fin d₁ → AE F E} (hc : At (evI F) c) :
    (arch F (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c))).1,
      arch F (M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c))).2) ∈ lagSetA M M₁ H H' := by
  refine ⟨0, c, 0, fun _ _ => smul_zero _, hc, fun _ _ => smul_zero _, by simp [arch_zero'], ?_⟩
  simp only [zero_vecMulVec', zero_add, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem mem_lagrangian_set_archimedean {z : Matrix (Fin n₁) (Fin d₁) (AE F E)} (hz : At (evI F) z) (hz1 : arch F (M₁.co.e z).1 = 0) :
    (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1, arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) ∈
      lagSetA M M₁ H H' := by
  refine ⟨0, 0, z, fun _ _ => smul_zero _, fun _ _ => smul_zero _, hz, hz1, ?_⟩
  simp only [zero_vecMulVec', zero_add, Matrix.mulVec_zero, vecMulVec_zero']

end Mem

end GlobalTheory.ArchSchA
