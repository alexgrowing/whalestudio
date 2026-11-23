import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

noncomputable section

namespace GlobalTheory.ThK.DecX

theorem decompose : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ),
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ w : Matrix (Fin n) (Fin d) (AE F E), At (evI F) w →
    ∃ (α β : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)), At (evI F) α ∧ At (evI F) β ∧ At (evI F) C ∧
      w = Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β := by
  intro F E _ _ _ _ _ σ B n d n₁ X X₁ H r s i₀ i₁ hX hH w hw
  obtain ⟨hdec, -⟩ := GlobalTheory.LeviRatHerm.decomp hX.lat hH
  choose a b u hsu using fun i : Fin n => hdec (Pi.single i 1)
  have hI : (1 : Matrix (Fin n) (Fin n) E) =
      Matrix.vecMulVec H.x a + H.ι * (Matrix.of u)ᵀ + Matrix.vecMulVec H.y b := by
    ext l i
    have := congrFun (hsu i) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
    simp only [Matrix.one_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.transpose_apply]
    rw [this]
    ring
  have h0 : ∀ c : AF F, evI F c = 0 → ∀ i j, c • w i j = 0 := fun c hc i j => by
    simpa using congrFun (congrFun (hw c hc) i) j
  have hAt : ∀ v : Fin n → AE F E, At (evI F) (v ᵥ* w) := by
    intro v c hc; funext j
    simp only [Pi.smul_apply, Matrix.vecMul, dotProduct, Finset.smul_sum, ← mul_smul_comm, h0 c hc, mul_zero,
      Finset.sum_const_zero, Pi.zero_apply]
  refine ⟨incV F a ᵥ* w, incV F b ᵥ* w, incM F (Matrix.of u)ᵀ * w, hAt _, hAt _, ?_, ?_⟩
  · intro c hc; ext k j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum, ← mul_smul_comm, h0 c hc, mul_zero,
      Finset.sum_const_zero, Matrix.zero_apply]
  · have hI' := congrArg (incM F) hI
    have e1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : incM F (Matrix.vecMulVec H.x a + H.ι * (Matrix.of u)ᵀ + Matrix.vecMulVec H.y b) =
        Matrix.vecMulVec (incV F H.x) (incV F a) + incM F H.ι * incM F (Matrix.of u)ᵀ +
          Matrix.vecMulVec (incV F H.y) (incV F b) := by
      ext i j
      simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_add, map_mul]
    rw [e1, e2] at hI'
    conv_lhs => rw [← Matrix.one_mul w, hI']
    have hv : ∀ (p : Fin n → AE F E) (q : Fin n → AE F E), Matrix.vecMulVec p q * w = Matrix.vecMulVec p (q ᵥ* w) := by
      intro p q; ext i l
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    rw [Matrix.add_mul, Matrix.add_mul, hv, hv, Matrix.mul_assoc]

end GlobalTheory.ThK.DecX
