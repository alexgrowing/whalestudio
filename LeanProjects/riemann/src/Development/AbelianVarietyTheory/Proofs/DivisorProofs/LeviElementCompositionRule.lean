import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueBis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviMulAdapted

theorem levi_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ (t u : (AE F E)ˣ) (a c d : UA σ X.J),
    IsLevi (W₁ := X₁) H t 1 a → IsLevi (W₁ := X₁) H u 1 c → IsLevi (W₁ := X₁) H (t * u) 1 d → a * c = d := by
  intro F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ r s r₁ s₁ hB hX _ hH t u a c d ha hc hd
  have hac : IsLevi (W₁ := X₁) H (t * u) 1 (a * c) := by
    have e : mat (a * c) = mat a * mat c := rfl
    have e1 : mat (1 : UA σ X₁.J) = 1 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e, ← Matrix.mulVec_mulVec, hc.1, Matrix.mulVec_smul, ha.1, smul_smul, Units.val_mul, mul_comm]
    · rw [e, ← Matrix.mulVec_mulVec, hc.2.1, Matrix.mulVec_smul, ha.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
    · rw [e, Matrix.mul_assoc, hc.2.2, e1, Matrix.mul_one, ha.2.2, e1, Matrix.mul_one]
  exact GlobalTheory.LeviUniqueGen.levi_unique_gen F E σ B (n₁ + 2) n₁ X X X₁ H r s i₀ i₁ hB hX hX hH (t * u) 1 (a * c) d hac hd

end GlobalTheory.LeviMulAdapted
