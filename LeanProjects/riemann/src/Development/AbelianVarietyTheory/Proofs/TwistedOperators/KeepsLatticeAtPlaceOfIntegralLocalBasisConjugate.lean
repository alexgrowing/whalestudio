import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.KeepInt

theorem mulVec_conj_mem {d : ℕ} {K : Type} [Field K] (S : ValuationSubring K)
    (b : GL (Fin d) K) (M : Matrix (Fin d) (Fin d) K) (w : Fin d → K)
    (hM : ∀ i j, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) i j ∈ S)
    (hw : ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) i ∈ S) :
    ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w)) i ∈ S := by
  intro i
  have key : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w) =
      (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) *ᵥ
        (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) := by
    have h1 : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (b : Matrix (Fin d) (Fin d) K), h1, Matrix.mul_one]
  rw [key]
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem (fun j _ => mul_mem (hM i j) (hw j))

end GlobalTheory.KeepInt

theorem GlobalTheory.KeepInt.keepLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) → (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hiff A hA₁ hA₂ z hz
  obtain ⟨hAt, h₁, h₂⟩ := (hiff z).1 hz
  refine (hiff _).2 ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [← Matrix.mulVec_smul, hAt u hu, Matrix.mulVec_zero]
  · have e : (fun j => π₁ ((A *ᵥ z) j)) = (A.map π₁) *ᵥ (fun j => π₁ (z j)) := by
      funext j; exact RingHom.map_mulVec π₁ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₁ _ _ hA₁ h₁
  · have e : (fun j => π₂ ((A *ᵥ z) j)) = (A.map π₂) *ᵥ (fun j => π₂ (z j)) := by
      funext j; exact RingHom.map_mulVec π₂ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₂ _ _ hA₂ h₂
