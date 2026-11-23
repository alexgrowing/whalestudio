import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacDiag

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul_mat_inv {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k * mat k⁻¹ = 1 := by
  show ((k * k⁻¹ : UA σ J) : GL (Fin d) (AE F E)).1 = 1
  rw [mul_inv_cancel]; rfl

theorem mat_inv_mul_mat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k⁻¹ * mat k = 1 := by
  show ((k⁻¹ * k : UA σ J) : GL (Fin d) (AE F E)).1 = 1
  rw [inv_mul_cancel]; rfl

def diagOne {R : Type} [CommRing R] {d : ℕ} (A B : Matrix (Fin d) (Fin d) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    GL (Fin d ⊕ Fin d) R :=
  ⟨fromBlocks A 0 0 1, fromBlocks B 0 0 1, by simp [fromBlocks_multiply, hAB, ← fromBlocks_one],
    by simp [fromBlocks_multiply, hBA, ← fromBlocks_one]⟩

theorem diag_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
        Matrix.fromBlocks (mat k) 0 0 1 ∧ g ∈ GlobalTheory.DblVac.KD σ W v := by
  intro k hk
  let M := diagOne (mat k) (mat k⁻¹) (mat_mul_mat_inv k) (mat_inv_mul_mat k)
  have hU : (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F W.J) *
      (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F W.J) := by
    have hk2 : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
    show (fromBlocks (mat k) 0 0 1)ᵀ * fromBlocks (incM F W.J) 0 0 (-incM F W.J) *
      (fromBlocks (mat k) 0 0 (1 : Matrix (Fin d) (Fin d) (AE F E))).map (cA σ) = fromBlocks (incM F W.J) 0 0 (-incM F W.J)
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hk2, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
  refine ⟨⟨M, hU⟩, rfl, ?_, ?_⟩
  · intro u hu
    have h1 := hk.1 u hu
    show u • (fromBlocks (mat k) 0 0 1 - 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = 0
    have h1' : u • (mat k - 1) = 0 := h1
    rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul, ← sub_eq_add_neg]
    simp [h1']
  · intro z hz
    have hinv : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W)⁻¹ = fromBlocks (mat k⁻¹) 0 0 1 := rfl
    have hfw : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W) = fromBlocks (mat k) 0 0 1 := rfl
    rw [hinv, hfw]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).1)
    · rw [fromBlocks_mulVec]; simpa using hz.2
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).2)
    · rw [fromBlocks_mulVec]; simpa using hz.2

end GlobalTheory.DblVacDiag
