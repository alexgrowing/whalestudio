import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.UnitFv

theorem unitary_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v))
  (hπ : ∀ z, π₁ (cA σ z) = π₂ z) (g : GlobalTheory.DblVac.UD σ W) :   (Matrix.fromBlocks (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))))ᵀ *
    Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) *
    (Matrix.fromBlocks (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) =
  Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) := by
  set M := GlobalTheory.DblVac.matD g with hMdef
  set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁
  have hg : Mᵀ * dbl (incM F W.J) * M.map (cA σ) = dbl (incM F W.J) := g.2
  have hmap := congrArg (fun X => X.map π₁) hg
  simp only [Matrix.map_mul, Matrix.transpose_map] at hmap
  have h2 : (M.map (cA σ)).map π₁ = M.map π₂ := by
    rw [Matrix.map_map]; ext i j; simp [hπ]
  have hD : (dbl (incM F W.J)).map π₁ = Matrix.fromBlocks J₁ 0 0 (-J₁) := by
    simp [dbl, Matrix.fromBlocks_map, hJ₁]
    try (ext i j; simp)
  rw [h2, hD] at hmap

  have hblk : ∀ (π : AE F E →+* Fv F v) (b : GL (Fin d) (Fv F v)),
      Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      = Matrix.fromBlocks ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
        * M.map π * Matrix.fromBlocks (b : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b : Matrix (Fin d) (Fin d) (Fv F v)) := by
    intro π b
    have : M.map π = Matrix.fromBlocks (M.toBlocks₁₁.map π) (M.toBlocks₁₂.map π) (M.toBlocks₂₁.map π) (M.toBlocks₂₂.map π) := by
      rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks]
    rw [this, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hmid : Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * J₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * J₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))))
      = (Matrix.fromBlocks (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))ᵀ * Matrix.fromBlocks J₁ 0 0 (-J₁)
        * Matrix.fromBlocks (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hinv : ∀ b : GL (Fin d) (Fv F v),
      Matrix.fromBlocks (b : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b : Matrix (Fin d) (Fin d) (Fv F v)) *
      Matrix.fromBlocks ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) = 1 := by
    intro b
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  rw [hblk π₁ b₁, hblk π₂ b₂, hmid]
  set P₁ := Matrix.fromBlocks (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₁ : Matrix (Fin d) (Fin d) (Fv F v))
  set P₂ := Matrix.fromBlocks (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₂ : Matrix (Fin d) (Fin d) (Fv F v))
  set Q₁ := Matrix.fromBlocks ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
  set Q₂ := Matrix.fromBlocks ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
  have e1 : Q₁ᵀ * P₁ᵀ = 1 := by rw [← Matrix.transpose_mul, hinv b₁, Matrix.transpose_one]
  have e2 : P₂ * Q₂ = 1 := hinv b₂
  set D := Matrix.fromBlocks J₁ 0 0 (-J₁)
  calc (Q₁ * M.map π₁ * P₁)ᵀ * (P₁ᵀ * D * P₂) * (Q₂ * M.map π₂ * P₂)
      = P₁ᵀ * ((M.map π₁)ᵀ * (Q₁ᵀ * P₁ᵀ) * D * (P₂ * Q₂) * M.map π₂) * P₂ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = P₁ᵀ * D * P₂ := by
        rw [e1, e2, Matrix.mul_one, Matrix.mul_one, hmap, Matrix.mul_assoc]

end GlobalTheory.UnitFv
