import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.fromBlocks_unitary_transfer : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  intro A O _ _ ι γ c n P K JL hinj hγ hP M G hM hG
  have hmul : ∀ {m : Type} [Fintype m] (X Y : Matrix m m O), (X * Y).map ι = X.map ι * Y.map ι := by
    intro m _ X Y; ext i j; simp [Matrix.mul_apply, map_sum]
  have hneg : (-JL).map ι = -(JL.map ι) := by ext i j; simp
  have hD : (Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ
      = (Matrix.fromBlocks JL 0 0 (-JL)).map ι := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hneg, ← hP]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  have hc : (G.map c).map ι = (G.map ι).map γ := by
    ext i j; simp [hγ]
  apply Matrix.map_injective hinj
  show (Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c).map ι = (Matrix.fromBlocks JL 0 0 (-JL)).map ι
  rw [hmul, hmul, Matrix.transpose_map, hc]
  conv_lhs => rw [← hD]
  have hG' : (Matrix.fromBlocks P 0 0 P * G.map ι).map γ = (Matrix.fromBlocks P 0 0 P).map γ * (G.map ι).map γ := by
    rw [Matrix.map_mul]
  calc (G.map ι)ᵀ * ((Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ) * (G.map ι).map γ
      = (Matrix.fromBlocks P 0 0 P * G.map ι)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P * G.map ι).map γ := by
        rw [hG', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (M * Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (M * Matrix.fromBlocks P 0 0 P).map γ := by rw [hG]
    _ = (Matrix.fromBlocks P 0 0 P)ᵀ * (Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ) * (Matrix.fromBlocks P 0 0 P).map γ := by
        rw [Matrix.map_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hD]
