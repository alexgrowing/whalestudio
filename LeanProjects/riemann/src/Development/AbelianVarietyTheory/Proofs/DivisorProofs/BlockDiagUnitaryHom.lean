import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory

theorem blockDiag_transpose {A : Type} [CommRing A] {m n ι : Type} (e : m ⊕ n ≃ ι) (x : Matrix m m A) (y : Matrix n n A) :
    (blkMat e x y)ᵀ = blkMat e xᵀ yᵀ := by
  simp [blkMat, Matrix.fromBlocks_transpose, Matrix.transpose_submatrix]

theorem blockDiag_unitary_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (W : Spc F E n)
    (W₂ : Spc F E (n + n)), W₂.J = dblGram finSumFinEquiv W.J →
    ∃ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, ∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h') := by
  intro F E _ _ _ _ _ σ n W W₂ hW
  have hJ : incM F W₂.J = blkMat finSumFinEquiv (incM F W.J) (-incM F W.J) := by
    rw [hW, incM, dblGram, blkMat_map _ _ (map_zero _)]
    congr 1
    ext i j; simp [incM]
  refine ⟨((blkGL finSumFinEquiv).comp ((UG (cA σ) (incM F W.J)).subtype.prodMap
    (UG (cA σ) (incM F W.J)).subtype)).codRestrict _ ?_, fun h h' => rfl⟩
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  change (blkMat finSumFinEquiv x.1 y.1)ᵀ * incM F W₂.J * (blkMat finSumFinEquiv x.1 y.1).map (cA σ) = incM F W₂.J
  have hx' : (x : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F W.J * (x : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F W.J := hx
  have hy' : (y : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F W.J * (y : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F W.J := hy
  rw [hJ, blockDiag_transpose, blkMat_map _ _ (map_zero _), blkMat_mul, blkMat_mul, hx']
  congr 1
  rw [Matrix.mul_neg, Matrix.neg_mul, hy']

end GlobalTheory
