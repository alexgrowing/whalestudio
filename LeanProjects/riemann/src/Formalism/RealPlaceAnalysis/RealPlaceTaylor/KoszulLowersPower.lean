import Formalism.RealPlaceAnalysis.UJLocCompact
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInducingCoeMatrix

open Matrix Topology

noncomputable section

namespace Formalism.REAL

def coeMatrixAlt {n : ℕ} (ε : Fin n → Bool) : UJ ε → Matrix (Fin n) (Fin n) ℂ :=
  fun g => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

lemma coeMatrix_left_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', jm_sq_lemma]

lemma coeMatrix_inv_eq {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ g.2)

lemma continuous_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Continuous (coeMatrixAlt ε) :=
  Units.continuous_val.comp continuous_subtype_val

lemma isClosed_pseudoUnitary {n : ℕ} (ε : Fin n → Bool) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε}
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

lemma range_coeMatrix {n : ℕ} (ε : Fin n → Bool) :
    Set.range (coeMatrixAlt ε) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have hl := coeMatrix_left_inv ε g hg
    let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp hl, hl⟩
    exact ⟨⟨u, hg⟩, rfl⟩

lemma isInducing_coeMatrix {n : ℕ} (ε : Fin n → Bool) : IsInducing (coeMatrixAlt ε) := by
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ =>
      (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  refine IsInducing.of_comp (continuous_coeMatrix ε) hc ?_
  have heq : (fun M : Matrix (Fin n) (Fin n) ℂ => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))) ∘ coeMatrixAlt ε
      = (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) ∘ (Subtype.val : UJ ε → _) := by
    funext g
    refine Prod.ext rfl ?_
    show MulOpposite.op (Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε) =
      MulOpposite.op (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)
    rw [coeMatrix_inv_eq]
  rw [heq]
  exact Units.isInducing_embedProduct.comp IsInducing.subtypeVal

lemma injective_coeMatrix {n : ℕ} (ε : Fin n → Bool) : Function.Injective (coeMatrixAlt ε) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

theorem isClosedEmbeddingMatrix : UJEmb := by
  intro n ε
  refine ⟨⟨⟨isInducing_coeMatrix ε, injective_coeMatrix ε⟩, ?_⟩, range_coeMatrix ε⟩
  show IsClosed (Set.range (coeMatrixAlt ε))
  rw [range_coeMatrix ε]
  exact isClosed_pseudoUnitary ε

theorem uJLocCompact_of (h : UJEmb) : UJLocCompact := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := Pi.locallyCompactSpace_of_finite
  exact (h n ε).1.locallyCompactSpace

end Formalism.REAL
