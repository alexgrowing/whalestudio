import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordEmbedBasis

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding

noncomputable section

variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

def mixedSpaceEquivPiOfTotallyComplex [IsTotallyComplex E] :
    mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ) where
  toFun p w := p.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun g := (0, fun w => g w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ rfl
    funext w
    exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
  right_inv _ := rfl

def embeddingBasisOfTotallyComplex [IsTotallyComplex E] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (InfinitePlace E → ℂ) :=
  (latticeBasis E).map (mixedSpaceEquivPiOfTotallyComplex E)

theorem embeddingBasisOfTotallyComplex_apply [IsTotallyComplex E]
    (j : Free.ChooseBasisIndex ℤ (𝓞 E)) (w : InfinitePlace E) :
    embeddingBasisOfTotallyComplex E j w = w.embedding (integralBasis E j) := by
  rw [embeddingBasisOfTotallyComplex, Basis.map_apply, latticeBasis_apply]
  exact mixedEmbedding_apply_isComplex _ _ ⟨w, IsTotallyComplex.isComplex w⟩

def piSwapEquiv : (ι → InfinitePlace E → ℂ) ≃ₗ[ℝ] (InfinitePlace E → ι → ℂ) :=
  { Equiv.piComm (fun (_ : ι) (_ : InfinitePlace E) => ℂ) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem CoordEmbedBasis.proof [IsTotallyComplex E] : CoordEmbedBasis.Statement E ι := by
  classical
  let B := (Pi.basis fun _ : ι => embeddingBasisOfTotallyComplex E).map (piSwapEquiv E ι)
  have hB : ∀ k, B k = coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) := by
    rintro ⟨i, j⟩
    funext w i'
    simp only [B, Basis.map_apply, Pi.basis_apply, coordEmbed_apply]
    show (Pi.single i (embeddingBasisOfTotallyComplex E j) : ι → InfinitePlace E → ℂ) i' w = _
    by_cases h : i' = i
    · subst h
      simp [embeddingBasisOfTotallyComplex_apply]
    · simp [Pi.single_eq_of_ne h]
  refine ⟨?_, ?_⟩
  · have hli := B.linearIndependent
    rwa [show (⇑B) = fun k => coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k) from
      funext hB] at hli
  · rw [finrank_eq_card_basis B, finrank_eq_card_basis (Pi.basis fun _ : ι => integralBasis E)]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
