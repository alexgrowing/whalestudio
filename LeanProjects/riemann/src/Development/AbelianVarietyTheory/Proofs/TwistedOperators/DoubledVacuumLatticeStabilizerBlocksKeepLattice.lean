import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac.BlocksPreserved

theorem blocks_keep {R : Type} [CommRing R] {d : ℕ} (S : AddSubgroup (Fin d → R))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R)
    (h : ∀ z : Fin d ⊕ Fin d → R, z ∘ Sum.inl ∈ S → z ∘ Sum.inr ∈ S →
      (M *ᵥ z) ∘ Sum.inl ∈ S ∧ (M *ᵥ z) ∘ Sum.inr ∈ S) :
    (∀ z ∈ S, M.toBlocks₁₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₁₂ *ᵥ z ∈ S) ∧
    (∀ z ∈ S, M.toBlocks₂₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₂₂ *ᵥ z ∈ S) := by
  have eL : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inl = z := fun z => rfl
  have eR : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inr = 0 := fun z => rfl
  have fL : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inl = 0 := fun z => rfl
  have fR : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inr = z := fun z => rfl
  have a11 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inl = M.toBlocks₁₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  have a21 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inr = M.toBlocks₂₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁]
  have a12 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inl = M.toBlocks₁₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂]
  have a22 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inr = M.toBlocks₂₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).1
    rwa [a11] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).1
    rwa [a12] at this
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).2
    rwa [a21] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).2
    rwa [a22] at this

end GlobalTheory.DblVac.BlocksPreserved

namespace GlobalTheory.DblVac

theorem KD_blocks_keep : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F), ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ σ d W v g hg
  have h1 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).1)
  have h2 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g⁻¹)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).2)
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

end GlobalTheory.DblVac
