import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsPreserveGramMatrixStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.QhtUnip

theorem cA_cA_of_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  have h : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    apply Algebra.TensorProduct.ext'
    intro a e
    simp [cA, hσ]
  exact congrArg (fun f => f z) h

theorem heis_rel_of_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ e, σ (σ e) = e) {m : ℕ} (J₁ : Matrix (Fin m) (Fin m) E) (a w : Fin m → AE F E) (α : AE F E)
    (hU : (Heisenberg₂ a w α)ᵀ * (gI J₁).map (inclR (F := F) (AF F)) * (Heisenberg₂ a w α).map (cA σ) =
      (gI J₁).map (inclR (F := F) (AF F))) :
    (∀ k, a k = -∑ j, inclR (F := F) (AF F) (J₁ k j) * cA σ (w j)) ∧
      cA σ (2 * α + ∑ j, ∑ k, w j * inclR (F := F) (AF F) (J₁ j k) * cA σ (w k)) =
        2 * α + ∑ j, ∑ k, w j * inclR (F := F) (AF F) (J₁ j k) * cA σ (w k) := by
  refine ⟨fun k => ?_, ?_⟩
  · have h1 := congrFun (congrFun hU (Sum.inl (Sum.inr k))) (Sum.inr 0)
    simp [Matrix.mul_apply, Heisenberg₂, gI, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply] at h1
    linear_combination h1
  · have h2 := congrFun (congrFun hU (Sum.inr 0)) (Sum.inr 0)
    simp [Matrix.mul_apply, Heisenberg₂, gI, Matrix.fromBlocks, Fintype.sum_sum_type] at h2
    have hQ : (∑ k, (∑ j, w j * inclR (F := F) (AF F) (J₁ j k)) * cA σ (w k)) =
        ∑ j, ∑ k, w j * inclR (F := F) (AF F) (J₁ j k) * cA σ (w k) := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [hQ] at h2
    have h3 := congrArg (cA σ) h2
    simp only [map_add, map_neg, map_zero, cA_cA_of_invol σ hσ] at h3
    rw [map_add, map_mul, map_ofNat]
    linear_combination h3 - h2

theorem heis_rel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ (g : UA σ W.J) (a w : Fin m → AE F E) (α : AE F E), crd H g = Heisenberg₂ a w α →
      (∀ k, a k = -∑ j, inclR (F := F) (AF F) (W₁.J k j) * cA σ (w j)) ∧
      cA σ (2 * α + ∑ j, ∑ k, w j * inclR (F := F) (AF F) (W₁.J j k) * cA σ (w k)) =
        2 * α + ∑ j, ∑ k, w j * inclR (F := F) (AF F) (W₁.J j k) * cA σ (w k) := by
  intro F E _ _ _ _ _ σ hσ B m W r s hW W₁ H i₀ i₁ hA g a w α hg
  have hU := GlobalTheory.T.coords_preserve_gram_matrix F E σ hσ B W r s hW W₁ H i₀ i₁ hA g
  rw [hg] at hU
  exact heis_rel_of_unit σ hσ W₁.J a w α hU

end GlobalTheory.QhtUnip
