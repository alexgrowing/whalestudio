import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section

namespace GlobalTheory.QhtUnip.BasisUnit

theorem isUnit_det_basQ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → IsUnit (basQ H).det := by
  intro F E _ _ _ _ _ σ B m W r s hW W₁ H i₀ i₁ hA
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  have hrange : LinearMap.range (Matrix.mulVecLin (basQ H)) = ⊤ := by
    rw [eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hA.split z hz
    refine ⟨(Sum.elim (Sum.elim (fun _ => a) u) (fun _ => b) : Ix m → E) ∘ ixE m, ?_⟩
    simp only [Matrix.mulVecLin_apply, basQ]
    rw [Matrix.submatrix_mulVec_equiv]
    ext r
    simp [Matrix.mulVec, dotProduct, basP, Fintype.sum_sum_type, Function.comp_def, mul_comm]
  intro z
  have : z ∈ LinearMap.range (Matrix.mulVecLin (basQ H)) := hrange ▸ Submodule.mem_top
  obtain ⟨v, hv⟩ := this
  exact ⟨v, hv⟩

end GlobalTheory.QhtUnip.BasisUnit

end
