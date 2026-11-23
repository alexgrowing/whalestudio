import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviScalarAt

theorem scalar_mem_idelesAt_of_isLevi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (v : Pl F) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H' t h₁ m →
    m ∈ UAt σ W (evFin F v) → t ∈ idelesAt E (evFin F v) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ hA v t h₁ m hL hm
  rw [mem_idelesAt]
  intro u hu

  have hx : H'.x ≠ 0 := by
    intro h0
    have := hA.xy
    rw [h0] at this
    simp [form] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hunit : IsUnit (inclR (F := F) (AF F) (H'.x i)) := (Ne.isUnit hi).map _

  have hv : (mat m - 1) *ᵥ incV F H'.x = ((t : AE F E) - 1) • incV F H'.x := by
    rw [Matrix.sub_mulVec, hL.1, Matrix.one_mulVec, sub_smul, one_smul]
  have h0 : (u • (mat m - 1)) *ᵥ incV F H'.x = 0 := by
    have := hm u hu
    rw [this, Matrix.zero_mulVec]
  rw [Matrix.smul_mulVec, hv] at h0
  have hi0 := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi0
  have : (u • ((t : AE F E) - 1)) * incV F H'.x i = 0 := by
    rw [smul_mul_assoc]; exact hi0
  exact (hunit.mul_left_eq_zero).1 this

end GlobalTheory.LeviScalarAt
