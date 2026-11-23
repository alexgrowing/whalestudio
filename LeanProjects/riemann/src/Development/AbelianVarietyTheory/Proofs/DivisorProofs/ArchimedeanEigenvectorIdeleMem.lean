import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LemF.IwasawaScal

theorem idele_mem_idelesAt_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ : ℕ),
    H.IsAdapted σ B X X₁ i₀ i₁ → ∀ p ∈ UAt σ X (evI F), ∀ t : (AE F E)ˣ,
    mat p *ᵥ incV F H.x = t.1 • incV F H.x → t ∈ idelesAt E (evI F) := by
  intro F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ hH p hp t ht
  rw [GlobalTheory.ThK.mem_idelesAt]
  intro u hu
  have hx : H.x ≠ 0 := by
    intro h0
    have := hH.xy
    simp [form, h0] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have h1 : u • (mat p - 1) = 0 := hp u hu
  have h2 : (mat p - 1) *ᵥ incV F H.x = ((t : AE F E) - 1) • incV F H.x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ht, sub_smul, one_smul]
  have h3 : u • ((mat p - 1) *ᵥ incV F H.x) = 0 := by
    rw [← Matrix.smul_mulVec, h1, Matrix.zero_mulVec]
  have h4 : (u • ((t : AE F E) - 1)) * incV F H.x i = 0 := by
    have := congrFun h3 i
    rw [h2] at this
    simpa [Pi.smul_apply, smul_eq_mul, smul_mul_assoc] using this
  have hu' : IsUnit (incV F H.x i) := by
    unfold incV
    exact (isUnit_iff_ne_zero.mpr hi).map _
  exact (hu'.mul_left_eq_zero).mp h4

end GlobalTheory.ThK.LemF.IwasawaScal
