import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaNonsplitIsotropicLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicEigenlineLocalSplitStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.IwasawaLineInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uAt_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g h : UA σ W.J}
    (hg : g ∈ UAt σ W (evFin F v)) (hh : h ∈ UAt σ W (evFin F v)) : g * h ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat (g * h) - 1 = mat g * (mat h - 1) + (mat g - 1) := by
    rw [show mat (g * h) = mat g * mat h from rfl, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

theorem uAt_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g : UA σ W.J}
    (hg : g ∈ UAt σ W (evFin F v)) : g⁻¹ ∈ UAt σ W (evFin F v) := by
  intro u hu
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem iwasawa_line_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F), IsEmpty (E →ₐ[F] Fv F v) → ∀ g ∈ UAt σ W (evFin F v),
      ∃ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) ∧ ∃ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J),
        IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧
        ∃ k ∈ KAt σ W v, g = u * m * k := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH v hv g hg
  have hx0 : H'.x ≠ 0 := by
    intro h0
    have := hH.xy
    rw [h0] at this
    simp [form] at this
  obtain ⟨k, hk, t, ht⟩ := GlobalTheory.T.iwasawa_nonsplit_isotropic_line F E σ B d W r s hB hW H'.x hx0 hH.xx v hv g hg
  have hp : g * k⁻¹ ∈ UAt σ W (evFin F v) := uAt_mul hg (uAt_inv hk.1)
  obtain ⟨u, hu, huA, h₁, m, hl, hm, hh₁, e⟩ :=
    GlobalTheory.T.parabolic_eigenline_local_split F E σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH v _ hp t ht
  exact ⟨u, hu, huA, t, h₁, m, hl, hm, hh₁, k, hk, by rw [← e, inv_mul_cancel_right]⟩

end GlobalTheory.IwasawaLineInert
end
