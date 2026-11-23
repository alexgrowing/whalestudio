import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransformStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem gram_grad_scale_arith (D c P Q a : ℝ) (ha : 0 < a) (hP : 0 < P) (hQ : 0 < Q)
    (h : P / Q * D ≤ c * P ^ 3 / a) : D ≤ c * P ^ 2 * Q / a := by
  have h1 : D = Q / P * (P / Q * D) := by field_simp
  have h2 : 0 ≤ Q / P := (div_pos hQ hP).le
  calc D = Q / P * (P / Q * D) := h1
    _ ≤ Q / P * (c * P ^ 3 / a) := mul_le_mul_of_nonneg_left h h2
    _ = c * P ^ 2 * Q / a := by field_simp

theorem gram_grad_comp_smul (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x' : E) (a P t : ℝ)
    (ha : 0 < a) (hP : 0 < P)
    (h1 : ∀ p q, DifferentiableAt ℝ (fun y => G (t • y) p q) x')
    (h2 : ∀ p q, DifferentiableAt ℝ (fun y => V (t • y) p q) x')
    (h3 : ∀ᶠ y in nhds x', (G (t • y)).PosDef ∧ LinearIndependent ℂ (V (t • y))ᵀ)
    (h4 : ((V (t • x'))ᴴ * G (t • x') * V (t • x') -
      (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    (h5 : ∀ p q, ‖G (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G (t • y) p q) x'‖ ≤ P)
    (h6 : ∀ p q, ‖V (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V (t • y) p q) x'‖ ≤ P) :
    ‖fderiv ℝ (fun y => Real.log ((V (t • y))ᴴ * G (t • y) * V (t • y)).det.re) x'‖ ≤
      3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 3 / a :=
  GlobalTheory.T.log_det_gram_subharmonic n k E (fun u => G (t • u)) (fun u => V (t • u)) x' a P ha hP.le h1 h2 h3 h4 h5 h6

theorem gram_grad_scaled : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  intro n k E _ _ G V x a P Q ha hP hPQ hGd hVd hev hH hGb hVb
  have hQ : 0 < Q := lt_of_lt_of_le hP hPQ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = P / Q := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ div_pos hP hQ
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨x', hx'⟩ : ∃ x' : E, x' = t⁻¹ • x := ⟨_, rfl⟩
  have hcx : t • x' = x := by rw [hx', smul_smul, mul_inv_cancel₀ htne, one_smul]
  have hL : DifferentiableAt ℝ (fun u : E => t • u) x' := (differentiableAt_id).const_smul t
  have hdiff : ∀ f : E → ℂ, DifferentiableAt ℝ f x →
      DifferentiableAt ℝ (fun u => f (t • u)) x' := by
    intro f hf
    have hf' : DifferentiableAt ℝ f (t • x') := by rw [hcx]; exact hf
    exact hf'.comp x' hL
  have hfd : ∀ f : E → ℂ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hfdR : ∀ f : E → ℝ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hbound : ∀ f : E → ℂ, ‖fderiv ℝ f x‖ ≤ Q →
      ‖fderiv ℝ (fun u => f (t • u)) x'‖ ≤ P := by
    intro f hf
    rw [hfd, norm_smul, Real.norm_of_nonneg ht0.le, ht]
    calc P / Q * ‖fderiv ℝ f x‖ ≤ P / Q * Q := mul_le_mul_of_nonneg_left hf (div_pos hP hQ).le
      _ = P := by field_simp
  have htend : Tendsto (fun u : E => t • u) (nhds x') (nhds x) := by
    have := hL.continuousAt.tendsto
    rwa [hcx] at this
  have key := gram_grad_comp_smul n k E G V x' a P t ha hP
    (fun p q => hdiff (fun y => G y p q) (hGd p q))
    (fun p q => hdiff (fun y => V y p q) (hVd p q))
    (htend.eventually hev)
    (by rw [hcx]; exact hH)
    (fun p q => ⟨by rw [hcx]; exact (hGb p q).1, hbound (fun y => G y p q) (hGb p q).2⟩)
    (fun p q => ⟨by rw [hcx]; exact (hVb p q).1, hbound (fun y => V y p q) (hVb p q).2⟩)
  have hk := hfdR (fun y => Real.log ((V y)ᴴ * G y * V y).det.re)
  rw [hk, norm_smul, Real.norm_of_nonneg ht0.le, ht] at key
  exact gram_grad_scale_arith _ _ P Q a ha hP hQ key

end GlobalTheory.CompanionTheory.Ar.PB.StepW
