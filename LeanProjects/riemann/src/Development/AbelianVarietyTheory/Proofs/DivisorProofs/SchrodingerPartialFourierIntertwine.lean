import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalIntegralComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralOfIntegrableBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerActionContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSeminormPolynomialGrowthStatement

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.SchrPairing

open MeasureTheory
open scoped FourierTransform

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + x ^ N) := by
        have : 0 ≤ x ^ N := pow_nonneg hx N
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) N]
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + x ^ N) := by
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) N]

theorem exists_multiplier : ∀ {V U : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (Λ₁ Λ₂ : U →L[ℝ] V) (φ : SchwartzMap U ℂ) (f₀ : SchwartzMap V ℂ),
    ∃ f : SchwartzMap V ℂ, ∀ (ℓ : SchwartzMap V ℂ →L[ℂ] ℂ) (ξ : U),
      (∀ (s : U) (g : SchwartzMap V ℂ), ⇑g = GlobalTheory.ArchUniq.schrF P (Λ₁ s, Λ₂ s) ⇑f₀ →
        ℓ g = Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ s ξ : ℝ) : ℂ)) * ℓ f₀) →
      ℓ f = φ ξ * ℓ f₀ := by
  intro V U _ _ _ _ _ _ _ _ P hP Λ₁ Λ₂ φ f₀
  set ψ : 𝓢(U, ℂ) := 𝓕 φ with hψ
  set G : U → 𝓢(V, ℂ) := fun s => schrSch hP (Λ₁ s, Λ₂ s) f₀ with hGdef
  set H : U → 𝓢(V, ℂ) := fun s => ψ s • G s with hHdef
  have hGc : Continuous G := (GlobalTheory.T.schrodinger_action_continuous hP f₀).comp (Λ₁.continuous.prodMk Λ₂.continuous)
  have hHc : Continuous H := ψ.continuous.smul hGc

  have hdom : ∀ k m : ℕ, ∃ c : U → ℝ, Integrable c volume ∧ ∀ s, SchwartzMap.seminorm ℂ k m (H s) ≤ c s := by
    intro k m
    obtain ⟨C, N, hC⟩ := GlobalTheory.T.schrodinger_seminorm_polynomial_growth hP f₀ k m
    set c0 : ℝ := 1 + ‖Λ₁‖ + ‖Λ₂‖ with hc0
    refine ⟨fun s => (|C| * c0 ^ N * 2 ^ N) * (‖ψ s‖ + ‖s‖ ^ N * ‖ψ s‖), ?_, fun s => ?_⟩
    · exact ((ψ.integrable.norm).add (SchwartzMap.integrable_pow_mul volume ψ N)).const_mul _
    · have h1 : SchwartzMap.seminorm ℂ k m (H s) = ‖ψ s‖ * SchwartzMap.seminorm ℂ k m (G s) := by
        simp only [hHdef, map_smul_eq_mul]
      have hw : ‖((Λ₁ s, Λ₂ s) : V × V)‖ ≤ (‖Λ₁‖ + ‖Λ₂‖) * ‖s‖ := by
        rw [Prod.norm_def]
        refine max_le ?_ ?_
        · nlinarith [Λ₁.le_opNorm s, norm_nonneg Λ₂, norm_nonneg s]
        · nlinarith [Λ₂.le_opNorm s, norm_nonneg Λ₁, norm_nonneg s]
      have hs0 := norm_nonneg s
      have h2 : (1 + ‖((Λ₁ s, Λ₂ s) : V × V)‖) ^ N ≤ c0 ^ N * (2 ^ N * (1 + ‖s‖ ^ N)) := by
        calc (1 + ‖((Λ₁ s, Λ₂ s) : V × V)‖) ^ N ≤ (c0 * (1 + ‖s‖)) ^ N := by
              refine pow_le_pow_left₀ (by positivity) ?_ N
              rw [hc0]; nlinarith [norm_nonneg Λ₁, norm_nonneg Λ₂]
          _ = c0 ^ N * (1 + ‖s‖) ^ N := mul_pow _ _ _
          _ ≤ c0 ^ N * (2 ^ N * (1 + ‖s‖ ^ N)) := by
              gcongr
              exact one_add_pow_le _ hs0 N
      have h3 : SchwartzMap.seminorm ℂ k m (G s) ≤ |C| * (c0 ^ N * (2 ^ N * (1 + ‖s‖ ^ N))) := by
        refine (hC _).trans ?_
        have : 0 ≤ (1 + ‖((Λ₁ s, Λ₂ s) : V × V)‖) ^ N := by positivity
        calc C * (1 + ‖((Λ₁ s, Λ₂ s) : V × V)‖) ^ N ≤ |C| * (1 + ‖((Λ₁ s, Λ₂ s) : V × V)‖) ^ N := by
              gcongr; exact le_abs_self C
          _ ≤ _ := by gcongr
      rw [h1]
      calc ‖ψ s‖ * SchwartzMap.seminorm ℂ k m (G s) ≤ ‖ψ s‖ * (|C| * (c0 ^ N * (2 ^ N * (1 + ‖s‖ ^ N)))) := by
            gcongr
        _ = (|C| * c0 ^ N * 2 ^ N) * (‖ψ s‖ + ‖s‖ ^ N * ‖ψ s‖) := by ring
  have hmeas : ∀ (n : ℕ) (x : V), AEStronglyMeasurable (fun s => iteratedFDeriv ℝ n (H s) x) volume :=
    fun n x => (GlobalTheory.SchwartzIntegral.continuous_iteratedFDeriv_param hHc n x).aestronglyMeasurable
  obtain ⟨f, hf, -, -⟩ := GlobalTheory.ConeSch.exists_schwartz_integral volume H hmeas hdom
  refine ⟨f, fun ℓ ξ hℓ => ?_⟩
  have hint : ∀ k m : ℕ, Integrable (fun s => SchwartzMap.seminorm ℂ k m (H s)) volume := by
    intro k m
    obtain ⟨c, hc, hcb⟩ := hdom k m
    refine hc.mono' ?_ (.of_forall fun s => ?_)
    · exact (((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, m)).comp hHc).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
      exact hcb s
  rw [GlobalTheory.SchwartzIntegral.clm_apply_eq_integral ℓ hHc hint hf]
  have hterm : ∀ s, ℓ (H s) = ψ s * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ s ξ : ℝ) : ℂ)) * ℓ f₀ := by
    intro s
    rw [hHdef, map_smul, smul_eq_mul, hℓ s (G s) (coe_schrSch hP _ f₀)]
    ring
  simp_rw [hterm]
  rw [integral_mul_const]
  congr 1
  have hinv : φ ξ = (𝓕⁻ ψ) ξ := by
    rw [hψ, FourierPair.fourierInv_fourier_eq]
  rw [hinv, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (.of_forall fun s => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory.SchrPairing
