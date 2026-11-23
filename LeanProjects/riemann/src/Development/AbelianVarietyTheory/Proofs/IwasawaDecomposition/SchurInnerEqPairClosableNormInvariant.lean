import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

theorem inner_eq_of_diag {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A A' : H →ₗ[ℂ] E) (c : ℂ)
    (h : ∀ w ∈ D, ⟪A w, A' w⟫_ℂ = c * ⟪w, w⟫_ℂ) :
    ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro w hw w' hw'
  have h1 := h (w + w') (D.add_mem hw hw')
  have h2 := h (w + Complex.I • w') (D.add_mem hw (D.smul_mem _ hw'))
  have h3 := h w hw
  have h4 := h w' hw'
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 - (1 / 2 - Complex.I / 2) * h3
    - (1 / 2 - Complex.I / 2) * h4
    + (1 / 2 : ℂ) * (⟪A w, A' w'⟫_ℂ - c * ⟪w, w'⟫_ℂ - ⟪A w', A' w⟫_ℂ + c * ⟪w', w⟫_ℂ
      - Complex.I * (⟪A w', A' w'⟫_ℂ - c * ⟪w', w'⟫_ℂ)) * hI

theorem tendsto_zero_of_norm_sq {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A : H →ₗ[ℂ] E) (a : ℝ)
    (h : ∀ w ∈ D, ‖A w‖ ^ 2 = a * ‖w‖ ^ 2) (u : ℕ → H) (hu : ∀ i, u i ∈ D)
    (h0 : Tendsto u atTop (𝓝 0)) : Tendsto (fun i => A (u i)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h0 ⊢
  have h1 : Tendsto (fun i => a * ‖u i‖ ^ 2) atTop (𝓝 0) := by
    simpa using (h0.pow 2).const_mul a
  have h2 := h1.sqrt
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun i => ?_
  rw [← h _ (hu i), Real.sqrt_sq (norm_nonneg _)]

theorem inner_eq_pair : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A A' hA hA' hAA' hc hc'
  obtain ⟨a, ha⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A hA hc
  obtain ⟨a', ha'⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A' hA' hc'
  have hexp : ∀ (z : ℂ) (w : H), ‖(z • A + A') w‖ ^ 2 =
      ‖z‖ ^ 2 * ‖A w‖ ^ 2 + 2 * ((starRingEnd ℂ) z * ⟪A w, A' w⟫_ℂ).re + ‖A' w‖ ^ 2 := by
    intro z w
    rw [LinearMap.add_apply, LinearMap.smul_apply, @norm_add_sq ℂ, inner_smul_left, norm_smul,
      mul_pow]
    rfl
  have key : ∀ z : ℂ, ∃ b : ℝ, ∀ w ∈ D, ‖(z • A + A') w‖ ^ 2 = b * ‖w‖ ^ 2 := by
    intro z
    refine norm_sq_eq ι H E ρ D hn hinv hirr hD (z • A + A') ?_ ?_
    · intro i w hw
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hexp, hexp, hA i w hw, hA' i w hw,
        hAA' i w hw]
    · intro u f hu h0 hf
      have h1 := tendsto_zero_of_norm_sq D A a ha u hu h0
      have h2 := tendsto_zero_of_norm_sq D A' a' ha' u hu h0
      have h3 := (h1.const_smul z).add h2
      rw [smul_zero, add_zero] at h3
      exact tendsto_nhds_unique hf h3
  obtain ⟨b, hb⟩ := key 1
  obtain ⟨b', hb'⟩ := key Complex.I
  refine ⟨⟨(b - a - a') / 2, (b' - a - a') / 2⟩, inner_eq_of_diag D A A' _ fun w hw => ?_⟩
  have e1 := hb w hw
  have e2 := hb' w hw
  rw [hexp, ha w hw, ha' w hw] at e1 e2
  have e3 : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e3]
  simp only [map_one, one_mul, norm_one, one_pow, Complex.norm_I, Complex.conj_I, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at e1 e2
  apply Complex.ext
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; linarith
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; linarith

end GlobalTheory.ClosableSchur
