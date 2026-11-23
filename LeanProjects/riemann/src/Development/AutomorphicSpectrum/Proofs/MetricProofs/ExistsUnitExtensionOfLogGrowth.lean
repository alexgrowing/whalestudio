import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainUnitaryTriangularStatement

open Complex Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_unit_extension_of_log_growth :
    ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ →
      DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} →
      (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → φ z ≠ 0 ∧
        ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N ∧
        ‖(φ z)⁻¹‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) →
      ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧
        (∀ z ∈ ball (0 : Fin n → ℂ) ρ, ψ z ≠ 0) ∧
        ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  intro n S φ ρ C N hρ hφ hb
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.T.removable_log_growth_singularity n S φ ρ C N hρ hφ (fun z hz hS => (hb z hz hS).2.1)
  obtain ⟨χ, hχ, hχe⟩ := GlobalTheory.T.removable_log_growth_singularity n S (fun z => (φ z)⁻¹) ρ C N hρ
    (hφ.inv fun z hz => (hb z hz.1 hz.2).1) (fun z hz hS => (hb z hz hS).2.2)
  refine ⟨ψ, hψ, fun z hz => ?_, hψe⟩
  have hF : ContinuousAt (fun w => ψ w * χ w) z :=
    ((hψ.mul hχ).differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ → (Fin n → ℂ),
      w = fun (ε : ℝ) i => if z i = 0 then (ε : ℂ) else z i := ⟨_, rfl⟩
  have hwc : Continuous w := by
    rw [hw_def]
    refine continuous_pi fun i => ?_
    by_cases h : z i = 0
    · simp only [h, if_true]
      exact continuous_ofReal
    · simp only [h, if_false]
      exact continuous_const
  have hw0 : w 0 = z := funext fun i => by by_cases h : z i = 0 <;> simp [hw_def, h]
  have hlim : Filter.Tendsto w (nhdsWithin 0 {0}ᶜ) (nhds z) := by
    rw [← hw0]
    exact hwc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, ψ (w ε) * χ (w ε) = 1 := by
    have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, w ε ∈ ball (0 : Fin n → ℂ) ρ :=
      hlim (isOpen_ball.mem_nhds hz)
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hε0
    have hS : ∀ i ∈ S, w ε i ≠ 0 := by
      intro i _
      by_cases h : z i = 0
      · simp only [hw_def, h, if_true]
        exact Complex.ofReal_ne_zero.2 hε0
      · simp only [hw_def, h, if_false]
        exact h
    rw [hψe _ hε hS, hχe _ hε hS]
    exact mul_inv_cancel₀ (hb _ hε hS).1
  have h2 : Filter.Tendsto (fun ε => ψ (w ε) * χ (w ε)) (nhdsWithin 0 {0}ᶜ) (nhds (ψ z * χ z)) :=
    hF.tendsto.comp hlim
  have h3 : ψ z * χ z = 1 :=
    tendsto_nhds_unique h2 (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  exact left_ne_zero_of_mul_eq_one h3

end GlobalTheory.CompanionTheory.Ar.Flat
