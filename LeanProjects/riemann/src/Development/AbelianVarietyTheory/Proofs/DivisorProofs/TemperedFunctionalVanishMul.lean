import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierModulatedSchwartzBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSuperpositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWeightedIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyPairingIntegralCommuteStatement

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem continuous_iteratedFDeriv_apply_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (x : V) :
    Continuous (fun f : SchwartzMap V ℂ => iteratedFDeriv ℝ n f x) := by
  let L : SchwartzMap V ℂ →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
    { toFun := fun f => iteratedFDeriv ℝ n f x
      map_add' := fun f g => iteratedFDeriv_add_apply ((f.smooth n).contDiffAt) ((g.smooth n).contDiffAt)
      map_smul' := fun c f => by
        simpa using iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := c) ((f.smooth n).contDiffAt) }
  have : Continuous L := by
    refine Seminorm.cont_withSeminorms_normedSpace _ (schwartz_withSeminorms ℝ V ℂ) L ⟨{(0, n)}, 1, fun f => ?_⟩
    simp only [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, one_smul]
    simpa [L] using SchwartzMap.le_seminorm ℝ 0 n f x
  exact this

theorem schwartz_functional_integral_exchange : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) (T : SchwartzMap V ℂ →L[ℂ] ℂ) (Φ : W → SchwartzMap V ℂ), Continuous Φ →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ w x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Φ w) x‖ ≤ C * (1 + ‖w‖) ^ n) →
    ∀ φ : W → ℂ, AEStronglyMeasurable φ μ → (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖) μ) →
    ∀ h : SchwartzMap V ℂ, (∀ x, h x = ∫ w, φ w * Φ w x ∂μ) → T h = ∫ w, φ w * T (Φ w) ∂μ := by
  intro V _ _ _ W _ _ _ _ _ μ T Φ hΦ hb φ hφ hmom h hh
  refine GlobalTheory.T.schwartz_family_pairing_integral_commute μ T Φ hΦ hb φ hφ hmom h (fun n x => ?_)
  have hfun : (⇑h) = fun y => ∫ w, φ w * Φ w y ∂μ := funext hh
  rw [hfun]
  refine GlobalTheory.T.iteratedFDeriv_weighted_integral μ Φ φ (fun m => ?_) (fun m y => ?_) n x
  · obtain ⟨C, hC⟩ := hb 0 m
    refine ⟨fun w => |C| * ((1 + ‖w‖) ^ m * ‖φ w‖), (hmom m).const_mul _, fun w y => ?_⟩
    have := hC w y
    simp only [pow_zero, one_mul] at this
    calc ‖φ w‖ * ‖iteratedFDeriv ℝ m (Φ w) y‖ ≤ ‖φ w‖ * (|C| * (1 + ‖w‖) ^ m) :=
          mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) (norm_nonneg _)
      _ = _ := by ring
  · exact hφ.smul ((continuous_iteratedFDeriv_apply_schwartz m y).comp hΦ).aestronglyMeasurable

theorem kill_schwartz_multiple_of_kill_characters : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (g : SchwartzMap V ℂ), (∀ (ξ : V →L[ℝ] ℝ) (h : SchwartzMap V ℂ), (∀ x, h x = Complex.exp ((ξ x : ℂ) * Complex.I) * g x) → T h = 0) →
    ∀ (ψ h : SchwartzMap V ℂ), (∀ x, h x = g x * ψ x) → T h = 0 := by
  intro V _ _ _ T g hT ψ h hh
  obtain ⟨H, hH, hHb⟩ := GlobalTheory.T.fourier_modulated_schwartz_bounds g
  obtain ⟨m, A, φ, hφc, hφi, hψ⟩ := GlobalTheory.T.schwartz_fourier_superposition ψ
  set Φ : EuclideanSpace ℝ (Fin m) → SchwartzMap V ℂ := fun w => H (A w) with hΦ
  have hb : ∀ k n : ℕ, ∃ C : ℝ, ∀ w x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Φ w) x‖ ≤ C * (1 + ‖w‖) ^ n := by
    intro k n
    obtain ⟨C, hC⟩ := hHb k n
    refine ⟨|C| * (1 + ‖A‖) ^ n, fun w x => (hC (A w) x).trans ?_⟩
    have h1 : 1 + ‖A w‖ ≤ (1 + ‖A‖) * (1 + ‖w‖) := by
      nlinarith [A.le_opNorm w, norm_nonneg A, norm_nonneg w]
    calc C * (1 + ‖A w‖) ^ n ≤ |C| * ((1 + ‖A‖) * (1 + ‖w‖)) ^ n :=
          mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) h1 n) (by positivity) (abs_nonneg C)
      _ = |C| * (1 + ‖A‖) ^ n * (1 + ‖w‖) ^ n := by rw [mul_pow]; ring
  have hcont : Continuous Φ := by
    rw [continuous_iff_continuousAt]
    intro w0
    refine schwartz_continuousAt_of_pointwise_of_bounded Φ w0 (fun v => ?_) (fun k n => ?_)
    · simp only [hΦ, hH]
      fun_prop
    · obtain ⟨C, hC⟩ := hb k n
      refine ⟨|C| * (2 + ‖w0‖) ^ n, ?_⟩
      filter_upwards [Metric.ball_mem_nhds w0 one_pos] with w hw v
      refine (hC w v).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ n) (by positivity) (abs_nonneg C))
      have h1 := mem_ball_iff_norm.1 hw
      have h2 := norm_sub_norm_le w w0
      linarith
  have hrep : ∀ x, h x = ∫ w, φ w * Φ w x := by
    intro x
    rw [hh, hψ, ← integral_const_mul]
    congr 1; funext w
    simp only [hΦ, hH]; ring
  rw [schwartz_functional_integral_exchange volume T Φ hcont hb φ hφc.aestronglyMeasurable hφi h hrep]
  have : ∀ w, T (Φ w) = 0 := fun w => hT (A w) (Φ w) (hH _)
  simp [this]
end GlobalTheory
