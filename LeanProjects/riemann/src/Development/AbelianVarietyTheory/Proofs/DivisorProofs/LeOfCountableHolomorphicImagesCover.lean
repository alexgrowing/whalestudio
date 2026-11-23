import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem dimH_image_le_of_differentiableOn_complex {d d' : ℕ} {U : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → (Fin d' → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    dimH (f '' U) ≤ (Module.finrank ℝ (Fin d → ℂ) : ENNReal) := by
  set S : ℕ → Set (Fin d → ℂ) := fun n =>
    {x | ∀ y, dist y x < 1 / ((n : ℝ) + 1) → dist (f y) (f x) ≤ ((n : ℝ) + 1) * dist y x}
    with hS
  have hcov : f '' U ⊆ ⋃ n, f '' S n := by
    rintro _ ⟨x, hx, rfl⟩
    have hd : DifferentiableAt ℂ f x := (hf x hx).differentiableAt (hU.mem_nhds hx)
    obtain ⟨C, hC, hCw⟩ := hd.hasFDerivAt.isBigO_sub.exists_pos
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hCw.bound
    obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / ε))
    refine Set.mem_iUnion.2 ⟨n, x, ?_, rfl⟩
    intro y hy
    have hn1 : C < (n : ℝ) + 1 := by linarith [le_max_left C (1 / ε)]
    have hn2 : 1 / ε < (n : ℝ) + 1 := by linarith [le_max_right C (1 / ε)]
    have hy' : dist y x < ε := by
      refine lt_of_lt_of_le hy ?_
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn2
      linarith
    have := hεb hy'
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖f y - f x‖ ≤ C * ‖y - x‖ := this
      _ ≤ ((n : ℝ) + 1) * ‖y - x‖ := by gcongr
  have hSn : ∀ n, dimH (f '' S n) ≤ dimH (S n) := by
    intro n
    apply dimH_image_le_of_locally_lipschitzOn
    intro x _
    refine ⟨((n : NNReal) + 1), S n ∩ Metric.ball x (1 / (2 * ((n : ℝ) + 1))),
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (by positivity)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hab : dist a b < 1 / ((n : ℝ) + 1) := by
      have h1 := Metric.mem_ball.1 ha.2
      have h2 := Metric.mem_ball'.1 hb.2
      calc dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
        _ < 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_lt_add h1 h2
        _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    have := hb.1 a hab
    simpa using this
  calc dimH (f '' U) ≤ dimH (⋃ n, f '' S n) := dimH_mono hcov
    _ = ⨆ n, dimH (f '' S n) := dimH_iUnion _
    _ ≤ dimH (Set.univ : Set (Fin d → ℂ)) :=
        iSup_le fun n => (hSn n).trans (dimH_mono (Set.subset_univ _))
    _ = _ := Real.dimH_univ_eq_finrank _

theorem le_of_countable_holomorphic_images_cover :
    ∀ (d d' : ℕ) (K : Type) [Countable K] (U : K → Set (Fin d → ℂ))
      (f : K → (Fin d → ℂ) → (Fin d' → ℂ)) (W : Set (Fin d' → ℂ)),
      (∀ i, IsOpen (U i)) → (∀ i, DifferentiableOn ℂ (f i) (U i)) → IsOpen W →
      W.Nonempty → W ⊆ ⋃ i, f i '' U i → d' ≤ d := by
  intro d d' K _ U f W hU hf hW hne hcov
  obtain ⟨w, hw⟩ := hne
  have h1 : dimH W = (Module.finrank ℝ (Fin d' → ℂ) : ENNReal) :=
    Real.dimH_of_mem_nhds (hW.mem_nhds hw)
  have h2 : dimH W ≤ (Module.finrank ℝ (Fin d → ℂ) : ENNReal) := by
    calc dimH W ≤ dimH (⋃ i, f i '' U i) := dimH_mono hcov
      _ = ⨆ i, dimH (f i '' U i) := dimH_iUnion _
      _ ≤ _ := iSup_le fun i => dimH_image_le_of_differentiableOn_complex (hU i) (hf i)
  rw [h1] at h2
  have h3 : Module.finrank ℝ (Fin d' → ℂ) ≤ Module.finrank ℝ (Fin d → ℂ) := by
    exact_mod_cast h2
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h3
  simp at h3
  omega

end GlobalTheory
