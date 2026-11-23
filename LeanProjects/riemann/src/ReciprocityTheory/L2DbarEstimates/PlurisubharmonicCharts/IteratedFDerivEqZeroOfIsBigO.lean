import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Lemmata.CharacterDirections.Cdir

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem fderiv_isBigO_of_isBigO_pow {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) {m : ℕ}
    (hO : f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1 + 1)) :
    fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  first | exact Bl.CoprimeDirections.goal1 .. | (apply Bl.CoprimeDirections.goal1 <;> assumption) | (intros; apply Bl.CoprimeDirections.goal1 <;> assumption)

theorem isBigO_succ_of_fderiv_isBigO {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (h0 : f x = 0) {m : ℕ}
    (hO : fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ m) :
    f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  obtain ⟨c, hc0, hc⟩ := hO.exists_pos
  rw [IsBigOWith] at hc
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 (hc.and (hU.mem_nhds hx))
  rw [isBigO_iff]
  refine ⟨c, ?_⟩
  filter_upwards [ball_mem_nhds x hε0] with v hv
  rw [norm_pow, norm_norm]
  have hvx : ‖v - x‖ < ε := by rwa [mem_ball, dist_eq_norm] at hv
  have hsub : closedBall x ‖v - x‖ ⊆ ball x ε := closedBall_subset_ball hvx
  have hmv := (convex_closedBall x ‖v - x‖).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := c * ‖v - x‖ ^ m)
    (fun w hw => (hf w (hε _ (hsub hw)).2).differentiableAt (hU.mem_nhds (hε _ (hsub hw)).2))
    (fun w hw => by
      calc ‖fderiv ℂ f w‖ ≤ c * ‖‖w - x‖ ^ m‖ := (hε _ (hsub hw)).1
        _ = c * ‖w - x‖ ^ m := by rw [norm_pow, norm_norm]
        _ ≤ c * ‖v - x‖ ^ m := by
          gcongr
          rw [mem_closedBall, dist_eq_norm] at hw; exact hw)
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall.2 (by rw [dist_eq_norm]))
  rw [h0, sub_zero] at hmv
  calc ‖f v‖ ≤ c * ‖v - x‖ ^ m * ‖v - x‖ := hmv
    _ = c * ‖v - x‖ ^ (m + 1) := by ring

theorem top_ne_zero_withTop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  exact_mod_cast (show (⊤ : ℕ∞) ≠ 0 by simp)

theorem top_add_one_le_top :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤)

theorem iteratedFDeriv_eq_zero_of_isBigO_alt {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1)) →
    ∀ k ≤ m, iteratedFDeriv ℂ k f x = 0 := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf hO k hk
    obtain rfl : k = 0 := by omega
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
    exact hO.eq_zero_of_norm_pow (by omega)
  | succ m ih =>
    intro F _ _ f U x hU hx hf hO k hk
    rcases k with _ | k
    · rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
      exact hO.eq_zero_of_norm_pow (by omega)
    · have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
      have hO' := fderiv_isBigO_of_isBigO_pow hU hx (hf.differentiableOn top_ne_zero_withTop) hO
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact ih (fderiv ℂ f) U x hU hx hd hO' k (by omega)

theorem isBigO_pow_of_iteratedFDeriv_zero {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (∀ k < m, iteratedFDeriv ℂ k f x = 0) →
    f =O[𝓝 x] fun v => ‖v - x‖ ^ m := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf _
    simp only [pow_zero]
    exact (hf.continuousOn.continuousAt (hU.mem_nhds hx)).tendsto.isBigO_one ℝ
  | succ m ih =>
    intro F _ _ f U x hU hx hf h
    have h0 : f x = 0 := by
      have := h 0 (by omega)
      rwa [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero] at this
    have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
    have hO := ih (fderiv ℂ f) U x hU hx hd (fun k hk => by
      rw [← norm_eq_zero, norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact h (k + 1) (by omega))
    exact isBigO_succ_of_fderiv_isBigO hU hx (hf.differentiableOn top_ne_zero_withTop) h0 hO

theorem iteratedFDeriv_eq_zero_of_bound {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (hO : ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1)) :
    ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0 := by
  intro k hk
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  obtain ⟨C, hC⟩ := hO
  have hO' : g =O[𝓝 v0] fun v => ‖v - v0‖ ^ (m + 1) := by
    rw [isBigO_iff]
    exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm]⟩
  exact iteratedFDeriv_eq_zero_of_isBigO_alt m g U v0 hU hv hc hO' k hk

theorem bound_of_iteratedFDeriv_eq_zero {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (h : ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1) := by
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  have hb := isBigO_pow_of_iteratedFDeriv_zero (m + 1) g U v0 hU hv hc (fun k hk => h k (by omega))
  obtain ⟨C, hC⟩ := isBigO_iff.1 hb
  exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm] at hv⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
