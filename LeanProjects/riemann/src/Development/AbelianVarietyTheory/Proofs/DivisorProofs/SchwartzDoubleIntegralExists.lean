import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem mul_norm_integral_le_of_mul_norm_le {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) (B : α → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hB : Integrable B μ) (h : ∀ k, c * ‖f k‖ ≤ B k) :
    c * ‖∫ k, f k ∂μ‖ ≤ ∫ k, B k ∂μ := by
  calc c * ‖∫ k, f k ∂μ‖ = ‖∫ k, c • f k ∂μ‖ := by
        rw [integral_smul, norm_smul, Real.norm_of_nonneg hc]
    _ ≤ ∫ k, B k ∂μ := norm_integral_le_of_norm_le hB
        (Filter.Eventually.of_forall fun k => by rw [norm_smul, Real.norm_of_nonneg hc]; exact h k)

theorem schwartz_integral_of_dominated {V α : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace α] (μ : Measure α) (F : α → SchwartzMap V ℂ)
    (hmeas : ∀ (m : ℕ) (t : V), AEStronglyMeasurable (fun k => iteratedFDeriv ℝ m (F k) t) μ)
    (hbd : ∀ n m : ℕ, ∃ Bd : α → ℝ, Integrable Bd μ ∧
      ∀ k t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (F k) t‖ ≤ Bd k) :
    ∃ g : SchwartzMap V ℂ, (∀ t, g t = ∫ k, F k t ∂μ) ∧
      ∀ m t, iteratedFDeriv ℝ m g t = ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ := by
  have hint : ∀ m t, Integrable (fun k => iteratedFDeriv ℝ m (F k) t) μ := by
    intro m t
    obtain ⟨B, hBi, hB⟩ := hbd 0 m
    refine hBi.mono' (hmeas m t) (Filter.Eventually.of_forall fun k => ?_)
    simpa using hB k t
  have hdiff : ∀ m k, Differentiable ℝ (iteratedFDeriv ℝ m (F k)) := fun m k =>
    (F k).smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
  have hder : ∀ m t, HasFDerivAt (fun t => ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ)
      (∫ k, fderiv ℝ (iteratedFDeriv ℝ m (F k)) t ∂μ) t := by
    intro m t
    obtain ⟨B, hBi, hB⟩ := hbd 0 (m + 1)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (F' := fun x k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) x) (bound := B)
      Filter.univ_mem (Filter.Eventually.of_forall fun x => hmeas m x) (hint m t) ?_ ?_ hBi ?_
    · have : (fun k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) t) = fun k =>
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ)
            (iteratedFDeriv ℝ (m + 1) (F k) t) := by
        funext k; rfl
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hmeas (m + 1) t)
    · exact Filter.Eventually.of_forall fun k x _ => by
        rw [norm_fderiv_iteratedFDeriv (𝕜 := ℝ)]; simpa using hB k x
    · exact Filter.Eventually.of_forall fun k x _ => (hdiff m k x).hasFDerivAt
  set g0 : V → ℂ := fun t => ∫ k, F k t ∂μ with hg0
  have hiter : ∀ m : ℕ, iteratedFDeriv ℝ m g0 = fun t => ∫ k, iteratedFDeriv ℝ m (F k) t ∂μ := by
    intro m
    induction m with
    | zero =>
      funext t
      exact ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => F k t)).symm
    | succ m ih =>
      funext t
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hder m t).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => fderiv ℝ (iteratedFDeriv ℝ m (F k)) t)).symm
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g0 :=
    contDiff_of_differentiable_iteratedFDeriv fun m _ => by
      rw [hiter m]; exact fun t => (hder m t).differentiableAt
  have hdecay : ∀ n m : ℕ, ∃ C, ∀ x, ‖x‖ ^ n * ‖iteratedFDeriv ℝ m g0 x‖ ≤ C := by
    intro n m
    obtain ⟨B, hBi, hB⟩ := hbd n m
    refine ⟨∫ k, B k ∂μ, fun x => ?_⟩
    rw [hiter m]
    exact mul_norm_integral_le_of_mul_norm_le μ _ B _ (by positivity) hBi fun k => hB k x
  exact ⟨⟨g0, hsmooth, hdecay⟩, fun t => rfl, fun m t => congrFun (hiter m) t⟩

theorem schwartz_iterated_integral_of_dominated :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {α β : Type} [MeasurableSpace α]
    [MeasurableSpace β] (μα : Measure α) (μβ : Measure β) (Fm : α → β → SchwartzMap V ℂ),
    (∀ (m : ℕ) (t : V) (k : α), AEStronglyMeasurable (fun l => iteratedFDeriv ℝ m (Fm k l) t) μβ) →
    (∀ (m : ℕ) (t : V), AEStronglyMeasurable (fun k => ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ) μα) →
    (∀ n m : ℕ, ∃ Bd : α → β → ℝ, (∀ k, Integrable (Bd k) μβ) ∧
      Integrable (fun k => ∫ l, Bd k l ∂μβ) μα ∧
      ∀ k l t, ‖t‖ ^ n * ‖iteratedFDeriv ℝ m (Fm k l) t‖ ≤ Bd k l) →
    ∃ g : SchwartzMap V ℂ, ∀ t, g t = ∫ k, ∫ l, Fm k l t ∂μβ ∂μα := by
  intro V _ _ α β _ _ μα μβ Fm h1 h2 hb
  have hin : ∀ k, ∃ g : SchwartzMap V ℂ, (∀ t, g t = ∫ l, Fm k l t ∂μβ) ∧
      ∀ m t, iteratedFDeriv ℝ m g t = ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ := by
    intro k
    refine schwartz_integral_of_dominated μβ (Fm k) (fun m t => h1 m t k) fun n m => ?_
    obtain ⟨Bd, hBi, -, hB⟩ := hb n m
    exact ⟨Bd k, hBi k, fun l t => hB k l t⟩
  choose g hg0 hg using hin
  obtain ⟨h, hh0, -⟩ := schwartz_integral_of_dominated μα g
    (fun m t => by
      have : (fun k => iteratedFDeriv ℝ m (g k) t) =
          fun k => ∫ l, iteratedFDeriv ℝ m (Fm k l) t ∂μβ := by
        funext k; exact hg k m t
      rw [this]; exact h2 m t)
    (fun n m => by
      obtain ⟨Bd, hBi, hBi2, hB⟩ := hb n m
      refine ⟨fun k => ∫ l, Bd k l ∂μβ, hBi2, fun k t => ?_⟩
      rw [hg k m t]
      exact mul_norm_integral_le_of_mul_norm_le μβ _ (Bd k) _ (by positivity) (hBi k)
        fun l => hB k l t)
  exact ⟨h, fun t => by rw [hh0]; simp only [hg0]⟩

end GlobalTheory
