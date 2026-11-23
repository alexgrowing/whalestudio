import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzIteratedIntegral

open MeasureTheory

noncomputable section

namespace GlobalTheory.ConeSch

theorem exists_schwartz_integral : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [MeasurableSpace S] (ν : Measure S)
    (f : S → SchwartzMap D ℂ),
    (∀ (n : ℕ) (x : D), AEStronglyMeasurable (fun s => iteratedFDeriv ℝ n (f s) x) ν) →
    (∀ m n : ℕ, ∃ c : S → ℝ, Integrable c ν ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
    ∃ G : SchwartzMap D ℂ, (∀ x, G x = ∫ s, f s x ∂ν) ∧
      (∀ (n : ℕ) (x : D), iteratedFDeriv ℝ n G x = ∫ s, iteratedFDeriv ℝ n (f s) x ∂ν) ∧
      ∀ (m n : ℕ) (c : S → ℝ), Integrable c ν → (∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
        SchwartzMap.seminorm ℂ m n G ≤ ∫ s, c s ∂ν := by
  intro D S _ _ _ ν f h1 h3
  choose b hbi hb using h3
  set G : (n : ℕ) → D → ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ :=
    fun n x => ∫ s, iteratedFDeriv ℝ n (f s) x ∂ν with hG
  have bound0 : ∀ n s x, ‖iteratedFDeriv ℝ n (f s) x‖ ≤ b 0 n s := fun n s x => by
    have := (SchwartzMap.le_seminorm ℂ 0 n (f s) x).trans (hb 0 n s)
    simpa using this
  have intI : ∀ n x, Integrable (fun s => iteratedFDeriv ℝ n (f s) x) ν := fun n x =>
    Integrable.mono' (hbi 0 n) (h1 n x) (ae_of_all _ fun s => bound0 n s x)
  have derivD : ∀ n s x, HasFDerivAt (fun w => iteratedFDeriv ℝ n (f s) w)
      (iteratedFDeriv ℝ (n + 1) (f s) x).curryLeft x := fun n s x =>
    (contDiff_iff_ftaylorSeries.1 ((f s).smooth ⊤)).fderiv n (by exact_mod_cast WithTop.coe_lt_top (n : ℕ)) x
  have derivG : ∀ n x, HasFDerivAt (G n) (G (n + 1) x).curryLeft x := fun n x =>
    hasFDerivAt_integral_curry ν (fun s w => iteratedFDeriv ℝ n (f s) w)
      (fun s w => iteratedFDeriv ℝ (n + 1) (f s) w) (b 0 (n + 1)) (fun s w => derivD n s w)
      (fun w => h1 n w) (fun w => intI n w) (fun w => h1 (n + 1) w) (fun s w => bound0 (n + 1) s w)
      (hbi 0 (n + 1)) x
  set g : D → ℂ := fun x => ∫ s, f s x ∂ν with hg
  have hT : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) g (fun x m => G m x) := by
    refine ⟨fun x => ?_, fun m _ x => derivG m x,
      fun m _ => continuous_iff_continuousAt.2 fun x => (derivG m x).continuousAt⟩
    have e : ∀ φ : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => D) ℂ,
        φ.curry0 = (continuousMultilinearCurryFin0 ℝ D ℂ).toLinearIsometry φ := fun _ => rfl
    rw [e, hG]
    simp only
    rw [← LinearIsometry.integral_comp_comm]
    congr 1
  have hD : ∀ n x, iteratedFDeriv ℝ n g x = G n x := fun n x =>
    (hT.eq_iteratedFDeriv (by exact_mod_cast le_top) x).symm
  have key : ∀ (p n : ℕ) (c : S → ℝ), Integrable c ν → (∀ s, SchwartzMap.seminorm ℂ p n (f s) ≤ c s) →
      ∀ x, ‖x‖ ^ p * ‖G n x‖ ≤ ∫ s, c s ∂ν := by
    intro p n c hci hcb x
    have ht : (0 : ℝ) ≤ ‖x‖ ^ p := pow_nonneg (norm_nonneg x) p
    calc ‖x‖ ^ p * ‖G n x‖ = ‖(‖x‖ ^ p) • G n x‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
      _ = ‖∫ s, (‖x‖ ^ p) • iteratedFDeriv ℝ n (f s) x ∂ν‖ := by
          rw [hG]; simp only; rw [integral_smul]
      _ ≤ ∫ s, c s ∂ν := by
          refine norm_integral_le_of_norm_le hci (ae_of_all _ fun s => ?_)
          rw [norm_smul, Real.norm_of_nonneg ht]
          exact (SchwartzMap.le_seminorm ℂ p n (f s) x).trans (hcb s)
  let GS : SchwartzMap D ℂ := ⟨g, hT.contDiff, fun p n =>
    ⟨∫ s, b p n s ∂ν, fun x => by rw [hD]; exact key p n (b p n) (hbi p n) (hb p n) x⟩⟩
  have hGS : ∀ n x, iteratedFDeriv ℝ n GS x = G n x := fun n x => hD n x
  refine ⟨GS, fun x => rfl, fun n x => hGS n x, fun m n c hci hcb => ?_⟩
  have hc0 : 0 ≤ ∫ s, c s ∂ν :=
    integral_nonneg fun s => (apply_nonneg _ _).trans (hcb s)
  refine SchwartzMap.seminorm_le_bound ℂ m n GS hc0 fun x => ?_
  rw [hGS]
  exact key m n c hci hcb x

end GlobalTheory.ConeSch
