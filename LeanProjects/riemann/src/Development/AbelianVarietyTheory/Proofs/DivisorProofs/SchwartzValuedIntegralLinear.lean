import Mathlib

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.ParamSchwartz

variable {Ω E F' : Type} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

theorem hasFDerivAt_integral_iter (g : Ω → E → F') (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hmeas : ∀ (n : ℕ) y, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (g t) y) μ)
    (b : ℕ → Ω → ℝ) (hb : ∀ n, Integrable (b n) μ)
    (hbd : ∀ n t y, ‖iteratedFDeriv ℝ n (g t) y‖ ≤ b n t) (k : ℕ) (y₀ : E) :
    HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ k (g t) y ∂μ)
      (∫ t, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F'
        (iteratedFDeriv ℝ (k + 1) (g t) y₀) ∂μ) y₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b (k + 1))
    (F' := fun y t => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F'
      (iteratedFDeriv ℝ (k + 1) (g t) y)) Filter.univ_mem
    (Eventually.of_forall fun y => hmeas k y)
    ((hb k).mono' (hmeas k y₀) (ae_of_all _ fun t => hbd k t y₀))
    ((LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hmeas (k + 1) y₀)) ?_ (hb (k + 1)) ?_
  · refine ae_of_all _ fun t y _ => ?_
    rw [LinearIsometryEquiv.norm_map]
    exact hbd (k + 1) t y
  · refine ae_of_all _ fun t y _ => ?_
    have hd : Differentiable ℝ (iteratedFDeriv ℝ k (g t)) :=
      (hg t).differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
    have := (hd y).hasFDerivAt
    simpa [iteratedFDeriv_succ_eq_comp_left] using this

theorem iteratedFDeriv_integral_eq (g : Ω → E → F') (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hmeas : ∀ (n : ℕ) y, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (g t) y) μ)
    (b : ℕ → Ω → ℝ) (hb : ∀ n, Integrable (b n) μ)
    (hbd : ∀ n t y, ‖iteratedFDeriv ℝ n (g t) y‖ ≤ b n t) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => ∫ t, g t y ∂μ) = fun y => ∫ t, iteratedFDeriv ℝ k (g t) y ∂μ := by
  induction k with
  | zero =>
    funext y
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F').symm.toContinuousLinearEquiv.integral_comp_comm
      (fun t => g t y)).symm
  | succ k ih =>
    funext y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih,
      (hasFDerivAt_integral_iter g hg hmeas b hb hbd k y).fderiv]
    have e := LinearIsometry.integral_comp_comm (μ := μ) (𝕜 := ℝ)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F')
      (F := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F')
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F').toLinearIsometry
      (fun t => iteratedFDeriv ℝ (k + 1) (g t) y)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at e
    rw [e]
    simp

theorem contDiff_integral (g : Ω → E → F') (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hmeas : ∀ (n : ℕ) y, AEStronglyMeasurable (fun t => iteratedFDeriv ℝ n (g t) y) μ)
    (b : ℕ → Ω → ℝ) (hb : ∀ n, Integrable (b n) μ)
    (hbd : ∀ n t y, ‖iteratedFDeriv ℝ n (g t) y‖ ≤ b n t) :
    ContDiff ℝ ∞ (fun y => ∫ t, g t y ∂μ) := by
  refine contDiff_of_differentiable_iteratedFDeriv fun k _ => ?_
  rw [iteratedFDeriv_integral_eq g hg hmeas b hb hbd k]
  exact fun y => (hasFDerivAt_integral_iter g hg hmeas b hb hbd k y).differentiableAt

end GlobalTheory.ParamSchwartz

namespace GlobalTheory.ParamSchwartz

theorem iteratedIntegral_clm : ∀ {D₁ D₂ Ω₁ Ω₂ : Type} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁] [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (m₁ : Measure Ω₁) (m₂ : Measure Ω₂) [IsFiniteMeasure m₁] [SFinite m₂]
    (G : SchwartzMap D₁ ℂ → Ω₁ → Ω₂ → SchwartzMap D₂ ℂ),
    (∀ (a b : ℂ) (f f' : SchwartzMap D₁ ℂ) k l, G (a • f + b • f') k l = a • G f k l + b • G f' k l) →
    (∀ f (n : ℕ) (y : D₂), StronglyMeasurable (Function.uncurry fun k l => iteratedFDeriv ℝ n (⇑(G f k l)) y)) →
    (∀ a n : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (w : Ω₂ → ℝ), Integrable w m₂ ∧
      ∀ f k l, SchwartzMap.seminorm ℂ a n (G f k l) ≤ C * w l * (s.sup (schwartzSeminormFamily ℂ D₁ ℂ)) f) →
    ∃ T : SchwartzMap D₁ ℂ →L[ℂ] SchwartzMap D₂ ℂ, ∀ f, ⇑(T f) = fun y => ∫ k, ∫ l, G f k l y ∂m₂ ∂m₁ := by
  intro D₁ D₂ Ω₁ Ω₂ _ _ _ _ _ _ m₁ m₂ _ _ G hlin hmeas hbd
  set μ := m₁.prod m₂ with hμ
  have hadd : ∀ f f' k l, G (f + f') k l = G f k l + G f' k l := fun f f' k l => by
    simpa using hlin 1 1 f f' k l
  have hsm : ∀ (a : ℂ) f k l, G (a • f) k l = a • G f k l := fun a f k l => by
    simpa using hlin a 0 f f k l
  choose s C w hw hC using hbd
  have hwint : ∀ a n, Integrable (fun t : Ω₁ × Ω₂ => |w a n t.2|) μ := fun a n => by
    exact (hw a n).abs.comp_snd m₁
  have key : ∀ a n f k l, SchwartzMap.seminorm ℂ a n (G f k l) ≤
      |C a n| * |w a n l| * (s a n).sup (schwartzSeminormFamily ℂ D₁ ℂ) f := by
    intro a n f k l
    refine (hC a n f k l).trans ?_
    have hp : 0 ≤ (s a n).sup (schwartzSeminormFamily ℂ D₁ ℂ) f := apply_nonneg _ _
    rw [← abs_mul]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hp
  have hbint : ∀ a n f, Integrable (fun t : Ω₁ × Ω₂ =>
      |C a n| * |w a n t.2| * (s a n).sup (schwartzSeminormFamily ℂ D₁ ℂ) f) μ := fun a n f =>
    ((hwint a n).const_mul |C a n|).mul_const _
  have hbd' : ∀ f n (t : Ω₁ × Ω₂) y, ‖iteratedFDeriv ℝ n (G f t.1 t.2) y‖ ≤
      |C 0 n| * |w 0 n t.2| * (s 0 n).sup (schwartzSeminormFamily ℂ D₁ ℂ) f := fun f n t y =>
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ _).trans (key 0 n f t.1 t.2)
  have hm' : ∀ f (n : ℕ) y, AEStronglyMeasurable
      (fun t : Ω₁ × Ω₂ => iteratedFDeriv ℝ n (G f t.1 t.2) y) μ :=
    fun f n y => (hmeas f n y).aestronglyMeasurable
  have hsmooth : ∀ f (t : Ω₁ × Ω₂), ContDiff ℝ ∞ (⇑(G f t.1 t.2)) := fun f t => (G f t.1 t.2).smooth ⊤
  have hval : ∀ f y, Integrable (fun t : Ω₁ × Ω₂ => G f t.1 t.2 y) μ := by
    intro f y
    have h0 := (hbint 0 0 f).mono' (hm' f 0 y) (ae_of_all _ fun t => hbd' f 0 t y)
    have := (continuousMultilinearCurryFin0 ℝ D₂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp h0
    simpa using this
  have hprod : ∀ f, (fun y => ∫ k, ∫ l, G f k l y ∂m₂ ∂m₁) = fun y => ∫ t, G f t.1 t.2 y ∂μ :=
    fun f => funext fun y => (integral_prod _ (hval f y)).symm
  have hprod' : ∀ f y, ∫ k, ∫ l, G f k l y ∂m₂ ∂m₁ = ∫ t, G f t.1 t.2 y ∂μ :=
    fun f y => congrFun (hprod f) y
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f y => ∫ k, ∫ l, G f k l y ∂m₂ ∂m₁)
    ?_ ?_ ?_ ?_, fun f => rfl⟩
  · intro f f' y
    simp only [hprod']
    rw [← integral_add (hval f y) (hval f' y)]
    congr 1
    funext t
    rw [hadd]
    rfl
  · intro a f y
    simp only [hprod', RingHom.id_apply]
    rw [← integral_smul]
    congr 1
    funext t
    rw [hsm]
    rfl
  · intro f
    rw [hprod f]
    exact contDiff_integral (μ := μ) (fun t => ⇑(G f t.1 t.2)) (hsmooth f) (hm' f) _
      (fun n => hbint 0 n f) (hbd' f)
  · intro n
    refine ⟨s n.1 n.2, |C n.1 n.2| * ∫ t, |w n.1 n.2 t.2| ∂μ,
      mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _), fun f y => ?_⟩
    rw [hprod f, iteratedFDeriv_integral_eq (μ := μ) (fun t => ⇑(G f t.1 t.2)) (hsmooth f) (hm' f) _
      (fun n => hbint 0 n f) (hbd' f)]
    calc ‖y‖ ^ n.1 * ‖∫ t, iteratedFDeriv ℝ n.2 (G f t.1 t.2) y ∂μ‖
        = ‖∫ t, (‖y‖ ^ n.1) • iteratedFDeriv ℝ n.2 (G f t.1 t.2) y ∂μ‖ := by
          rw [integral_smul, norm_smul, norm_pow, norm_norm]
      _ ≤ ∫ t, |C n.1 n.2| * |w n.1 n.2 t.2| * (s n.1 n.2).sup (schwartzSeminormFamily ℂ D₁ ℂ) f ∂μ := by
          refine norm_integral_le_of_norm_le (hbint n.1 n.2 f) (ae_of_all _ fun t => ?_)
          rw [norm_smul, norm_pow, norm_norm]
          exact (SchwartzMap.le_seminorm ℂ _ _ _ _).trans (key n.1 n.2 f t.1 t.2)
      _ = |C n.1 n.2| * (∫ t, |w n.1 n.2 t.2| ∂μ) * (s n.1 n.2).sup (schwartzSeminormFamily ℂ D₁ ℂ) f := by
          rw [integral_mul_const, integral_const_mul]

end GlobalTheory.ParamSchwartz
