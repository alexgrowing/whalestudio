import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.SchurTotal

open Filter Topology

theorem span_ext {G H : Type} [MeasurableSpace G] (μ : Measure G) [AddCommGroup H] [Module ℂ H]
    (S : Set H) (f : H → G → ℂ) (r : H → ℂ) (φ : ℂ → ℂ)
    (hf0 : ∀ g, f 0 g = 0) (hr0 : r 0 = 0)
    (hfa : ∀ a b g, f (a + b) g = f a g + f b g) (hra : ∀ a b, r (a + b) = r a + r b)
    (hfs : ∀ (c : ℂ) a g, f (c • a) g = φ c * f a g) (hrs : ∀ (c : ℂ) a, r (c • a) = φ c * r a)
    (h : ∀ v ∈ S, Integrable (f v) μ ∧ ∫ g, f v g ∂μ = r v) :
    ∀ v ∈ Submodule.span ℂ S, Integrable (f v) μ ∧ ∫ g, f v g ∂μ = r v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have : f 0 = fun _ => 0 := funext hf0
    rw [this, hr0]
    exact ⟨integrable_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
    have : f (x + y) = fun g => f x g + f y g := funext (hfa x y)
    rw [this, hra]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2]⟩
  | smul c x _ hx =>
    have : f (c • x) = fun g => φ c * f x g := funext (hfs c x)
    rw [this, hrs]
    exact ⟨hx.1.const_mul _, by rw [integral_const_mul, hx.2]⟩

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) (d : ℝ)

def Rel (v w v' w' : H) : Prop :=
  Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

theorem rel_span (S : Set H) (h : ∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ S, Rel μ σ d v w v' w') :
    ∀ v ∈ Submodule.span ℂ S, ∀ w ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      ∀ w' ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
  have h1 : ∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
    intro v hv w hw v' hv'
    refine span_ext μ S (fun w' g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun w' => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => c) ?_ ?_ ?_ ?_ ?_ ?_ (h v hv w hw v' hv')
    · intro g; simp
    · simp
    · intro a b g; simp only [inner_add_left, star_add]; ring
    · intro a b; simp only [inner_add_right]; ring
    · intro c a g; simp only [inner_smul_left, star_mul', RCLike.star_def, Complex.conj_conj]; ring
    · intro c a; simp only [inner_smul_right]; ring
  have h2 : ∀ v ∈ S, ∀ w ∈ S, ∀ w' ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      Rel μ σ d v w v' w' := by
    intro v hv w hw w' hw'
    refine span_ext μ S (fun v' g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun v' => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => star c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun v' hv' => h1 v hv w hw v' hv' w' hw')
    · intro g; simp
    · simp
    · intro a b g; simp only [map_add, inner_add_right, star_add]; ring
    · intro a b; simp only [inner_add_left]; ring
    · intro c a g; simp only [map_smul, inner_smul_right, star_mul']; ring
    · intro c a; simp only [inner_smul_left, RCLike.star_def]; ring
  have h3 : ∀ v ∈ S, ∀ w' ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      ∀ w ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
    intro v hv w' hw' v' hv'
    refine span_ext μ S (fun w g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun w => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => star c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun w hw => h2 v hv w hw w' hw' v' hv')
    · intro g; simp
    · simp
    · intro a b g; simp only [inner_add_left]; ring
    · intro a b; simp only [inner_add_left]; ring
    · intro c a g; simp only [inner_smul_left, RCLike.star_def]; ring
    · intro c a; simp only [inner_smul_left, RCLike.star_def]; ring
  intro v hv w hw v' hv' w' hw'
  revert v
  refine span_ext μ S (fun v g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun v => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun v hv => h3 v hv w' hw' v' hv' w hw)
  · intro g; simp
  · simp
  · intro a b g; simp only [map_add, inner_add_right]; ring
  · intro a b; simp only [inner_add_right]; ring
  · intro c a g; simp only [map_smul, inner_smul_right]; ring
  · intro c a; simp only [inner_smul_right]; ring

theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem lint_of_rel (v w : H) (h : Rel μ σ d v w v w) :
    ∫⁻ g, ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) ∂μ = ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨h1, h2⟩ := h
  simp only [mul_star_eq] at h1 h2
  have h3 : Integrable (fun g => ‖⟪w, σ g v⟫_ℂ‖ ^ 2) μ := by
    have := h1.re
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  rw [← ofReal_integral_eq_lintegral_ofReal h3 (ae_of_all _ fun g => by positivity)]
  congr 1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  apply Complex.ofReal_injective
  rw [h2]; push_cast; rfl

theorem lint_le (T : Set H) (hT : Dense T) (hm : ∀ v w : H, Measurable fun g => ⟪w, σ g v⟫_ℂ)
    (h : ∀ v ∈ T, ∀ w ∈ T, Rel μ σ d v w v w) (v w : H) :
    ∫⁻ g, ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨a, ha, hav⟩ := mem_closure_iff_seq_limit.1 (hT v)
  obtain ⟨b, hb, hbw⟩ := mem_closure_iff_seq_limit.1 (hT w)
  have h1 := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun (n : ℕ) g => ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2))
    (fun n => ((hm (a n) (b n)).norm.pow_const 2).ennreal_ofReal)
  have h2 : ∀ g, liminf (fun n => ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2)) atTop
      = ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) := by
    intro g
    apply Tendsto.liminf_eq
    exact ENNReal.tendsto_ofReal
      ((hbw.inner (((σ g).continuous.tendsto v).comp hav)).norm.pow 2)
  have h3 : liminf (fun n => ∫⁻ g, ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2) ∂μ) atTop
      = ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
    apply Tendsto.liminf_eq
    simp only [fun n => lint_of_rel μ σ d (a n) (b n) (h _ (ha n) _ (hb n))]
    exact ENNReal.tendsto_ofReal (((hav.norm.pow 2).mul (hbw.norm.pow 2)).div_const d)
  simpa only [h2, h3] using h1

theorem inner_toLp {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hg.toLp g, hf.toLp f⟫_ℂ = ∫ x, f x * star (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]; simp

theorem rel_dense (hd : 0 < d) (T : Set H) (hT : Dense T)
    (hm : ∀ v w : H, Measurable fun g => ⟪w, σ g v⟫_ℂ)
    (h : ∀ v ∈ T, ∀ w ∈ T, ∀ v' ∈ T, ∀ w' ∈ T, Rel μ σ d v w v' w') (v w v' w' : H) :
    Rel μ σ d v w v' w' := by
  have hle := lint_le μ σ d T hT hm (fun v hv w hw => h v hv w hw v hv w hw)
  have hint : ∀ v w : H, Integrable (fun g => ‖⟪w, σ g v⟫_ℂ‖ ^ 2) μ := by
    intro v w
    refine ⟨((hm v w).norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => by positivity)]
    exact (hle v w).trans_lt ENNReal.ofReal_lt_top
  have hL : ∀ v w : H, MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 μ := fun v w =>
    (memLp_two_iff_integrable_sq_norm (hm v w).aestronglyMeasurable).2 (hint v w)
  let C : H → H → Lp ℂ 2 μ := fun v w => (hL v w).toLp _
  have hC : ∀ v w, ‖C v w‖ ≤ ‖v‖ * ‖w‖ / √d := by
    intro v w
    have e1 : ((‖C v w‖ ^ 2 : ℝ) : ℂ) = ((∫ g, ‖⟪w, σ g v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      have := inner_toLp μ (hL v w) (hL v w)
      simp only [mul_star_eq] at this
      rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at this
      rw [← this]; push_cast; rfl
    have e2 := Complex.ofReal_injective e1
    have e3 : ∫ g, ‖⟪w, σ g v⟫_ℂ‖ ^ 2 ∂μ ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 / d := by
      have := hle v w
      rw [← ofReal_integral_eq_lintegral_ofReal (hint v w) (ae_of_all _ fun g => by positivity)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    apply le_of_sq_le_sq _ (by positivity)
    rw [e2, div_pow, mul_pow, Real.sq_sqrt hd.le]
    exact e3
  have hsplit : ∀ v w v0 w0, C v w - C v0 w0 = C (v - v0) w + C v0 (w - w0) := by
    intro v w v0 w0
    simp only [C]
    rw [← MemLp.toLp_sub, ← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine ae_of_all _ fun g => ?_
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, inner_sub_left, inner_sub_right]
    ring
  have hcont : Continuous fun p : H × H => C p.1 p.2 := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous fun q : H × H =>
        ‖q.1 - p.1‖ * ‖q.2‖ / √d + ‖p.1‖ * ‖q.2 - p.2‖ / √d := by fun_prop
    have ht := hc.tendsto p
    simp only [sub_self, norm_zero, zero_mul, mul_zero, zero_div, add_zero] at ht
    refine squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) ht
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hC _ _) (hC _ _))
  refine ⟨?_, ?_⟩
  · exact (hL v w).integrable_mul (hL v' w').star
  · have key : ∀ x : (H × H) × (H × H), ⟪C x.2.1 x.2.2, C x.1.1 x.1.2⟫_ℂ
        = ⟪x.2.1, x.1.1⟫_ℂ * ⟪x.1.2, x.2.2⟫_ℂ / (d : ℂ) := by
      have hD : Dense ((T ×ˢ T) ×ˢ (T ×ˢ T)) := (hT.prod hT).prod (hT.prod hT)
      have := Continuous.ext_on hD
        (f := fun x : (H × H) × (H × H) => ⟪C x.2.1 x.2.2, C x.1.1 x.1.2⟫_ℂ)
        (g := fun x => ⟪x.2.1, x.1.1⟫_ℂ * ⟪x.1.2, x.2.2⟫_ℂ / (d : ℂ))
        ((hcont.comp continuous_snd).inner (hcont.comp continuous_fst))
        (by fun_prop) (by
          rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
          exact (inner_toLp μ (hL a b) (hL a' b')).trans (h a ha b hb a' ha' b' hb').2)
      exact congrFun this
    exact (inner_toLp μ (hL v w) (hL v' w')).symm.trans (key ((v, w), (v', w')))

end GlobalTheory.Dec.SchurTotal

theorem GlobalTheory.Dec.isFdegG_of_total : ∀ (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) (d : ℝ) (S : Set H), IsURep σ → 0 < d → Dense (Submodule.span ℂ S : Set H) → (∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ S, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → IsFdegG μ σ d := by
  intro G _ _ _ _ μ H _ _ σ d S hσ hd hS h
  refine ⟨hd, fun v w v' w' => ?_⟩
  exact GlobalTheory.Dec.SchurTotal.rel_dense μ σ d hd _ hS
    (fun v w => (continuous_const.inner (hσ.2.2.2 v)).measurable)
    (GlobalTheory.Dec.SchurTotal.rel_span μ σ d S h) v w v' w'
