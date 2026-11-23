import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSmallCT

theorem eq_of_continuousAt_of_eventuallyEq_nhdsNE {f h : ℂ → ℂ} {s : ℂ} (hf : ContinuousAt f s)
    (hh : ContinuousAt h s) (he : ∀ᶠ z in 𝓝[≠] s, f z = h z) : f s = h s :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hh.tendsto.mono_left nhdsWithin_le_nhds).congr' (he.mono fun _ hz => hz.symm))

theorem eventually_mem_ball_ne {s₀ s : ℂ} {r : ℝ} (hs : s ∈ Metric.ball s₀ r) :
    ∀ᶠ z in 𝓝[≠] s, z ∈ Metric.ball s₀ r ∧ z ≠ s₀ := by
  refine Filter.Eventually.and (nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hs)) ?_
  by_cases h : s = s₀
  · rw [← h]; exact eventually_mem_nhdsWithin
  · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds

theorem eisGood_qht_measurable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : ℕ) (Eis : ℂ → UA σ J → ℂ) (hE : EisGood b Eis)
    (hinv : ∀ s₀ : ℂ, ∀ γ ∈ ratU σ J, ∀ g, ∀ᶠ s in 𝓝[≠] s₀, Eis s (γ * g) = Eis s g)
    (hmeas : ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, Measurable (Eis s)) :
    (∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (Hol : ℂ → UA σ J → ℂ) (C : ℝ) (N : ℕ), 0 < r ∧
      (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧
      (∀ g, DifferentiableOn ℂ (Hol · g) (Metric.ball s₀ r)) ∧
      (∀ s ∈ Metric.ball s₀ r, ∀ g, ‖Hol s g‖ ≤ C * (qht g : ℝ) ^ N) ∧ ∀ s ∈ Metric.ball s₀ r, Measurable (Hol s)) ∧
    ∃ (r C : ℝ) (N : ℕ), 0 < r ∧ (∀ g, DifferentiableOn ℂ (Eis · g) (Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r)) ∧
      (∀ s ∈ Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r, ∀ g, ‖Eis s g‖ ≤ C * (qht g : ℝ) ^ N) ∧
      ∀ s ∈ Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r, Measurable (Eis s) := by
  obtain ⟨h1, h2⟩ := hE

  have hball : ∀ (s₀ : ℂ) (U : Set ℂ), U ∈ 𝓝 s₀ → ∃ r > 0, Metric.ball s₀ r ⊆ U ∧
      ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → Measurable (Eis s) := by
    intro s₀ U hU
    have hh := (eventually_nhdsWithin_iff.1 (hmeas s₀)).and (show ∀ᶠ x in 𝓝 s₀, x ∈ U from hU)
    obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff_ball.1 hh
    exact ⟨r, hr, fun s hs => (hr' s hs).2, fun s hs hne => (hr' s hs).1 hne⟩

  have hinvB : ∀ (s₀ : ℂ) (r : ℝ) (k : ℕ) (H : ℂ → UA σ J → ℂ),
      (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) →
      (∀ g, DifferentiableOn ℂ (H · g) (Metric.ball s₀ r)) →
      ∀ s ∈ Metric.ball s₀ r, ∀ γ ∈ ratU σ J, ∀ g, H s (γ * g) = H s g := by
    intro s₀ r k H hH hd s hs γ hγ g
    have hc : ∀ g, ContinuousAt (H · g) s := fun g =>
      ((hd g).differentiableAt (Metric.isOpen_ball.mem_nhds hs)).continuousAt
    refine eq_of_continuousAt_of_eventuallyEq_nhdsNE (hc (γ * g)) (hc g) ?_
    filter_upwards [eventually_mem_ball_ne hs, hinv s γ hγ g] with z hz hz'
    rw [hH z hz.1 hz.2, hH z hz.1 hz.2, hz']
  refine ⟨fun s₀ => ?_, ?_⟩
  · obtain ⟨k, U, Hol, C, N, hU, hHol, hd, hb⟩ := h1 s₀
    obtain ⟨r, hr, hrU, hrm⟩ := hball s₀ U hU
    have hHb : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g :=
      fun s hs => hHol s (hrU hs)
    have hdb : ∀ g, DifferentiableOn ℂ (Hol · g) (Metric.ball s₀ r) := fun g => (hd g).mono hrU
    have hi := hinvB s₀ r k Hol hHb hdb
    have hm : ∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → Measurable (Hol s) := by
      intro s hs hne
      have e : Hol s = fun g => (s - s₀) ^ k * Eis s g := funext (hHb s hs hne)
      rw [e]; exact (hrm s hs hne).const_mul _
    refine ⟨k, r, Hol, max C 0, N, hr, hHb, hdb, fun s hs g =>
      GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (g := Hol s) (hi s hs) (hb s (hrU hs)) g, fun s hs => ?_⟩
    by_cases hne : s = s₀
    swap
    · exact hm s hs hne
    rw [hne]
    have hs0 : s₀ ∈ Metric.ball s₀ r := Metric.mem_ball_self hr
    let t : ℕ → ℂ := fun m => s₀ + ((r / 2 * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ)
    have hpos : ∀ m : ℕ, 0 < r / 2 * (1 / ((m : ℝ) + 1)) := fun m => by positivity
    have ht_ball : ∀ m, t m ∈ Metric.ball s₀ r := by
      intro m
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := m.cast_nonneg (α := ℝ); linarith
      have hle : 1 / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact hm1
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [t, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos m)]
      nlinarith
    have ht_ne : ∀ m, t m ≠ s₀ := by
      intro m h
      have h' : ((r / 2 * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) = 0 := by
        simpa [t] using h
      exact (hpos m).ne' (Complex.ofReal_eq_zero.1 h')
    have ht_lim : Tendsto t atTop (𝓝 s₀) := by
      have h0 : Tendsto (fun m : ℕ => r / 2 * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / 2)
      have h3 : Tendsto t atTop (𝓝 (s₀ + ((0 : ℝ) : ℂ))) :=
        tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).comp h0)
      simpa using h3
    refine measurable_of_tendsto_metrizable (f := fun m => Hol (t m))
      (fun m => hm _ (ht_ball m) (ht_ne m)) ?_
    rw [tendsto_pi_nhds]
    intro g
    exact (((hdb g).differentiableAt (Metric.isOpen_ball.mem_nhds hs0)).continuousAt.tendsto).comp ht_lim
  · obtain ⟨U, hU, C, N, hU'⟩ := h2
    obtain ⟨r, hr, hrU, hrm⟩ := hball _ U hU
    have hdb : ∀ g, DifferentiableOn ℂ (Eis · g) (Metric.ball (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) r) :=
      fun g => (hU' g).1.mono hrU
    have hi := hinvB _ r 0 Eis (fun s _ _ g => by simp) hdb
    refine ⟨r, max C 0, N, hr, hdb, fun s hs g =>
      GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (g := Eis s) (hi s hs) (fun h => (hU' h).2.1 s (hrU hs)) g,
      fun s hs => ?_⟩
    by_cases hne : s = -((((b + 2 : ℕ) : ℂ) - 1) / 2)
    · have e : Eis s = fun _ => 1 := funext fun g => by rw [hne]; exact (hU' g).2.2
      rw [e]; exact measurable_const
    · exact hrm s hs hne

end GlobalTheory.ConeSmallCT

end
