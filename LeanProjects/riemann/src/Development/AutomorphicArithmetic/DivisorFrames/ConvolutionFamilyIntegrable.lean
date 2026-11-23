import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem norm_projection_le {ι : Type} [Fintype ι] {n : ℕ} (v η : Fin n × ι → ℂ) :
    ‖pr v η‖ ≤ n * ‖η‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
  unfold pr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖v (i, w) * η (i, w)‖ ≤ ∑ _i : Fin n, ‖η‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, mul_comm]
        exact mul_le_mul (norm_le_pi_norm η _) (norm_le_pi_norm v _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

private theorem power_weight_inequality (C a b c A W x : ℝ) (D r : ℕ) (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 < b)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hW0 : 0 ≤ W)
    (h1 : x ≤ C / b ^ (D + r)) (h2 : a ≤ b * (A * c)) (hW : W ≤ a ^ D) :
    x * W ≤ c ^ (D + r) * (C * A ^ (D + r) * (a ^ r)⁻¹) := by
  have hbp : 0 < b ^ (D + r) := by positivity
  have h3 : x * b ^ (D + r) ≤ C := (le_div_iff₀ hbp).1 h1
  have h4 : a ^ (D + r) ≤ (b * (A * c)) ^ (D + r) := pow_le_pow_left₀ ha.le h2 _
  have har : 0 < a ^ r := by positivity
  rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ har]
  calc x * W * a ^ r ≤ x * a ^ D * a ^ r := by gcongr
    _ = x * a ^ (D + r) := by rw [pow_add]; ring
    _ ≤ x * (b * (A * c)) ^ (D + r) := by gcongr
    _ = (x * b ^ (D + r)) * (A ^ (D + r) * c ^ (D + r)) := by rw [mul_pow, mul_pow]; ring
    _ ≤ C * (A ^ (D + r) * c ^ (D + r)) := by gcongr
    _ = _ := by ring

theorem UpperTheory.convolution_family_integrable :
    ∀ {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
        [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (κ : ι → ℤ) (e : ℕ)
        (η : K → Fin n × ι → ℂ), Continuous η → ∀ (φ : K → (ι → ℂ) → ℂ), Continuous (Function.uncurry φ) →
        (∀ N : ℕ, ∃ C : ℝ, ∀ k s, ‖φ k s‖ ≤ C / (1 + ‖s‖) ^ N) →
        ∀ h : (Fin n × ι → ℂ) → ℂ, Continuous h → (∀ N : ℕ, Integrable fun v => (1 + ‖v‖) ^ N * ‖h v‖) →
        ∫ k, ∫ s, (∫ v, h v * φ k (s + pr v (η k))) * wt κ e s ∂volume ∂μ =
          ∫ v, h v * ∫ k, ∫ s, φ k (s + pr v (η k)) * wt κ e s ∂volume ∂μ := by
  intro ι _ n K _ _ _ _ _ μ _ κ e η hη φ hφ hdec h hh hint
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ k, ‖η k‖ ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_range hη).isBounded.exists_norm_le
    exact ⟨R, fun k => hR _ ⟨k, rfl⟩⟩
  set D : ℕ := 2 * e * Fintype.card ι with hD
  set r : ℕ := Module.finrank ℝ (ι → ℂ) + 1 with hr
  obtain ⟨C, hC⟩ := hdec (D + r)
  set A : ℝ := 1 + n * |R| with hA
  let F : (Fin n × ι → ℂ) → K × (ι → ℂ) → ℂ := fun v p => h v * (φ p.1 (p.2 + pr v (η p.1)) * wt κ e p.2)
  have hg : Integrable (fun s : ι → ℂ => C * A ^ (D + r) * ((1 + ‖s‖) ^ r)⁻¹) := by
    refine Integrable.const_mul ?_ _
    have := integrable_one_add_norm (E := ι → ℂ) (μ := volume) (r := (r : ℝ)) (by rw [hr]; push_cast; linarith)
    refine this.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hg2 : Integrable (fun p : K × (ι → ℂ) => C * A ^ (D + r) * ((1 + ‖p.2‖) ^ r)⁻¹) (μ.prod volume) :=
    hg.comp_snd μ
  have hg3 := (hint (D + r)).mul_prod hg2
  have hc : Continuous fun q : (Fin n × ι → ℂ) × (K × (ι → ℂ)) => φ q.2.1 (q.2.2 + pr q.1 (η q.2.1)) := by
    have h1 : Continuous fun q : (Fin n × ι → ℂ) × (K × (ι → ℂ)) => (q.2.1, q.2.2 + pr q.1 (η q.2.1)) := by
      unfold pr
      fun_prop
    exact hφ.comp h1
  have hm : Measurable (Function.uncurry F) :=
    (hh.measurable.comp measurable_fst).mul
      (hc.measurable.mul ((measurable_wt κ e).comp (measurable_snd.comp measurable_snd)))
  have hF : Integrable (Function.uncurry F) (volume.prod (μ.prod volume)) := by
    refine hg3.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    rintro ⟨v, k, s⟩
    simp only [Function.uncurry, F, norm_mul]
    have ht : ‖pr v (η k)‖ ≤ n * |R| * ‖v‖ :=
      (norm_projection_le v (η k)).trans (by gcongr; exact (hR k).trans (le_abs_self R))
    have hs : ‖s‖ ≤ ‖s + pr v (η k)‖ + ‖pr v (η k)‖ := by
      simpa using norm_sub_le (s + pr v (η k)) (pr v (η k))
    have h0 : (0 : ℝ) ≤ n * |R| := by positivity
    have h2 : 1 + ‖s‖ ≤ (1 + ‖s + pr v (η k)‖) * (A * (1 + ‖v‖)) := by
      have h3 : 1 + ‖pr v (η k)‖ ≤ A * (1 + ‖v‖) := by
        rw [hA]; nlinarith [norm_nonneg v]
      calc 1 + ‖s‖ ≤ (1 + ‖s + pr v (η k)‖) * (1 + ‖pr v (η k)‖) := by
            nlinarith [mul_nonneg (norm_nonneg (s + pr v (η k))) (norm_nonneg (pr v (η k)))]
        _ ≤ _ := by gcongr
    have := power_weight_inequality C (1 + ‖s‖) (1 + ‖s + pr v (η k)‖) (1 + ‖v‖) A ‖wt κ e s‖ _ D r (norm_nonneg _)
      (by positivity) (by positivity) (by positivity) (by positivity) (norm_nonneg _) (hC k _) h2 (norm_wt_le κ e s)
    calc _ ≤ ‖h v‖ * _ := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  calc _ = ∫ k, ∫ s, ∫ v, F v (k, s) ∂volume ∂volume ∂μ := by
        simp only [F, ← integral_mul_const, mul_assoc]
    _ = ∫ p, ∫ v, F v p ∂volume ∂(μ.prod volume) := (integral_prod _ hF.integral_prod_right).symm
    _ = ∫ v, ∫ p, F v p ∂(μ.prod volume) := (integral_integral_swap hF).symm
    _ = _ := by
        refine integral_congr_ae (hF.prod_right_ae.mono fun v hv => ?_)
        simp only
        rw [integral_prod (F v) hv]
        simp only [F, integral_const_mul]
