import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogBallEstimates

theorem neg_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) : -Real.log t ≤ t ^ (-ε) / ε := by
  have := Real.log_le_rpow_div (inv_pos.2 ht).le hε
  rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this

theorem large_power_bound {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 1 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  rw [min_eq_right ((inv_le_one_of_one_le₀ ht).trans ht), Real.rpow_one]
  have h1 : t ^ σ * t ≤ t ^ M := by
    rw [← Real.rpow_add_one t0.ne', ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht hM
  have hp : 0 < t ^ M := by positivity
  have h2 : c ≤ |C| * (t ^ M)⁻¹ := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h3 : t ^ σ ≤ t ^ M * t⁻¹ := by
    rw [le_mul_inv_iff₀ t0]; exact h1
  calc c * t ^ σ ≤ |C| * (t ^ M)⁻¹ * t ^ σ := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * ((t ^ M)⁻¹ * t ^ σ) := by ring
    _ ≤ |C| * ((t ^ M)⁻¹ * (t ^ M * t⁻¹)) := by gcongr
    _ = |C| * t⁻¹ := by field_simp

theorem big_log {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 2 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ * |Real.log t| ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  have hl : |Real.log t| ≤ t := by
    rw [abs_of_nonneg (Real.log_nonneg ht)]; linarith [Real.log_le_sub_one_of_pos t0]
  calc c * t ^ σ * |Real.log t| ≤ c * t ^ σ * t := by gcongr
    _ = c * t ^ (σ + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ _ := large_power_bound ht (by linarith) hc h

theorem small_power_bound {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * t ^ (2 * ε) := by
  have h2 : c ≤ |C| * t := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) t0.le)
  calc c * t ^ b ≤ |C| * t * t ^ b := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * t ^ (b + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ |C| * t ^ (2 * ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge t0 t1.le hb) (abs_nonneg _)

theorem small0 {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have h2 : t ^ (2 * ε) ≤ t ^ ε := Real.rpow_le_rpow_of_exponent_ge t0 t1.le (by linarith)
  have h3 : 0 ≤ |C| * t ^ ε * ε⁻¹ := by positivity
  calc c * t ^ b ≤ |C| * t ^ ε := h1.trans (by gcongr)
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem small_log {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b * |Real.log t| ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have hl : |Real.log t| ≤ t ^ (-ε) / ε := by
    rw [abs_of_neg (Real.log_neg t0 t1)]; exact neg_log_le t0 hε
  have e : t ^ (2 * ε) * (t ^ (-ε) / ε) = t ^ ε * ε⁻¹ := by
    rw [mul_div_assoc', ← Real.rpow_add t0, div_eq_mul_inv]; ring_nf
  have h3 : 0 ≤ |C| * t ^ ε := by positivity
  calc c * t ^ b * |Real.log t| ≤ |C| * t ^ (2 * ε) * (t ^ (-ε) / ε) := by
        gcongr
    _ = |C| * t ^ ε * ε⁻¹ := by rw [mul_assoc, e]; ring
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem bddBelow_support_primePowerComponent_coeff {t ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hc : 0 ≤ c) (h : c ≤ C) :
    c * t ^ ε ≤ |C| * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  exact mul_le_mul_of_nonneg_right (h.trans (le_abs_self C)) (by positivity)

theorem re_lt_of_ball {s s₀ : ℂ} {r : ℝ} (hs : s ∈ Metric.ball s₀ r) : |s.re - s₀.re| < r := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hs

variable {X : Type*} [MeasurableSpace X]

theorem intg (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s : ℂ) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s.re ≤ g x) : Integrable (fun x => F x * (D x : ℂ) ^ s) ν :=
  hg.mono' (hF.mul ((Complex.measurable_ofReal.comp hDm).pow_const s).aestronglyMeasurable)
    (h0.mono fun x hx => by rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x)]; exact hx)

theorem diffAt (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s₀ : ℂ) (r : ℝ) (hr : 0 < r) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s₀.re ≤ g x)
    (hb : ∀ᵐ x ∂ν, ∀ s ∈ Metric.ball s₀ r, ‖F x‖ * D x ^ s.re * |Real.log (D x)| ≤ g x) :
    DifferentiableAt ℂ (fun s => ∫ x, F x * (D x : ℂ) ^ s ∂ν) s₀ := by
  have hDc : Measurable fun x => (D x : ℂ) := Complex.measurable_ofReal.comp hDm
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (D x : ℂ) ^ s) ν := fun s =>
    hF.mul (hDc.pow_const s).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := ν)
    (F := fun s x => F x * (D x : ℂ) ^ s) (F' := fun s x => F x * ((D x : ℂ) ^ s * Complex.log (D x)))
    (x₀ := s₀) (bound := g) (Metric.ball_mem_nhds s₀ hr) (Filter.Eventually.of_forall fun s => hmeas s)
    (intg ν D hD hDm F hF s₀ g hg h0)
    (hF.mul ((hDc.pow_const s₀).mul (Complex.measurable_log.comp hDc)).aestronglyMeasurable)
    (hb.mono fun x hx s hs => by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x), ← Complex.ofReal_log (hD x).le,
        Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      exact hx s hs)
    hg
    (Filter.Eventually.of_forall fun x s _ =>
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (hD x).ne'))).hasDerivAt.const_mul (F x)))
  exact this.2.differentiableAt

end LogBallEstimates

open LogBallEstimates in
theorem duality_diagonalClass_of_affineProperBaseChange : D0 → V1 → E1 → E2 := by
  intro hD0 hV1 hE1 E _ _ _ k μ _ hk β hβ H H₀ hG
  obtain ⟨hpos, -, hcont, -⟩ := hD0 E k
  have hmin := (hV1 E k μ hk β hβ).2.2
  have hE := hE1 E k μ hk β hβ H₀ hG.meas₀ hG.inv₀ hG.cen hG.bdd
  have hDm : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hS : MeasurableSet {g : GA E k | Dt g < 1} := measurableSet_lt hDm measurable_const
  obtain ⟨C₀, hC₀⟩ := hG.bdd
  obtain ⟨C₁, hC₁⟩ := hG.small
  have hFm : Measurable fun g => (Dt g : ℂ) * H g - H₀ g :=
    ((Complex.measurable_ofReal.comp hDm).mul hG.meas).sub hG.meas₀

  have hAb : ∀ (σ : ℝ), ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1}ᶜ (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1}ᶜ → ∀ τ, τ ≤ σ →
        ‖H x‖ * Dt x ^ τ ≤ g x ∧ ‖H x‖ * Dt x ^ τ * |Real.log (Dt x)| ≤ g x := by
    intro σ
    obtain ⟨C, hC⟩ := hG.big (⌈σ⌉₊ + 2)
    refine ⟨fun x => |C| * min (Dt x) (Dt x)⁻¹ ^ (1 : ℝ), ((hmin 1 one_pos).const_mul |C|).integrableOn,
      fun x hx τ hτ => ?_⟩
    have h1 : 1 ≤ Dt x := not_lt.1 hx
    have hM : τ + 2 ≤ ((⌈σ⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil σ]
    exact ⟨large_power_bound h1 (by linarith) (norm_nonneg _) (hC x h1), big_log h1 hM (norm_nonneg _) (hC x h1)⟩
  have hBb : ∀ ε : ℝ, 0 < ε → ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1} (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1} → ∀ b, 2 * ε ≤ b + 1 →
        ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b ≤ g x ∧
          ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b * |Real.log (Dt x)| ≤ g x := by
    intro ε hε
    refine ⟨fun x => |C₁| * (1 + ε⁻¹) * min (Dt x) (Dt x)⁻¹ ^ ε,
      ((hmin ε hε).const_mul (|C₁| * (1 + ε⁻¹))).integrableOn, fun x hx b hb => ?_⟩
    have h1 : Dt x < 1 := hx
    exact ⟨small0 (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1),
      small_log (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1)⟩
  let κ : ℂ := ((k : ℂ) * Module.finrank ℚ E)⁻¹ * ∫ g in band E k, H₀ g ∂μ.withDensity β
  let A : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}ᶜ, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β
  let B : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}, ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)
    ∂μ.withDensity β
  have hA : ∀ s₀ : ℂ, DifferentiableAt ℂ A s₀ := by
    intro s₀
    obtain ⟨g, hg, hgb⟩ := hAb (s₀.re + 1)
    refine diffAt _ Dt hpos hDm H hG.meas.aestronglyMeasurable s₀ 1 one_pos g hg ?_ ?_
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgb x hx _ (by linarith)).1)
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by linarith [(abs_lt.1 (re_lt_of_ball hs)).2])).2)
  have hB : ∀ s₀ : ℂ, 0 < s₀.re → DifferentiableAt ℂ B s₀ := by
    intro s₀ h0
    obtain ⟨g, hg, hgb⟩ := hBb (s₀.re / 4) (by linarith)
    have := diffAt _ Dt hpos hDm _ hFm.aestronglyMeasurable (s₀ - 1) (s₀.re / 2) (by linarith) g hg
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
        (hgb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by
          have := (abs_lt.1 (re_lt_of_ball hs)).1
          rw [Complex.sub_re, Complex.one_re] at this; linarith)).2))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s₀ := differentiableAt_id.sub_const 1
    have h3 := DifferentiableAt.comp s₀ this h2
    exact h3
  refine ⟨fun s => (s - 1) * (A s + B s) + κ, fun s hs => ?_, fun s hs => ?_, fun hb => ?_⟩
  · have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
    exact (h2.mul ((hA s).add (hB s hs))).add_const κ |>.differentiableWithinAt
  · obtain ⟨gA, hgA, hgAb⟩ := hAb s.re
    obtain ⟨gB, hgB, hgBb⟩ := hBb (1 / 2) (by norm_num)
    have i1 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1}ᶜ (μ.withDensity β) :=
      intg _ Dt hpos hDm H hG.meas.aestronglyMeasurable s gA hgA
        ((ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgAb x hx _ le_rfl).1))
    have i2 : IntegrableOn (fun g => ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1}
        (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hFm.aestronglyMeasurable (s - 1) gB hgB
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          (hgBb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
    have hs1 : 0 < (s - 1).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have i3 : IntegrableOn (fun g => H₀ g * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1} (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hG.meas₀.aestronglyMeasurable (s - 1) _
        ((hmin _ hs1).const_mul |C₀|).integrableOn
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          bddBelow_support_primePowerComponent_coeff (hpos x) hx (norm_nonneg _) (hC₀ x)))
    have hid : ∀ g, H g * (Dt g : ℂ) ^ s =
        ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1) + H₀ g * (Dt g : ℂ) ^ (s - 1) := by
      intro g
      have h0 : (Dt g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos g).ne'
      rw [Complex.cpow_sub _ _ h0, Complex.cpow_one]
      field_simp
      ring
    have i4 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1} (μ.withDensity β) := by
      simp_rw [hid]; exact i2.add i3
    have hint : Integrable (fun g => H g * (Dt g : ℂ) ^ s) (μ.withDensity β) := by
      have := i4.union i1
      rwa [Set.union_compl_self, integrableOn_univ] at this
    have hE' := hE (s - 1) hs1
    rw [← integral_add_compl hS hint]
    have hsplit : ∫ g in {g | Dt g < 1}, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β =
        B s + ∫ g in {g | Dt g < 1}, H₀ g * (Dt g : ℂ) ^ (s - 1) ∂μ.withDensity β := by
      simp_rw [hid]; exact integral_add i2 i3
    rw [hsplit]
    show (s - 1) * (A s + B s) + κ = _
    linear_combination -hE'
  · show (1 - 1) * (A 1 + B 1) + κ = 0
    simp only [sub_self, zero_mul, zero_add, κ, hb, mul_zero]

end PositivityTheory.AdelicQuotientData

end
