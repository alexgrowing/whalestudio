import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExistsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

section Abstract

variable {Y : Type} [MeasurableSpace Y] {ν : Measure Y}

theorem integrableOn_and_sub_withDensity {g F : Y → ℝ} {S : Set Y} (hg : Measurable g)
    (hS : MeasurableSet S)
    (h₁ : IntegrableOn F S (ν.withDensity fun y => ENNReal.ofReal (g y)))
    (h₂ : IntegrableOn F S (ν.withDensity fun y => ENNReal.ofReal (-g y))) :
    IntegrableOn (fun y => g y * F y) S ν ∧
      (∫ y in S, F y ∂(ν.withDensity fun y => ENNReal.ofReal (g y))) -
        (∫ y in S, F y ∂(ν.withDensity fun y => ENNReal.ofReal (-g y))) =
      ∫ y in S, g y * F y ∂ν := by
  have m₁ : Measurable fun y => ENNReal.ofReal (g y) := hg.ennreal_ofReal
  have m₂ : Measurable fun y => ENNReal.ofReal (-g y) := hg.neg.ennreal_ofReal
  have t₁ : ∀ᵐ y ∂(ν.restrict S), ENNReal.ofReal (g y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have t₂ : ∀ᵐ y ∂(ν.restrict S), ENNReal.ofReal (-g y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold IntegrableOn at h₁ h₂ ⊢
  rw [restrict_withDensity hS] at h₁ h₂
  rw [restrict_withDensity hS, restrict_withDensity hS]
  have i₁ := (integrable_withDensity_iff_integrable_smul' m₁ t₁).1 h₁
  have i₂ := (integrable_withDensity_iff_integrable_smul' m₂ t₂).1 h₂
  have e : ∀ y, g y * F y =
      (ENNReal.ofReal (g y)).toReal • F y - (ENNReal.ofReal (-g y)).toReal • F y := fun y => by
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', smul_eq_mul, smul_eq_mul, ← sub_mul]
    congr 1
    rcases le_total 0 (g y) with h | h
    · simp [h]
    · simp [h]
  refine ⟨(i₁.sub i₂).congr (Eventually.of_forall fun y => (e y).symm), ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul₀ m₁.aemeasurable t₁,
    integral_withDensity_eq_integral_toReal_smul₀ m₂.aemeasurable t₂, ← integral_sub i₁ i₂]
  exact integral_congr_ae (Eventually.of_forall fun y => (e y).symm)

theorem tendsto_partial_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (-Real.log (1 - x))) := by
  have := (Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg h0])).tendsto_sum_nat
  exact this

theorem partial_log_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1) ∧
      ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1) ≤ -Real.log (1 - x) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg h0])
  have hn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨Finset.sum_nonneg fun n _ => hn n, ?_⟩
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ fun n _ => hn n

theorem integral_log_eq_of_forall_pow [IsFiniteMeasure ν] {v D d : Y → ℝ}
    (hv : Measurable v) (hD : Measurable D) (hd : Measurable d)
    (bD : ∃ C, ∀ y, |D y| ≤ C) (bd : ∃ C, ∀ y, |d y| ≤ C)
    (h0 : ∀ y, 0 ≤ v y) (h1 : ∀ᵐ y ∂ν, v y < 1)
    (hi : Integrable (fun y => D y * Real.log (1 - v y)) ν)
    (H : ∀ n : ℕ, ∫ y, (v y ^ (n + 1) * D y + (n + 1) * v y ^ n * (1 - v y) * d y) ∂ν = 0) :
    ∫ y, D y * Real.log (1 - v y) ∂ν = ∫ y, d y ∂ν := by
  obtain ⟨CD, hCD⟩ := bD
  obtain ⟨Cd, hCd⟩ := bd
  have hdi : Integrable d ν := Integrable.of_bound hd.aestronglyMeasurable Cd
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hCd y)
  have hhm : ∀ n : ℕ, Measurable fun y =>
      v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y := fun n =>
    ((hv.pow_const _).mul hD).add
      (((measurable_const.mul (hv.pow_const _)).mul (measurable_const.sub hv)).mul hd)
  have hhi : ∀ n : ℕ, Integrable (fun y =>
      v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y) ν := fun n => by
    refine Integrable.of_bound (hhm n).aestronglyMeasurable (CD + ((n : ℝ) + 1) * Cd) ?_
    filter_upwards [h1] with y hy
    have a0 : 0 ≤ v y ^ (n + 1) := pow_nonneg (h0 y) _
    have a1 : v y ^ (n + 1) ≤ 1 := pow_le_one₀ (h0 y) hy.le
    have b0 : 0 ≤ v y ^ n * (1 - v y) := mul_nonneg (pow_nonneg (h0 y) _) (by linarith)
    have b1 : v y ^ n * (1 - v y) ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ (h0 y) hy.le) (by linarith) (by linarith [h0 y])
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg a0]
      calc v y ^ (n + 1) * |D y| ≤ 1 * |D y| := by gcongr
        _ ≤ CD := by simpa using hCD y
    · have e : ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y =
          ((n : ℝ) + 1) * ((v y ^ n * (1 - v y)) * d y) := by ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg b0]
      gcongr
      calc v y ^ n * (1 - v y) * |d y| ≤ 1 * |d y| := by gcongr
        _ ≤ Cd := by simpa using hCd y

  have hQ : ∀ N : ℕ, ∫ y, (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) ∂ν = 0 := fun N => by
    rw [integral_finset_sum _ fun n _ => (hhi n).const_mul _]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [integral_const_mul]
    have := H n
    push_cast at this
    rw [this, mul_zero]
  have hform : ∀ (N : ℕ) (y : Y), (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) =
      (∑ n ∈ Finset.range N, v y ^ (n + 1) / ((n : ℝ) + 1)) * D y + (1 - v y ^ N) * d y := by
    intro N y
    rw [← geom_sum_mul_neg, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∫ y, (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) ∂ν) atTop
      (𝓝 (∫ y, (-(D y * Real.log (1 - v y)) + d y) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => |D y * Real.log (1 - v y)| + |d y|)
      (fun N => (Finset.measurable_sum _ fun n _ =>
        measurable_const.mul (hhm n)).aestronglyMeasurable)
      (hi.abs.add hdi.abs) (fun N => ?_) ?_
    · filter_upwards [h1] with y hy
      rw [hform, Real.norm_eq_abs]
      obtain ⟨q0, q1⟩ := partial_log_bound (h0 y) hy N
      have l0 : 0 ≤ -Real.log (1 - v y) :=
        neg_nonneg.2 (Real.log_nonpos (by linarith) (by linarith [h0 y]))
      have p0 : 0 ≤ v y ^ N := pow_nonneg (h0 y) _
      have p1 : v y ^ N ≤ 1 := pow_le_one₀ (h0 y) hy.le
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_nonneg q0, mul_comm, ← abs_neg (Real.log _),
          abs_of_nonneg l0]
        gcongr
      · rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - v y ^ N)]
        calc (1 - v y ^ N) * |d y| ≤ 1 * |d y| := by gcongr; linarith
          _ = |d y| := one_mul _
    · filter_upwards [h1] with y hy
      simp_rw [hform]
      have t1 := tendsto_partial_log (h0 y) hy
      have t2 : Tendsto (fun N : ℕ => v y ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (h0 y) hy
      have := (t1.mul_const (D y)).add ((tendsto_const_nhds (x := (1 : ℝ)).sub t2).mul_const (d y))
      convert this using 2
      ring
  have hz : ∫ y, (-(D y * Real.log (1 - v y)) + d y) ∂ν = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp_rw [hQ]
    exact tendsto_const_nhds
  rw [integral_add (show Integrable (fun y => -(D y * Real.log (1 - v y))) ν from hi.neg) hdi,
    integral_neg] at hz
  linarith

end Abstract

theorem green_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (κ κ' δ : AlgChart p σ 1 → CxPts p σ → ℝ), IsDens κ → IsDens κ' → IsDens δ → ∀ (v f : CxPts p σ → ℝ) (S : Set (CxPts p σ)), Continuous v → (∀ y, 0 ≤ v y ∧ v y ≤ 1) → IsOpen S → Sᶜ.Finite → (∀ y ∈ S, v y < 1 ∧ f y = Real.log (1 - v y) / 2) → IntegrableOn f S (part κ) → IntegrableOn f S (part fun c y => -κ c y) → IntegrableOn f S (part κ') → IntegrableOn f S (part fun c y => -κ' c y) → (∀ n : ℕ, total (fun c y => v y ^ (n + 1) * (κ c y - κ' c y) + (n + 1) * v y ^ n * (1 - v y) * δ c y) = 0) → 2 * ((∫ y in S, f y ∂(part κ) - ∫ y in S, f y ∂(part fun c y => -κ c y)) - (∫ y in S, f y ∂(part κ') - ∫ y in S, f y ∂(part fun c y => -κ' c y))) = total δ := by
  intro k _ X p σ _ _ _ hR κ κ' δ hκ hκ' hδ v f S hv hv01 hSo hSf hSv i1 i2 i3 i4 H
  obtain ⟨ν, w, hfin, hno, hdens, hmeas⟩ := GlobalTheory.T.finite_measure_density_exists k X p σ hR
  obtain ⟨g, hg, hgw⟩ := hdens κ hκ
  obtain ⟨g', hg', hgw'⟩ := hdens κ' hκ'
  obtain ⟨d, hd, hdw⟩ := hdens δ hδ
  have p1 := (hmeas κ g hg hgw).1
  have p2 := (hmeas (fun c y => -κ c y) (fun y => -g y) hg.neg
    fun c y hy => by rw [hgw c y hy, neg_mul]).1
  have p3 := (hmeas κ' g' hg' hgw').1
  have p4 := (hmeas (fun c y => -κ' c y) (fun y => -g' y) hg'.neg
    fun c y hy => by rw [hgw' c y hy, neg_mul]).1
  have hSm : MeasurableSet S := hSo.measurableSet
  haveI : NullSingletonClass ν := hno
  have hae : ∀ᵐ y ∂ν, y ∈ S := mem_ae_iff.2 (hSf.measure_zero ν)
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hF : Set.EqOn f (fun y => Real.log (1 - v y) / 2) S := fun y hy => (hSv y hy).2
  rw [p1] at i1
  rw [p2] at i2
  rw [p3] at i3
  rw [p4] at i4
  obtain ⟨a1, e1⟩ := integrableOn_and_sub_withDensity hg.measurable hSm
    (i1.congr_fun hF hSm) (i2.congr_fun hF hSm)
  obtain ⟨a2, e2⟩ := integrableOn_and_sub_withDensity hg'.measurable hSm
    (i3.congr_fun hF hSm) (i4.congr_fun hF hSm)
  unfold IntegrableOn at a1 a2
  rw [hres] at a1 a2 e1 e2
  have hi : Integrable (fun y => (g y - g' y) * Real.log (1 - v y)) ν :=
    ((a1.sub a2).const_mul 2).congr (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
  have key := integral_log_eq_of_forall_pow (ν := ν) (v := v) (D := fun y => g y - g' y) (d := d)
    hv.measurable (hg.sub hg').measurable hd.measurable
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hg.sub hg').continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hd.continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (fun y => (hv01 y).1) (hae.mono fun y hy => (hSv y hy).1) hi
    (fun n => by
      have hc : Continuous fun y => v y ^ (n + 1) * (g y - g' y) +
          ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y := by fun_prop
      rw [← (hmeas _ _ hc fun c y hy => ?_).2]
      · exact H n
      · rw [hgw c y hy, hgw' c y hy, hdw c y hy]
        ring)
  rw [p1, p2, p3, p4, (hmeas δ d hd hdw).2, ← key,
    setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF,
    setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF, e1, e2, ← integral_sub a1 a2,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

end GlobalTheory.CurveDens
