import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsRegLimit
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsRegLimit.abs_half_log_le {x ε : ℝ} (hx : x ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (x ^ 2 + ε) / 2| ≤ |Real.log x| + |Real.log (x ^ 2 + 1) / 2| := by
  have h2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
  have hlo : Real.log x ≤ Real.log (x ^ 2 + ε) / 2 := by
    have : Real.log x = Real.log (x ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
    rw [this]
    exact div_le_div_of_nonneg_right (Real.log_le_log h2 (by linarith)) (by norm_num)
  have hhi : Real.log (x ^ 2 + ε) / 2 ≤ Real.log (x ^ 2 + 1) / 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log x), abs_nonneg (Real.log (x ^ 2 + 1) / 2)]
  · linarith [le_abs_self (Real.log (x ^ 2 + 1) / 2), abs_nonneg (Real.log x)]

theorem PtsRegLimit.tendsto_half_log {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have h2 : x ^ 2 + 0 ≠ 0 := by rw [add_zero]; exact pow_ne_zero 2 hx
  have hc : ContinuousAt (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) 0 :=
    ((continuousAt_const.add continuousAt_id).log h2).div_const 2
  have hv : Real.log (x ^ 2 + 0) / 2 = Real.log x := by
    rw [add_zero, Real.log_pow]; push_cast; ring
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem PtsRegLimit.proof (hInt : PtsIntegrableStatement) (hAbs : PtsAbsIntegrable.Statement) :
    PtsRegLimit.Statement := by
  intro K _ ι _ Q e M E t ht hQ hM hE htQ
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds
  simp only [dif_pos hΨ]
  have hgood := hΨ.choose_spec
  generalize hΨ.choose = Ψ at hgood ⊢
  unfold ptsIntegralAt
  obtain ⟨a, haE, hta⟩ := id ht
  have hfin : ∀ y, (fibre Q Ψ y).Finite := fibreFinite K ι Q e Ψ hQ hgood
  have h1 : (1 : MRing ι) ∉ Q := fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  have hone : ∀ ε, IsSectionOn Q (regLine E t ht ε) 1 := fun ε =>
    ⟨fun _ => 0, fun k => by rw [regLine_a]; simp, fun m hm k => by
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp, h1⟩

  have hsdlog : ∀ (B : HermLine ι) y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (B.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm B 1) y w := by
    intro B y w
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, logNorm, map_one, norm_one, one_div, Real.log_inv]
      ring
    · simp only [sheetDensity, dif_neg hγ, neg_zero]
  have hFint : ∀ ε, 0 < ε → Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht ε).h z)) y w) := by
    intro ε hε
    refine (hInt K ι Q e Ψ M (regLine E t ht ε) 1 hQ hgood hM (isSmoothHerm_regLine hE hε)
      (hone ε)).neg.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => (hsdlog _ y w).symm

  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJP : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hN : ∀ᵐ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ := compl_mem_ae_iff.mpr (projB_null Ψ hQ hgood hJ hJP)
  have hpt : ∀ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ → ∀ w (hγ : ∃ γ, IsSheet Q Ψ y w γ), secNorm E t (hγ.choose y) ≠ 0 := by
    intro y hy w hγ h0
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hev0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact norm_eq_zero.mp h
      · exact absurd h (E.pos _ hmem.1).ne'
    refine hy ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hev0, mul_zero]
  have hB1 : ∀ z, |Real.log ((regLine E t ht 1).h z)| = |Real.log (secNorm E t z ^ 2 + 1) / 2| := fun z => by
    rw [log_regLine_h]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => ∑ᶠ w ∈ fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (logNorm E t) y w| +
      ∑ᶠ w ∈ fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht 1).h z)) y w|)
    (eventually_mem_nhdsWithin.mono fun ε hε => (hFint ε hε).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hN] with y hy
    rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [hB1, log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.abs_half_log_le (hpt y hy w hγ) hε.1 hε.2.le
    · simp only [sheetDensity, dif_neg hγ, abs_zero, add_zero, le_refl]
  ·
    have hts : IsSectionOn Q E t := ⟨a, haE, hta, htQ⟩
    refine (hAbs K ι Q e Ψ M E t hQ hgood hM hE hts).add ((hAbs K ι Q e Ψ M (regLine E t ht 1) 1 hQ hgood hM
      (isSmoothHerm_regLine hE one_pos) (hone 1)).congr (Eventually.of_forall fun y => ?_))
    exact finsum_mem_congr rfl fun w _ => by rw [hsdlog, abs_neg]
  ·
    filter_upwards [hN] with y hy
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun w _ => ?_
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ]
      refine Tendsto.mul_const _ ?_
      simp only [log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.tendsto_half_log (hpt y hy w hγ)
    · simp only [sheetDensity, dif_neg hγ]
      exact tendsto_const_nhds

end GroundTheory.Heights₂.Heights.Inter
