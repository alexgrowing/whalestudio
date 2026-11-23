import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableA
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsSumMeasurableWeightA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PtsBddConv.maDensity_div_const {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) (r : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j y => ψ j y / r) z = r⁻¹ ^ D * maDensity ψ z := by
  have hH : ∀ j, cxHessian (fun y => ψ j y / r) z = (((r⁻¹ : ℝ) : ℂ)) • cxHessian (ψ j) z := by
    intro j
    have h1 : (fun y => ψ j y / r) = r⁻¹ • ψ j := by
      funext y
      simp [div_eq_inv_mul]
    have h2 : fderiv ℝ (fderiv ℝ (fun y => ψ j y / r)) = r⁻¹ • fderiv ℝ (fderiv ℝ (ψ j)) := by
      rw [h1, fderiv_const_smul_field]
      exact fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (ψ j)) r⁻¹
    ext a b
    simp only [cxHessian, h2, Pi.smul_apply, smul_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hS : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (fun y => ψ k y / r) z).det =
      ((r⁻¹ ^ D : ℝ) : ℂ) * ((-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) := by
    intro S
    simp only [hH, ← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin]
    push_cast
    ring
  simp only [maDensity, mixedDisc, hS, ← Finset.mul_sum]
  rw [show (1 / (D.factorial : ℂ)) * (((r⁻¹ ^ D : ℝ) : ℂ) *
      ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) =
      ((r⁻¹ ^ D : ℝ) : ℂ) * ((1 / (D.factorial : ℂ)) *
      ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) by ring,
    Complex.re_ofReal_mul]
  ring

theorem PtsBddConv.proof (hAbs : Inter.PtsAbsIntegrable.Statement) : PtsBddConv.Statement := by
  intro K _ ι _ P e L r g g₀ N C s₀ hP hL hr hN hs₀ hg hlim
  classical

  have key : ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ y w) ∧
      Tendsto (fun s => ptsIntegralAt P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegralAt P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀)) := by
    intro Ψ hΨ
    have hfin : ∀ y, (fibre P Ψ y).Finite := fibreFinite K ι P e Ψ hP hΨ
    have hL' : ∀ j : Fin e, IsSmoothHerm ((fun _ => L) j) := fun _ => hL
    have hone : IsSectionOn P (oneLine (ι := ι)) 1 := by
      refine ⟨0, fun k => by simp [oneLine, HermLine.ofWeight], fun m hm k => ?_,
        fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    have hB := hAbs K ι P e Ψ (fun _ => L) oneLine 1 hP hΨ hL' isSmoothHerm_oneLine hone

    have hbd : ∀ (h : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ hγ : ∃ γ, IsSheet P Ψ y w γ, |h (hγ.choose y)| ≤ C) →
        |sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) h y w| ≤
          C * r⁻¹ ^ e * |sheetDensity P Ψ (pot fun _ => L) (logNorm oneLine 1) y w| := by
      intro h y w hh
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [sheetDensity, dif_pos hγ, logNorm_oneLine, one_mul, pot]
        rw [PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (hγ.choose y'))) r y, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) e), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hh hγ)
          (pow_nonneg (inv_nonneg.mpr hr.le) e)) (abs_nonneg _)
      · simp only [sheetDensity, dif_neg hγ, abs_zero, mul_zero, le_refl]
    have hsum : ∀ (h : ((Σ k, ι k) → ℂ) → ℝ) y, (∀ w (hγ : ∃ γ, IsSheet P Ψ y w γ), |h (hγ.choose y)| ≤ C) →
        ‖∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) h y w‖ ≤
          C * r⁻¹ ^ e * ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot fun _ => L) (logNorm oneLine 1) y w| := by
      intro h y hh
      rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
        finsum_mem_eq_finite_toFinset_sum _ (hfin y), Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => hbd h y w (hh w))

    set S : Set (Fin e → ℂ) := {y | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} with hSdef
    have hS : volume S = 0 := hN Ψ hΨ
    have hSae : ∀ᵐ y, y ∉ S := measure_eq_zero_iff_ae_notMem.mp hS
    have hpt : ∀ y w (hγ : ∃ γ, IsSheet P Ψ y w γ), hγ.choose y ∈ mcPts P ∧ Ψ (segre (hγ.choose y)) = Fin.cons 1 y :=
      fun y w hγ => ⟨hγ.choose_spec.2.self_of_nhds.2.1, hγ.choose_spec.2.self_of_nhds.2.2⟩
    have hoff : ∀ y ∉ S, ∀ w (hγ : ∃ γ, IsSheet P Ψ y w γ), hγ.choose y ∉ N :=
      fun y hy w hγ hz => hy ⟨_, (hpt y w hγ).1, hz, (hpt y w hγ).2⟩

    have hmeas : ∀ s, 0 < s → s < s₀ → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s) y w) volume := by
      intro s hs hs1
      obtain ⟨-, hgc, hgt⟩ := hg s hs hs1
      set M := toMeasurable volume S with hMdef
      have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
      have hSM : S ⊆ M := subset_toMeasurable _ _
      have hM0 : volume M = 0 := by rw [hMdef, measure_toMeasurable]; exact hS
      obtain ⟨g', hg'⟩ : ∃ g' : ((Σ k, ι k) → ℂ) → ℝ, ∀ z,
          g' z = if ∃ y ∈ M, Ψ (segre z) = Fin.cons 1 y then 0 else g s z := ⟨_, fun _ => rfl⟩
      obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
      have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
        (hlift m y hy).1.continuousAt.continuousWithinAt
      have hcons : ∀ {y y' : Fin e → ℂ}, (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 y' → y = y' := by
        intro y y' h
        simpa using congrArg Fin.tail h
      set v : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m \ M).piecewise (fun y => g s (γ m y)) 0 with hvdef
      have hvm : ∀ m, Measurable (v m) := by
        intro m
        refine ContinuousOn.measurable_piecewise ?_ continuousOn_const ((hBo m).measurableSet.diff hMm)
        refine hgc.comp ((hγc m).mono Set.sdiff_subset) fun y hy => ⟨(hlift m y hy.1).2.1, fun hz => ?_⟩
        exact hy.2 (hSM ⟨_, (hlift m y hy.1).2.1, hz, (hlift m y hy.1).2.2⟩)
      have hind0 := sheetIndep K ι P e Ψ (fun _ => L) oneLine 1 hP hΨ hL' isSmoothHerm_oneLine hone
      have hae := PtsSumMeasurableWeight.aestronglyMeasurable_fibreSum_of_lifts
        (fun (_ : Fin e) z => Real.log (L.h z) / r) g' id measurable_id rfl hfin B γ hBo hlift hcov
        (fun m y => v m y * maDensity (fun j y' => (fun (_ : Fin e) z => Real.log (L.h z) / r) j (γ m y')) y)
        (fun m => (hvm m).mul (PtsSumMeasurable.measurable_maDensity _))
        (fun m y hy => by
          rw [hg']
          simp only [hvdef]
          by_cases hyM : y ∈ M
          · rw [if_pos ⟨y, hyM, (hlift m y hy).2.2⟩,
              Set.piecewise_eq_of_notMem _ _ _ (fun h : y ∈ B m \ M => h.2 hyM)]
            simp
          · have hne : ¬ ∃ y' ∈ M, Ψ (segre (γ m y)) = Fin.cons 1 y' := by
              rintro ⟨y', hy'M, h⟩
              obtain rfl := hcons (((hlift m y hy).2.2).symm.trans h)
              exact hyM hy'M
            rw [if_neg hne, Set.piecewise_eq_of_mem (B m \ M) _ _ (Set.mem_sdiff_of_mem hy hyM)])
        (by
          filter_upwards [hind0] with y hy w γ₁ γ₂ h₁ h₂
          have hd := hy w γ₁ γ₂ h₁ h₂
          simp only [logNorm_oneLine, one_mul, pot] at hd
          have hm₁ : γ₁ y ∈ mcPts P := h₁.2.self_of_nhds.2.1
          have hm₂ : γ₂ y ∈ mcPts P := h₂.2.self_of_nhds.2.1
          have hseg : segre (γ₁ y) = segre (γ₂ y) := h₁.1.trans h₂.1.symm
          choose i0 hi0 using hm₁.1
          obtain ⟨hc0, hc⟩ := eq_bsmul_of_segre_eq i0 hi0 hseg
          have hgg : g s (γ₂ y) = g s (γ₁ y) := by
            rw [hc]
            exact hgt _ (fun k => div_ne_zero (hc0 k) (hi0 k)) _ hm₁
          rw [PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (γ₁ y'))) r y,
            PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (γ₂ y'))) r y, hd, hg', hg', hseg, hgg])
      refine hae.congr ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0] with y hy
      refine finsum_mem_congr rfl fun w _ => ?_
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [id, sheetDensity, dif_pos hγ]
        have hne : ¬ ∃ y' ∈ M, Ψ (segre (hγ.choose y)) = Fin.cons 1 y' := by
          rintro ⟨y', hy'M, h⟩
          obtain rfl := hcons ((hpt y w hγ).2.symm.trans h)
          exact hy hy'M
        rw [hg', if_neg hne]
      · simp only [id, sheetDensity, dif_neg hγ]

    have hlimpt : ∀ᵐ y, Tendsto (fun s => ∑ᶠ w ∈ fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s) y w) (𝓝[>] 0)
        (𝓝 (∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ y w)) := by
      filter_upwards [hSae] with y hy
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      refine tendsto_finsetSum _ fun w _ => ?_
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [sheetDensity, dif_pos hγ]
        exact (hlim _ (hpt y w hγ).1 (hoff y hy w hγ)).mul_const _
      · simp only [sheetDensity, dif_neg hγ]
        exact tendsto_const_nhds
    have hbound := hB.const_mul (C * r⁻¹ ^ e)

    have hg₀ : ∀ z ∈ mcPts P, z ∉ N → |g₀ z| ≤ C := fun z hz hzN =>
      le_of_tendsto ((continuous_abs.tendsto _).comp (hlim z hz hzN))
        (by filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs using (hg s hs.1 hs.2).1 z hz)
    set u : ℕ → ℝ := fun n => s₀ / 2 * (1 / ((n : ℝ) + 1)) with hudef
    have hupos : ∀ n, 0 < u n := fun n => by positivity
    have hult : ∀ n, u n < s₀ := fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc u n ≤ s₀ / 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ < s₀ := by linarith
    have hu : Tendsto u atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hupos⟩
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (s₀ / 2)
      rw [mul_zero] at h
      exact h
    have hmeas₀ := aestronglyMeasurable_of_tendsto_ae atTop (fun n => hmeas (u n) (hupos n) (hult n))
      (by filter_upwards [hlimpt] with y hy using hy.comp hu)
    refine ⟨hbound.mono' hmeas₀ ?_, ?_⟩
    · filter_upwards [hSae] with y hy
      exact hsum g₀ y fun w hγ => hg₀ _ (hpt y w hγ).1 (hoff y hy w hγ)
    · refine tendsto_integral_filter_of_dominated_convergence _
        (by filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs using hmeas s hs.1 hs.2) ?_ hbound hlimpt
      filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      exact Eventually.of_forall fun y => hsum (g s) y fun w hγ => (hg s hs.1 hs.2).1 _ (hpt y w hγ).1
  refine ⟨fun Ψ hΨ => (key Ψ hΨ).1, ?_⟩
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    exact (key _ hΨ.choose_spec).2
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds

end GroundTheory.Heights₂.Heights.LowerBoundFree
