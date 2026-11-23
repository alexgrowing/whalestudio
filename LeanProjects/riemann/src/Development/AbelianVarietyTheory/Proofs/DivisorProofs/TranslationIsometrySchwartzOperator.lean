import Mathlib
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory.TransDecay

theorem seminorm_mul_shift_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ h : 𝓢(V, ℂ)) (hχ : HasCompactSupport (χ : V → ℂ)) (l m M : ℕ) :
    ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ l m k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  obtain ⟨r, hr⟩ := hχ.isCompact.isBounded.subset_closedBall (0 : V)
  set R := max r 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ tsupport (χ : V → ℂ), ‖x‖ ≤ R := fun x hx => by
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set S := ((Finset.Iic (M, m)).sup fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set A := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)), fun v k' hk' => ?_⟩
  have hvpos : 0 < (1 + ‖v‖) ^ M := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ l m k' (by positivity) fun x => ?_
  have hfun : (k' : V → ℂ) = fun y => χ y * h (y + v) := funext hk'
  rw [hfun]
  have hsh : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (y + v)) :=
    (h.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (χ.smooth ⊤) hsh x (n := m) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) ≤
      R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) * ((1 + R) ^ M * (2 ^ M * S)) *
        ((1 + ‖v‖) ^ M)⁻¹ := by
    intro i _
    by_cases hx : x ∈ tsupport (χ : V → ℂ)
    · have hx1 := hxR x hx
      rw [iteratedFDeriv_comp_add_right]
      have hj : (1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤ 2 ^ M * S :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, m)) le_rfl (Nat.sub_le _ _) h (x + v)
      have hv : 1 + ‖v‖ ≤ (1 + R) * (1 + ‖x + v‖) := by
        have : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
          calc ‖v‖ = ‖(x + v) - x‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        nlinarith [norm_nonneg (x + v)]
      have hD : ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤
          (1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hvpos]
        calc ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * (1 + ‖v‖) ^ M
            ≤ ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * ((1 + R) * (1 + ‖x + v‖)) ^ M := by gcongr
          _ = (1 + R) ^ M * ((1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖) := by
            rw [mul_pow]; ring
          _ ≤ (1 + R) ^ M * (2 ^ M * S) := by gcongr
      have hχi : ‖iteratedFDeriv ℝ i χ x‖ ≤ SchwartzMap.seminorm ℂ 0 i χ :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ i x
      calc ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (m - i) h (x + v)‖)
          ≤ R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ *
            ((1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹)) := by gcongr
        _ = _ := by ring
    · have h0 : iteratedFDeriv ℝ i χ x = 0 := by
        by_contra hne
        exact hx (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
      rw [h0, norm_zero, mul_zero, zero_mul, mul_zero]
      positivity
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => χ y * h (y + v)) x‖
      ≤ ‖x‖ ^ l * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) *
          ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := Finset.sum_le_sum hterm
    _ = R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]

theorem decay : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  intro V _ _ _ _ _ μ _ T hinv χ ψ h hχ M
  have hp : Continuous ((SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ 𝓢(V, ℂ)).comp
      (T : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))) :=
    ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, 0)).comp T.continuous
  obtain ⟨s, C0, -, hC0⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) _ hp
  have hA : ∀ i : ℕ × ℕ, ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ i.1 i.2 k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ :=
    fun i => seminorm_mul_shift_le χ h hχ i.1 i.2 M
  choose Cf hCf using hA
  set Cs := ∑ i ∈ s, |Cf i|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set I := ∫ x, ‖T ψ x‖ ∂μ
  have hint : Integrable (fun x => ‖T ψ x‖) μ := (SchwartzMap.integrable (T ψ)).norm
  refine ⟨(C0 : ℝ) * Cs * I, fun v k ψv hk hψv => ?_⟩
  set k' := SchwartzMap.compSubConstCLM ℂ (-v) k
  have hk' : ∀ x, k' x = k (x + v) := by
    intro x; simp [k', SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have hk'' : ∀ x, k' x = χ x * h (x + v) := by intro x; rw [hk', hk]; simp
  have hψ : ∀ x, ψ x = ψv (x + v) := by intro x; rw [hψv]; simp
  rw [← hinv v k k' ψv ψ hk' hψ]
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    calc schwartzSeminormFamily ℂ V ℂ i k' ≤ Cf i * ((1 + ‖v‖) ^ M)⁻¹ := hCf i v k' hk''
      _ ≤ |Cf i| * ((1 + ‖v‖) ^ M)⁻¹ := by gcongr; exact le_abs_self _
      _ ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
        gcongr
        exact Finset.single_le_sum (f := fun i => |Cf i|) (fun i _ => abs_nonneg _) hi
  have hTk : ∀ x, ‖T k' x‖ ≤ (C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹) := by
    intro x
    have h2 := hC0 k'
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
    calc ‖T k' x‖ ≤ SchwartzMap.seminorm ℂ 0 0 (T k') := SchwartzMap.norm_le_seminorm ℂ _ x
      _ ≤ (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' := h2
      _ ≤ _ := by gcongr
  calc ‖∫ x, T k' x * starRingEnd ℂ (T ψ x) ∂μ‖
      ≤ ∫ x, ((C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹)) * ‖T ψ x‖ ∂μ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun x => ?_)
        rw [norm_mul, RCLike.norm_conj]
        gcongr
        exact hTk x
    _ = (C0 : ℝ) * Cs * I * ((1 + ‖v‖) ^ M)⁻¹ := by rw [integral_const_mul]; ring

end GlobalTheory.TransDecay
