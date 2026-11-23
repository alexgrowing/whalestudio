import Mathlib

namespace CompanionTheory.NFCpt

open MeasureTheory Filter Topology

theorem ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ a, c a ≠ 0 := by
  rw [ae_all_iff]
  intro a
  have h : (volume : Measure (Fin n → ℂ)) {c | c a = 0} = 0 := Measure.pi_hyperplane _ a 0
  rw [ae_iff]
  simpa using h

theorem ae_ne_zero_c : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  simp

theorem tower_integral : ∀ (n : ℕ) (E : (j : ℕ) → (Fin j → ℂ) → ℝ),
    AEStronglyMeasurable (E n) volume → (∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c) →
    (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ a, c a ≠ 0) →
      Integrable (fun t : ℂ => E (j + 1) (Fin.snoc c t)) ∧ ∫ t : ℂ, E (j + 1) (Fin.snoc c t) = E j c) →
    Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0)
  | 0, E, _, _, _ => by
    have e : E 0 = fun _ => E 0 (fun a => a.elim0) := funext fun c => congrArg _ (Subsingleton.elim _ _)
    refine ⟨by rw [e]; exact integrable_const _, ?_⟩
    rw [e, integral_const]
    simp [Measure.real, volume_pi]
  | n + 1, E, hm, h0, hs => by
    let e : (Fin (n + 1) → ℂ) ≃ᵐ (Fin n → ℂ) × ℂ :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last n)).trans MeasurableEquiv.prodComm
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n))
    have he : ∀ q : (Fin n → ℂ) × ℂ, e.symm q = Fin.snoc q.1 q.2 := by
      intro q
      apply e.injective
      rw [e.apply_symm_apply]
      simp [e, MeasurableEquiv.piFinSuccAbove]
      ext <;> rfl
    set G : (Fin n → ℂ) × ℂ → ℝ := fun q => E (n + 1) (Fin.snoc q.1 q.2) with hG
    have hGe : G = E (n + 1) ∘ e.symm := funext fun q => by simp [hG, he]
    have hGm : AEStronglyMeasurable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [hGe]
      exact hm.comp_measurePreserving (hmp.symm e)
    have hGpos : ∀ c : Fin n → ℂ, (∀ a, c a ≠ 0) → ∀ᵐ t : ℂ, 0 ≤ G (c, t) := by
      intro c hc
      filter_upwards [ae_ne_zero_c] with t ht
      refine h0 _ fun a => ?_
      induction a using Fin.lastCases with
      | last => simpa using ht
      | cast i => simpa using hc i
    have hae : (fun c : Fin n → ℂ => ∫ t, G (c, t)) =ᵐ[volume] E n := by
      filter_upwards [ae_coords_ne_zero n] with c hc
      exact (hs n (Nat.lt_succ_self n) c hc).2
    have hmn : AEStronglyMeasurable (E n) volume := hGm.integral_prod_right'.congr hae
    have h0n : ∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c := by
      intro c hc
      rw [← (hs n (Nat.lt_succ_self n) c hc).2]
      exact integral_nonneg_of_ae (hGpos c hc)
    obtain ⟨hI, hV⟩ := tower_integral n E hmn h0n fun j hj => hs j (Nat.lt_succ_of_lt hj)
    have hGI : Integrable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hGm]
      refine ⟨?_, ?_⟩
      · filter_upwards [ae_coords_ne_zero n] with c hc
        exact (hs n (Nat.lt_succ_self n) c hc).1
      · refine hI.congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← (hs n (Nat.lt_succ_self n) c hc).2]
        refine integral_congr_ae ?_
        filter_upwards [hGpos c hc] with t ht
        exact (Real.norm_of_nonneg ht).symm
    refine ⟨?_, ?_⟩
    · have : E (n + 1) = G ∘ e := funext fun c => by simp [hGe]
      rw [this]
      exact (hmp.integrable_comp_emb e.measurableEmbedding).2 hGI
    · have h1 : ∫ c, E (n + 1) c = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
        have := hmp.integral_comp' G
        rw [← show ∫ q, G q = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) from rfl, ← this]
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp [hGe]
      rw [h1, integral_prod G hGI, integral_congr_ae hae, hV]

theorem abs_sub_le_of_sqrt {a b d δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hδ : 0 < δ)
    (h : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt d) : |a - b| ≤ d / δ + δ * (a + b) := by
  set x := Real.sqrt a
  set y := Real.sqrt b
  set z := Real.sqrt d
  have hx : a = x ^ 2 := (Real.sq_sqrt ha).symm
  have hy : b = y ^ 2 := (Real.sq_sqrt hb).symm
  have hz : d = z ^ 2 := (Real.sq_sqrt hd).symm
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have e : |a - b| = |x - y| * (x + y) := by
    rw [hx, hy, show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
  rw [e, hx, hy, hz]
  have h1 : |x - y| * (x + y) ≤ z * (x + y) := mul_le_mul_of_nonneg_right h (add_nonneg hx0 hy0)
  refine h1.trans ?_
  rw [div_add' _ _ _ hδ.ne', le_div_iff₀ hδ]
  nlinarith [sq_nonneg (z - δ * x), sq_nonneg (z - δ * y), sq_nonneg (δ * x), sq_nonneg (δ * y), sq_nonneg z]

theorem integral_eq_of_sqrt_cauchy {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℕ → α → ℝ} {v : α → ℝ}
    {d : ℕ → ℕ → α → ℝ} {a : ℝ} (hq : ∀ n, Integrable (q n) μ) (hq0 : ∀ n x, 0 ≤ q n x)
    (hd : ∀ n m, Integrable (d n m) μ) (hd0 : ∀ n m x, 0 ≤ d n m x)
    (htri : ∀ n m x, |Real.sqrt (q n x) - Real.sqrt (q m x)| ≤ Real.sqrt (d n m x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (v x)))
    (ha : Tendsto (fun n => ∫ x, q n x ∂μ) atTop (𝓝 a))
    (hC : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → ∫ x, d n m x ∂μ ≤ η) :
    Integrable v μ ∧ ∫ x, v x ∂μ = a := by
  have hv : AEStronglyMeasurable v μ := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hq n).1) hlim
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, ∫ x, q n x ∂μ ≤ B := by
    obtain ⟨B, hB⟩ := ha.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hB0 : 0 ≤ B := (integral_nonneg (hq0 0)).trans (hB 0)
  have key : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → ∫⁻ x, ‖q n x - v x‖ₑ ∂μ ≤ ENNReal.ofReal η := by
    intro η hη
    set δ : ℝ := η / (4 * (B + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := hC (δ * (η / 2)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hnm : ∀ m, N ≤ m → ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ ≤ ENNReal.ofReal η := by
      intro m hm
      have hI : Integrable (fun x => d n m x / δ + δ * (q n x + q m x)) μ :=
        ((hd n m).div_const δ).add (((hq n).add (hq m)).const_mul δ)
      have h1 : ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (d n m x / δ + δ * (q n x + q m x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le_of_sqrt (hq0 n x) (hq0 m x) (hd0 n m x) hδ (htri n m x))
      refine h1.trans ?_
      rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => by
        have := hd0 n m x; have := hq0 n x; have := hq0 m x; positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hI2 : Integrable (fun x => δ * (q n x + q m x)) μ := ((hq n).add (hq m)).const_mul δ
      rw [integral_add ((hd n m).div_const δ) hI2, integral_div, integral_const_mul, integral_add (hq n) (hq m)]
      have h2 : (∫ x, d n m x ∂μ) / δ ≤ η / 2 := by
        rw [div_le_iff₀ hδ]; linarith [hN n m hn hm]
      have h3 : δ * (∫ x, q n x ∂μ + ∫ x, q m x ∂μ) ≤ δ * (2 * (B + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith [hB n, hB m]) hδ.le
      have h4 : δ * (2 * (B + 1)) = η / 2 := by rw [hδdef]; field_simp; ring
      linarith
    have hae : ∀ᵐ x ∂μ, ‖q n x - v x‖ₑ = liminf (fun m => ‖q n x - q m x‖ₑ) atTop := by
      filter_upwards [hlim] with x hx
      exact ((continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hx)).liminf_eq.symm
    rw [lintegral_congr_ae hae]
    refine (lintegral_liminf_le' fun m => ((hq n).1.sub (hq m).1).enorm).trans ?_
    calc liminf (fun m => ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ) atTop
        ≤ liminf (fun _ : ℕ => ENNReal.ofReal η) atTop :=
          liminf_le_liminf (eventually_atTop.2 ⟨N, hnm⟩)
      _ = ENNReal.ofReal η := liminf_const _
  have hvi : Integrable v μ := by
    obtain ⟨N, hN⟩ := key 1 one_pos
    have hd₁ : Integrable (fun x => q N x - v x) μ :=
      ⟨(hq N).1.sub hv, (hN N le_rfl).trans_lt ENNReal.ofReal_lt_top⟩
    exact ((hq N).sub hd₁).congr (ae_of_all _ fun x => by simp)
  refine ⟨hvi, tendsto_nhds_unique ?_ ha⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := key (η / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, ← integral_sub (hq n) hvi]
  have h1 := (enorm_integral_le_lintegral_enorm (fun x => q n x - v x)).trans (hN n hn)
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
  linarith

end CompanionTheory.NFCpt
