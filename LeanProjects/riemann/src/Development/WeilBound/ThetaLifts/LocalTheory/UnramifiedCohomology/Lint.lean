import Development.WeilBound.ThetaLifts.SmallCones.UnfAbs

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace PositivityTheory.ThKG.Loc.KInv

open PositivityTheory.ThKCT.Unf

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {T : Type} [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  {μN : Measure N} [SigmaFinite μN] [IsFiniteMeasureOnCompacts μN] {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0}
  (ν : Measure G) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
  (μT : Measure T) [μT.IsHaarMeasure]

include ν μH μT in
theorem lint (h : Par μN nn ι mm χ) (hR : ∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x))
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]
    (hG : ∀ g, ∃ p u t, ∃ k ∈ K, g = nn p * ι u * mm t * k) {f : G → ℝ≥0∞} (hf : Measurable f)
    (hP : ∀ p u t x, f (nn p * ι u * mm t * x) * χ t = f x) (g : G) : ∫⁻ k, f (k.1 * g) ∂μK = ∫⁻ k, f k.1 ∂μK := by
  obtain ⟨c, c0, ct, hc⟩ := haar_eq ν μH μT h hK μK hG
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hCK := hC.mul hK
  have cn := h.cn.measurable
  have ci := h.ci.measurable
  have cm := h.cm.measurable
  set b : G → ℝ≥0∞ := (C * (K : Set G)).indicator 1 with hb
  have mb : Measurable b := measurable_one.indicator hCK.measurableSet
  have bK : ∀ x, ∀ k ∈ K, b (x * k) = b x := fun x k hk => by
    have : x * k ∈ C * (K : Set G) ↔ x ∈ C * (K : Set G) :=
      ⟨fun ⟨y, hy, z, hz, e⟩ => ⟨y, hy, z * k⁻¹, mul_mem hz (inv_mem hk), by
          change y * z = _ at e
          change y * (z * k⁻¹) = _
          rw [← mul_assoc, e, mul_inv_cancel_right]⟩,
        fun ⟨y, hy, z, hz, e⟩ => ⟨y, hy, z * k, mul_mem hz hk, by rw [← e]; exact (mul_assoc _ _ _).symm⟩⟩
    by_cases hx : x ∈ C * (K : Set G)
    · rw [hb, indicator_of_mem hx, indicator_of_mem (this.2 hx)]; rfl
    · rw [hb, indicator_of_notMem hx, indicator_of_notMem (mt this.1 hx)]
  set B : G → ℝ≥0∞ := fun y => ∫⁻ t, ∫⁻ u, ∫⁻ p, b (nn p * ι u * mm t * y) ∂μN ∂μH ∂μT with hB
  have B1 : ∀ y, B y = B 1 := fun y => by
    obtain ⟨p', u', t', k, hk, rfl⟩ := hG y
    have e1 : ∀ t u, ∫⁻ p, b (nn p * ι u * mm t * (nn p' * ι u' * mm t' * k)) ∂μN =
        ∫⁻ p, b (nn p * ι (u * u') * mm (t * t') * 1) ∂μN := fun t u => by
      obtain ⟨L₃, -, -, h3⟩ := h.h3 t
      obtain ⟨L₂, -, h2⟩ := h.h2 u
      obtain ⟨R, hRm, hR'⟩ := hR (L₂ (L₃ p'))
      rw [← hRm.lintegral_comp (f := fun p => b (nn p * ι (u * u') * mm (t * t') * 1)) (by fun_prop)]
      refine lintegral_congr fun p => ?_
      rw [← hR', ← bK (nn p * nn (L₂ (L₃ p')) * ι (u * u') * mm (t * t') * 1) k hk]
      congr 1
      calc nn p * ι u * mm t * (nn p' * ι u' * mm t' * k) = nn p * (ι u * (mm t * nn p')) * (ι u' * mm t' * k) := by group
        _ = nn p * nn (L₂ (L₃ p')) * ι u * (mm t * ι u') * mm t' * k := by
          rw [h3, ← mul_assoc (ι u), h2]; group
        _ = _ := by rw [h.h4, map_mul, map_mul]; group
    simp only [hB, e1]
    rw [← lintegral_mul_right_eq_self (fun t => ∫⁻ u, ∫⁻ p, b (nn p * ι u * mm t * 1) ∂μN ∂μH) t']
    exact lintegral_congr fun t => lintegral_mul_right_eq_self (fun u => ∫⁻ p, b (nn p * ι u * mm (t * t') * 1) ∂μN) u'
  have key : ∀ (f' : G → ℝ≥0∞), Measurable f' → (∀ p u t x, f' (nn p * ι u * mm t * x) * χ t = f' x) → ∀ y,
      c * ∫⁻ x, f' x * b (x * y) ∂ν = (∫⁻ k, f' k.1 ∂μK) * B 1 := fun f' hf' hP' y => by
    rw [hc _ (by fun_prop), ← lintegral_mul_const _ (by fun_prop)]
    refine lintegral_congr fun k => ?_
    rw [← B1 (k.1 * y), hB, ← lintegral_const_mul _ (by
      refine Measurable.lintegral_prod_right' (f := fun z : T × H => ∫⁻ p, b (nn p * ι z.2 * mm z.1 * (k.1 * y)) ∂μN) ?_
      exact Measurable.lintegral_prod_right' (f := fun z : (T × H) × N => b (nn z.2 * ι z.1.2 * mm z.1.1 * (k.1 * y)))
        (by fun_prop))]
    refine lintegral_congr fun t => ?_
    rw [← lintegral_mul_const' _ _ ENNReal.coe_ne_top, ← lintegral_const_mul _ (
      Measurable.lintegral_prod_right' (f := fun z : H × N => b (nn z.2 * ι z.1 * mm t * (k.1 * y))) (by fun_prop))]
    refine lintegral_congr fun u => ?_
    rw [← lintegral_mul_const' _ _ ENNReal.coe_ne_top, ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun p => ?_
    rw [← hP' p u t k.1, mul_assoc _ k.1 y]
    ring
  have Bt : B 1 ≠ ⊤ := by
    have hc' := h.emb.isCompact_preimage hCK
    have hc2 : IsCompact ((fun z : N × H × T => z.1) '' _) := hc'.image continuous_fst
    have hc3 : IsCompact ((fun z : N × H × T => z.2.1) '' _) := hc'.image (by fun_prop)
    have hc4 : IsCompact ((fun z : N × H × T => z.2.2) '' _) := hc'.image (by fun_prop)
    generalize hA : (fun z : N × H × T => z.1) '' _ = A at hc2
    generalize hD : (fun z : N × H × T => z.2.1) '' _ = D at hc3
    generalize hE : (fun z : N × H × T => z.2.2) '' _ = E at hc4
    have le : ∀ t u p, b (nn p * ι u * mm t * 1) ≤ E.indicator 1 t * (D.indicator 1 u * A.indicator 1 p) := fun t u p => by
      rw [mul_one]
      by_cases hm : nn p * ι u * mm t ∈ C * (K : Set G)
      · rw [hb, indicator_of_mem hm, indicator_of_mem (hE ▸ ⟨(p, u, t), hm, rfl⟩), indicator_of_mem (hD ▸ ⟨(p, u, t), hm, rfl⟩),
          indicator_of_mem (hA ▸ ⟨(p, u, t), hm, rfl⟩)]
        simp
      · rw [hb, indicator_of_notMem hm]; exact zero_le
    have i1 : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (S : Set X), ∫⁻ x, S.indicator 1 x ∂μ ≤ μ S := fun μ S =>
      (lintegral_indicator_le _ _).trans (by simp)
    have fin : ∀ {X : Type} (S : Set X) (x : X), S.indicator (1 : X → ℝ≥0∞) x ≠ ⊤ := fun S x =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (indicator_le_self' (fun _ _ => zero_le) x)
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hc4.measure_lt_top.ne (ENNReal.mul_ne_top hc3.measure_lt_top.ne
      hc2.measure_lt_top.ne) : μT E * (μH D * μN A) ≠ ⊤) ?_
    refine (lintegral_mono fun t => (?_ : _ ≤ E.indicator 1 t * (μH D * μN A))).trans ?_
    · refine (lintegral_mono fun u => (?_ : _ ≤ E.indicator 1 t * (D.indicator 1 u * μN A))).trans ?_
      · refine (lintegral_mono (le t u)).trans ?_
        rw [lintegral_const_mul' _ _ (fin _ _), lintegral_const_mul' _ _ (fin _ _)]
        gcongr
        exact i1 _ _
      · rw [lintegral_const_mul' _ _ (fin _ _), lintegral_mul_const' _ _ hc2.measure_lt_top.ne]
        gcongr
        exact i1 _ _
    · rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hc3.measure_lt_top.ne hc2.measure_lt_top.ne)]
      gcongr
      exact i1 _ _
  have B0 : B 1 ≠ 0 := fun h0 => by
    have e := hc b mb
    have z : ∀ k : K, ∫⁻ t, (∫⁻ u, ∫⁻ p, b (nn p * ι u * mm t * k.1) ∂μN ∂μH) * χ t ∂μT = 0 := fun k => by
      have m : Measurable fun t => ∫⁻ u, ∫⁻ p, b (nn p * ι u * mm t * k.1) ∂μN ∂μH := by
        refine Measurable.lintegral_prod_right' (f := fun z : T × H => ∫⁻ p, b (nn p * ι z.2 * mm z.1 * k.1) ∂μN) ?_
        exact Measurable.lintegral_prod_right' (f := fun z : (T × H) × N => b (nn z.2 * ι z.1.2 * mm z.1.1 * k.1)) (by fun_prop)
      have := (lintegral_eq_zero_iff m).1 ((B1 k.1).trans h0)
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [this] with t ht
      rw [ht]; simp
    simp only [z, lintegral_zero, mul_eq_zero, c0, false_or] at e
    rw [hb, lintegral_indicator_one hCK.measurableSet] at e
    exact (Measure.measure_pos_of_mem_nhds ν (Filter.mem_of_superset hC1 fun x hx => (⟨x, hx, 1, one_mem K, mul_one x⟩ : x ∈ C * (K : Set G)))).ne' e
  have e1 := key (fun x => f (x * g)) (by fun_prop) (fun p u t x => by rw [mul_assoc _ x g, hP]) 1
  have e2 := key f hf hP g⁻¹
  rw [← lintegral_mul_right_eq_self _ g] at e2
  simp only [mul_inv_cancel_right, mul_one] at e1 e2
  exact (ENNReal.mul_left_inj B0 Bt).1 (e1.symm.trans e2)

include ν μH μT in
theorem int (h : Par μN nn ι mm χ) (hR : ∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x))
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]
    (hG : ∀ g, ∃ p u t, ∃ k ∈ K, g = nn p * ι u * mm t * k) {f : G → ℂ} (hf : Continuous f)
    (hP : ∀ p u t x, f (nn p * ι u * mm t * x) * ((χ t : ℝ) : ℂ) = f x) (g : G) : ∫ k, f (k.1 * g) ∂μK = ∫ k, f k.1 ∂μK := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have re : ∀ f : G → ℝ, Continuous f → (∀ p u t x, f (nn p * ι u * mm t * x) * (χ t : ℝ) = f x) →
      ∫ k, f (k.1 * g) ∂μK = ∫ k, f k.1 ∂μK := fun f hf hP => by
    have a : ∀ f : G → ℝ, Continuous f → (∀ p u t x, f (nn p * ι u * mm t * x) * (χ t : ℝ) = f x) →
        ∫⁻ k, ENNReal.ofReal (f (k.1 * g)) ∂μK = ∫⁻ k, ENNReal.ofReal (f k.1) ∂μK := fun f hf hP =>
      lint ν μH μT h hR hK μK hG (f := fun x => ENNReal.ofReal (f x)) hf.measurable.ennreal_ofReal (fun p u t x => by
        rw [← hP p u t x, ENNReal.ofReal_mul' (χ t).coe_nonneg]; simp) g
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
        ((by fun_prop : Continuous fun k : K => f (k.1 * g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part
        ((by fun_prop : Continuous fun k : K => f k.1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      a f hf hP, a (fun x => -f x) hf.neg fun p u t x => by rw [neg_mul, hP]]
  have i1 := (by fun_prop : Continuous fun k : K => f (k.1 * g)).integrable_of_hasCompactSupport (μ := μK)
    (HasCompactSupport.of_compactSpace _)
  have i2 := (by fun_prop : Continuous fun k : K => f k.1).integrable_of_hasCompactSupport (μ := μK)
    (HasCompactSupport.of_compactSpace _)
  refine Complex.ext ?_ ?_
  · have := re (fun x => (f x).re) (by fun_prop) fun p u t x => by rw [← hP p u t x]; simp
    exact (Complex.reCLM.integral_comp_comm i1).symm.trans (this.trans (Complex.reCLM.integral_comp_comm i2))
  · have := re (fun x => (f x).im) (by fun_prop) fun p u t x => by rw [← hP p u t x]; simp
    exact (Complex.imCLM.integral_comp_comm i1).symm.trans (this.trans (Complex.imCLM.integral_comp_comm i2))

end PositivityTheory.ThKG.Loc.KInv

end
