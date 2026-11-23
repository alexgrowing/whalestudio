import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace QPK

theorem ennreal_eq_one_of_mul {a b : ℝ≥0∞} (h0 : b ≠ 0) (ht : b ≠ ⊤) (h : a * b = b) : a = 1 := by
  calc a = a * b / b := (ENNReal.mul_div_cancel_right h0 ht).symm
    _ = b / b := by rw [h]
    _ = 1 := ENNReal.div_self h0 ht

theorem ennreal_le_one_of_pow_le {d M : ℝ≥0∞} (hdt : d ≠ ⊤) (hM : M ≠ ⊤)
    (h : ∀ k : ℕ, d ^ k ≤ M) : d ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  lift d to NNReal using hdt
  lift M to NNReal using hM
  have h1 : (1 : NNReal) < d := by exact_mod_cast hlt
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M).exists
  have h2 := h k
  rw [← ENNReal.coe_pow, ENNReal.coe_le_coe] at h2
  exact absurd h2 (not_le.mpr hk)

section
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem measurable_conj (h : G) : Measurable (fun x : G => h * x * h⁻¹) := ((continuous_const.mul continuous_id).mul continuous_const).measurable

theorem conj_comp (g h : G) :
    (fun x : G => g * x * g⁻¹) ∘ (fun x : G => h * x * h⁻¹) = fun x => (g * h) * x * (g * h)⁻¹ := by
  funext x
  simp only [Function.comp_apply, mul_inv_rev]
  group

theorem invOn_map_conj {N : Set G} (hNc : IsClosed N) (h : G)
    (hn1 : ∀ m ∈ N, h * m * h⁻¹ ∈ N) (hn2 : ∀ m ∈ N, h⁻¹ * m * h⁻¹⁻¹ ∈ N)
    {μ : Measure G} (hμ : InvOn μ N) : InvOn (μ.map (fun x => h * x * h⁻¹)) N := by
  obtain ⟨hsf, hne, hc, hinv⟩ := hμ
  haveI := hsf
  have hm : Measurable (fun x : G => h * x * h⁻¹) := measurable_conj h
  have hm' : Measurable (fun x : G => h⁻¹ * x * h⁻¹⁻¹) := measurable_conj h⁻¹
  have hid : (fun x : G => h⁻¹ * x * h⁻¹⁻¹) ∘ (fun x : G => h * x * h⁻¹) = id := by
    rw [conj_comp]
    funext x
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : SigmaFinite ((μ.map (fun x : G => h * x * h⁻¹)).map (fun x : G => h⁻¹ * x * h⁻¹⁻¹)) := by
      rw [Measure.map_map hm' hm, hid, Measure.map_id]
      exact hsf
    exact SigmaFinite.of_map _ hm'.aemeasurable h1
  · exact (Measure.map_ne_zero_iff hm.aemeasurable).mpr hne
  · rw [Measure.map_apply hm hNc.measurableSet.compl]
    refine measure_mono_null ?_ hc
    intro x hx hxN
    exact hx (hn1 x hxN)
  · intro s hs
    have hs' : h⁻¹ * s * h⁻¹⁻¹ ∈ N := hn2 s hs
    have hms : Measurable (fun x : G => s * x) := measurable_const_mul s
    have hms' : Measurable (fun x : G => (h⁻¹ * s * h⁻¹⁻¹) * x) := measurable_const_mul _
    rw [Measure.map_map hms hm]
    have e : (fun x : G => s * x) ∘ (fun x : G => h * x * h⁻¹) =
        (fun x : G => h * x * h⁻¹) ∘ (fun x : G => (h⁻¹ * s * h⁻¹⁻¹) * x) := by
      funext x
      simp only [Function.comp_apply, inv_inv]
      group
    rw [e, ← Measure.map_map hm hms', hinv _ hs']

end

theorem conjugation_invariant_measure : ConjInv := by
  intro G _ _ _ _ _ _ _ _ N H hN hH hGN hGH hnorm μ hμ hfin hpos h hh
  haveI := hfin
  have hinvH : ∀ g ∈ H, g⁻¹ ∈ H := hGH.2.2
  have hinv : ∀ g ∈ H, InvOn (μ.map (fun x => g * x * g⁻¹)) N := fun g hg =>
    invOn_map_conj hN g (hnorm g hg) (hnorm g⁻¹ (hinvH g hg)) hμ
  have hd : ∀ g ∈ H, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (fun x => g * x * g⁻¹) = c • μ :=
    fun g hg => haar_measure_uniqueness G N hN hGN _ _ (hinv g hg) hμ
  choose d hd0 hdt hdmap using hd
  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : G)
  have hAi : μ (interior K0) ≠ 0 :=
    hpos _ isOpen_interior ⟨1, mem_interior_iff_mem_nhds.mpr hK0n, hGN.1⟩
  have hK0pos : μ K0 ≠ 0 := fun h0 => hAi (measure_mono_null interior_subset h0)
  have hK0fin : μ K0 ≠ ⊤ := hK0c.measure_lt_top.ne
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  let Bc : Set G := (fun p : G × G × G => p.1 * p.2.1 * p.2.2) '' (H ×ˢ (K0 ×ˢ H))
  have hBc : IsCompact Bc :=
    (hH.prod (hK0c.prod hH)).image (by fun_prop)
  have hBcfin : μ Bc ≠ ⊤ := hBc.measure_lt_top.ne

  have hle : ∀ g (hg : g ∈ H), d g hg ≤ 1 := by
    intro g hg
    have hpowmem : ∀ k : ℕ, g ^ k ∈ H := by
      intro k
      induction k with
      | zero => simpa using hGH.1
      | succ k ih => rw [pow_succ]; exact hGH.2.1 _ ih _ hg
    have hpow : ∀ k : ℕ, μ.map (fun x => g ^ k * x * (g ^ k)⁻¹) = d g hg ^ k • μ := by
      intro k
      induction k with
      | zero => simp [Measure.map_id']
      | succ k ih =>
        have e := conj_comp g (g ^ k)
        rw [← pow_succ'] at e
        rw [← e, ← Measure.map_map (measurable_conj g) (measurable_conj (g ^ k)), ih, Measure.map_smul,
          hdmap g hg, smul_smul, pow_succ]
    have hbd : ∀ k : ℕ, d g hg ^ k ≤ μ Bc / μ K0 := by
      intro k
      rw [ENNReal.le_div_iff_mul_le (Or.inl hK0pos) (Or.inl hK0fin)]
      have h1 : (μ.map (fun x => g ^ k * x * (g ^ k)⁻¹)) K0 = d g hg ^ k * μ K0 := by
        rw [hpow k]
        rfl
      rw [← h1, Measure.map_apply (measurable_conj _) hK0m]
      apply measure_mono
      intro x hx
      refine ⟨((g ^ k)⁻¹, (g ^ k * x * (g ^ k)⁻¹, g ^ k)), ⟨hinvH _ (hpowmem k), hx, hpowmem k⟩, ?_⟩
      simp only
      group
    exact ennreal_le_one_of_pow_le (hdt g hg) (ENNReal.div_ne_top hBcfin hK0pos) hbd

  have hprod : d h hh * d h⁻¹ (hinvH h hh) = 1 := by
    have e := conj_comp h⁻¹ h
    have e2 : (fun x : G => (h⁻¹ * h) * x * (h⁻¹ * h)⁻¹) = id := by
      funext x
      simp
    rw [e2] at e
    have h1 : μ = (d h⁻¹ (hinvH h hh) * d h hh) • μ := by
      conv_lhs => rw [← Measure.map_id (μ := μ), ← e, ← Measure.map_map (measurable_conj h⁻¹) (measurable_conj h)]
      rw [hdmap h hh, Measure.map_smul, hdmap h⁻¹ (hinvH h hh), smul_smul, mul_comm]
    have h2 := congrArg (fun ν : Measure G => ν K0) h1
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    rw [mul_comm]
    exact ennreal_eq_one_of_mul hK0pos hK0fin h2.symm
  have hone : d h hh = 1 := by
    apply le_antisymm (hle h hh)
    calc (1 : ℝ≥0∞) = d h hh * d h⁻¹ (hinvH h hh) := hprod.symm
      _ ≤ d h hh * 1 := mul_le_mul_of_nonneg_left (hle h⁻¹ (hinvH h hh)) (by simp)
      _ = d h hh := mul_one _
  rw [hdmap h hh, hone, one_smul]

end QPK
