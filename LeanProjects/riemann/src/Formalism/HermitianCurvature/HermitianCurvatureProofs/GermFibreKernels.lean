import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRealisation

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propG

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure GermBlockL2 {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H) (N : ℂ → ι → ι → ℂ) : Prop where
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ
  memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ
  sup : ∃ B : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ∫ D, ‖U (h, x) D‖ ^ 2 ∂μ ≤ B
  dom : ∀ h ∈ Y, ∃ ab : ℂ → ℝ, MemLp ab 2 μ ∧ ∀ x : ℂ, x ≠ 0 → ∀ᵐ D ∂μ, ‖A (h, x) D‖ ≤ ab D
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D ∂μ, D ∈ K → ‖U (h, x) D - A (h, x) D‖ ≤ C * ‖x‖⁻¹
  lim : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 (N σ h h'))

theorem eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx

theorem eventually_rate_cocompact (σ : ℂ) (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in cocompact ℂ, C * ‖x + σ‖⁻¹ ≤ δ := by
  have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h := h0.eventually_ge_atTop (‖σ‖ + |C| / δ + 1)
  filter_upwards [h] with x hx
  have h1 : |C| / δ + 1 ≤ ‖x + σ‖ := by
    have := norm_sub_norm_le x (-σ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖x + σ‖ := lt_of_lt_of_le (by positivity) h1
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : |C| = δ * (|C| / δ) := by
    first
    | (field_simp; ring)
    | field_simp
  calc C ≤ |C| := le_abs_self C
    _ = δ * (|C| / δ) := h2
    _ ≤ δ * ‖x + σ‖ := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        linarith

theorem integral_sq_sub_le {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).1).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.1).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]

variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

theorem GermBlockL2.tendsto_rem [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ] (hG : GermBlockL2 μ Y U A N)
    {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ τ : ℂ) :
    Tendsto (fun x => ∫ D, ⟪U (h, x + σ) D - A (h, x + σ) D, A (h', x + τ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨B, hB⟩ := hG.sup
  obtain ⟨ab, hab, hdom⟩ := hG.dom h' hh'
  obtain ⟨ab0, hab0, hdom0⟩ := hG.dom h hh
  refine tendsto_integral_inner_germ μ (fun x => fun D => U (h, x + σ) D - A (h, x + σ) D)
    (fun x => A (h', x + τ)) ab hab (2 * B + 2 * ∫ D, ab0 D ^ 2 ∂μ) ?_ ?_ ?_
  · filter_upwards [eventually_ne_cocompact (-σ)] with x hx
    have hx' : x + σ ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
    have hu := hG.memU h hh _ hx'
    have ha := hG.memA h hh _ hx'
    refine ⟨hu.sub ha, ?_⟩
    have h1 := integral_sq_sub_le hu ha hab0 (hdom0 _ hx')
    have hb := hB h hh _ hx'
    beta_reduce
    linarith
  · filter_upwards [eventually_ne_cocompact (-τ)] with x hx
    exact hdom _ (fun h0 => hx (eq_neg_of_add_eq_zero_left h0))
  · intro K hK hK0 δ hδ
    obtain ⟨C, hC⟩ := hG.germ h hh K hK hK0
    filter_upwards [eventually_ne_cocompact (-σ), eventually_rate_cocompact σ C δ hδ] with x hx hr
    have hx' : x + σ ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
    filter_upwards [hC _ hx'] with D hD hDK
    exact (hD hDK).trans hr

theorem GermBlockL2.propG [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ] (hG : GermBlockL2 μ Y U A N) :
    (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) →
      KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A)) ∧
    (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖gramL μ A A (h, x) (h, x)‖ ≤ B') ∧
    ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => gramL μ A A (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (N σ h h')) ∧
      Tendsto (fun x => gramL μ U A (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (N σ h h')) ∧
      Tendsto (fun x => conj (gramL μ U A (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (N σ h h')) := by
  refine ⟨fun Xs hXs => blockPSD_gramL μ Y U A hG.memU hG.memA Xs hXs, ?_, ?_⟩
  · choose! ab hab hdom using hG.dom
    refine ⟨∑ h ∈ Y, ∫ D, ab h D ^ 2 ∂μ, fun h hh x hx => ?_⟩
    have hA := hG.memA h hh x hx
    have i1 : Integrable (fun D => ‖A (h, x) D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hA.1).1 hA
    have i2 : Integrable (fun D => ab h D ^ 2) μ :=
      (memLp_two_iff_integrable_sq (hab h hh).1).1 (hab h hh)
    unfold gramL
    calc ‖∫ D, ⟪A (h, x) D, A (h, x) D⟫_ℂ ∂μ‖ ≤ ∫ D, ‖⟪A (h, x) D, A (h, x) D⟫_ℂ‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = ∫ D, ‖A (h, x) D‖ ^ 2 ∂μ := by
          congr 1
          funext D
          rw [inner_self_eq_norm_sq_to_K]
          simp
      _ ≤ ∫ D, ab h D ^ 2 ∂μ := by
          refine integral_mono_ae i1 i2 ?_
          filter_upwards [hdom h hh x hx] with D hD
          exact pow_le_pow_left₀ (norm_nonneg _) hD 2
      _ ≤ ∑ h ∈ Y, ∫ D, ab h D ^ 2 ∂μ :=
          Finset.single_le_sum (f := fun h => ∫ D, ab h D ^ 2 ∂μ)
            (fun i _ => integral_nonneg fun _ => sq_nonneg _) hh
  · intro h hh h' hh' σ
    refine ⟨hG.lim h hh h' hh' σ, ?_, ?_⟩
    · have h1 := hG.tendsto_rem hh hh' 0 σ
      simp only [add_zero] at h1
      have h2 := h1.add (hG.lim h hh h' hh' σ)
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ne_cocompact 0, eventually_ne_cocompact (-σ)] with x hx hxσ
      have hxσ' : x + σ ≠ 0 := fun h0 => hxσ (eq_neg_of_add_eq_zero_left h0)
      have i1 : Integrable (fun D => ⟪U (h, x) D - A (h, x) D, A (h', x + σ) D⟫_ℂ) μ :=
        integrable_inner_of_memLp ((hG.memU h hh x hx).sub (hG.memA h hh x hx)) (hG.memA h' hh' _ hxσ')
      have ia : Integrable (fun D => ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ) μ :=
        integrable_inner_of_memLp (hG.memA h hh x hx) (hG.memA h' hh' _ hxσ')
      unfold gramL
      rw [← integral_add i1 ia]
      congr 1
      funext D
      rw [inner_sub_left]
      ring
    · have h1 := hG.tendsto_rem hh' hh σ 0
      simp only [add_zero] at h1
      have h1c := (Complex.continuous_conj.tendsto 0).comp h1
      rw [map_zero] at h1c
      have h2 := h1c.add (hG.lim h hh h' hh' σ)
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ne_cocompact 0, eventually_ne_cocompact (-σ)] with x hx hxσ
      have hxσ' : x + σ ≠ 0 := fun h0 => hxσ (eq_neg_of_add_eq_zero_left h0)
      have i1 : Integrable (fun D => ⟪U (h', x + σ) D - A (h', x + σ) D, A (h, x) D⟫_ℂ) μ :=
        integrable_inner_of_memLp ((hG.memU h' hh' _ hxσ').sub (hG.memA h' hh' _ hxσ'))
          (hG.memA h hh x hx)
      have ia : Integrable (fun D => ⟪A (h', x + σ) D, A (h, x) D⟫_ℂ) μ :=
        integrable_inner_of_memLp (hG.memA h' hh' _ hxσ') (hG.memA h hh x hx)
      have hsplit : ∫ D, ⟪U (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ
          = ∫ D, ⟪U (h', x + σ) D - A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ
            + ∫ D, ⟪A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ := by
        rw [← integral_add i1 ia]
        congr 1
        funext D
        rw [inner_sub_left]
        ring
      have hswap : (starRingEnd ℂ) (∫ D, ⟪A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ)
          = ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ := by
        rw [← integral_conj]
        congr 1
        funext D
        exact inner_conj_symm _ _
      show (starRingEnd ℂ) (∫ D, ⟪U (h', x + σ) D - A (h', x + σ) D, A (h, x) D⟫_ℂ ∂μ)
          + ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ = (starRingEnd ℂ) (gramL μ U A (h', x + σ) (h, x))
      unfold gramL
      rw [hsplit, map_add, hswap]

end propG

end

end Formalism.FourierDecayAlt.P.PBK
