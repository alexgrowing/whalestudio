import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont

noncomputable section

open MeasureTheory Measure Set
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem invInvariant {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.IsInvInvariant := by
  constructor
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ν.inv = c • ν :=
    ⟨haarScalarFactor ν.inv ν, by
      have := isMulLeftInvariant_eq_smul ν.inv ν
      rwa [ENNReal.smul_def] at this⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have hpos : ν K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hfin : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hsq : ν = (c * c) • ν := by
    conv_lhs => rw [← Measure.inv_inv ν, hc]
    rw [Measure.inv_def (c • ν), Measure.map_smul, ← Measure.inv_def, hc, smul_smul]
  have h1 : c * c = 1 := by
    have : (c * c) * ν K = 1 * ν K := by
      rw [one_mul]; conv_rhs => rw [hsq]
      simp
    exact (ENNReal.mul_left_inj hpos hfin).1 this
  have h2 : c = 1 := by
    rcases lt_trichotomy c 1 with h | h | h
    · exact absurd h1 (ne_of_lt (by
        calc c * c ≤ c * 1 := by gcongr
          _ < 1 := by simpa using h))
    · exact h
    · exact absurd h1 (ne_of_gt (by
        calc 1 < c := h
          _ = 1 * c := by simp
          _ ≤ c * c := by gcongr))
  rw [hc, h2, one_smul]

private theorem unf {G H ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    [Countable ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] (μ : Measure G) (ν : Measure H)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (Γ' : Subgroup G) (Γ : Subgroup H)
    [Countable Γ'] [Countable Γ] (DG : Set G) (DH : Set H) (r : ι → G) (hj : Continuous j)
    (hinj : Function.Injective j) (hDG : IsFundamentalDomain Γ' DG μ) (hDH : IsFundamentalDomain Γ DH ν)
    (hr : ∀ i, r i ∈ Γ') (hjΓ : ∀ δ ∈ Γ, j δ ∈ Γ') (hdec : ∀ γ ∈ Γ', ∃! i, ∃ δ ∈ Γ, γ = r i * j δ)
    (f : G × G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ', ∀ x y, f (γ * x, y) = f (x, y)) :
    ∫⁻ p : G × ι, ∫⁻ g, f (p.1, j g * ((r p.2)⁻¹ * p.1)) ∂ν ∂((μ.restrict DG).prod Measure.count) =
      ∫⁻ y, ∫⁻ g in DH, f (j g * y, y) ∂ν ∂μ := by
  haveI := invInvariant ν
  have hjm : Measurable j := hj.measurable
  have hrm : Measurable r := Measurable.of_discrete
  let e : ι × Γ → Γ' := fun q => ⟨r q.1 * j q.2, Γ'.mul_mem (hr _) (hjΓ _ q.2.2)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨i, δ⟩ ⟨i', δ'⟩ h
      have h' : r i * j δ = r i' * j δ' := congrArg Subtype.val h
      have hi : i = i' := (hdec _ (Γ'.mul_mem (hr i) (hjΓ _ δ.2))).unique ⟨δ, δ.2, rfl⟩ ⟨δ', δ'.2, h'⟩
      subst hi
      have : δ = δ' := Subtype.ext (hinj (mul_left_cancel h'))
      rw [this]
    · rintro ⟨γ, hγ⟩
      obtain ⟨i, ⟨δ, hδ, h⟩, -⟩ := hdec γ hγ
      exact ⟨(i, ⟨δ, hδ⟩), Subtype.ext h.symm⟩

  let K : G → ℝ≥0∞ := fun x => ∫⁻ g in DH, f (x, (j g)⁻¹ * x) ∂ν
  have hK : Measurable K := by
    refine Measurable.lintegral_prod_right' (f := fun q : G × H => f (q.1, (j q.2)⁻¹ * q.1)) ?_
    exact hf.comp (by fun_prop)
  have h1 : ∀ x i, ∫⁻ g, f (x, j g * ((r i)⁻¹ * x)) ∂ν =
      ∑' δ : Γ, ∫⁻ g in DH, f (x, (j g)⁻¹ * (((e (i, δ) : Γ') : G)⁻¹ * x)) ∂ν := by
    intro x i
    rw [← lintegral_inv_eq_self (μ := ν) (fun g => f (x, j g * ((r i)⁻¹ * x))), hDH.lintegral_eq_tsum'']
    refine tsum_congr fun δ => lintegral_congr fun g => ?_
    simp [e, Subgroup.smul_def, mul_assoc]
  have h2 : ∀ x, ∑' i, ∫⁻ g, f (x, j g * ((r i)⁻¹ * x)) ∂ν = ∑' γ : Γ', K ((γ : G)⁻¹ * x) := by
    intro x
    simp_rw [h1]
    rw [← ENNReal.tsum_prod' (f := fun q : ι × Γ => ∫⁻ g in DH, f (x, (j g)⁻¹ * (((e q : Γ') : G)⁻¹ * x)) ∂ν),
      ← (Equiv.ofBijective e he).tsum_eq (fun γ : Γ' => K ((γ : G)⁻¹ * x))]
    refine tsum_congr fun q => lintegral_congr fun g => ?_
    have := hinv _ (Γ'.inv_mem (e q).2) x ((j g)⁻¹ * (((e q : Γ') : G)⁻¹ * x))
    simpa [K] using this.symm
  have hmeasL : Measurable fun q : (G × ι) × H => f (q.1.1, j q.2 * ((r q.1.2)⁻¹ * q.1.1)) :=
    hf.comp (by fun_prop)
  have hmeasR : Measurable fun p : G × ι => ∫⁻ g, f (p.1, j g * ((r p.2)⁻¹ * p.1)) ∂ν :=
    hmeasL.lintegral_prod_right'
  rw [lintegral_prod _ hmeasR.aemeasurable]
  simp_rw [lintegral_count]
  simp_rw [h2]
  rw [lintegral_tsum (f := fun (γ : Γ') x => K ((γ : G)⁻¹ * x))
    fun γ => (hK.comp (measurable_const_mul _)).aemeasurable]
  have h3 : ∫⁻ x, K x ∂μ = ∑' γ : Γ', ∫⁻ x in DG, K ((γ : G)⁻¹ * x) ∂μ := by
    rw [hDG.lintegral_eq_tsum' K]
    refine tsum_congr fun γ => lintegral_congr fun x => ?_
    simp [Subgroup.smul_def]
  rw [← h3]
  have hF : Measurable (Function.uncurry fun (x : G) (g : H) => f (x, (j g)⁻¹ * x)) :=
    hf.comp (by fun_prop)
  have hF' : Measurable (Function.uncurry fun (y : G) (g : H) => f (j g * y, y)) :=
    hf.comp (by fun_prop)
  rw [show ∫⁻ x, K x ∂μ = ∫⁻ g in DH, ∫⁻ x, f (x, (j g)⁻¹ * x) ∂μ ∂ν from
      lintegral_lintegral_swap hF.aemeasurable,
    lintegral_lintegral_swap hF'.aemeasurable]
  refine lintegral_congr fun g => ?_
  rw [← lintegral_mul_left_eq_self (fun x => f (x, (j g)⁻¹ * x)) (j g)]
  simp

theorem absUnf : AbsUnf := by
  intro G H ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ _ j Γ' Γ _ _ DG DH r φ c hj hinj hDG hDH hfin hr hjΓ hdec
    hφ hφinv hbd hc hci
  obtain ⟨B₀, hB₀⟩ := hbd
  have hjm : Measurable j := hj.measurable
  have hrm : Measurable r := Measurable.of_discrete
  have U := fun (f : G × G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ', ∀ x y, f (γ * x, y) = f (x, y)) =>
    unf μ ν j Γ' Γ DG DH r hj hinj hDG hDH hr hjΓ hdec f hf hinv
  refine ⟨fun B hB => ?_, ?_⟩
  · have hBe : ∀ x, ‖φ x‖ₑ ≤ ENNReal.ofReal B := fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB x)
    calc ∫⁻ p : G × ι, ‖(∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1‖ₑ ∂((μ.restrict DG).prod Measure.count)
        ≤ ∫⁻ p : G × ι, ∫⁻ g, ‖c (j g * ((r p.2)⁻¹ * p.1)) * φ p.1‖ₑ ∂ν ∂((μ.restrict DG).prod Measure.count) := by
          refine lintegral_mono fun p => ?_
          rw [← integral_mul_const]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ∫⁻ g in DH, ‖c y * φ (j g * y)‖ₑ ∂ν ∂μ :=
          U (fun q => ‖c q.2 * φ q.1‖ₑ) (by fun_prop) (fun γ hγ x y => by simp only [hφinv γ hγ x])
      _ ≤ ∫⁻ y, ∫⁻ g in DH, ‖c y‖ₑ * ENNReal.ofReal B ∂ν ∂μ := by
          refine lintegral_mono fun y => lintegral_mono fun g => ?_
          rw [enorm_mul]
          gcongr
          exact hBe _
      _ = ENNReal.ofReal B * ν DH * ∫⁻ y, ‖c y‖ₑ ∂μ := by
          simp_rw [setLIntegral_const, mul_assoc]
          rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne), mul_comm, mul_assoc]
  · let P₁ : Measure ((G × ι) × H) := ((μ.restrict DG).prod Measure.count).prod ν
    let P₂ : Measure (G × H) := μ.prod (ν.restrict DH)
    let T₁ : (G × ι) × H → ℂ × G := fun q => (φ q.1.1, j q.2 * ((r q.1.2)⁻¹ * q.1.1))
    let T₂ : G × H → ℂ × G := fun q => (φ (j q.2 * q.1), q.1)
    have hT₁ : Measurable T₁ := by fun_prop
    have hT₂ : Measurable T₂ := by fun_prop
    have hmap : P₁.map T₁ = P₂.map T₂ := by
      ext S hS
      rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS, lintegral_map (measurable_one.indicator hS) hT₁,
        lintegral_map (measurable_one.indicator hS) hT₂]
      have hm : Measurable (S.indicator (1 : ℂ × G → ℝ≥0∞)) := measurable_one.indicator hS
      have hu := U (fun q => S.indicator (1 : ℂ × G → ℝ≥0∞) (φ q.1, q.2)) (hm.comp (by fun_prop))
        (fun γ hγ x y => by simp only [hφinv γ hγ x])
      have e₁ : ∫⁻ a, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₁ a) ∂P₁ =
          ∫⁻ p, ∫⁻ g, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₁ (p, g)) ∂ν ∂((μ.restrict DG).prod Measure.count) :=
        lintegral_prod _ (hm.comp hT₁).aemeasurable
      have e₂ : ∫⁻ a, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₂ a) ∂P₂ =
          ∫⁻ y, ∫⁻ g in DH, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₂ (y, g)) ∂ν ∂μ :=
        lintegral_prod _ (hm.comp hT₂).aemeasurable
      rw [e₁, e₂]
      exact hu
    let h : ℂ × G → ℂ := fun w => c w.2 * w.1
    have hh : Measurable h := by fun_prop
    haveI : IsFiniteMeasure (ν.restrict DH) := ⟨by simpa using hfin⟩
    have hI₂ : Integrable (h ∘ T₂) P₂ := by
      refine ((hci.comp_fst (ν.restrict DH)).norm.mul_const B₀).mono' (hh.comp hT₂).aestronglyMeasurable
        (ae_of_all _ fun q => ?_)
      simp only [h, T₂, Function.comp, norm_mul, norm_norm]
      gcongr
      exact hB₀ _
    have hI : Integrable h (P₂.map T₂) :=
      (integrable_map_measure hh.aestronglyMeasurable hT₂.aemeasurable).2 hI₂
    have hI₁ : Integrable (h ∘ T₁) P₁ :=
      (integrable_map_measure hh.aestronglyMeasurable hT₁.aemeasurable).1 (hmap ▸ hI)
    calc ∫ p : G × ι, (∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1 ∂((μ.restrict DG).prod Measure.count)
        = ∫ p : G × ι, ∫ g, (h ∘ T₁) (p, g) ∂ν ∂((μ.restrict DG).prod Measure.count) := by
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          simp only [h, T₁, Function.comp]
          rw [integral_mul_const]
      _ = ∫ q, (h ∘ T₁) q ∂P₁ := (integral_prod _ hI₁).symm
      _ = ∫ w, h w ∂(P₁.map T₁) := (integral_map hT₁.aemeasurable hh.aestronglyMeasurable).symm
      _ = ∫ w, h w ∂(P₂.map T₂) := by rw [hmap]
      _ = ∫ q, (h ∘ T₂) q ∂P₂ := integral_map hT₂.aemeasurable hh.aestronglyMeasurable
      _ = ∫ y, ∫ g in DH, (h ∘ T₂) (y, g) ∂ν ∂μ := integral_prod _ hI₂
      _ = ∫ y, c y * ∫ g in DH, φ (j g * y) ∂ν ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [h, T₂, Function.comp]
          rw [integral_const_mul]

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
