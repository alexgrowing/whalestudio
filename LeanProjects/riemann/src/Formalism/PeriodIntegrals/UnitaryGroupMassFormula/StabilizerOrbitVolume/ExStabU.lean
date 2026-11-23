import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExStabTop

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal NNReal Pointwise

section AbstractU

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by
  have hc : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
    continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
  exact (hf.comp hc.measurable).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using this

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) ∘ Quotient.mk'') =
      fun g => ∫⁻ h, f (g * (h : G)) ∂ν := by
    funext g
    exact avg_out H ν f g
  rw [this]
  exact meas_avg H ν hf

theorem meas_smul_q (H : Subgroup G) (g : G) : Measurable (fun q : G ⧸ H => g • q) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => g • q) ∘ Quotient.mk'') = (QuotientGroup.mk : G → G ⧸ H) ∘ (g * ·) := by
    funext k
    rfl
  rw [this]
  exact measurable_quotient_mk''.comp (measurable_const_mul g)

theorem induced_eq (H : Subgroup G) (hcl : IsClosed (H : Set G)) (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] (ρ' : Measure (G ⧸ H))
    (hinv : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s)
    (hfin : ∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) (hne : ρ' ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ q, ∫⁻ h, f (q.out * (h : G)) ∂ν ∂ρ' := by
  classical
  have : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite ν := inferInstance
  have hmulc : ∀ x : G, Measurable (fun h : H => x * (h : G)) := fun x =>
    (continuous_const.mul continuous_subtype_val).measurable
  set κ : G ⧸ H → Measure G := fun q => ν.map (fun h : H => q.out * (h : G)) with hκdef
  have hκA : ∀ (q : G ⧸ H) (A : Set G), MeasurableSet A →
      κ q A = ∫⁻ h, A.indicator 1 (q.out * (h : G)) ∂ν := by
    intro q A hA
    rw [← lintegral_indicator_one hA, hκdef]
    exact lintegral_map (measurable_one.indicator hA) (hmulc _)
  have hκ : Measurable κ := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have e : (fun q => κ q A) = fun q : G ⧸ H => ∫⁻ h, A.indicator 1 (q.out * (h : G)) ∂ν :=
      funext fun q => hκA q A hA
    rw [e]
    exact meas_avg_q H ν (measurable_one.indicator hA)
  set m : Measure G := ρ'.bind κ with hmdef
  have hmf : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂m = ∫⁻ q, ∫⁻ h, f (q.out * (h : G)) ∂ν ∂ρ' := by
    intro f hf
    rw [hmdef, Measure.lintegral_bind hκ.aemeasurable hf.aemeasurable]
    apply lintegral_congr
    intro q
    exact lintegral_map hf (hmulc _)
  have hρmap : ∀ g : G, ρ'.map (fun q => g • q) = ρ' := by
    intro g
    ext s hs
    rw [Measure.map_apply (meas_smul_q H g) hs]
    exact hinv g s hs
  have hmA : ∀ A : Set G, MeasurableSet A →
      m A = ∫⁻ q, ∫⁻ h, A.indicator 1 (q.out * (h : G)) ∂ν ∂ρ' := by
    intro A hA
    rw [← lintegral_indicator_one hA]
    exact hmf _ (measurable_one.indicator hA)
  have hleft : m.IsMulLeftInvariant := by
    constructor
    intro g
    ext A hA
    rw [Measure.map_apply (measurable_const_mul g) hA, hmA _ (hA.preimage (measurable_const_mul g)),
      hmA A hA]
    have e : ∀ q : G ⧸ H, ∫⁻ h, ((fun x => g * x) ⁻¹' A).indicator 1 (q.out * (h : G)) ∂ν =
        (fun q' : G ⧸ H => ∫⁻ h, A.indicator 1 (q'.out * (h : G)) ∂ν) (g • q) := by
      intro q
      have h1 : g • q = ((g * q.out : G) : G ⧸ H) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      simp only
      rw [h1, avg_out H ν]
      apply lintegral_congr
      intro h
      simp only [Set.indicator, Set.mem_preimage, mul_assoc, Pi.one_apply]
    simp_rw [e]
    rw [← lintegral_map (meas_avg_q H ν (measurable_one.indicator hA)) (meas_smul_q H g), hρmap]

  have hfinm : IsFiniteMeasureOnCompacts m := by
    constructor
    intro K hK
    set S : Set H := (Subtype.val : H → G) ⁻¹' (K⁻¹ * K) with hSdef
    have hS : IsCompact S :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)
    have hbound : ∀ q : G ⧸ H, κ q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν S) q := by
      intro q
      rw [hκdef, Measure.map_apply (hmulc _) hK.isClosed.measurableSet]
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul H k
        rw [hh0]
        calc ν ((fun h : H => k * h0 * (h : G)) ⁻¹' K) ≤ ν ((fun h : H => h0 * h) ⁻¹' S) := by
              apply measure_mono
              intro h hh
              have hh' : k * (h0 : G) * (h : G) ∈ K := hh
              show ((h0 * h : H) : G) ∈ K⁻¹ * K
              rw [Subgroup.coe_mul]
              exact ⟨k⁻¹, Set.inv_mem_inv.2 hk, k * h0 * h, hh', by group⟩
          _ = ν S := measure_preimage_mul ν h0 S
      · rw [Set.indicator_of_notMem hq]
        apply le_of_eq
        apply measure_mono_null _ (measure_empty (μ := ν))
        intro h hh
        exfalso
        apply hq
        refine ⟨q.out * h, hh, ?_⟩
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rw [QuotientGroup.eq]
        simp
    rw [hmdef, Measure.bind_apply hK.isClosed.measurableSet hκ.aemeasurable]
    calc ∫⁻ q, κ q K ∂ρ' ≤ ∫⁻ q, ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
          (fun _ => ν S) q ∂ρ' := lintegral_mono hbound
      _ ≤ ν S * ρ' ((QuotientGroup.mk : G → G ⧸ H) '' K) := lintegral_indicator_const_le _ _
      _ < ⊤ := ENNReal.mul_lt_top hS.measure_lt_top
          (hfin _ (hK.image QuotientGroup.continuous_mk))
  have hm : m = Measure.haarScalarFactor m μ • μ := Measure.isMulLeftInvariant_eq_smul m μ
  set c : ℝ≥0 := Measure.haarScalarFactor m μ with hcdef
  have hmne : m ≠ 0 := by
    intro h0
    have hu := hmA Set.univ MeasurableSet.univ
    simp only [Set.indicator_univ, Pi.one_apply, lintegral_const, one_mul, lintegral_one] at hu
    rw [h0, Measure.coe_zero, Pi.zero_apply] at hu
    have hν : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν Set.univ_nonempty
    have hρ : ρ' Set.univ ≠ 0 := by
      intro h; exact hne (Measure.measure_univ_eq_zero.1 h)
    exact mul_ne_zero hν hρ hu.symm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    apply hmne
    rw [hm]
    ext s _
    simp [← hcdef, ENNReal.coe_eq_zero.1 h0]
  have hctop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  refine ⟨(c : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.2 hctop, ENNReal.inv_ne_top.2 hc0, fun f hf => ?_⟩
  rw [← hmf f hf, hm]
  rw [show (c • μ : Measure G) = (c : ℝ≥0∞) • μ from rfl, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]

end AbstractU

section OrbitU

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem weil_orbit_u (x0 : X) (hcl : IsClosed (MulAction.stabilizer G x0 : Set G))
    (μ : Measure G) [μ.IsHaarMeasure]
    (νX : Measure X) (hnull : νX {y | ¬ ∃ g : G, g • x0 = y} = 0)
    (hinv : ∀ (g : G) (s : Set X), MeasurableSet s → νX ((fun y => g • y) ⁻¹' s) = νX s)
    (hfin : ∀ K : Set X, IsCompact K → νX K < ⊤) (hne : νX ≠ 0)
    (hemb : MeasurableEmbedding (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0))
    (hcont : Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0)) :
    ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧
      ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) →
        ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂νX := by
  classical
  have : LocallyCompactSpace (MulAction.stabilizer G x0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set ι : G ⧸ MulAction.stabilizer G x0 → X := fun q => q.out • x0 with hιdef
  have hrange : ∀ y, y ∈ Set.range ι ↔ ∃ g : G, g • x0 = y := by
    intro y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.out, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ MulAction.stabilizer G x0), orb_mk x0 g⟩
  set ρ' : Measure (G ⧸ MulAction.stabilizer G x0) := νX.comap ι with hρ'def
  have hmap : ρ'.map ι = νX := by
    rw [hρ'def, hemb.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    convert hnull using 2
    ext y
    simp only [Set.mem_ofPred_eq, hrange]
  have hρ'inv : ∀ (g : G) (s : Set (G ⧸ MulAction.stabilizer G x0)), MeasurableSet s →
      ρ' ((fun y => g • y) ⁻¹' s) = ρ' s := by
    intro g s hs
    rw [hρ'def, hemb.comap_apply, hemb.comap_apply]
    have himg : ι '' ((fun y => g • y) ⁻¹' s) = (fun y => g • y) ⁻¹' (ι '' s) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, orb_smul x0 g q⟩
      · rintro ⟨q', hq', hy⟩
        refine ⟨g⁻¹ • q', by simpa [smul_smul] using hq', ?_⟩
        show (g⁻¹ • q').out • x0 = y
        rw [orb_smul x0 g⁻¹ q']
        show g⁻¹ • ι q' = y
        rw [hy, inv_smul_smul]
    rw [himg]
    exact hinv g _ (hemb.measurableSet_image.2 hs)
  have hρ'fin : ∀ K : Set (G ⧸ MulAction.stabilizer G x0), IsCompact K → ρ' K < ⊤ := by
    intro K hK
    rw [hρ'def, hemb.comap_apply]
    exact hfin _ (hK.image hcont)
  have hρ'ne : ρ' ≠ 0 := by
    intro h0
    apply hne
    rw [← hmap, h0, Measure.map_zero]
  set ν : Measure (MulAction.stabilizer G x0) := Measure.haar with hνdef
  obtain ⟨c, hc0, hctop, hF⟩ := induced_eq (MulAction.stabilizer G x0) hcl μ ν ρ' hρ'inv hρ'fin hρ'ne
  refine ⟨c • ν, Measure.IsHaarMeasure.smul ν hc0 hctop, ?_⟩
  intro f hf s hs
  rw [hF f hf]
  have hin : ∀ q : G ⧸ MulAction.stabilizer G x0, ∫⁻ h', f (s (ι q) * (h' : G)) ∂(c • ν) =
      c * ∫⁻ h, f (q.out * (h : G)) ∂ν := by
    intro q
    rw [lintegral_smul_measure, smul_eq_mul]
    congr 1
    have hsq : s (ι q) • x0 = q.out • x0 := hs (ι q) ⟨q.out, rfl⟩
    have hk : q.out⁻¹ * s (ι q) ∈ MulAction.stabilizer G x0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hsq, inv_smul_smul]
    have hsk : s (ι q) = q.out * (q.out⁻¹ * s (ι q)) := by group
    rw [hsk]
    have := lintegral_mul_left_eq_self (μ := ν)
      (fun h : MulAction.stabilizer G x0 => f (q.out * (h : G))) ⟨q.out⁻¹ * s (ι q), hk⟩
    simpa [mul_assoc] using this
  rw [← hmap, hemb.lintegral_map]
  simp_rw [hin]
  rw [lintegral_const_mul' _ _ hctop]

end OrbitU

theorem exStab_of_U (hW : SecCtblW) (hP : LCSCPolish) (hO : OrbTup) (hI : NuInv) (hF : NuFin)
    (hN : NuNeZero) : ExStab := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secCtblG_of hW F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : T2Space (HA (AF F) σ J) := inferInstanceAs (T2Space (HR (AF F) σ J))
  have : μ.IsHaarMeasure := hμ
  have hnull : νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0 := by
    apply measure_mono_null _ hν.1
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    intro hg
    exact hy (hO F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet y hg)
  obtain ⟨hemb, hcont⟩ := orbEmb_of hW hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨μ', h1, h2⟩ := weil_orbit_u (G := HA (AF F) σ J) (ratTup (AF F) X0)
    (stabClosed_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet) μ νX hnull
    (hI F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hF F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν)
    (hN F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν) hemb hcont
  exact ⟨μ', h1, hnull, fun f hf s hs => h2 f hf s hs⟩

end PI.VolStabSW
