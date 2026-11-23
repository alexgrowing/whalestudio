import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.HolDict.ZClosed

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem exists_bound_orbit (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ x : G, ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) ≤ N := by
  classical
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hKK : IsCompact (K * K⁻¹) := hK.mul hK.inv
  have hfin : (((↑) : Γ → G) ⁻¹' (K * K⁻¹)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKK).finite_of_discrete
  refine ⟨hfin.toFinset.card, fun x => ?_⟩
  by_cases h : ∃ γ₀ : Γ, γ₀⁻¹ • x ∈ K
  · obtain ⟨γ₀, h₀⟩ := h
    have hs : ∑' γ : Γ, K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) =
        ∑ γ ∈ hfin.toFinset.image (fun δ => γ₀ * δ⁻¹), K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) := by
      refine tsum_eq_sum fun γ hγ => Set.indicator_of_notMem (fun hx => hγ ?_) _
      refine Finset.mem_image.2 ⟨γ⁻¹ * γ₀, ?_, by group⟩
      rw [Set.Finite.mem_toFinset]
      refine ⟨_, hx, _, Set.inv_mem_inv.2 h₀, ?_⟩
      simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hs]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun γ _ =>
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)) ?_
    simp only [nsmul_eq_mul, mul_one, Nat.cast_le]
    exact Finset.card_image_le
  · push_neg at h
    simp only [Set.indicator_of_notMem (h _), tsum_zero, zero_le]

variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

theorem exists_lintegral_le (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {K : Set G} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      ∫⁻ x in K, f x ∂μ ≤ N * ∫⁻ x in 𝓕, f x ∂μ := by
  obtain ⟨N, hN⟩ := exists_bound_orbit Γ hK
  refine ⟨N, fun f hf hinv => ?_⟩
  have hKm := hK.measurableSet
  rw [← lintegral_indicator hKm, h𝓕.lintegral_eq_tsum', ← lintegral_tsum, ← lintegral_const_mul _ hf]
  · refine lintegral_mono fun x => ?_
    have : ∀ γ : Γ, K.indicator f (γ⁻¹ • x) = K.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • x) * f x := by
      intro γ
      by_cases h : γ⁻¹ • x ∈ K
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
        exact hinv _ (γ⁻¹).2 x
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [this]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_left (hN x) _
  · intro γ
    exact ((hf.indicator hKm).comp (measurable_const_mul ((γ⁻¹ : Γ) : G))).aemeasurable

theorem lintegral_average_le (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] {X : Type} [MeasurableSpace X]
    (m : Measure X) [IsFiniteMeasure m] {j : X → G} (hj : Measurable j) {K Ω : Set G}
    (hΩ : IsCompact Ω) (hm : ∀ᵐ z ∂m, j z ∈ K) {h : G → ℂ} (hh : Continuous h) :
    ∫⁻ g in Ω, ‖∫ z, h (j z * g) ∂m‖ₑ ∂μ ≤ m Set.univ * ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ := by
  have hmeas : Measurable fun p : G × X => ‖h (j p.2 * p.1)‖ₑ :=
    hh.enorm.measurable.comp ((hj.comp measurable_snd).mul measurable_fst)
  calc _ ≤ ∫⁻ g in Ω, ∫⁻ z, ‖h (j z * g)‖ₑ ∂m ∂μ := lintegral_mono fun g => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, ∫⁻ g in Ω, ‖h (j z * g)‖ₑ ∂μ ∂m := lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ _z, ∫⁻ x in K * Ω, ‖h x‖ₑ ∂μ ∂m := by
        refine lintegral_mono_ae (hm.mono fun z hz => ?_)
        have e := (measurePreserving_mul_left μ (j z)).setLIntegral_comp_emb
          (MeasurableEquiv.mulLeft (j z)).measurableEmbedding (fun x => ‖h x‖ₑ) Ω
        refine (le_of_eq e).trans (lintegral_mono_set ?_)
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨_, hz, _, hg, rfl⟩
    _ = _ := by rw [lintegral_const, mul_comm]

theorem average_eq_zero_of_mem_closure [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] [Countable Γ]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Q : Type} [MeasurableSpace Q] {π : G → Q} (hπ : Measurable π)
    (ρ : G → Lp ℂ 2 ((μ.restrict 𝓕).map π) → Lp ℂ 2 ((μ.restrict 𝓕).map π))
    (hρ : ∀ g F, ∀ᵐ x ∂μ, ρ g F (π x) = F (π (x * g)))
    {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]
    {j : X → G} (hj : Continuous j) {s : Set X} (hs : IsCompact s) (hm : ∀ᵐ z ∂m, z ∈ s)
    {φ ψ : G → ℂ} {F₀ F : Lp ℂ 2 ((μ.restrict 𝓕).map π)}
    (hφ : Continuous φ) (hφΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hφ0 : ∀ g, ∫ z, φ (j z * g) ∂m = 0)
    (hF₀ : ∀ᵐ x ∂μ, F₀ (π x) = φ x)
    (hψ : Continuous ψ) (hψΓ : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hF : ∀ᵐ x ∂μ, F (π x) = ψ x)
    (hcl : F ∈ closure (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))))
    (g₀ : G) : ∫ z, ψ (j z * g₀) ∂m = 0 := by
  have hms : m.restrict s = m := Measure.restrict_eq_self_of_ae_mem hm
  have hint : ∀ h : G → ℂ, Continuous h → ∀ g, Integrable (fun z => h (j z * g)) m := by
    intro h hh g
    rw [← hms]
    exact (hh.comp (hj.mul continuous_const)).continuousOn.integrableOn_compact hs
  have hspan : ∀ H ∈ Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀}, ∃ h : G → ℂ, Continuous h ∧
      (∀ γ ∈ Γ, ∀ g, h (γ * g) = h g) ∧ (∀ g, ∫ z, h (j z * g) ∂m = 0) ∧ ∀ᵐ x ∂μ.restrict 𝓕, H (π x) = h x := by
    intro H hH
    induction hH using Submodule.span_induction with
    | mem H hH =>
      obtain ⟨u, rfl⟩ := hH
      refine ⟨fun x => φ (x * u), hφ.comp (continuous_id.mul continuous_const), fun γ hγ g => ?_, fun g => ?_,
        ae_restrict_of_ae ?_⟩
      · simp only [mul_assoc, hφΓ γ hγ]
      · simp only [mul_assoc, hφ0]
      · filter_upwards [hρ u F₀, (measurePreserving_mul_right μ u).quasiMeasurePreserving.ae hF₀] with x h1 h2
        rw [h1, h2]
    | zero =>
      refine ⟨0, continuous_const, fun _ _ _ => rfl, fun g => by simp, ?_⟩
      exact ae_of_ae_map hπ.aemeasurable (Lp.coeFn_zero ℂ 2 _)
    | add H H' _ _ h1 h2 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      obtain ⟨h', hc', hi', h0', ha'⟩ := h2
      refine ⟨h + h', hc.add hc', fun γ hγ g => by simp only [Pi.add_apply, hi γ hγ, hi' γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.add_apply]
        rw [integral_add (hint h hc g) (hint h' hc' g), h0, h0', add_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_add H H'), ha, ha'] with x e1 e2 e3
        rw [e1, Pi.add_apply, Pi.add_apply, e2, e3]
    | smul a H _ h1 =>
      obtain ⟨h, hc, hi, h0, ha⟩ := h1
      refine ⟨a • h, hc.const_smul a, fun γ hγ g => by simp only [Pi.smul_apply, hi γ hγ], fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply]
        rw [integral_smul, h0, smul_zero]
      · filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_smul a H), ha] with x e1 e2
        rw [e1, Pi.smul_apply, Pi.smul_apply, e2]
  obtain ⟨Ω, hΩ, hg₀⟩ := exists_compact_mem_nhds g₀
  have hK : IsCompact (j '' s) := hs.image hj
  obtain ⟨N, hN⟩ := exists_lintegral_le Γ μ h𝓕 (hK.mul hΩ)
  set c : ℝ≥0∞ := m Set.univ * (N * μ 𝓕 ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) with hc
  have hc' : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_)
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hfin
    norm_num
  have hbd : ∀ H ∈ (Submodule.span ℂ {z | ∃ u : G, z = ρ u F₀} : Set (Lp ℂ 2 ((μ.restrict 𝓕).map π))),
      ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ := by
    intro H hH
    obtain ⟨h, hh, hi, h0, ha⟩ := hspan H hH
    have hd : Continuous (ψ - h) := hψ.sub hh
    have e1 : ∀ g, ∫ z, ψ (j z * g) ∂m = ∫ z, (ψ - h) (j z * g) ∂m := by
      intro g
      simp only [Pi.sub_apply]
      rw [integral_sub (hint ψ hψ g) (hint h hh g), h0, sub_zero]
    simp only [e1]
    refine (lintegral_average_le μ m hj.measurable hΩ (K := j '' s)
      (hm.mono fun z hz => Set.mem_image_of_mem j hz) hd).trans ?_
    rw [hc, mul_assoc, mul_assoc]
    refine mul_le_mul_right ((hN _ hd.enorm.measurable fun γ hγ g => ?_).trans (mul_le_mul_right ?_ _)) _
    · simp only [Pi.sub_apply, hψΓ γ hγ, hi γ hγ]
    · rw [← eLpNorm_one_eq_lintegral_enorm]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (q := 2) one_le_two hd.aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ, mul_comm, Lp.enorm_def,
        eLpNorm_map_measure (Lp.aestronglyMeasurable _) hπ.aemeasurable]
      refine le_of_eq (congrArg _ (eLpNorm_congr_ae ?_))
      filter_upwards [ae_of_ae_map hπ.aemeasurable (Lp.coeFn_sub F H), ha, ae_restrict_of_ae hF] with x e1 e2 e3
      rw [Function.comp_apply, e1, Pi.sub_apply, Pi.sub_apply, e2, e3]
  have hz : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ = 0 := by
    have hcont : Continuous fun H : Lp ℂ 2 ((μ.restrict 𝓕).map π) => c * ‖F - H‖ₑ :=
      (ENNReal.continuous_const_mul hc').comp (continuous_const.sub continuous_id).enorm
    have : ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - F‖ₑ :=
      closure_minimal (t := {H | ∫⁻ g in Ω, ‖∫ z, ψ (j z * g) ∂m‖ₑ ∂μ ≤ c * ‖F - H‖ₑ}) hbd
        (isClosed_le continuous_const hcont) hcl
    simpa using this
  have hC : Continuous fun g => ∫ z, ψ (j z * g) ∂m := by
    have := continuous_parametric_integral_of_continuous (μ := m) (f := fun g z => ψ (j z * g))
      (hψ.comp ((hj.comp continuous_snd).mul continuous_fst)) hs
    rwa [hms] at this
  rw [lintegral_eq_zero_iff hC.enorm.measurable] at hz
  have hz' : (fun g => ∫ z, ψ (j z * g) ∂m) =ᵐ[μ.restrict (interior Ω)] fun _ => 0 := by
    refine ae_restrict_of_ae_restrict_of_subset interior_subset (hz.mono fun g hg => ?_)
    simpa using hg
  exact Measure.eqOn_open_of_ae_eq hz' isOpen_interior hC.continuousOn continuousOn_const
    (mem_interior_iff_mem_nhds.2 hg₀)

end Abstract

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zcusp_of_mem_closure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (φ ψ : GA D V → ℂ) F₀ F, IsAutFun V φ → ZCusp V φ → Repr V μ 𝓕 F₀ φ → IsAutFun V ψ → Repr V μ 𝓕 F ψ → F ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕))) → ZCusp V ψ := by
  intro D θ V hθ μ 𝓕 ρ hP hρ φ ψ F₀ F hφ hφ0 hF₀ hψ hF hcl ξ hξ ν 𝓖 hν h𝓖 g
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨ν₀, 𝓖₀, hν₀, h𝓖₀, hc⟩ := (GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ).1
  have hZ : IsClosed (ZI V ξ : Set (GA D V)) := (GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ).2.1
  haveI : LocallyCompactSpace (ZI V ξ) := hZ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun x : (GQ V).subgroupOf (ZI V ξ) => (⟨x.1.1, x.2⟩ : GQ V))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : GQ V => (t : GA D V)) h))
  haveI : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology (ZI V ξ : Set (GA D V))
  have h₁ : IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓖₀ ν :=
    h𝓖₀.mono (Measure.absolutelyContinuous_isHaarMeasure ν ν₀)
  haveI := hP.haar
  haveI := hP.right
  haveI : IsFiniteMeasure (ν.restrict 𝓖₀) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hc.measure_lt_top).ne
  rw [h𝓖.setIntegral_eq h₁ (f := fun z : ZI V ξ => ψ ((z : GA D V) * g)) fun γ z => by
    have := hψ.left γ.1.1 γ.2 (z.1 * g)
    rw [← mul_assoc] at this
    exact this]
  exact average_eq_zero_of_mem_closure (GQ V) μ hP.fd hP.fin (π := autMk V) measurable_quotient_mk'' (fun u H => ρ u H)
    hρ.val (ν.restrict 𝓖₀) continuous_subtype_val hc
    ((ae_restrict_mem₀ h₁.nullMeasurableSet).mono fun z hz => subset_closure hz)
    hφ.cont hφ.left (hφ0 ξ hξ ν 𝓖₀ hν h₁) hF₀ hψ.cont hψ.left hF hcl g

end GlobalTheory.HolDict.ZClosed
