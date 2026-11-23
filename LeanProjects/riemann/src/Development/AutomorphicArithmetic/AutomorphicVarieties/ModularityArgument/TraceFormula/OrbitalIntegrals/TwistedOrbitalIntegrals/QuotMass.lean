import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

noncomputable section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal Pointwise

namespace UpperTheory.V.Z.Tf.Orb

private theorem unfold_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μ : Measure H} [SFinite μ] [μ.IsInvInvariant]
    {ψ ρ : G → ℝ≥0∞} (hψ : Measurable ψ) (hρ : IsQuotNormaliser H μ ρ) :
    ∫⁻ g, ρ g * ∫⁻ h : H, ψ ((h : G) * g) ∂μ ∂μG = ∫⁻ g, ψ g ∂μG := by
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have e1 : ∫⁻ g, ρ g * ∫⁻ h : H, ψ ((h : G) * g) ∂μ ∂μG
      = ∫⁻ h : H, ∫⁻ g, ρ g * ψ ((h : G) * g) ∂μG ∂μ := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul]
      exact hψ.comp (measurable_subtype_coe.mul_const g)
    · exact ((hρ.1.comp measurable_snd).mul (hψ.comp hmulH)).aemeasurable
  have e2 : ∀ h : H, ∫⁻ g, ρ g * ψ ((h : G) * g) ∂μG =
      ∫⁻ g, ψ g * ρ (((h⁻¹ : H) : G) * g) ∂μG := by
    intro h
    rw [← lintegral_mul_left_eq_self _ ((h : G)⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [mul_inv_cancel_left, Subgroup.coe_inv, mul_comm]
  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun h : H => ρ ((h : G) * g)), hρ.2 g, mul_one]
    exact hρ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const g)
  · have : Measurable fun p : G × H => ((p.2⁻¹ : H) : G) * p.1 :=
      (measurable_subtype_coe.comp (measurable_snd.inv)).mul measurable_fst
    exact ((hψ.comp measurable_fst).mul (hρ.1.comp this)).aemeasurable

theorem quotMass : QuotMass := by
  intro G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv ρ hρ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SFinite μ := inferInstance
  haveI : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  haveI : μ.IsMulRightInvariant := by
    have h := (inferInstance : μ.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  have key : ∀ C : Set G, IsCompact C →
      IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} ∧
        ∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG ≠ ∞ := by
    intro C hC
    have hcl : IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} := by
      have e : {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} = (H : Set G) * C := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]
      rw [e]
      exact hH.mul_right_of_isCompact hC
    refine ⟨hcl, ?_⟩
    obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
    have hD : IsCompact (V * C) := hV.mul hC
    have hDm : MeasurableSet (V * C) := hD.isClosed.measurableSet
    have hVm : MeasurableSet ((↑) ⁻¹' V : Set H) :=
      measurable_subtype_coe hV.isClosed.measurableSet
    have hm : μ ((↑) ⁻¹' V : Set H) ≠ 0 := by
      refine (Measure.measure_pos_of_mem_nhds μ (x := 1) ?_).ne'
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds hV1
    have hψ : Measurable ((V * C).indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hDm
    have hE := unfold_eq (μG := μG) hψ hρ
    rw [lintegral_indicator_one hDm] at hE
    have hlow : ∀ g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c},
        μ ((↑) ⁻¹' V : Set H) ≤ ∫⁻ h : H, (V * C).indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μ := by
      rintro g ⟨h0, hh0, c, hc, rfl⟩
      have := lintegral_mul_right_eq_self (μ := μ)
        (fun h : H => (V * C).indicator (1 : G → ℝ≥0∞) ((h : G) * c)) ⟨h0, hh0⟩
      simp only [Subgroup.coe_mul, mul_assoc] at this
      rw [this, ← lintegral_indicator_one hVm]
      refine lintegral_mono fun h => ?_
      by_cases hh : h ∈ ((↑) ⁻¹' V : Set H)
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mul_mem_mul (show (h : G) ∈ V from hh) hc)]
        rfl
      · rw [Set.indicator_of_notMem hh]
        exact zero_le
    have hle : (∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG) * μ ((↑) ⁻¹' V : Set H)
        ≤ μG (V * C) := by
      rw [← hE, ← lintegral_mul_const _ hρ.1]
      refine le_trans (setLIntegral_mono' hcl.measurableSet fun g hg => ?_)
        (setLIntegral_le_lintegral _ _)
      exact mul_le_mul_right (hlow g hg) _
    intro htop
    rw [htop, ENNReal.top_mul hm] at hle
    exact hD.measure_lt_top.not_ge hle
  refine ⟨?_, key⟩
  have hloc : ∀ n, ∀ᵐ g ∂μG, g ∈ compactCovering G n → ρ g ≠ ∞ := by
    intro n
    have hC := isCompact_compactCovering G n
    have h1 := ae_lt_top hρ.1 (key _ hC).2
    rw [ae_restrict_iff' (key _ hC).1.measurableSet] at h1
    filter_upwards [h1] with g hg hgC
    exact (hg ⟨1, H.one_mem, g, hgC, (one_mul g).symm⟩).ne
  filter_upwards [ae_all_iff.2 hloc] with g hg
  obtain ⟨n, hn⟩ := exists_mem_compactCovering g
  exact hg n hn

end UpperTheory.V.Z.Tf.Orb
