import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotDiscrete

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have h1 : μ.inv = Measure.haarScalarFactor μ.inv μ • μ :=
    Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ with hc
  have h2 : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [← h1]
      _ = c • μ.inv := by
          ext s _
          simp [Measure.inv_apply]
      _ = (c * c) • μ := by rw [h1, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K < ∞ := hK.measure_lt_top
  have h3 : ((c * c : NNReal) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [h2]
    rfl
  have h4 : ((c * c : NNReal) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h3
  have h5 : ((c : ℝ) * c) = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  exact ⟨by rw [h1, h6, one_smul]⟩

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf {G : Type} [Group G] {Γ H : Subgroup G} (hΓ : Γ ≤ H) {F : Set G}
    (hF : ∀ x : G, ∃! γ : Γ, γ • x ∈ F) (g : G) (h : H) :
    ∃! γ : Γ.subgroupOf H, γ • h ∈ {h : H | (h : G) * g ∈ F} := by
  obtain ⟨γ, hγ, huniq⟩ := hF (h * g)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hγ ⊢
    simpa [mul_assoc] using hγ
  · intro δ hδ
    have hδ' : (⟨((δ : H) : G), Subgroup.mem_subgroupOf.1 δ.2⟩ : Γ) • ((h : G) * g) ∈ F := by
      simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at hδ ⊢
      simpa [mul_assoc] using hδ
    have := huniq _ hδ'
    have h2 : ((δ : H) : G) = (γ : G) := congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h2)

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.QuotDiscrete.discreteClause : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.DiscreteClause
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ hH hG hHu dg _ ν _ μ hμ hQ Γ hΓ hd
  haveI : Countable Γ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  haveI : Countable (Γ.subgroupOf H) :=
    Countable.of_equiv _ (Subgroup.subgroupOfEquivOfLe hΓ).toEquiv.symm
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ν.IsMulRightInvariant := hHu ν inferInstance
  haveI : ν.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν
  haveI : dg.IsMulRightInvariant := hG dg inferInstance
  haveI : dg.IsInvInvariant := _root_.GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant dg
  obtain ⟨F, hFm, hF⟩ := _root_.GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hFg : ∀ g : G, MeasurableSet {h : H | (h : G) * g ∈ F} := fun g =>
    hFm.preimage (measurable_subtype_coe.mul_const g)
  have hFD : IsFundamentalDomain Γ F dg := IsFundamentalDomain.mk' hFm.nullMeasurableSet hF
  have hFD' : ∀ g : G, IsFundamentalDomain (Γ.subgroupOf H) {h : H | (h : G) * g ∈ F} ν :=
    fun g => IsFundamentalDomain.mk' (hFg g).nullMeasurableSet
      (_root_.GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓ hF g)
  refine ⟨⟨F, hFm, hFD⟩, ⟨_, hFg 1, hFD' 1⟩, ?_⟩
  intro D D' hD hD' f hf hinv
  have hFi : Measurable (F.indicator f) := hf.indicator hFm
  have hK : Measurable (fun x : G => F.indicator f x⁻¹) := hFi.comp measurable_inv
  obtain ⟨hcm, hcint⟩ := hQ _ hK
  have he : Continuous (QuotientGroup.quotientRightRelEquivQuotientLeftRel H) := by
    refine (Topology.IsQuotientMap.continuous_iff isQuotientMap_quotient_mk').2 ?_
    have hc : Continuous fun g : G => ((g⁻¹ : G) : G ⧸ H) :=
      continuous_quotient_mk'.comp continuous_inv
    exact hc
  refine ⟨fun q => _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q), hcm.comp he.measurable, ?_, ?_⟩
  · intro g
    show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) ((g⁻¹ : G) : G ⧸ H) = _
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk]
    calc ∫⁻ h : H, F.indicator f (g⁻¹ * (h : G))⁻¹ ∂ν = ∫⁻ h : H, F.indicator f ((h : G) * g) ∂ν := by
          rw [← lintegral_inv_eq_self (μ := ν) (fun h : H => F.indicator f ((h : G) * g))]
          congr 1
          funext h
          simp [mul_inv_rev]
      _ = ∫⁻ h in {h : H | (h : G) * g ∈ F}, f ((h : G) * g) ∂ν := by
          rw [← lintegral_indicator (hFg g)]
          congr 1
      _ = ∫⁻ h in D', f ((h : G) * g) ∂ν := by
          refine (hFD' g).setLIntegral_eq hD' (fun h : H => f ((h : G) * g)) (fun γ h => ?_)
          simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
          exact hinv _ (Subgroup.mem_subgroupOf.1 γ.2) _
  · unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.rightMeasure
    calc ∫⁻ x in D, f x ∂dg = ∫⁻ x in F, f x ∂dg :=
          hD.setLIntegral_eq hFD f (fun γ x => hinv _ γ.2 x)
      _ = ∫⁻ x, F.indicator f x ∂dg := (lintegral_indicator hFm f).symm
      _ = ∫⁻ x, F.indicator f x⁻¹ ∂dg := (lintegral_inv_eq_self (μ := dg) (F.indicator f)).symm
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹) q ∂μ := hcint
      _ = ∫⁻ q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral H ν (fun x : G => F.indicator f x⁻¹)
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q)) ∂μ := by
          congr 1
          funext q
          rw [show _root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.invCoset H q =
            (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm q from rfl,
            Equiv.apply_symm_apply]
      _ = _ := (lintegral_map (hcm.comp he.measurable)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.continuous_invCoset H).measurable).symm

end GlobalTheory.QuotDiscrete
