import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.UnipQuot

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_domain (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ C ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ D := by
  obtain ⟨ψ, hψm, hψi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated G
  have he := measurableEmbedding_embeddingReal (ℕ → Bool)
  set φ : G → ℝ := fun x => embeddingReal (ℕ → Bool) (ψ x) with hφ
  have hφm : Measurable φ := he.measurable.comp hψm
  have hφi : Function.Injective φ := he.injective.comp hψi
  have hCm : MeasurableSet C := hC.measurableSet
  refine ⟨C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}, ?_, Set.inter_subset_left, ?_⟩
  · refine hCm.inter (MeasurableSet.iInter fun γ => ?_)
    have h1 : MeasurableSet {y : G | (γ : G) * y ∈ C} := (measurable_const_mul (γ : G)) hCm
    have h2 : MeasurableSet {y : G | φ y ≤ φ ((γ : G) * y)} :=
      measurableSet_le hφm (hφm.comp (measurable_const_mul (γ : G)))
    have : {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} =
        {y : G | (γ : G) * y ∈ C}ᶜ ∪ {y : G | φ y ≤ φ ((γ : G) * y)} := by
      ext y; simp [imp_iff_not_or]
    rw [this]; exact h1.compl.union h2
  · intro x
    have hK : IsCompact ((fun y => y * x⁻¹) '' C) := hC.image (continuous_mul_const _)
    have hF := hfin _ hK
    obtain ⟨γ₀, hγ₀, hγ₀C⟩ := hcov x
    have hne : ((fun y => y * x⁻¹) '' C ∩ (Γ : Set G)).Nonempty :=
      ⟨γ₀, ⟨γ₀ * x, hγ₀C, by simp⟩, hγ₀⟩
    obtain ⟨γ, ⟨⟨y, hy, hyγ⟩, hγΓ⟩, hmin⟩ := Set.exists_min_image _ (fun g => φ (g * x)) hF hne
    have hγx : γ * x ∈ C := by rw [← hyγ]; simpa using hy
    have hmem : (⟨γ, hγΓ⟩ : Γ) • x ∈
        C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} := by
      refine ⟨hγx, Set.mem_iInter.2 fun δ hδ => ?_⟩
      have hδ' : (δ : G) * (γ * x) ∈ C := hδ
      have := hmin ((δ : G) * γ) ⟨⟨_, hδ', by simp [mul_assoc]⟩, Γ.mul_mem δ.2 hγΓ⟩
      show φ (γ * x) ≤ φ ((δ : G) * (γ * x))
      simpa [mul_assoc] using this
    refine ⟨⟨γ, hγΓ⟩, hmem, fun δ hδ => ?_⟩
    have hδC : (δ : G) * x ∈ C := hδ.1
    have h1 : φ ((δ : G) * x) ≤ φ (γ * x) := by
      have := Set.mem_iInter.1 hδ.2 ⟨γ * (δ : G)⁻¹, Γ.mul_mem hγΓ (Γ.inv_mem δ.2)⟩
      have e : γ * (δ : G)⁻¹ * (δ • x) = γ * x := by
        show γ * (δ : G)⁻¹ * ((δ : G) * x) = γ * x
        simp [mul_assoc]
      simp only [Set.mem_ofPred_eq, e] at this
      exact this hγx
    have h2 : φ (γ * x) ≤ φ ((δ : G) * x) := hmin δ ⟨⟨_, hδC, by simp⟩, δ.2⟩
    exact Subtype.ext (mul_right_cancel (hφi (le_antisymm h1 h2)))

theorem exists_prob [LocallyCompactSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) → ∀ g : G, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  obtain ⟨D, hDm, hDC, hD⟩ := exists_domain Γ hfin C hC hcov
  set μ : Measure G := Measure.haar
  have hfd : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hfd' : ∀ g : G, IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by
      have := hD (x * g)
      simpa [Subgroup.smul_def, mul_assoc] using this
  have h0 : μ D ≠ 0 := hfd.measure_ne_zero (NeZero.ne μ)
  have htop : μ D ≠ ⊤ := ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC)
  have hinv : ∀ g : G, Measure.map (fun y => y * g) μ = μ := by
    intro g
    have : IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ) := ⟨fun K hK => by
      rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet]
      exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩
    have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ
    set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ
    have h1 : Measure.map (fun y => y * g) μ D = μ D := by
      rw [Measure.map_apply (measurable_mul_const g) hDm]
      exact (hfd' g).measure_eq hfd
    rw [h] at h1
    have h2 : (c : ENNReal) = 1 := by
      have : (c : ENNReal) * μ D = 1 * μ D := by simpa using h1
      exact (ENNReal.mul_left_inj h0 htop).1 this
    have h3 : c = 1 := by exact_mod_cast h2
    rw [h, h3, one_smul]
  refine ⟨(μ D)⁻¹ • μ.restrict D, ⟨?_⟩, ?_, ?_⟩
  · simp [ENNReal.inv_mul_cancel h0 htop]
  · have : Cᶜ ∩ D = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => h1 (hDC h2)
    rw [Measure.smul_apply, Measure.restrict_apply hC.measurableSet.compl, this]
    simp
  · intro f hf g
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    have hemb : MeasurableEmbedding (fun y : G => y * g) := measurableEmbedding_mulRight g
    have h1 := hemb.setIntegral_map (μ := μ) f ((fun y => y * g⁻¹) ⁻¹' D)
    have h2 : (fun y : G => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D := by
      ext y; simp
    rw [hinv g, h2] at h1
    rw [← h1]
    exact (hfd' g⁻¹).setIntegral_eq hfd fun γ x => hf γ γ.2 x

theorem exists_prob_subgroup [LocallyCompactSpace G] (N Γ : Subgroup G) (hN : IsClosed (N : Set G))
    [Countable Γ] (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m ∈ N, ∃ γ ∈ Γ, γ ∈ N ∧ γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧ ν (N : Set G)ᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, γ ∈ N → ∀ y, f (γ * y) = f y) →
        ∀ g ∈ N, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  have hce : Topology.IsClosedEmbedding (Subtype.val : N → G) := hN.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace N := hce.locallyCompactSpace
  have : SecondCountableTopology N := hce.isEmbedding.secondCountableTopology
  have hemb : MeasurableEmbedding (Subtype.val : N → G) := hce.measurableEmbedding
  have : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ)) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  obtain ⟨ν, hν, hνC, hνf⟩ := exists_prob (Γ.subgroupOf N) (fun K hK => by
      have := hfin _ (hK.image continuous_subtype_val)
      refine (this.preimage (f := (Subtype.val : N → G)) Subtype.val_injective.injOn).subset ?_
      rintro x ⟨hx, hx'⟩
      exact ⟨⟨x, hx, rfl⟩, hx'⟩)
    (Subtype.val ⁻¹' C) (hce.isCompact_preimage hC) (fun m => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov m m.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  refine ⟨ν.map Subtype.val, Measure.isProbabilityMeasure_map hemb.measurable.aemeasurable, ?_, ?_, ?_⟩
  · rw [hemb.map_apply]; exact hνC
  · rw [hemb.map_apply]
    have : (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · intro f hf g hg
    rw [hemb.integral_map, hemb.integral_map]
    exact hνf (fun y => f y) (fun γ hγ y => hf γ hγ γ.2 y) ⟨g, hg⟩

end General

theorem exists_quot_prob (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧
      ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  obtain ⟨h2, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨⟨N, hN⟩, hcl, -, -, C, hC, hCN, hcov⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  obtain ⟨Γ, hΓ, hΓc, hfin, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  have : BorelSpace I.GA := inferInstance
  have mN : ∀ x, x ∈ N ↔ x ∈ I.NA W := fun x => by rw [← hN]; rfl
  have mΓ : ∀ x, x ∈ Γ ↔ x ∈ I.GFset := fun x => by rw [← hΓ]; rfl
  obtain ⟨ν, hν, hνC, hνN, hf⟩ := exists_prob_subgroup N Γ (hN ▸ hcl) (hΓ ▸ hfin) C hC (fun m hm => by
    obtain ⟨γ, ⟨h1, h1'⟩, h3⟩ := hcov m ((mN m).1 hm)
    exact ⟨γ⁻¹, Γ.inv_mem ((mΓ γ).2 h1), N.inv_mem ((mN γ).2 h1'), h3⟩)
  refine ⟨ν, hν, ⟨inferInstance, IsProbabilityMeasure.ne_zero ν, hN ▸ hνN, ?_⟩, C, hC, hCN, hνC⟩
  intro f hfi g hg
  exact hf f (fun γ h1 h1' y => hfi γ ⟨(mΓ γ).1 h1, (mN γ).1 h1'⟩ y) g ((mN g).2 hg)

end GlobalTheory.UnipQuot
