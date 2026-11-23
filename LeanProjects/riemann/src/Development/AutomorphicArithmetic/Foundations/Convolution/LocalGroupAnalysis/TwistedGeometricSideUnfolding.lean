import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.TraceFormulaGeometric
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace PositivityTheory.Rg.Tf.Loc

namespace UpperTheory.ConvolutionTheory.G.UnitaryOne

variable {X : Type} [Group X]

private def twEquiv (Γ : Subgroup X) (θ : X →* X) (hθ : ∀ g ∈ Γ, θ g ∈ Γ) (g : Γ) : Γ ≃ Γ :=
  (Equiv.mulLeft g⁻¹).trans (Equiv.mulRight ⟨θ g, hθ _ g.2⟩)

private theorem twEquiv_apply (Γ : Subgroup X) (θ : X →* X) (hθ : ∀ g ∈ Γ, θ g ∈ Γ) (g δ : Γ) (y : X) :
    y⁻¹ * (twEquiv Γ θ hθ g δ : X) * θ y = ((g : X) * y)⁻¹ * δ * θ ((g : X) * y) := by
  simp [twEquiv, mul_assoc]

private theorem out_mk (H : Subgroup X) (x : X) : ∃ h : H, Quotient.out (mk H x) = (h : X) * x := by
  have : mk H (Quotient.out (mk H x)) = mk H x := Quotient.out_eq _
  obtain ⟨h, hh⟩ := mk_eq_mk_iff.1 this
  exact ⟨h, hh.symm⟩

variable [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem finite_meet (Γ : Subgroup X) [DiscreteTopology Γ] (θ : X →* X) (hc : Continuous θ)
    (f : CompactlySupportedContinuousMap X ℂ) {C : Set X} (hC : IsCompact C) :
    {δ : Γ | ∃ y ∈ C, f (y⁻¹ * δ * θ y) ≠ 0}.Finite := by
  have hK : IsCompact ((fun p : X × X => p.1 * p.2 * (θ p.1)⁻¹) '' (C ×ˢ tsupport f)) :=
    (hC.prod f.hasCompactSupport).image (by fun_prop)
  have ht := Γ.tendsto_coe_cofinite_of_discrete (isDiscrete_iff_discreteTopology.2 ‹_›)
  have hfin := ht hK.compl_mem_cocompact
  rw [mem_map, mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro δ ⟨y, hy, hf⟩
  simp only [mem_compl_iff, mem_preimage, not_not]
  exact ⟨(y, y⁻¹ * δ * θ y), ⟨hy, subset_tsupport _ hf⟩, by simp [mul_assoc]⟩

private theorem tsum_lintegral_ne_top (Γ : Subgroup X) [DiscreteTopology Γ] (μ : Measure X) [μ.IsHaarMeasure]
    (θ : X →* X) (hc : Continuous θ) (hθ : ∀ g ∈ Γ, θ g ∈ Γ)
    (f : CompactlySupportedContinuousMap X ℂ) {C : Set X} (hC : IsCompact C)
    (hsupp : ∀ x, ∀ δ ∈ Γ, f (x⁻¹ * δ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y) :
    ∑' δ : Γ, ∫⁻ x in fundamentalDomain Γ, ‖f (x⁻¹ * δ * θ x)‖ₑ ∂μ ≠ ∞ := by
  classical
  obtain ⟨B, hB⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hS := finite_meet Γ θ hc f hC
  set M : ℝ≥0∞ := ∑ _δ ∈ hS.toFinset, ENNReal.ofReal B with hM
  have hMt : M ≠ ∞ := ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  have hm : MeasurableSet (mk Γ '' C) := (hC.image (continuous_mk Γ)).isClosed.measurableSet
  have hbd : ∀ x, ∑' δ : Γ, ‖f (x⁻¹ * δ * θ x)‖ₑ ≤ (mk Γ ⁻¹' (mk Γ '' C)).indicator (fun _ => M) x := by
    intro x
    by_cases hx : ∃ g ∈ Γ, ∃ y ∈ C, x = g * y
    · obtain ⟨g, hg, y, hy, rfl⟩ := hx
      rw [indicator_of_mem (show g * y ∈ mk Γ ⁻¹' (mk Γ '' C) from ⟨y, hy, (mk_mul_of_mem hg y).symm⟩)]
      have h1 : ∑' δ : Γ, ‖f ((g * y)⁻¹ * δ * θ (g * y))‖ₑ = ∑' δ : Γ, ‖f (y⁻¹ * δ * θ y)‖ₑ := by
        rw [← (twEquiv Γ θ hθ ⟨g, hg⟩).tsum_eq (fun δ : Γ => ‖f (y⁻¹ * δ * θ y)‖ₑ)]
        simp only [twEquiv_apply]
      rw [h1, tsum_eq_sum (s := hS.toFinset)]
      · refine Finset.sum_le_sum fun δ _ => ?_
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hB _)
      · intro δ hδ
        by_contra h0
        exact hδ (hS.mem_toFinset.2 ⟨y, hy, fun h => h0 (by simp [h])⟩)
    · have : ∀ δ : Γ, f (x⁻¹ * δ * θ x) = 0 := fun δ => by
        by_contra h0
        exact hx (hsupp x δ δ.2 h0)
      simp [this]
  rw [← lintegral_tsum fun δ => (Continuous.measurable (by fun_prop)).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hbd)
  rw [lintegral_indicator (measurable_mk Γ hm), setLIntegral_const,
    Measure.restrict_apply (measurable_mk Γ hm),
    ← quotientMeasure_apply μ (isFundamentalDomain_fundamentalDomain Γ μ) hm]
  exact ENNReal.mul_ne_top hMt ((quotientMeasure_mk_image_le μ hm).trans_lt hC.measure_lt_top).ne

omit [LocallyCompactSpace X] [T2Space X] in
private theorem isFund (Γ : Subgroup X) [DiscreteTopology Γ] (μ : Measure X) (θ : X →* X)
    (γ : X) {d : {γ' : Γ // ∃ g ∈ Γ, (γ' : X) = g⁻¹ * γ * θ g} → Γ} (hθ : ∀ g ∈ Γ, θ g ∈ Γ) (hγ : γ ∈ Γ)
    (hd : ∀ i, (d i : X)⁻¹ * γ * θ (d i) = i.1) :
    IsFundamentalDomain ↥(Γ ⊓ twCent θ γ) (⋃ i, ((d i : Γ) : X) • fundamentalDomain Γ) μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine IsFundamentalDomain.mk' (MeasurableSet.iUnion fun i =>
    (measurableSet_fundamentalDomain Γ).const_smul _).nullMeasurableSet fun x => ?_
  obtain ⟨η, hη, -⟩ := existsUnique_smul_mem_fundamentalDomain Γ x
  change (η : X) * x ∈ fundamentalDomain Γ at hη
  set i : {γ' : Γ // ∃ g ∈ Γ, (γ' : X) = g⁻¹ * γ * θ g} :=
    ⟨⟨η * γ * (θ η)⁻¹, Γ.mul_mem (Γ.mul_mem η.2 hγ) (Γ.inv_mem (hθ _ η.2))⟩,
      η⁻¹, Γ.inv_mem η.2, by simp⟩ with hi_def
  have hi : ((d i : X))⁻¹ * γ * θ (d i) = η * γ * (θ η)⁻¹ := hd i
  have hmem : ((d i : X) * η) ∈ Γ ⊓ twCent θ γ := by
    refine ⟨Γ.mul_mem (d i).2 η.2, ?_⟩
    change ((d i : X) * η)⁻¹ * γ * θ ((d i : X) * η) = γ
    calc ((d i : X) * η)⁻¹ * γ * θ ((d i : X) * η)
        = (η : X)⁻¹ * ((d i : X)⁻¹ * γ * θ (d i)) * θ η := by rw [map_mul]; group
      _ = γ := by rw [hi]; group
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · refine mem_iUnion.2 ⟨i, ?_⟩
    rw [mem_smul_set_iff']
    change ((d i : X))⁻¹ * (((d i : X) * η) * x) ∈ _
    convert hη using 1
    group
  · rintro ⟨ε, hε⟩ hεx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hεx
    rw [mem_smul_set_iff'] at hj
    change ((d j : X))⁻¹ * (ε * x) ∈ _ at hj
    have hεΓ : ε ∈ Γ := hε.1
    have hη' : (d j)⁻¹ * (⟨ε, hεΓ⟩ : Γ) = η :=
      eq_of_mul_mem_fundamentalDomain Γ (by push_cast; rw [mul_assoc]; exact hj) hη
    have hε' : ε = (d j : X) * η := by
      have := congrArg Subtype.val hη'
      push_cast at this
      rw [← this]
      group
    have hc : ε⁻¹ * γ * θ ε = γ := hε.2
    rw [hε'] at hc
    have hj1 : ((j.1 : Γ) : X) = (i.1 : X) := by
      rw [← hd j]
      calc ((d j : X))⁻¹ * γ * θ (d j)
          = η * (((d j : X) * η)⁻¹ * γ * θ ((d j : X) * η)) * (θ η)⁻¹ := by rw [map_mul]; group
        _ = η * γ * (θ η)⁻¹ := by rw [hc]
    have hji : j = i := Subtype.ext (Subtype.ext hj1)
    apply Subtype.ext
    change ε = (d i : X) * η
    rw [hε', hji]

private theorem integrable_quot_iff (H : Subgroup X) [DiscreteTopology H] (μ : Measure X)
    (h : RightCosetSpace H → ℂ) :
    Integrable h (quotientMeasure H μ) ↔ IntegrableOn (fun g => h (mk H g)) (fundamentalDomain H) μ := by
  rw [quotientMeasure_eq_map_fundamentalDomainEquiv, integrable_map_equiv,
    integrableOn_iff_comap_subtypeVal (measurableSet_fundamentalDomain H)]
  rfl

private theorem one_class (Γ : Subgroup X) [DiscreteTopology Γ] (μ : Measure X) [μ.IsHaarMeasure]
    (θ : X →* X) (hθ : ∀ g ∈ Γ, θ g ∈ Γ) (f : X → ℂ)
    (hI : ∀ δ : Γ, IntegrableOn (fun x => f (x⁻¹ * δ * θ x)) (fundamentalDomain Γ) μ)
    (hs : Summable fun δ : Γ => ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * δ * θ x)‖ ∂μ)
    (γ : X) (hγ : γ ∈ Γ) [DiscreteTopology ↥(Γ ⊓ twCent θ γ)] :
    HasSum (fun i : {γ' : Γ // ∃ g ∈ Γ, (γ' : X) = g⁻¹ * γ * θ g} =>
        ∫ x in fundamentalDomain Γ, f (x⁻¹ * (i.1 : X) * θ x) ∂μ)
      (∫ y, f ((Quotient.out y)⁻¹ * γ * θ (Quotient.out y)) ∂quotientMeasure (Γ ⊓ twCent θ γ) μ) ∧
    Integrable (fun y => f ((Quotient.out y)⁻¹ * γ * θ (Quotient.out y))) (quotientMeasure (Γ ⊓ twCent θ γ) μ) := by
  classical
  have hd : ∀ i : {γ' : Γ // ∃ g ∈ Γ, (γ' : X) = g⁻¹ * γ * θ g}, ∃ d : Γ,
      (d : X)⁻¹ * γ * θ d = i.1 := fun i => by
    obtain ⟨c, hc, h⟩ := i.2
    exact ⟨⟨c, hc⟩, h.symm⟩
  choose d hd using hd
  set E : {γ' : Γ // ∃ g ∈ Γ, (γ' : X) = g⁻¹ * γ * θ g} → Set X :=
    fun i => ((d i : Γ) : X) • fundamentalDomain Γ with hE
  have hEm : ∀ i, MeasurableSet (E i) := fun i =>
    (measurableSet_fundamentalDomain Γ).const_smul _
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro y hi hj
    rw [hE, mem_smul_set_iff'] at hi hj
    have h := eq_of_mul_mem_fundamentalDomain Γ (η₁ := (d i)⁻¹) (η₂ := (d j)⁻¹)
      (by push_cast; exact hi) (by push_cast; exact hj)
    apply hij
    rw [inv_inj] at h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hd i, ← hd j, h]
  have hconj : ∀ i (x : X),
      ((d i : X) * x)⁻¹ * γ * θ ((d i : X) * x) = x⁻¹ * (i.1 : X) * θ x := by
    intro i x
    rw [← hd i, map_mul]
    group
  have hterm : ∀ i, ∫ x in E i, f (x⁻¹ * γ * θ x) ∂μ =
      ∫ x in fundamentalDomain Γ, f (x⁻¹ * (i.1 : X) * θ x) ∂μ := by
    intro i
    rw [hE]
    dsimp only
    rw [setIntegral_smul_set μ]
    simp_rw [hconj]
  have hnorm : ∀ i, ∫ x in E i, ‖f (x⁻¹ * γ * θ x)‖ ∂μ =
      ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * (i.1 : X) * θ x)‖ ∂μ := by
    intro i
    rw [hE]
    dsimp only
    rw [setIntegral_smul_set μ]
    simp_rw [hconj]
  have hEi : ∀ i, IntegrableOn (fun x => f (x⁻¹ * γ * θ x)) (E i) μ := by
    intro i
    have h := (measurePreserving_mul_left μ (d i : X)).integrableOn_comp_preimage
      (MeasurableEquiv.mulLeft (d i : X)).measurableEmbedding (f := fun x => f (x⁻¹ * γ * θ x)) (s := E i)
    have hpre : (fun x => (d i : X) * x) ⁻¹' (E i) = fundamentalDomain Γ := by
      ext x
      simp [hE, Set.mem_smul_set_iff_inv_smul_mem]
    rw [hpre] at h
    refine h.1 ?_
    simpa only [Function.comp_def, hconj] using hI i.1
  have hint : IntegrableOn (fun x => f (x⁻¹ * γ * θ x)) (⋃ i, E i) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm hEi ?_
    simp_rw [hnorm]
    exact hs.comp_injective Subtype.val_injective
  have h1 := hasSum_integral_iUnion hEm hdisj hint
  simp_rw [hterm] at h1
  have hinv : ∀ (g : ↥(Γ ⊓ twCent θ γ)) (x : X),
      f (((g : X) * x)⁻¹ * γ * θ ((g : X) * x)) = f (x⁻¹ * γ * θ x) := by
    intro g x
    have hc : (g : X)⁻¹ * γ * θ g = γ := g.2.2
    congr 1
    calc ((g : X) * x)⁻¹ * γ * θ ((g : X) * x) = x⁻¹ * ((g : X)⁻¹ * γ * θ g) * θ x := by
          rw [map_mul]; group
      _ = _ := by rw [hc]
  have hout : ∀ x : X, f ((Quotient.out (mk (Γ ⊓ twCent θ γ) x))⁻¹ * γ *
      θ (Quotient.out (mk (Γ ⊓ twCent θ γ) x))) = f (x⁻¹ * γ * θ x) := by
    intro x
    obtain ⟨h, hh⟩ := out_mk (Γ ⊓ twCent θ γ) x
    rw [hh, hinv]
  have hF := isFund Γ μ θ γ hθ hγ hd
  constructor
  · rw [integral_quotientMeasure]
    simp_rw [hout]
    rw [IsFundamentalDomain.setIntegral_eq (isFundamentalDomain_fundamentalDomain _ μ) hF hinv]
    exact h1
  · rw [integrable_quot_iff]
    simp_rw [hout]
    exact (IsFundamentalDomain.integrableOn_iff (isFundamentalDomain_fundamentalDomain _ μ) hF hinv).2 hint

end UpperTheory.ConvolutionTheory.G.UnitaryOne

open UpperTheory.ConvolutionTheory.G.UnitaryOne in
theorem UpperTheory.ConvolutionTheory.G.twistedGeometricSide_unfolding :
    U1 := by
  intro X _ _ _ _ _ _ _ _ Γ _ μ _ _ θ hc hθ f ⟨C, hC, hsupp⟩ ι r hr hex huniq _
  have hfin := tsum_lintegral_ne_top Γ μ θ hc hθ f hC hsupp
  have hI : ∀ δ : Γ, IntegrableOn (fun x => f (x⁻¹ * δ * θ x)) (fundamentalDomain Γ) μ := fun δ =>
    ⟨(Continuous.aestronglyMeasurable (by fun_prop)),
      (ne_top_of_le_ne_top hfin (ENNReal.le_tsum δ)).lt_top⟩
  have hs : Summable fun δ : Γ => ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * δ * θ x)‖ ∂μ := by
    refine (ENNReal.summable_toReal hfin).congr fun δ => ?_
    rw [integral_norm_eq_lintegral_enorm (hI δ).1]
  refine ⟨?_, fun i => (one_class Γ μ θ hθ f hI hs (r i) (hr i)).2⟩
  have hsum : ∀ x : X, ∑ᶠ γ : Γ, f ((Quotient.out (mk Γ x))⁻¹ * (γ : X) * θ (Quotient.out (mk Γ x))) =
      ∑' γ : Γ, f (x⁻¹ * γ * θ x) := by
    intro x
    obtain ⟨h, hh⟩ := out_mk Γ x
    rw [hh, ← tsum_eq_finsum (L := SummationFilter.unconditional Γ),
      ← (twEquiv Γ θ hθ h).tsum_eq (fun δ : Γ => f (x⁻¹ * δ * θ x))]
    · simp only [twEquiv_apply]
    · exact (finite_meet Γ θ hc f (isCompact_singleton (x := (h : X) * x))).subset
        fun δ hδ => ⟨_, rfl, hδ⟩
  rw [integral_quotientMeasure]
  simp_rw [hsum]
  have h0 := hasSum_integral_of_summable_integral_norm hI hs
  let e : (Σ i : ι, {γ' : Γ // ∃ g ∈ Γ, (γ' : X) = g⁻¹ * r i * θ g}) → Γ := fun p => p.2.1
  have he : Function.Injective e := by
    rintro ⟨i, a, g, hg, ha⟩ ⟨j, b, k, hk, hb⟩ hab
    change a = b at hab
    subst hab
    have hij : i = j := huniq i j (g * k⁻¹) (Γ.mul_mem hg (Γ.inv_mem hk)) (by
      have : r j = k * (k⁻¹ * r j * θ k) * (θ k)⁻¹ := by group
      rw [this, ← hb, ha, map_mul, map_inv]
      group)
    subst hij
    rfl
  have hz : ∀ δ ∉ Set.range e, ∫ x in fundamentalDomain Γ, f (x⁻¹ * (δ : X) * θ x) ∂μ = 0 := by
    intro δ hδ
    have : ∀ x, f (x⁻¹ * (δ : X) * θ x) = 0 := fun x => by
      by_contra hne
      obtain ⟨i, hi⟩ := hex δ δ.2 ⟨x, hne⟩
      exact hδ ⟨⟨i, δ, hi⟩, rfl⟩
    simp [this]
  exact ((he.hasSum_iff hz).2 h0).sigma fun i => (one_class Γ μ θ hθ f hI hs (r i) (hr i)).1
