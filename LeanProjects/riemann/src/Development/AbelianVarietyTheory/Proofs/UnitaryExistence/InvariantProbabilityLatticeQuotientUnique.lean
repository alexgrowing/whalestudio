import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume

noncomputable section
open MeasureTheory
open scoped Pointwise Topology ENNReal
namespace GlobalTheory.LatticeQuotUniq
open GlobalTheory.AutQuotCheck

section Alg
variable {G : Type} [Group G] [MeasurableSpace G] (Γ : Subgroup G)

def fibreMeasure (q : Quotient (QuotientGroup.rightRel Γ)) : Measure G :=
  Quotient.lift (fun g : G => Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) (by
    intro a b hab
    obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
    have := Measure.sum_comp_equiv (Equiv.mulRight (⟨δ, hδ⟩ : Γ))
      (fun γ : Γ => Measure.dirac ((γ : G) * a))
    rw [← this]
    congr 1
    ext1 γ
    simp [mul_assoc]) q

theorem fibreMeasure_apply (g : G) {A : Set G} (hA : MeasurableSet A) :
    fibreMeasure Γ (cls Γ g) A = ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g) := by
  show (Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) A = _
  rw [Measure.sum_apply _ hA]
  simp only [Measure.dirac_apply' _ hA]

theorem measurable_fibreMeasure [MeasurableMul G] [Countable Γ] : Measurable (fibreMeasure Γ) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  refine measurable_from_quotient.2 ?_
  have : ((fun q => fibreMeasure Γ q A) ∘ Quotient.mk'') =
      fun g : G => ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g) := by
    ext g; exact fibreMeasure_apply Γ g hA
  rw [this]
  exact Measurable.ennreal_tsum fun γ =>
    (measurable_one.indicator hA).comp (measurable_const_mul _)

theorem fibreMeasure_of_injOn {A : Set G} (hA : MeasurableSet A)
    (h : ∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) (q : Quotient (QuotientGroup.rightRel Γ)) :
    fibreMeasure Γ q A = (cls Γ '' A).indicator 1 q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [show fibreMeasure Γ (Quotient.mk _ g) A = _ from fibreMeasure_apply Γ g hA]
    by_cases hg : (Quotient.mk _ g) ∈ cls Γ '' A
    · rw [Set.indicator_of_mem hg]
      obtain ⟨a, ha, hag⟩ := hg
      obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ g a).1 hag.symm
      rw [tsum_eq_single (⟨δ, hδ⟩ : Γ)]
      · simp [Set.indicator_of_mem ha]
      · intro γ hγ
        refine Set.indicator_of_notMem (fun hm => hγ ?_) _
        have := h (γ * (⟨δ, hδ⟩ : Γ)⁻¹) _ ha (by simpa [mul_assoc] using hm)
        exact mul_inv_eq_one.1 this
    · rw [Set.indicator_of_notMem hg]
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => hg ?_) _
      exact ⟨_, hm, cls_smul Γ γ g⟩

theorem indicator_le_fibreMeasure {s : Set (Quotient (QuotientGroup.rightRel Γ))} (hs : MeasurableSet s)
    (q : Quotient (QuotientGroup.rightRel Γ)) :
    s.indicator 1 q ≤ fibreMeasure Γ q (cls Γ ⁻¹' s) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [show fibreMeasure Γ (Quotient.mk _ g) _ = _ from fibreMeasure_apply Γ g (measurable_cls Γ hs)]
    refine le_trans ?_ (ENNReal.le_tsum (1 : Γ))
    by_cases hg : (Quotient.mk _ g) ∈ s
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (by simpa using hg)]; simp
    · rw [Set.indicator_of_notMem hg]; exact zero_le

theorem preimage_image_cls (A : Set G) :
    cls Γ ⁻¹' (cls Γ '' A) = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ x a).1 h.symm
    exact ⟨⟨δ, hδ⟩, ha⟩
  · rintro ⟨γ, h⟩
    exact ⟨_, h, cls_smul Γ γ x⟩

theorem measurableSet_image_cls [MeasurableMul G] [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    MeasurableSet (cls Γ '' A) := by
  show MeasurableSet (cls Γ ⁻¹' (cls Γ '' A))
  rw [preimage_image_cls]
  exact MeasurableSet.iUnion fun γ => measurable_const_mul _ hA

theorem exists_strict_domain [MeasurableMul G] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {F : Set G} (hF : IsFundamentalDomain Γ F μ) :
    ∃ E : Set G, MeasurableSet E ∧ E =ᵐ[μ] F ∧ (∀ γ : Γ, ∀ x ∈ E, (γ : G) * x ∈ E → γ = 1) ∧
      μ (cls Γ ⁻¹' (cls Γ '' E)ᶜ) = 0 := by
  obtain ⟨E, hsub, hE, hae⟩ := hF.fundamentalInterior.nullMeasurableSet.exists_measurable_subset_ae_eq
  have h2 : fundamentalInterior Γ F =ᵐ[μ] F := by
    rw [← sdiff_fundamentalFrontier]
    exact diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right hF.measure_fundamentalFrontier)
  have h3 := hae.trans h2
  refine ⟨E, hE, h3, ?_, ?_⟩
  · intro γ x hx hγ
    by_contra hne
    have := (mem_fundamentalInterior.1 (hsub hγ)).2 γ hne
    exact this ⟨x, fundamentalInterior_subset (hsub hx), rfl⟩
  · rw [Set.preimage_compl, preimage_image_cls]
    have h4 : ∀ᵐ x ∂μ, ∀ γ : Γ, ((γ : G) * x ∈ F → (γ : G) * x ∈ E) := by
      refine ae_all_iff.2 fun γ => ?_
      exact (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h3.symm.le
    have h5 : ∀ᵐ x ∂μ, x ∈ ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' E := by
      filter_upwards [h4, hF.ae_covers] with x hx ⟨γ, hγ⟩
      exact Set.mem_iUnion.2 ⟨γ, hx γ hγ⟩
    exact h5

end Alg

theorem invariant_prob_eq : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ ⊤ → ∀ (ν : Measure (Quotient (QuotientGroup.rightRel Γ))) [IsProbabilityMeasure ν], (∀ (h : G) (ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ)), (∀ g : G, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s) → ν = (μ 𝓕)⁻¹ • (μ.restrict 𝓕).map (fun g : G => (Quotient.mk _ g : Quotient (QuotientGroup.rightRel Γ))) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ F hF hfin ν _ hinv
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  haveI : μ.IsMulRightInvariant := ⟨rightInvariant_of_covolume Γ μ hF h0 hfin⟩
  obtain ⟨E, hE, hEF, hEs, hEn⟩ := exists_strict_domain Γ μ hF
  have hκ := measurable_fibreMeasure Γ
  set L : Measure G := ν.bind (fibreMeasure Γ) with hL
  have hLa : ∀ A, MeasurableSet A → L A = ∫⁻ q, fibreMeasure Γ q A ∂ν :=
    fun A hA => Measure.bind_apply hA hκ.aemeasurable
  have hLi : ∀ A, MeasurableSet A → (∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) →
      L A = ν (cls Γ '' A) := by
    intro A hA h
    rw [hLa A hA]
    simp_rw [fibreMeasure_of_injOn Γ hA h]
    exact lintegral_indicator_one (measurableSet_image_cls Γ hA)
  haveI : L.IsMulRightInvariant := by
    refine ⟨fun h => ?_⟩
    let ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
      Quotient.lift (fun g => cls Γ (g * h)) (by
        intro a b hab
        obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
        exact (cls_eq_iff Γ _ _).2 ⟨δ, hδ, mul_assoc _ _ _⟩)
    have hρ : Measurable ρ :=
      measurable_from_quotient.2 ((measurable_cls Γ).comp (measurable_mul_const h))
    have hmp : MeasurePreserving ρ ν ν := ⟨hρ, by
      ext s hs
      rw [Measure.map_apply hρ hs]
      exact hinv h ρ (fun _ => rfl) s hs⟩
    ext A hA
    rw [Measure.map_apply (measurable_mul_const h) hA, hLa _ (measurable_mul_const h hA), hLa _ hA,
      ← hmp.lintegral_comp (f := fun q => fibreMeasure Γ q A) ((Measure.measurable_coe hA).comp hκ)]
    refine lintegral_congr fun q => ?_
    induction q using Quotient.inductionOn with
    | h g =>
      refine (fibreMeasure_apply Γ g (measurable_mul_const h hA)).trans
        (Eq.trans ?_ (fibreMeasure_apply Γ (g * h) hA).symm)
      refine tsum_congr fun γ => ?_
      rw [← mul_assoc]
      rfl
  haveI : IsLocallyFiniteMeasure L := by
    have hpos : 0 < μ E := by rw [measure_congr hEF]; exact pos_iff_ne_zero.2 h0
    have hn := Measure.div_mem_nhds_one_of_haar_pos μ E hE hpos
    refine ⟨fun g => ?_⟩
    have hc : ContinuousAt (fun p : G × G => p.1 / p.2) (g, g) := continuous_div'.continuousAt
    have h1 : (fun p : G × G => p.1 / p.2) ⁻¹' (E / E) ∈ 𝓝 (g, g) := hc (by simpa using hn)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 h1
    obtain ⟨W, hW, hWo, hgW⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hV)
    refine ⟨W, hWo.mem_nhds hgW, ?_⟩
    rw [hLi W hWo.measurableSet]
    · exact measure_lt_top _ _
    · intro γ x hx hγ
      have : ((γ : G) * x) / x ∈ E / E := hUV (Set.mk_mem_prod (hW hγ).1 (hW hx).2)
      obtain ⟨a, ha, b, hb, hab⟩ := this
      refine hEs γ b hb ?_
      have : a = (γ : G) * b := by
        simp only [mul_div_cancel_right] at hab
        rw [← hab]; simp
      rwa [← this]
  haveI : μ.inv.IsHaarMeasure := {}
  have e := Measure.isMulLeftInvariant_eq_smul L.inv μ.inv
  set c := Measure.haarScalarFactor L.inv μ.inv
  have e2 : L = (c : ℝ≥0∞) • μ := by
    have := congrArg Measure.inv e
    rw [Measure.inv_inv] at this
    rw [this]
    show Measure.map _ _ = _
    rw [Measure.map_smul]
    exact congrArg (c • ·) (Measure.inv_inv μ)
  have hT := measurableSet_image_cls Γ hE
  have hnull : ν (cls Γ '' E)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc ν (cls Γ '' E)ᶜ = ∫⁻ q, (cls Γ '' E)ᶜ.indicator 1 q ∂ν := (lintegral_indicator_one hT.compl).symm
      _ ≤ _ := lintegral_mono fun q => indicator_le_fibreMeasure Γ hT.compl q
      _ = L _ := (hLa _ (measurable_cls Γ hT.compl)).symm
      _ = 0 := by rw [e2, Measure.smul_apply, hEn, smul_zero]
  have key : ν = (c : ℝ≥0∞) • (μ.restrict F).map (cls Γ) := by
    ext s hs
    rw [Measure.smul_apply, Measure.map_apply (measurable_cls Γ) hs, ← Measure.restrict_congr_set hEF,
      Measure.restrict_apply (measurable_cls Γ hs), ← Measure.smul_apply, ← e2,
      hLi _ ((measurable_cls Γ hs).inter hE) (fun γ x hx hγ => hEs γ x hx.2 hγ.2),
      Set.image_preimage_inter]
    exact (measure_inter_conull hnull).symm
  have h1 : (c : ℝ≥0∞) * μ F = 1 := by
    have := congrArg (fun m => m Set.univ) key
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul] at this
    rw [Measure.map_apply (measurable_cls Γ) MeasurableSet.univ] at this
    simpa using this.symm
  rw [← ENNReal.eq_inv_of_mul_eq_one_left h1]
  exact key

end GlobalTheory.LatticeQuotUniq
