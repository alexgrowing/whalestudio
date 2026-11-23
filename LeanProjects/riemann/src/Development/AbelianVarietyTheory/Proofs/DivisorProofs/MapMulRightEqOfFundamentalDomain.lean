import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
open MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.ConjModulus

theorem map_mul_right_eq_of_fundamentalDomain {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (Λ : Subgroup H) [Countable Λ] (ρ : Measure H)
    [ρ.IsHaarMeasure] (𝓡 : Set H) (h𝓡 : IsFundamentalDomain Λ 𝓡 ρ) (hfin : ρ 𝓡 ≠ ⊤) (x₀ : H) :
    ρ.map (· * x₀) = ρ := by
  haveI : (ρ.map (· * x₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ρ x₀
  have hc := Measure.isMulLeftInvariant_eq_smul (ρ.map (· * x₀)) ρ
  set c := Measure.haarScalarFactor (ρ.map (· * x₀)) ρ
  have h' : IsFundamentalDomain Λ ((· * x₀) ⁻¹' 𝓡) ρ := by
    refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀) (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ρ ((· * x₀) ⁻¹' 𝓡) = ρ 𝓡 := h'.measure_eq h𝓡
  have h0 : ρ 𝓡 ≠ 0 := h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hmap : (ρ.map (· * x₀)) 𝓡 = ρ ((· * x₀) ⁻¹' 𝓡) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x₀) 𝓡
  have h1 : (c : ℝ≥0∞) * ρ 𝓡 = 1 * ρ 𝓡 := by
    calc (c : ℝ≥0∞) * ρ 𝓡 = (c • ρ) 𝓡 := by simp [Measure.smul_apply]
      _ = (ρ.map (· * x₀)) 𝓡 := by rw [hc]
      _ = 1 * ρ 𝓡 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

def conjB {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) (b : B) : B :=
  ⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩

def conjCME {H G : Type} [Group H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ι : H →* G) (B : Subgroup G) (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) :
    B ≃ₜ* B where
  toFun := conjB ι B hB x
  invFun := conjB ι B hB x⁻¹
  left_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  right_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [conjB, mul_assoc]
  continuous_toFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  continuous_invFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem conjB_mul {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x y : H) :
    conjB ι B hB (x * y) = conjB ι B hB x ∘ conjB ι B hB y := by
  funext b; apply Subtype.ext; simp [conjB, mul_assoc]

end GlobalTheory.ConjModulus

namespace GlobalTheory.ConjModulus

theorem map_conj_eq_self_of_lattice : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ι : H →* G), Continuous ι → ∀ B : Subgroup G, IsClosed (B : Set G) →
    ∀ (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (β : Measure B), β.IsHaarMeasure →
    ∀ (Λ : Subgroup H) [Countable Λ] (ρ : Measure H) (𝓡 : Set H), ρ.IsHaarMeasure → IsFundamentalDomain Λ 𝓡 ρ → ρ 𝓡 ≠ ⊤ →
    (∀ x ∈ Λ, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β) →
    ∀ x : H, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β := by
  intro H _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _ ι hι B hBc hB β hβ Λ _ ρ 𝓡 hρ h𝓡 hfin hΛ
  haveI := hβ
  haveI := hρ
  haveI : LocallyCompactSpace B := hBc.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology (B : Set G)
  haveI : SigmaCompactSpace B := inferInstance
  haveI : SigmaFinite β := inferInstance
  have hΛ' : ∀ x ∈ Λ, β.map (conjB ι B hB x) = β := hΛ
  show ∀ x : H, β.map (conjB ι B hB x) = β
  have hφm : ∀ x, Measurable (conjB ι B hB x) := fun x => (conjCME ι B hB x).continuous.measurable
  have hHaar : ∀ x, (β.map (conjB ι B hB x)).IsHaarMeasure := fun x =>
    (conjCME ι B hB x).isHaarMeasure_map β
  obtain ⟨d, hdβ⟩ : ∃ d : H → ℝ≥0, ∀ x, β.map (conjB ι B hB x) = d x • β := ⟨fun x =>
    Measure.haarScalarFactor (β.map (conjB ι B hB x)) β, fun x => by
      haveI := hHaar x; exact Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : B)
  have hK0 : β K ≠ 0 := (Measure.measure_pos_of_mem_nhds β hK1).ne'
  have hKt : β K ≠ ⊤ := hKc.measure_lt_top.ne
  have hcancel : ∀ a b : ℝ≥0, a • β = b • β → a = b := by
    intro a b h
    have h2 : (a : ℝ≥0∞) * β K = (b : ℝ≥0∞) * β K := by
      have := congrArg (fun m : Measure B => m K) h
      simpa [Measure.smul_apply] using this
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).1 h2
  have hmul : ∀ x y, d (x * y) = d x * d y := by
    intro x y
    apply hcancel
    rw [← hdβ, conjB_mul, ← Measure.map_map (hφm x) (hφm y), hdβ y, Measure.map_smul, hdβ x,
      smul_smul, mul_comm]
  have hdΛ : ∀ x ∈ Λ, d x = 1 := by
    intro x hx
    apply hcancel
    rw [← hdβ, hΛ' x hx, one_smul]
  have hpos : ∀ x, 0 < d x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := congrArg (fun m : Measure B => m Set.univ) (hdβ x)
    simp only [h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    rw [Measure.map_apply (hφm x) MeasurableSet.univ, Set.preimage_univ] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne β)).ne' h1

  have hΦ : Continuous (fun p : H × B => conjB ι B hB p.1 p.2) :=
    continuous_induced_rng.2 (((hι.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul (hι.comp continuous_fst).inv)
  have hS : MeasurableSet ((fun p : H × B => conjB ι B hB p.1 p.2) ⁻¹' K) :=
    (hKc.isClosed.preimage hΦ).measurableSet
  have hDm : Measurable fun x => β (conjB ι B hB x ⁻¹' K) := measurable_measure_prodMk_left hS
  have hdK : ∀ x, (d x : ℝ≥0∞) = β (conjB ι B hB x ⁻¹' K) / β K := by
    intro x
    rw [ENNReal.eq_div_iff hK0 hKt, ← Measure.map_apply (hφm x) hKc.isClosed.measurableSet, hdβ x]
    simp [Measure.smul_apply, mul_comm]
  have hdm : Measurable d := by
    apply measurable_coe_nnreal_ennreal_iff.1
    simp_rw [hdK]
    exact hDm.div_const _

  obtain ⟨g, hgm, hgs, hg1⟩ : ∃ g : ℝ≥0 → ℝ≥0∞, Measurable g ∧
      (∀ a b : ℝ≥0, 0 < a → a < b → g a < g b) ∧ ∀ t, g t ≤ 1 := by
    refine ⟨fun t => ENNReal.ofReal ((t : ℝ) / (1 + t)), ?_, ?_, ?_⟩
    · exact (measurable_coe_nnreal_real.div (measurable_const.add measurable_coe_nnreal_real)).ennreal_ofReal
    · intro a b ha hab
      have ha' : (0 : ℝ) < a := ha
      have hab' : (a : ℝ) < b := hab
      have hb' : (0 : ℝ) < b := ha'.trans hab'
      have hpos' : (0 : ℝ) < (b : ℝ) / (1 + b) := div_pos hb' (by linarith)
      simp only
      rw [ENNReal.ofReal_lt_ofReal_iff hpos', div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · intro t
      apply ENNReal.ofReal_le_one.2
      rw [div_le_one (by positivity)]
      linarith

  have hR : ∀ x₀ : H, ρ.map (· * x₀) = ρ := map_mul_right_eq_of_fundamentalDomain Λ ρ 𝓡 h𝓡 hfin
  have hfΛ : ∀ (l : Λ) (z : H), g (d (l • z)) = g (d z) := by
    intro l z
    rw [Subgroup.smul_def, smul_eq_mul, hmul, hdΛ _ l.2, one_mul]
  have hshift : ∀ x₀ : H, ∫⁻ z in 𝓡, g (d z) ∂ρ = ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
    intro x₀
    have hmp : MeasurePreserving (· * x₀) ρ ρ := ⟨measurable_mul_const x₀, hR x₀⟩
    have hemb : MeasurableEmbedding (· * x₀ : H → H) := (MeasurableEquiv.mulRight x₀).measurableEmbedding
    have h' : IsFundamentalDomain Λ ((· * x₀) '' 𝓡) ρ := by
      rw [Set.image_mul_right]
      refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀⁻¹) (e := id)
        Function.bijective_id ?_
      intro l y
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    have := (h𝓡.setLIntegral_eq h' (fun z => g (d z)) hfΛ).trans
      (hmp.setLIntegral_comp_emb hemb (fun z => g (d z)) 𝓡).symm
    simpa [hmul] using this
  have hne : ρ.restrict 𝓡 ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hfinI : ∀ c : ℝ≥0, ∫⁻ z in 𝓡, g (d z * c) ∂ρ ≠ ⊤ := by
    intro c
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in 𝓡, 1 ∂ρ) ?_ (lintegral_mono fun z => hg1 _)
    rw [setLIntegral_const, one_mul]; exact hfin
  have hd1 : ∀ x, d x = 1 := by
    intro x₀
    by_contra hne1
    have hsh := hshift x₀
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have hlt' : ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ < ∫⁻ z in 𝓡, g (d z) ∂ρ := by
        refine lintegral_strict_mono hne (hgm.comp hdm).aemeasurable (hfinI _)
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (mul_pos (hpos z) (hpos x₀)) (mul_lt_of_lt_one_right (hpos z) hlt)
      exact hlt'.ne hsh.symm
    · have hlt' : ∫⁻ z in 𝓡, g (d z) ∂ρ < ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
        have h1 := hfinI 1
        simp only [mul_one] at h1
        refine lintegral_strict_mono hne ((hgm.comp (hdm.mul_const _))).aemeasurable h1
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (hpos z) (lt_mul_of_one_lt_right (hpos z) hgt)
      exact hlt'.ne hsh
  intro x
  rw [hdβ x, hd1 x, one_smul]

end GlobalTheory.ConjModulus
