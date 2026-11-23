import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.ParabModulus

section General

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

noncomputable def prodMul (μM μN : Measure G) : Measure G := (μM.prod μN).map (fun z => z.1 * z.2)

theorem lintegral_prodMul (μM μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂prodMul μM μN = ∫⁻ m, ∫⁻ u, f (m * u) ∂μN ∂μM := by
  rw [prodMul, lintegral_map hf measurable_mul]
  exact lintegral_prod (fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul).aemeasurable

theorem measurable_inner (μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    Measurable fun m => ∫⁻ u, f (m * u) ∂μN :=
  Measurable.lintegral_prod_right' (f := fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul)

theorem prodMul_left_fst (M : Subgroup G) (μM μN : Measure G) [SFinite μN]
    (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM) (s : G) (hs : s ∈ M) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iM s hs) _ (measurable_inner μN f hf)
  simpa only [mul_assoc] using this

theorem prodMul_left_snd (M N : Subgroup G) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m⁻¹ * u * m ∈ N)
    (μM μN : Measure G) [SFinite μN] (h1 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (s : G) (hs : s ∈ N) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  refine lintegral_congr_ae (aM.mono fun m hm => ?_)
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iN _ (hnorm m hm s hs)) (fun u => f (m * u))
    (hf.comp (measurable_const_mul m))
  show ∫⁻ u, f (s * (m * u)) ∂μN = ∫⁻ u, f (m * u) ∂μN
  rw [← this]
  refine lintegral_congr fun u => ?_
  rw [show m * (m⁻¹ * s * m * u) = s * (m * u) by group]

theorem prodMul_facts (M N P : Subgroup G) (hM : IsClosed (M : Set G)) (hN : IsClosed (N : Set G))
    (hPm : MeasurableSet (P : Set G)) (hMN : ∀ m ∈ M, m ∈ N → m = 1)
    (hMP : ∀ m ∈ M, ∀ u ∈ N, m * u ∈ P) (hdec : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ N, p = m * u)
    (μM μN : Measure G) [SigmaFinite μN] [IsFiniteMeasureOnCompacts μM] [IsFiniteMeasureOnCompacts μN]
    (hM0 : μM ≠ 0) (hN0 : μN ≠ 0) (h1 : μM (M : Set G)ᶜ = 0) (h2 : μN (N : Set G)ᶜ = 0) :
    prodMul μM μN (P : Set G)ᶜ = 0 ∧ SigmaFinite (prodMul μM μN) ∧
      ∃ T : Set G, MeasurableSet T ∧ prodMul μM μN T ≠ 0 ∧ prodMul μM μN T ≠ ⊤ := by
  set ρ₀ := prodMul μM μN with hρ₀
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  have aN : ∀ᵐ u ∂μN, u ∈ N := mem_ae_iff.2 h2
  have hP0 : ρ₀ (P : Set G)ᶜ = 0 := by
    rw [← lintegral_indicator_one hPm.compl, hρ₀, lintegral_prodMul _ _ _ (measurable_one.indicator hPm.compl)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aM] with m hm
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aN] with u hu
    rw [Set.indicator_of_notMem (show m * u ∉ (P : Set G)ᶜ from fun h => h (hMP m hm u hu))]
    simp
  set Q : ℕ → Set G := fun i => (compactCovering G i ∩ M) * (compactCovering G i ∩ N) with hQ
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    ((isCompact_compactCovering G i).inter_right hM).mul ((isCompact_compactCovering G i).inter_right hN)
  have uniq : ∀ i, ∀ m ∈ M, ∀ u ∈ N, m * u ∈ Q i → m ∈ compactCovering G i ∧ u ∈ compactCovering G i := by
    rintro i m hm u hu ⟨m', ⟨hm'C, hm'M⟩, u', ⟨hu'C, hu'N⟩, e⟩
    have e : m' * u' = m * u := e
    have e' : m'⁻¹ * m = u' * u⁻¹ := by
      calc m'⁻¹ * m = m'⁻¹ * (m * u) * u⁻¹ := by group
        _ = m'⁻¹ * (m' * u') * u⁻¹ := by rw [e]
        _ = u' * u⁻¹ := by group
    have h := hMN _ (M.mul_mem (M.inv_mem hm'M) hm) (by rw [e']; exact N.mul_mem hu'N (N.inv_mem hu))
    have hm' : m = m' := (inv_mul_eq_one.1 h).symm
    rw [h] at e'
    have hu' : u = u' := (mul_inv_eq_one.1 e'.symm).symm
    exact ⟨hm' ▸ hm'C, hu' ▸ hu'C⟩
  have hQ1 : ∀ i, ρ₀ (Q i) < ⊤ := by
    intro i
    have hC := isCompact_compactCovering G i
    rw [← lintegral_indicator_one (hQc i).measurableSet, hρ₀,
      lintegral_prodMul _ _ _ (measurable_one.indicator (hQc i).measurableSet)]
    calc _ ≤ ∫⁻ m, (compactCovering G i).indicator (fun _ => μN (compactCovering G i)) m ∂μM := by
          refine lintegral_mono_ae ?_
          filter_upwards [aM] with m hm
          by_cases hmC : m ∈ compactCovering G i
          · rw [Set.indicator_of_mem hmC, ← lintegral_indicator_one hC.measurableSet]
            refine lintegral_mono_ae ?_
            filter_upwards [aN] with u hu
            by_cases hq : m * u ∈ Q i
            · simp [Set.indicator_of_mem hq, Set.indicator_of_mem (uniq i m hm u hu hq).2]
            · simp [Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem hmC]
            refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
            filter_upwards [aN] with u hu
            rw [Set.indicator_of_notMem (fun h => hmC (uniq i m hm u hu h).1)]
            simp
      _ < ⊤ := by
          rw [lintegral_indicator_const hC.measurableSet]
          exact ENNReal.mul_lt_top hC.measure_lt_top hC.measure_lt_top
  have hS : ⋃ i, (Q i ∪ (P : Set G)ᶜ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ?_
    by_cases hg : g ∈ P
    · obtain ⟨m, hm, u, hu, rfl⟩ := hdec g hg
      obtain ⟨i, hi⟩ := exists_mem_compactCovering m
      obtain ⟨k, hk⟩ := exists_mem_compactCovering u
      exact ⟨max i k, Or.inl (Set.mul_mem_mul ⟨compactCovering_subset G (le_max_left _ _) hi, hm⟩
        ⟨compactCovering_subset G (le_max_right _ _) hk, hu⟩)⟩
    · exact ⟨0, Or.inr hg⟩
  have hS1 : ∀ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) < ⊤ := fun i =>
    lt_of_le_of_lt (measure_union_le _ _) (by rw [hP0, add_zero]; exact hQ1 i)
  have sf : SigmaFinite ρ₀ := ⟨⟨⟨fun i => Q i ∪ (P : Set G)ᶜ, fun _ => trivial, hS1, hS⟩⟩⟩
  have huniv : ρ₀ Set.univ ≠ 0 := by
    rw [hρ₀, prodMul, Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (fun h => hM0 (Measure.measure_univ_eq_zero.1 h))
      (fun h => hN0 (Measure.measure_univ_eq_zero.1 h))
  obtain ⟨i, hi⟩ : ∃ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact huniv (by rw [← hS]; exact measure_iUnion_null h)
  refine ⟨hP0, sf, Q i, (hQc i).measurableSet, fun h => hi ?_, (hQ1 i).ne⟩
  exact measure_union_null h hP0

theorem eq_smul_of_left_inv (P : Subgroup G) (hPm : MeasurableSet (P : Set G)) (ρ ρ₀ : Measure G)
    [SigmaFinite ρ] [SigmaFinite ρ₀] (h0 : ρ (P : Set G)ᶜ = 0) (h0' : ρ₀ (P : Set G)ᶜ = 0)
    (hi : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ) (hi' : ∀ s ∈ P, ρ₀.map (fun g => s * g) = ρ₀)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ₀ T ≠ 0) (hT1 : ρ₀ T ≠ ⊤) :
    ∃ c : ENNReal, ρ = c • ρ₀ := by
  have hemb : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hPm
  haveI : MeasurableMul₂ P := ⟨Measurable.subtype_mk
    ((hemb.measurable.comp measurable_fst).mul (hemb.measurable.comp measurable_snd))⟩
  haveI : MeasurableInv P := ⟨Measurable.subtype_mk hemb.measurable.inv⟩
  have hmap : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (τ.comap Subtype.val).map (Subtype.val : P → G) = τ := by
    intro τ h
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem h
  have hinv : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (∀ s ∈ P, τ.map (fun g => s * g) = τ) →
      (τ.comap (Subtype.val : P → G)).IsMulLeftInvariant := by
    intro τ h hτ
    refine ⟨fun s => ?_⟩
    rw [← hemb.comap_map ((τ.comap Subtype.val).map (fun g => s * g)),
      Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : P → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap τ h, hτ s s.2]
  haveI := hinv ρ h0 hi
  haveI := hinv ρ₀ h0' hi'
  haveI : SigmaFinite (ρ.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ h0]; infer_instance)
  haveI : SigmaFinite (ρ₀.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ₀ h0']; infer_instance)
  have hT' : ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) = ρ₀ T := by
    rw [← hmap ρ₀ h0', Measure.map_apply hemb.measurable hT, hmap ρ₀ h0']
  set c : ENNReal := ρ.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) /
    ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) with hc
  have key : ρ.comap (Subtype.val : P → G) = c • ρ₀.comap (Subtype.val : P → G) :=
    measure_eq_div_smul (ρ.comap (Subtype.val : P → G)) (ρ₀.comap (Subtype.val : P → G))
      (s := Subtype.val ⁻¹' T) (by rw [hT']; exact hT0) (by rw [hT']; exact hT1)
  refine ⟨c, ?_⟩
  conv_lhs => rw [← hmap ρ h0, key]
  rw [Measure.map_smul, hmap ρ₀ h0']

end General

end GlobalTheory.ParabModulus
