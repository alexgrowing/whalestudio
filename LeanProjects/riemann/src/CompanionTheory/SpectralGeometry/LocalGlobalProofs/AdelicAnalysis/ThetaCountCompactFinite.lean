import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeInductionCompactSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaustStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CntFin

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
  {μ : Measure (HA (AF F) σ J)} {𝓕 : Set (HA (AF F) σ J)}

theorem cntI_mono_fun {S : Set (Fin n → Fin M → E)}
    {Φ Ψ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞} (h : ∀ Y, Φ Y ≤ Ψ Y) :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S Ψ :=
  lintegral_mono fun _ => ENNReal.tsum_le_tsum fun _ => h _

theorem cntI_le_of_contrib {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (h : ∀ (g : HA (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ≠ 0 → X ∈ S') :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S' Φ := by
  refine lintegral_mono fun g => ?_
  rw [tsum_subtype S (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))),
    tsum_subtype S' (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)))]
  refine ENNReal.tsum_le_tsum fun X => ?_
  by_cases hX : X ∈ S
  · by_cases h0 : Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) = 0
    · simp [Set.indicator, h0]
    · simp [Set.indicator, hX, h g X hX h0]
  · simp [Set.indicator, hX]

theorem cntI_union_le [Countable E] {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (hm : ∀ X : Fin n → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) :
    cntI σ J μ 𝓕 (S ∪ S') Φ ≤ cntI σ J μ 𝓕 S Φ + cntI σ J μ 𝓕 S' Φ := by
  unfold cntI
  rw [← lintegral_add_left (Measurable.ennreal_tsum fun X : S => hm X)]
  exact lintegral_mono fun g => ENNReal.tsum_union_le
    (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) S S'

end SlopeTestRemainingChoices

theorem cntI_nonzero_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      cntI σ J μ 𝓕 {X | X ≠ 0} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hFD Ω hΩ
  classical
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  obtain ⟨hTG, -, -, -, hBor, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := hTG
  haveI := hBor
  obtain ⟨-, -, -, hKt2, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hKt2
  haveI : Countable E :=
    ((Module.finBasis ℚ E).equivFun.toEquiv).injective.countable
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hcl : IsClosed Ω := hΩ.isClosed
  set Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞ := Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) with hΦ

  have hm : ∀ X : Fin 1 → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) := by
    intro X
    have hc : Continuous fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X) :=
      (hact 1).1.comp (continuous_inv.prodMk continuous_const)
    have hs : MeasurableSet ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω) :=
      (hcl.preimage hc).measurableSet
    have he : (fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) =
        Set.indicator ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω)
          (fun _ => (1 : ℝ≥0∞)) := by
      funext g
      by_cases hg : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω <;> simp [hΦ, Set.indicator, hg]
    rw [he]
    exact measurable_const.indicator hs

  have hzero : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} Φ < ⊤ := by
    obtain ⟨-, hbox, -⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ (Module.finBasis F E) 1 M
    obtain ⟨N, r, hN, hr, hsub⟩ := hbox Ω hΩ
    obtain ⟨C, hC⟩ := GlobalTheory.T.isotropic_vector_count_box_bound F E σ hCM M J hJ hM μ 𝓕 hH hFD _ (Module.finBasis F E) N hN
    refine lt_of_le_of_lt (le_trans (cntI_mono_fun fun Y => ?_) (hC r hr)) ENNReal.ofReal_lt_top
    exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) Y

  have hlen : ∀ t : F, t ≠ 0 →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro t ht
    exact GlobalTheory.T.finite_volume_induction_compact_sum F E σ hCM M J hJ
      (fun M' _ J' hJ' => GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M' J' hJ') t ht μ 𝓕 hH hFD Ω hΩ

  have hfinset : ∀ T : Finset F, (∀ t ∈ T, t ≠ 0) →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
        ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa using hzero
    | insert a T _ ih =>
      intro hT
      have hsub : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
          ∃ t ∈ insert a T, gramE σ J X = fun _ _ => algebraMap F E t} Φ ≤
          cntI σ J μ 𝓕 ({X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E a} ∪
            {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
              ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t}) Φ := by
        refine cntI_le_of_contrib fun g X hX _ => ?_
        rcases hX with hX | ⟨t, ht, hX⟩
        · exact Or.inr (Or.inl hX)
        · rcases Finset.mem_insert.1 ht with rfl | ht'
          · exact Or.inl hX
          · exact Or.inr (Or.inr ⟨t, ht', hX⟩)
      refine lt_of_le_of_lt (hsub.trans (cntI_union_le hm)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
      · exact hlen a (hT a (Finset.mem_insert_self a T))
      · exact ih fun t ht => hT t (Finset.mem_insert_of_mem ht)
  obtain ⟨hlenQ, hgram, hfin⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hCM M J hJ
  refine lt_of_le_of_lt ?_ (hfinset ((hfin Ω hΩ).toFinset.erase 0)
    fun t ht => (Finset.mem_erase.1 ht).1)
  refine cntI_le_of_contrib fun g X hX hne => ?_
  have hY : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω := by
    by_contra hY
    exact hne (by simp [hΦ, Set.indicator, hY])
  obtain ⟨t, ht⟩ := hlenQ X
  by_cases h0 : t = 0
  · refine Or.inl ⟨hX, ?_⟩
    rw [ht, h0]
    funext a b
    simp
  · refine Or.inr ⟨t, Finset.mem_erase.2 ⟨h0, ?_⟩, ht⟩
    refine (Set.Finite.mem_toFinset _).2 ⟨_, hY, ?_⟩
    rw [((hact 1).2.2.2 g⁻¹ (ratTup (AF F) X)), hgram 1 X, ht]
    funext a b
    rfl

end GlobalTheory.CompanionTheory.SW.CntFin
