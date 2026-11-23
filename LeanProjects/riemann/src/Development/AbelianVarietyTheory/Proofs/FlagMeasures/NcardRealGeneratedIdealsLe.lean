import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardAbsNormLePowPred
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealIdealCount

theorem eq_map_comap {E : Type} [Field E] [NumberField E] [StarRing E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {𝔫 : Ideal (𝓞 E)}
    (h : 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t}) :
    𝔫 = (𝔫.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
  refine le_antisymm ?_ Ideal.map_comap_le
  conv_lhs => rw [h]
  refine Ideal.span_le.mpr ?_
  rintro t ⟨ht, hst⟩
  have hreal : (t : E) ∈ maximalRealSubfield E := by
    intro φ
    have key := hs φ (t : E)
    rw [hst, starRingEnd_apply] at key
    exact key.symm
  have hint : IsIntegral ℤ (⟨(t : E), hreal⟩ : maximalRealSubfield E) := by
    have ht' : IsIntegral ℤ (t : E) := t.isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
      (algebraMap (maximalRealSubfield E) E).injective).mp ht'
  let s : 𝓞 (maximalRealSubfield E) := ⟨⟨(t : E), hreal⟩, hint⟩
  have hs' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s = t := by
    apply RingOfIntegers.ext
    rfl
  rw [← hs']
  refine Ideal.mem_map_of_mem _ ?_
  rw [Ideal.mem_comap, hs']
  exact ht

private theorem isCMField_of_star_compat {E : Type} [Field E] [NumberField E] [StarRing E]
    [hTC : IsTotallyComplex E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField E := by
  refine GlobalTheory.LeastExponentCompare.isCMField_of_conj E (fun z => star z)
    (fun φ z => by rw [hs, starRingEnd_apply]) ?_
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have hreal : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext z
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := hs w.embedding z
    rw [hne z, starRingEnd_apply] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)) hreal

private theorem finrank_maximalRealSubfield_eq_fDeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ (maximalRealSubfield E) = Formalism.HermitianLatticesTheory.fDeg E := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    IsTotallyComplex.finrank (K := E)] at h1
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h2
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem ncard_real_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ hE Y hY
  obtain ⟨hTC, hs, -⟩ := hE
  haveI := hTC
  haveI : IsCMField E := isCMField_of_star_compat hs
  set F := maximalRealSubfield E
  set S : Set (Ideal (𝓞 E)) := {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧
    (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2} with hSdef
  set T : Set (Ideal (𝓞 F)) := {𝔞 : Ideal (𝓞 F) | 𝔞 ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ Y} with hTdef
  let g : Ideal (𝓞 E) → Ideal (𝓞 F) := fun 𝔫 => 𝔫.comap (algebraMap (𝓞 F) (𝓞 E))
  have hmap : ∀ 𝔫 ∈ S, 𝔫 = (g 𝔫).map (algebraMap (𝓞 F) (𝓞 E)) := fun 𝔫 h𝔫 =>
    eq_map_comap hs h𝔫.2.1
  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hinj : Set.InjOn g S := by
    intro 𝔫₁ h₁ 𝔫₂ h₂ heq
    rw [hmap 𝔫₁ h₁, hmap 𝔫₂ h₂, heq]
  have hmaps : Set.MapsTo g S T := by
    intro 𝔫 h𝔫
    have hn := hmap 𝔫 h𝔫
    refine ⟨?_, ?_⟩
    · intro hbot
      apply h𝔫.1
      rw [hn, hbot, Ideal.map_bot]
    · have hnorm : Ideal.absNorm 𝔫 = Ideal.absNorm (g 𝔫) ^ 2 := by
        conv_lhs => rw [hn]
        rw [Ideal.absNorm_algebraMap, hdeg]
      have hle := h𝔫.2.2
      rw [hnorm] at hle
      push_cast at hle
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by linarith) two_ne_zero).mp hle
  have hT : T.Finite := GlobalTheory.IdealBoundedNorm.finite_setOf_absNorm_le F Y
  refine ⟨Set.Finite.of_injOn hmaps hinj hT, ?_⟩
  have hcard : S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn g hmaps hinj hT
  have hTb := GlobalTheory.IdealBoundedNorm.ncard_absNorm_le F Y hY
  rw [finrank_maximalRealSubfield_eq_fDeg E] at hTb
  calc ((S.ncard : ℕ) : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := hTb

end GlobalTheory.RealIdealCount
