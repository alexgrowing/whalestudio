import Mathlib
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density

open Filter Topology Set in

theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hsub : degreeOnePrimes L F ⊆ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∪ (B \ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}) := by
    intro v hv
    by_cases hvB : v ∈ B
    · by_cases hvS : v ∈ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}
      · exact Or.inl hvS
      · exact Or.inr ⟨hvB, hvS⟩
    · exact Or.inl (hcon v hv hvB)
  have hDd := GroundTheory.Global.hasDirichletDensity_degreeOnePrimes L F
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely F M
  have hBfin : (B \ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}).Finite := hB.subset Set.sdiff_subset
  have hBd := GroundTheory.Global.hasDirichletDensity_zero_of_finite hBfin
  have hle : ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum (degreeOnePrimes L F) s / NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 F))) s ≤
        NumberField.Set.primeIdealZetaSum {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} s /
            NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 F))) s +
          NumberField.Set.primeIdealZetaSum (B \ {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}) s /
            NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 F))) s := by
    intro s hs
    rw [← add_div, ← GroundTheory.Global.primeIdealZetaSum_union Set.disjoint_sdiff_right hs]
    apply div_le_div_of_nonneg_right (GroundTheory.Global.primeIdealZetaSum_mono hsub hs)
    exact tsum_nonneg (fun _ => by positivity)
  have hlim := le_of_tendsto_of_tendsto hDd (Filter.Tendsto.add hSd hBd) (eventually_nhdsWithin_of_forall hle)
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
