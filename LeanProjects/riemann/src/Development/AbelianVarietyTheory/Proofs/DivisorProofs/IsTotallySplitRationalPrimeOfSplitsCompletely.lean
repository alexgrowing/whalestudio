import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.SplitLevelsBall

theorem setOf_prime_mem_eq_primesOver (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime) :
    {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} = (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) := by
  ext P
  simp only [Set.mem_setOf_eq, Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show (g : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
      rw [Ideal.mem_comap, map_natCast]
      exact hgP
    have hne : P.under ℤ ≠ ⊤ := (Ideal.IsPrime.comap (f := algebraMap ℤ (𝓞 E)) (hK := hP)).ne_top
    exact hmax.eq_of_le hne hle
  · rintro ⟨hP, hlo⟩
    refine ⟨hP, ?_⟩
    have : (g : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this

theorem isTotallySplitPrime_of_splitsCompletely :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  intro E _ _ g ⟨hg, hc⟩
  exact ⟨hg, by rw [← setOf_prime_mem_eq_primesOver E g hg]; exact hc⟩

end GlobalTheory.SplitLevelsBall
