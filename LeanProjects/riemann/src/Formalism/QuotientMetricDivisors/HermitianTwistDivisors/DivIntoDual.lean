import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.DivIntoDual
import Formalism.QuotientMetricDivisors.ReductionLemmaZero

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace DualLatticeDivisor

variable {K : Type} [Field K] [NumberField K]

theorem mem_range_of_vw_nonneg (a : K) (ha : a ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) :
    a ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have key : ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (FractionalIdeal.count K v I) := by
    refine finprod_induction
      (fun X : FractionalIdeal (nonZeroDivisors (𝓞 K)) K =>
        ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = X)
      ⟨1, by simp⟩ ?_ ?_
    · rintro x y ⟨J1, h1⟩ ⟨J2, h2⟩
      exact ⟨J1 * J2, by rw [FractionalIdeal.coeIdeal_mul, h1, h2]⟩
    · intro v
      have hv : 0 ≤ FractionalIdeal.count K v I := h v
      refine ⟨v.asIdeal ^ (FractionalIdeal.count K v I).toNat, ?_⟩
      rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, Int.toNat_of_nonneg hv]
  rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI] at key
  obtain ⟨J, hJ⟩ := key
  have hmem : a ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hJ, hIdef]
    exact FractionalIdeal.mem_spanSingleton_self _ a
  obtain ⟨y, -, hy⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨y, hy⟩

end DualLatticeDivisor

theorem divisor_into_dual_lattice : DivIntoDual := by
  intro K _ _ _ D R B n M π ι P ζ hζ hvζ hP hM hloc x hx
  by_cases hBx : B x = 0
  · rw [hBx]; exact ⟨0, map_zero _⟩
  · apply DualLatticeDivisor.mem_range_of_vw_nonneg _ hBx
    intro w
    have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hloc w] at hxl
    rcases reduction_first_step K w (n w) D (M w) (π w) (ι w) B (P w) (ζ w) 0 (hζ w) (hvζ w) (hP w) (hM w) x
      hxl with h | h
    · exact absurd h hBx
    · exact h

end Formalism.DivisionValues
