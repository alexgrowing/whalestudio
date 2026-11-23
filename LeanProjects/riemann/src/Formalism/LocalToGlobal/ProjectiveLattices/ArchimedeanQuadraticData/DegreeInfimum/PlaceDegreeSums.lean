import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobSt

noncomputable section

namespace Formalism.L2.Pj.QAt.PlaceDegreeSums

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem sum_infinite_places_mult (f : InfinitePlace K → ℝ) :
    ∑ σ : InfinitePlace K, (σ.mult : ℝ) * f σ = ∑ τ : K →+* ℂ, f (InfinitePlace.mk τ) := by
  classical
  refine Eq.trans ?_ (Finset.sum_fiberwise Finset.univ (fun τ : K →+* ℂ => InfinitePlace.mk τ)
    (fun τ => f (InfinitePlace.mk τ)))
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f w) (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
    Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem sum_count_log_norm (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K w I : ℝ) * logN w =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  classical
  have h00 := FractionalIdeal.finite_factors I
  have hfs : {v : HeightOneSpectrum (𝓞 K) | ¬ FractionalIdeal.count K v I = 0}.Finite :=
    Filter.eventually_cofinite.mp h00
  have hN : ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I) : ℚ) : ℝ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I := by
    intro v
    simp [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    exact_mod_cast Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : FractionalIdeal.absNorm I = ∏ v ∈ hfs.toFinset,
      FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I) := by
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv
      by_contra h0
      apply hv
      have h0' : FractionalIdeal.count K v I = 0 := by
        by_contra hc
        exact h0 (Finset.mem_coe.mpr (hfs.mem_toFinset.mpr hc))
      simp [h0']), map_prod]
  have hterm : ∀ v : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K v I : ℝ) * logN v =
      Real.log ((FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        FractionalIdeal.count K v I) : ℚ) : ℝ) := by
    intro v
    rw [hN, Real.log_zpow, logN]
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_, hprod]
  · rw [Rat.cast_prod, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => hterm v
    · intro v _
      rw [hN]
      exact (zpow_pos (hNpos v) _).ne'
  · intro v hv
    by_contra h0
    apply hv
    have h0' : FractionalIdeal.count K v I = 0 := by
        by_contra hc
        exact h0 (Finset.mem_coe.mpr (hfs.mem_toFinset.mpr hc))
    simp [h0']

end Formalism.L2.Pj.QAt.PlaceDegreeSums
