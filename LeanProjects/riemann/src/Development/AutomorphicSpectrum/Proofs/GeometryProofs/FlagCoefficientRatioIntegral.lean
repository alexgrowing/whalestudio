import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem leadCoef_ratio_mem (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ)
    (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω) (hb : LinearIndependent Ω b)
    (hbf : ∀ j, flagStep Ω b j = flagStep Ω b₀ j) (_hbf' : ∀ j, flagStep Ω b' j = flagStep Ω b₀ j)
    (hN : ∀ j, N • b' j ∈ Submodule.span W (Set.range b))
    (ht : b k - t • b₀ k ∈ flagStep Ω b₀ k) (ht' : b' k - t' • b₀ k ∈ flagStep Ω b₀ k) :
    N * (t' / t) ∈ W := by
  by_cases ht0 : t = 0
  · rw [ht0, div_zero, mul_zero]
    exact W.zero_mem
  obtain ⟨u, hu_def⟩ : ∃ u : Ω, u = t' / t := ⟨_, rfl⟩
  rw [← hu_def]
  have hu : u * t = t' := by rw [hu_def, div_mul_cancel₀ t' ht0]
  have hF : N • b' k - (N * u) • b k ∈ flagStep Ω b k := by
    rw [hbf]
    have h1 := Submodule.sub_mem _ (Submodule.smul_mem _ N ht') (Submodule.smul_mem _ (N * u) ht)
    rw [← hu] at h1
    convert h1 using 1
    module
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun W).mp (hN k)
  rw [← hw] at hF
  have hF' : (∑ i, w i • b i) - (N * u) • b k ∈ Submodule.span Ω (b '' {j : Fin r | (j : ℕ) < k}) := hF
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hF'
  have hsum : Finsupp.linearCombination Ω b
      (Finsupp.equivFunOnFinite.symm fun i => (w i : Ω) - if i = k then N * u else 0) =
      (∑ i, w i • b i) - (N * u) • b k := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ (fun i a => a • b i) (fun i => zero_smul Ω _)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Subring.smul_def]
  have h0 : Finsupp.linearCombination Ω b
      ((Finsupp.equivFunOnFinite.symm fun i => (w i : Ω) - if i = k then N * u else 0) - l) = 0 := by
    rw [map_sub, hsum, hlc, sub_self]
  have hl0 := sub_eq_zero.mp (linearIndependent_iff.mp hb _ h0)
  have hk := DFunLike.congr_fun hl0 k
  simp only [Finsupp.coe_equivFunOnFinite_symm, ↓reduceIte] at hk
  have hlk : l k = 0 := (Finsupp.mem_supported' Ω l).mp hl k (by simp)
  rw [hlk, sub_eq_zero] at hk
  rw [← hk]
  exact (w k).2

end GlobalTheory.CompanionTheory.Ar
