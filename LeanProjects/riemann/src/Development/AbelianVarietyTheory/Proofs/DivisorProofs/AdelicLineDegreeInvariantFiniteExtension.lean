import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula

open NumberField IsDedekindDomain Module GlobalTheory.FlatLine Formalism.BasicNotions

namespace GlobalTheory.FlatLine

section Descent

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']

theorem exp_ne_zero_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) : ε 𝔓 ≠ 0 := by
  intro h0
  have hmem : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k') ∈ 𝔓.asIdeal := Ideal.absNorm_mem _
  have h2 : 𝔓.valuation k' (algebraMap (𝓞 k') k' ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k')) < 1 := by
    rwa [HeightOneSpectrum.valuation_lt_one_iff_mem]
  have h1 := hv 𝔓 (Ideal.absNorm 𝔓.asIdeal : k)
  rw [h0, pow_zero, map_natCast] at h1
  rw [map_natCast, h1] at h2
  exact lt_irrefl _ h2

theorem mem_iff_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) (x : 𝓞 k) :
    x ∈ (π 𝔓).asIdeal ↔ 𝔓.valuation k' (algebraMap k k' (x : k)) < 1 := by
  rw [hv, pow_lt_one_iff (exp_ne_zero_of_valuation_pow hv 𝔓), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k)]

theorem eq_of_valuation_pow {π π' : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε ε' : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (hv' : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π' 𝔓).valuation k z ^ ε' 𝔓) :
    π = π' ∧ ε = ε' := by
  have hπ : π = π' := by
    funext 𝔓
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_iff_of_valuation_pow hv, mem_iff_of_valuation_pow hv']
  refine ⟨hπ, ?_⟩
  funext 𝔓
  obtain ⟨z, hz⟩ := (π 𝔓).valuation_exists_uniformizer k
  have h := (hv 𝔓 z).symm.trans (hv' 𝔓 z)
  rw [← hπ, hz, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
  simpa using h

theorem lineDeg_descent : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']
    (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ),
    (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) →
    ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ),
    (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite →
    (Function.support ρ).Finite ∧
      lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  intro k k' _ _ _ _ _ π ε hv r ρ hfin
  classical
  obtain ⟨π₀, ε₀, hv₀, hsum⟩ :=
    GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm k k' (algebraMap k k')
  obtain ⟨hπ, hε'⟩ := eq_of_valuation_pow hv hv₀
  rw [← hπ, ← hε'] at hsum
  choose s hs hne hid using hsum
  have hε : ∀ 𝔓, ε 𝔓 ≠ 0 := exp_ne_zero_of_valuation_pow hv
  have hk : (0 : ℝ) < finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hk' : (0 : ℝ) < finrank ℚ k' := by exact_mod_cast Module.finrank_pos

  have hρ : (Function.support ρ).Finite := by
    refine (hfin.image π).subset ?_
    intro 𝔭 h𝔭
    obtain ⟨𝔓, h𝔓⟩ := hne 𝔭
    have he : π 𝔓 = 𝔭 := (hs 𝔭 𝔓).1 h𝔓
    refine ⟨𝔓, ?_, he⟩
    simp only [Function.mem_support, he]
    exact mul_ne_zero (by exact_mod_cast hε 𝔓) h𝔭
  refine ⟨hρ, ?_⟩

  have harch := GlobalTheory.finrank_mul_sum_embeddings_comp k k' (algebraMap k k') (fun σ => Real.log (r σ))
  have hA : (∑ σ : k' →+* ℂ, Real.log (r (σ.comp (algebraMap k k')))) / (finrank ℚ k' : ℝ)
      = (∑ σ : k →+* ℂ, Real.log (r σ)) / (finrank ℚ k : ℝ) := by
    rw [div_eq_div_iff hk'.ne' hk.ne']
    linarith [harch]

  have hdisj : ((hρ.toFinset : Finset (HeightOneSpectrum (𝓞 k))) : Set (HeightOneSpectrum (𝓞 k))).PairwiseDisjoint s := by
    intro a _ b _ hab
    exact Finset.disjoint_left.2 fun 𝔓 ha hb => hab (((hs a 𝔓).1 ha).symm.trans ((hs b 𝔓).1 hb))
  unfold lineDeg lw
  beta_reduce
  have h1 : Function.support (fun la : HeightOneSpectrum (𝓞 k) =>
      ρ la * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k : ℝ))) ⊆ ↑hρ.toFinset := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
    simp [hx]
  have h2 : Function.support (fun la : HeightOneSpectrum (𝓞 k') =>
      (ε la : ℝ) * ρ (π la) * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k' : ℝ)))
      ⊆ ↑(hρ.toFinset.biUnion s) := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    have h0 : ρ (π x) = 0 := by
      by_contra h
      apply hx
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset,
        Function.mem_support]
      exact ⟨π x, h, (hs _ _).2 rfl⟩
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, hA,
    Finset.sum_biUnion hdisj]
  congr 1
  refine Finset.sum_congr rfl fun 𝔭 _ => ?_
  have e1 : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * ρ (π 𝔓) * (Real.log (Ideal.absNorm 𝔓.asIdeal) / (finrank ℚ k' : ℝ))
      = ρ 𝔭 / (finrank ℚ k' : ℝ) * ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔓 h => ?_
    rw [(hs 𝔭 𝔓).1 h]
    ring
  have hS : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal)
      = (finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) / (finrank ℚ k : ℝ) := by
    rw [eq_div_iff hk.ne']
    linarith [hid 𝔭]
  rw [e1, hS]
  field_simp

end Descent

end GlobalTheory.FlatLine
