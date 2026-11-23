import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldTarget
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.FinPlaceApproxPos

theorem exists_approx_totally_positive (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ φ : F →+* ℝ, 0 < φ a := by
  classical
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.FinPlaceApprox.approx_target F T t M
  set J : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ M with hJ
  have hJ0 : J ≠ ⊥ := by
    rw [hJ, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  set d : ℕ := Ideal.absNorm J with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hdJ : ((d : ℤ) : 𝓞 F) ∈ J := by
    simpa [hd] using Ideal.absNorm_mem J
  have hJv : ∀ v ∈ T, J ≤ v.asIdeal ^ M := fun v hv =>
    Ideal.prod_le_inf.trans (Finset.inf_le hv)
  obtain ⟨B, hB⟩ := (Set.finite_range (fun φ : F →+* ℝ => |φ a₀|)).bddAbove
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  refine ⟨a₀ + (N * d : ℕ), fun v hv => ?_, fun φ => ?_⟩
  · have hmem : ((N * d : ℕ) : 𝓞 F) ∈ v.asIdeal ^ M := by
      apply hJv v hv
      have : ((N * d : ℕ) : 𝓞 F) = (N : 𝓞 F) * ((d : ℤ) : 𝓞 F) := by push_cast; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hdJ
    have hval : v.valuation F ((N * d : ℕ) : F) ≤ WithZero.exp (-(M : ℤ)) := by
      have : ((N * d : ℕ) : F) = algebraMap (𝓞 F) F ((N * d : ℕ) : 𝓞 F) := by simp
      rw [this, HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
    have : a₀ + ((N * d : ℕ) : F) - t v = (a₀ - t v) + ((N * d : ℕ) : F) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (ha₀ v hv) hval)
  · have h1 : φ a₀ ≥ -B := by
      have := hB ⟨φ, rfl⟩
      have := neg_abs_le (φ a₀)
      simp only at *
      linarith
    have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    have hNB : B < N := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil B) (by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [map_add, map_natCast]
    push_cast
    nlinarith

theorem approxpos_target : ∀ (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ),
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a :=
  fun F _ _ T t M => exists_approx_totally_positive F T t M

end GlobalTheory.FinPlaceApproxPos
