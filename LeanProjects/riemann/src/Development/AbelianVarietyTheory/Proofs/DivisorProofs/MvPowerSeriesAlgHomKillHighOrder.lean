import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_kill_high_order :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∃ N : ℕ, ∀ f : MvPowerSeries σ k,
          (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → φ f = 0 := by
  intro k _ σ _ A _ _ φ hφ
  classical
  haveI := Fintype.ofFinite σ
  choose m hm using hφ
  set M := Finset.univ.sup m with hMdef
  have hM : ∀ i, φ (X i) ^ M = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hm i)
  refine ⟨Fintype.card σ * M + 1, fun f hf => ?_⟩

  let fi : σ → MvPowerSeries σ k := fun i α =>
    if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0
  have hcoeff : ∀ i α, coeff α (fi i) =
      if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0 :=
    fun i α => rfl
  have hsum : f = ∑ i, fi i := by
    ext α
    rw [map_sum]
    simp only [hcoeff]
    by_cases h : ∃ j, M ≤ α j
    · simp only [dif_pos h]
      rw [Finset.sum_ite_eq]
      simp
    · simp only [dif_neg h, Finset.sum_const_zero]
      apply hf
      push_neg at h
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, α i ≤ ∑ _i : σ, M := Finset.sum_le_sum fun i _ => (h i).le
        _ = Fintype.card σ * M := by simp
        _ < Fintype.card σ * M + 1 := Nat.lt_succ_self _
  have hdvd : ∀ i, (X i : MvPowerSeries σ k) ^ M ∣ fi i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro α hα
    rw [hcoeff]
    split_ifs with h h'
    · exact absurd (h'.symm ▸ h.choose_spec) (not_le.mpr hα)
    · rfl
    · rfl
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨g, hg⟩ := hdvd i
  rw [hg, map_mul, map_pow, hM i, zero_mul]

end GlobalTheory
