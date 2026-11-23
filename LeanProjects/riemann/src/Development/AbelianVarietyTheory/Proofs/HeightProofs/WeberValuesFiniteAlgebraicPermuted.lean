import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvariantIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem weberSet_finite (L : PeriodPair) {n : ℕ} (hn : 0 < n) : (weberSet L n).Finite := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  let f : ℤ × ℤ → ℂ := fun s => L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) *
    L.weierstrassP ((s.1 * L.ω₁ + s.2 * L.ω₂) / n)
  refine Set.Finite.insert _
    ((((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image f).subset ?_)
  rintro _ ⟨z, hz, -, rfl⟩
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩,
    ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩⟩, ?_⟩
  have e : (a * L.ω₁ + b * L.ω₂) / n = (((a % n : ℤ) : ℂ) * L.ω₁ + ((b % n : ℤ) : ℂ) * L.ω₂) / n +
      (((a / n : ℤ) : ℂ) * L.ω₁ + ((b / n : ℤ) : ℂ) * L.ω₂) := by
    have a1 : ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) = a := by
      exact_mod_cast Int.emod_add_mul_ediv a n
    have a2 : ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) = b := by
      exact_mod_cast Int.emod_add_mul_ediv b n
    rw [← a1, ← a2]
    field_simp
    ring
  simp only [f]
  rw [e, L.weierstrassP_add_coe _ ⟨_, PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩⟩]

theorem exists_map_weber_eq (L : PeriodPair) (n : ℕ) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (τ : ℂ ≃+* ℂ)
    (hτ : τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))
    (t : ℂ) (hnt : (n : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧
      τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) =
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t' := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  set J := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hJ
  set u := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hu
  have hu0 : u ≠ 0 := div_ne_zero (mul_ne_zero h2 h3) hD
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hu0 (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = u := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have hJ1 : J - 1 = 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [hJ, div_sub_one hD, sub_sub_cancel]
  have e2 : L'.g₂ = J * (J - 1) / 27 := by
    rw [H.g₂_eq, show (m ^ 4)⁻¹ = ((m ^ 2)⁻¹) ^ 2 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have e3 : L'.g₃ = J * (J - 1) ^ 2 / 729 := by
    rw [H.g₃_eq, show (m ^ 6)⁻¹ = ((m ^ 2)⁻¹) ^ 3 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have f2 : L'.g₂ = τ L'.g₂ := by
    rw [e2]; simp [hτ, map_ofNat]
  have f3 : L'.g₃ = τ L'.g₃ := by
    rw [e3]; simp [hτ, map_ofNat]
  obtain ⟨s, -, hc⟩ := GlobalTheory.ConjPoint.exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L' (m * t)))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  have hconj := (hc _ _).2 hw.symm
  have h1 := (hconj.nsmul_mem_iff f2 f3 n).1 (by rw [mul_left_comm]; exact (H _).2 hnt)
  rw [mul_left_comm] at h1
  obtain ⟨-, h4, h5, -⟩ := hconj.resolve_left fun h => ht ((H t).1 h.1)
  refine ⟨t', (H _).1 h1, fun h => h4 ((H _).2 h), ?_⟩
  rw [H.weierstrassP_mul, H.weierstrassP_mul, hmu] at h5
  exact h5.symm

theorem weberSet_finite_algebraic_permuted : ∀ (L : PeriodPair) (n : ℕ), 0 < n → L.g₂ ≠ 0 → L.g₃ ≠ 0 → (weberSet L n).Finite ∧ (IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ w ∈ weberSet L n, IsAlgebraic ℚ w) ∧ ∀ τ : ℂ ≃+* ℂ, τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧ τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) = (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') := by
  intro L n hn h2 h3
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨weberSet_finite L hn, fun hj => ?_, exists_map_weber_eq L n h2 h3⟩
  rintro _ (rfl | ⟨z, hz, hz', rfl⟩)
  · exact hj
  · exact GlobalTheory.WeberField.weber_isAlgebraic L hj hn hz' (by rwa [mul_div_cancel₀ _ hn0])

end GlobalTheory.FieldSize
