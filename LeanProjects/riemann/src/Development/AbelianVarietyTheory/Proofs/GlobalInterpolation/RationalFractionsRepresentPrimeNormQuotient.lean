import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.Proof.IntegralPowerExpansion

variable {E : Type} [Field E] [NumberField E]

theorem intAt_int (P : HeightOneSpectrum (𝓞 E)) (n : ℤ) : IntAt P (n : E) := by
  simpa using IntAt.coe P (n : 𝓞 E)

theorem q_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {n : ℤ}
    (h : IntAt P ((qOf P : E)⁻¹ * n)) : (qOf P : ℤ) ∣ n := by
  by_contra hn
  have hpr : Prime (qOf P : ℤ) := Nat.prime_iff_prime_int.1 hP.1
  obtain ⟨x, y, hxy⟩ := (hpr.coprime_iff_not_dvd).2 hn
  have hq := q_ne_zero hP
  have h1 : IntAt P ((qOf P : E)⁻¹) := by
    have e : (qOf P : E)⁻¹ = x + y * ((qOf P : E)⁻¹ * n) := by
      have := congrArg (Int.cast : ℤ → E) hxy
      push_cast at this
      field_simp
      linear_combination -this
    rw [e]
    exact (intAt_int P x).add ((intAt_int P y).mul h)
  rw [intAt_iff_val, map_inv₀, val_q hP, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem q_pow_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (k : ℕ) {n : ℤ}
    (h : IntAt P (((qOf P : E) ^ k)⁻¹ * n)) : (qOf P : ℤ) ^ k ∣ n := by
  have hq := q_ne_zero hP
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have h1 : IntAt P ((qOf P : E)⁻¹ * n) := by
      have e : (qOf P : E)⁻¹ * n = (((qOf P : ℤ) ^ k : ℤ) : E) * (((qOf P : E) ^ (k + 1))⁻¹ * n) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact (intAt_int P _).mul h
    obtain ⟨m, rfl⟩ := q_dvd_of_intAt hP h1
    have e : ((qOf P : E) ^ (k + 1))⁻¹ * (((qOf P : ℤ) * m : ℤ) : E) = ((qOf P : E) ^ k)⁻¹ * m := by
      push_cast
      field_simp
      ring
    rw [e] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)

theorem valsQ_reps : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ,
    (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B,
      IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧
    ∀ a : E, IntAt P ((qOf P : E) ^ A * a) →
      ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  intro E _ _ P hP A B
  classical
  have hq := q_ne_zero hP
  constructor
  · intro a ha b hb h
    unfold LocE.valsQ at ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_range] at hi hj
    have h1 : IntAt P (((qOf P : E) ^ (A + B))⁻¹ * (((i : ℤ) - j : ℤ) : E)) := by
      convert h using 1
      push_cast
      field_simp
      ring
    have h2 := q_pow_dvd_of_intAt hP _ h1
    have hi' : (i : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hi
    have hj' : (j : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hj
    have h3 : (i : ℤ) - j = 0 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
    have h4 : i = j := by omega
    rw [h4]
  · intro a ha
    obtain ⟨k, u, hu, e⟩ := exists_int_add_q_pow_mul hP (A + B) ha
    have hpos : (0 : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast pow_pos hP.1.pos (A + B)
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg k hpos.ne')
    have hlt : i < qOf P ^ (A + B) := by
      have := Int.emod_lt_of_pos k hpos
      rw [hi] at this
      exact_mod_cast this
    have hk : (k : E) = i + (qOf P : E) ^ (A + B) * ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) := by
      have := Int.emod_add_mul_ediv k ((qOf P : ℤ) ^ (A + B))
      rw [hi] at this
      have h5 := congrArg (Int.cast : ℤ → E) this
      rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast] at h5
      exact h5.symm
    unfold LocE.valsQ
    refine ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hlt, rfl⟩, ?_⟩
    have h6 := (intAt_int P (k / (qOf P : ℤ) ^ (A + B))).add hu
    generalize ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) = m at hk h6
    have ea : a = ((qOf P : E) ^ A)⁻¹ * (i + (qOf P : E) ^ (A + B) * (m + u)) := by
      rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hq), e, hk]
      ring
    convert h6 using 1
    rw [ea]
    field_simp
    ring

end GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient
