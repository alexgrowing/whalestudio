import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1
open scoped ComplexConjugate

theorem an_two_shift (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ) :
    F.sgStar L (z + ω₀ / 2)
      = -(Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2)) := by
  have h := F.sgStarQuasi L ω₀ (z - ω₀ / 2) h0
  have e1 : z - ω₀ / 2 + ω₀ = z + ω₀ / 2 := by ring
  have e2 : (Real.pi : ℂ) * F.herm L (z - ω₀ / 2) ω₀ + (Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2
      = (Real.pi : ℂ) * F.herm L z ω₀ := by
    unfold F.herm; ring
  have e3 : F.semiChar L ω₀ = -1 := by
    unfold F.semiChar; exact if_neg h1
  rw [e1, e2, e3] at h
  rw [h]; ring

theorem an_two_sq (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2) ^ 2
      = F.sgStar L z ^ 2 * F.sgStar L (ω₀ / 2) ^ 2
        * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) := by
  have h := F.sgStarAdd L z (ω₀ / 2) hz h1
  rw [an_two_shift L ω₀ h0 h1 z] at h
  linear_combination -h

theorem an_two_kap (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) * F.sgStar L (ω₀ / 2) ^ 4
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
  have hz : ω₀ / 4 ∉ L.lattice := by
    intro h
    apply h1
    have := L.lattice.add_mem h h
    have e : ω₀ / 4 + ω₀ / 4 = ω₀ / 2 := by ring
    rwa [e] at this
  have hzt : ω₀ / 4 + ω₀ / 2 ∉ L.lattice := by
    intro h
    apply hz
    have := L.lattice.sub_mem h0 h
    have e : ω₀ - (ω₀ / 4 + ω₀ / 2) = ω₀ / 4 := by ring
    rwa [e] at this
  have h2t : 2 * (ω₀ / 2) ∈ L.lattice := by
    have e : 2 * (ω₀ / 2) = ω₀ := by ring
    rwa [e]
  have hH := F.halfShift L (ω₀ / 2) (ω₀ / 4) h1 h2t hz hzt
  have hA := an_two_shift L ω₀ h0 h1 (ω₀ / 4)
  have hB1 := an_two_sq L ω₀ h0 h1 (ω₀ / 4) hz
  have hB2 := an_two_sq L ω₀ h0 h1 (ω₀ / 4 + ω₀ / 2) hzt
  have e1 : ω₀ / 4 + ω₀ / 2 - ω₀ / 2 = ω₀ / 4 := by ring
  have e2 : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4 + ω₀ / 2) ω₀)
      = Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀)
        * Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
    rw [← Complex.exp_add]; congr 1; unfold F.herm; ring
  rw [e1, e2, hA] at hB2
  have hs : F.sgStar L (ω₀ / 4) ≠ 0 := fun h => hz (((F.sgStarBasic L).2.2.1 _).1 h)
  have hE : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) ≠ 0 := Complex.exp_ne_zero _
  have hne : Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) * F.sgStar L (ω₀ / 4) ^ 2 ≠ 0 :=
    mul_ne_zero hE (pow_ne_zero _ hs)
  apply mul_left_cancel₀ hne
  rw [← hH]
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L (ω₀ / 4) ω₀) = E at *
  generalize Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) = X at *
  generalize F.sgStar L (ω₀ / 4) = s at *
  generalize F.sgStar L (ω₀ / 4 - ω₀ / 2) = s' at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize L.weierstrassP (ω₀ / 4) - L.weierstrassP (ω₀ / 2) = a at *
  generalize L.weierstrassP (ω₀ / 4 + ω₀ / 2) - L.weierstrassP (ω₀ / 2) = b at *
  linear_combination (-1 : ℂ) * hB2 + (-(E * T ^ 2 * b)) * hB1

theorem an_two_odd (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (m : ℕ) :
    F.sgStar L (((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2)) ^ 2
      = Complex.exp ((Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2) ^ (2 * (m ^ 2 + m))
        * F.sgStar L (ω₀ / 2) ^ 2 := by
  have hm : (m : ℂ) * ω₀ ∈ L.lattice := by
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem h0 m
  have h := F.sgStarQuasi L ((m : ℂ) * ω₀) (ω₀ / 2) hm
  have e1 : ((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ / 2 + (m : ℂ) * ω₀ := by push_cast; ring
  have hchi : F.semiChar L ((m : ℂ) * ω₀) ^ 2 = 1 := by
    unfold F.semiChar; split_ifs <;> norm_num
  rw [e1, h, mul_pow, mul_pow, hchi, one_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  unfold F.herm
  simp only [map_mul, Complex.conj_natCast]
  push_cast
  ring

theorem an_two_card (L : PeriodPair) (n : ℕ) (hn : n ≠ 0) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) : S.card + 1 = n ^ 2 := by
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem hω n
  have h := F.kerRepsCard L (n : ℂ) S (by exact_mod_cast hn) hst hS
  have e : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.normSq_ofReal]; ring
  rw [e] at h
  exact_mod_cast h

theorem an_two (L : PeriodPair) (n : ℕ) (hn : Odd n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    ((n : ℂ) ^ 2 * ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P)) ^ 2
      = (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) ^ (n ^ 2 - 1) := by
  obtain ⟨m, rfl⟩ := hn
  have hn0 : 2 * m + 1 ≠ 0 := by omega
  have hst : F.MulStable L ((2 * m + 1 : ℕ) : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem hω _
  have hI := F.isogenySigma L ((2 * m + 1 : ℕ) : ℂ) S (by exact_mod_cast hn0) hst hS (ω₀ / 2) h1
  rw [an_two_card L _ hn0 S hS, an_two_odd L ω₀ h0 m, ← an_two_kap L ω₀ h0 h1] at hI
  have hT : F.sgStar L (ω₀ / 2) ≠ 0 := fun h => h1 (((F.sgStarBasic L).2.2.1 _).1 h)
  have ek : (2 * m + 1) ^ 2 - 1 = 4 * (m ^ 2 + m) := by
    have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    omega
  have ek2 : 2 * (2 * m + 1) ^ 2 = 8 * (m ^ 2 + m) + 2 := by ring
  rw [ek]
  rw [ek2] at hI
  clear ek ek2
  generalize m ^ 2 + m = k at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) = κ at *
  generalize ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P) = Q at *
  generalize ((2 * m + 1 : ℕ) : ℂ) = N at *
  have hT' : T ^ (8 * k + 2) ≠ 0 := pow_ne_zero _ hT
  have h3 : κ ^ (2 * k) = N ^ 2 * Q := by
    apply mul_left_cancel₀ hT'
    have : (κ * T ^ 4) ^ (2 * k) * T ^ 2 = T ^ (8 * k + 2) * κ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, pow_add]
      have : 4 * (2 * k) = 8 * k := by ring
      rw [this]; ring
    rw [← this, hI]; ring
  rw [← h3, ← pow_mul]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.L1
