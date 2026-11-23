import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

namespace HomotheticLatticeIntegrality

lemma alpha_sq (dK : ℕ) :
    (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK dK) ^ 2 = -(dK : ℂ) := by
  have h : (((Real.sqrt dK : ℝ) : ℂ)) ^ 2 = (dK : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK dK) = Complex.I * ((Real.sqrt dK : ℝ) : ℂ) := by
    unfold omegaK; push_cast; ring
  rw [e, mul_pow, h, Complex.I_sq]; ring

end HomotheticLatticeIntegrality

theorem homothetic_lattice_integral_of : HomotheticLatticeIntegralS2 := by
  intro cm4 dK L hsq h4 hcm l _ hl5 hld hin ι g2 g3 hgm
  obtain ⟨k2, k3, n2, n3, nd, lam, hlam, e2, e3⟩ := hgm
  have hlp : l.Prime := Fact.out

  have hc0 : ι.symm lam ≠ 0 := by
    intro h; apply hlam
    have := congrArg ι h
    simpa using this
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hc0
  obtain ⟨-, -, -, -, -, -, hs2, -, -, hg2, hg3⟩ := Formalism.L2.Th1.F.homogeneity L _ hc
  have es : ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L _ hc)) = lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) := by
    rw [hs2]; simp
  refine ⟨(ι.symm lam)⁻¹, hc, ?_, ?_, ?_⟩
  · rw [hg2, e2]; simp
  · rw [hg3, e3]; simp
  rw [es]

  have hd0 : 0 < dK := by omega
  obtain ⟨S, hS, -, -, hsum⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0
  obtain ⟨hst, hns⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2
  rw [HomotheticLatticeIntegrality.alpha_sq, hns] at hsum
  have hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P := by
    rw [← hsum]; push_cast; ring

  have hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ MaximalUnramifiedExtension l ∧ ‖lam ^ 2 * ι (L.weierstrassP P)‖ ≤ 1 := by
    intro P hPS
    obtain ⟨h1, h2⟩ := hS.1 P hPS
    have h3 : (dK : ℂ) * P ∈ L.lattice := by
      have h4 := hst _ h1
      have h5 : (dK : ℂ) * P
          = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK dK)
              * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK dK) * P)) := by
        rw [← mul_assoc, ← sq, HomotheticLatticeIntegrality.alpha_sq]; ring
      rw [h5]; exact neg_mem h4
    obtain ⟨a, -, b, -⟩ := cm4 dK L hsq h4 hcm l hl5 hld ι lam hlam (e2 ▸ k2) (e3 ▸ k3) (e2 ▸ n2)
      (e3 ▸ n3) (by rw [← e2, ← e3]; exact nd) P dK hd0 hld h3 h2
    exact ⟨a, b⟩
  have hn : ¬ l ∣ 2 * dK := by
    intro h
    rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hld h
  have hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (UnramifiedCompletion.normL_lt_one l) hn
  have hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hN; exact zero_ne_one hN
  have key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L)
      = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P)) := by
    have h := congrArg ι hsum'
    rw [map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast] at h
    rw [← Finset.mul_sum, ← h]
    push_cast
    push_cast at hN0
    have hd : (dK : ℂ_[l]) ≠ 0 := right_ne_zero_of_mul hN0
    field_simp
  rw [key]
  constructor
  · exact neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => (hP P hPS).1))
  · rw [norm_neg, norm_mul, norm_inv, hN, inv_one, one_mul]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun P hPS => (hP P hPS).2

end Formalism.L2.Th1.D
