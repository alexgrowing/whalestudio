import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem redOmegaK_quad (d m : ℕ) (hm : d + 1 = 4 * m) : omegaK d ^ 2 - omegaK d + (m : ℂ) = 0 := by
  have hs : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hm' : (d : ℂ) + 1 = 4 * (m : ℂ) := by exact_mod_cast hm
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  have : ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) ^ 2 - (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2
      + (m : ℂ) = (Complex.I ^ 2 * (((Real.sqrt d : ℝ) : ℂ)) ^ 2 - 1 + 4 * (m : ℂ)) / 4 := by ring
  rw [this, hI, hs, ← hm']
  ring

theorem omega_mem_kur (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (l : ℕ) [Fact l.Prime] (hld : ¬ l ∣ d)
    (ι : ℂ ≃+* ℂ_[l]) : ι (omegaK d) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  set w : ℂ_[l] := ι (omegaK d) with hw
  have hq : w ^ 2 - w + (m : ℂ_[l]) = 0 := by
    have := congrArg ι (redOmegaK_quad d m hm)
    simpa using this
  have hm1 : ‖(m : ℂ_[l])‖ ≤ 1 := by
    rw [norm_natCast_Cl]
    exact Padic.norm_int_le_one (m : ℤ)
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd l hld
  have hw1 : ‖w‖ ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : ‖w - 1‖ = ‖w‖ := by
      have hne : ‖w‖ ≠ ‖(-1 : ℂ_[l])‖ := by rw [norm_neg, norm_one]; exact hgt.ne'
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one]
      exact max_eq_left hgt.le
    have h2 : w * (w - 1) = -(m : ℂ_[l]) := by linear_combination hq
    have h3 : ‖w‖ * ‖w‖ ≤ 1 := by
      have := congrArg norm h2
      rw [norm_mul, h1, norm_neg] at this
      rw [this]; exact hm1
    nlinarith
  have hder : ‖2 * w - 1‖ = 1 := by
    have h2 : (2 * w - 1) ^ 2 = -(d : ℂ_[l]) := by
      have hm' : (d : ℂ_[l]) + 1 = 4 * (m : ℂ_[l]) := by exact_mod_cast hm
      linear_combination 4 * hq + hm'
    have h3 : ‖2 * w - 1‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_neg, hd1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h3
  have hco : ∀ i, (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).coeff i =
      (if i = 2 then 1 else 0) - (if 1 = i then 1 else 0) + (if i = 0 then (m : ℂ_[l]) else 0) := fun i => by
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_X]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l])) ?_ ?_ w hw1 ?_ ?_
  · intro i
    rw [hco]
    refine (MaximalUnramifiedExtension l).add_mem ((MaximalUnramifiedExtension l).sub_mem ?_ ?_) ?_
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact natCast_mem (MaximalUnramifiedExtension l) m
      · exact (MaximalUnramifiedExtension l).zero_mem
  · intro i
    rw [hco]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_sub_le_max_Cl l _ _).trans (max_le ?_ ?_)) ?_)
    · split_ifs <;> simp
    · split_ifs <;> simp
    · split_ifs
      · exact hm1
      · simp
  · simpa using hq
  · have hd : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).derivative.eval w
        = 2 * w - 1 := by
      simp
      left; norm_num
    rw [hd, hder]

end ReciprocityTheory.ChartRestriction.L1
