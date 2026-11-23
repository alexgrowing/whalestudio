import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

open MvPolynomial

abbrev flagTwoFirstRoot : RootRing 1 (1+1) := X ((0:Fin 1), (0 : Fin (1+1)))
abbrev flagTwoSecondRoot : RootRing 1 (1+1) := X ((0:Fin 1), (1 : Fin (1+1)))

theorem inh_mu_eq : smallBlockMu 1 1 1 .last = flagTwoSecondRoot := by
  simp [smallBlockMu, yRoot, yIndex, SmallBlock.sign]

theorem inh_fib_eq : fibreClass 1 1 1 .last = 1 := by
  simp [fibreClass, vandermondeOf]

theorem inh_F_eq : restPolynomial 1 1 1 .last = flagTwoSecondRoot ^ 2 := by
  simp [restPolynomial, inh_mu_eq, inh_fib_eq]

theorem inh_decomp : IsPowerSumDecomposition 1 (1+1) (restPolynomial 1 1 1 .last)
    (fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0) := by
  have h2 : (C (2⁻¹ : ℚ) : RootRing 1 (1+1)) * 2 = 1 := by
    have : (2 : RootRing 1 (1+1)) = C 2 := (map_ofNat C 2).symm
    rw [this, ← C_mul]; norm_num
  have hI : Finset.Icc 1 (1+1) = ({1, 2} : Finset ℕ) := by decide
  rw [inh_F_eq, IsPowerSumDecomposition, hI]
  simp [blockPowerSum, Fin.sum_univ_two]
  linear_combination (-(flagTwoSecondRoot ^ 2)) * h2

theorem inh_van_eq : blockVandermonde 1 (1+1) = flagTwoFirstRoot - flagTwoSecondRoot := by
  have hIoi0 : Finset.Ioi (0 : Fin (1+1)) = {1} := by decide
  have hIoi1 : Finset.Ioi (1 : Fin (1+1)) = ∅ := by decide
  simp [blockVandermonde, vandermondeOf, Fin.prod_univ_two, hIoi0, hIoi1]

theorem inh_J_eq : fibreDegree 1 1 1 .last = -1 := by
  have hH : smallBlockMu 1 1 1 .last ^ (1 * (1 * 1)) * fibreClass 1 1 1 .last = flagTwoSecondRoot := by
    simp [inh_mu_eq, inh_fib_eq]
  rw [fibreDegree, hH, flagIntegral, inh_van_eq]
  have hne : ((0:Fin 1), (0 : Fin (1+1))) ≠ ((0:Fin 1), (1 : Fin (1+1))) := by decide
  rw [Finset.sum_eq_single (Finsupp.single ((0:Fin 1), (1 : Fin (1+1))) 1)]
  · simp [flagTwoFirstRoot, flagTwoSecondRoot, coeff_X', Finsupp.single_left_inj, hne, hne.symm, Finsupp.single_eq_single_iff]
  · intro b _ hb
    have : coeff b flagTwoSecondRoot = 0 := by
      rw [coeff_X']; exact if_neg (fun h => hb h.symm)
    simp [this]
  · intro h
    have : coeff (Finsupp.single ((0:Fin 1), (1 : Fin (1+1))) 1) (flagTwoFirstRoot - flagTwoSecondRoot) = 0 := by
      simpa using h
    simp [flagTwoFirstRoot, flagTwoSecondRoot, coeff_X', Finsupp.single_eq_single_iff, hne, hne.symm] at this

end

end RestTerms

end GroundTheory.Heights₂.Heights
