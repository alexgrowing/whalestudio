import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYOff_of : OffClrRed → VdmSplit → SchurYOff := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))) * vdm g =
      sch lam g * vdm g * ∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hSplit R n g i]
  have key : (∏ k ∈ univ.erase i, (g i - y * g k) * Ring.inverse (g i - g k)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (g i - y * g k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [mul_assoc, Ring.inverse_mul_cancel _ (by simpa using (hu i k hki).neg), mul_one]
  rw [← key]
  ring

end UpperTheory.Gal.Schur
