import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreePrimeRemoval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NewPrimesSetDescriptionStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem telescope_finset (f : Finset ℕ → ℝ) (d : ℕ → ℝ) (A T : Finset ℕ) (hd : Disjoint A T)
    (h : ∀ p ∈ T, ∀ S : Finset ℕ, f (S.erase p) - f (insert p S) = d p) :
    f A = f (A ∪ T) + ∑ p ∈ T, d p := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T hp ih =>
    have hpA : p ∉ A := fun hA => Finset.disjoint_left.mp hd hA (Finset.mem_insert_self p T)
    have h1 := ih (hd.mono_right (Finset.subset_insert p T))
      (fun q hq => h q (Finset.mem_insert_of_mem hq))
    have h2 := h p (Finset.mem_insert_self p T) (A ∪ T)
    have hn : p ∉ A ∪ T := by simp [hpA, hp]
    rw [Finset.erase_eq_of_notMem hn] at h2
    rw [Finset.sum_insert hp, Finset.union_insert]
    linarith

end GlobalTheory.Mean4
