import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormPowEqSumMonomial
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory.Mean4

theorem rename_linRoot_perm {ι : Type} [Fintype ι] {N : ℕ} (σ : Equiv.Perm ι) (v : ι → Fin N → ℝ) :
    rename (Prod.map σ id) (linRoot (fun ρ i => v (σ ρ) i)) = linRoot v := by
  simp only [linRoot, map_neg, map_sum, map_mul, rename_C, rename_X]
  congr 1
  exact Fintype.sum_equiv (σ.prodCongr (Equiv.refl (Fin N))) _ _ (fun x => rfl)

end GlobalTheory.Mean4
