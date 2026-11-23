import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RealBranch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealFunctionalsSeparateOfHypothesis

section
noncomputable section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace
namespace UpperTheory.Lit.Branch
variable {n : ℕ}
variable {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
  {mu : Fin n → ℝ} {B : ℝ}
end UpperTheory.Lit.Branch
end
namespace UpperTheory.Lit
theorem functionalsSeparate_of_howeUnram_of_siegelWeil (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hH : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent) : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
  _root_.UpperTheory.Lit.real_functionals_separate_of_hypothesis P hH hSW realInputE_holds
end UpperTheory.Lit
end
