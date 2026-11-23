import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinWeightTwoQSeries
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) := by
  first | exact @GlobalTheory.HeckeTwoSum.summable_qClass | exact GlobalTheory.HeckeTwoSum.summable_qClass | (intros; apply GlobalTheory.HeckeTwoSum.summable_qClass <;> assumption)
