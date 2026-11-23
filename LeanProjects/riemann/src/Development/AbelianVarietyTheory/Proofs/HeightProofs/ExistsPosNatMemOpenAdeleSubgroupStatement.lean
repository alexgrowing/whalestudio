import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_mem_open_adele_subgroup : ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (AF F)), IsOpen (U : Set (AF F)) → ∃ N : ℕ, 0 < N ∧ pairA F 0 (N : Af F) ∈ U := by
  first | exact @GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen | exact GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen | (intros; apply GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen <;> assumption)
