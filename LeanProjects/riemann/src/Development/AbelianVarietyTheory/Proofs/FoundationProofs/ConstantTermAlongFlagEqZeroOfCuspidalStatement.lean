import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstantTermAlongFlagEqZeroOfCuspidal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTermAlongFlag_eq_zero_of_cuspidal : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), φ ∈ cuspCont V → ∀ 𝔉 : IsoFlag V, 𝔉.Proper → constTerm 𝔉 φ = 0 := by
  first | exact @GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont | exact GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont | (intros; apply GlobalTheory.Cusp.constTerm_eq_zero_of_mem_cuspCont <;> assumption)
