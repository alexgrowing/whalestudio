import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticMemClosureGenerators
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_mem_closure_generators : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F),
  gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 → g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  first | exact @GlobalTheory.sympGen | exact GlobalTheory.sympGen | (intros; apply GlobalTheory.sympGen <;> assumption)
