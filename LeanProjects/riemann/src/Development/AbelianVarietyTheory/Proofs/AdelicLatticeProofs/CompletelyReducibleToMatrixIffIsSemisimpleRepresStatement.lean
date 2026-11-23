import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepres
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | exact GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | (intros; apply GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation <;> assumption)
