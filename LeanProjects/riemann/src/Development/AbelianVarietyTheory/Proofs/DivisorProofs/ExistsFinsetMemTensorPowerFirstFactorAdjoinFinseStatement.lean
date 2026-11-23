import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)), ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  first | (exact @GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (exact GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (intros; apply GlobalTheory.EtC.exists_finset_mem_firstAndFinite  <;> assumption)
