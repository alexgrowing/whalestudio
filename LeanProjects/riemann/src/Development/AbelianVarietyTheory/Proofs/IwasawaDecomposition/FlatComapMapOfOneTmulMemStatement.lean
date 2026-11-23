import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapMapOfOneTmulMem
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map : ∀ {B C R : Type} [CommRing B] [CommRing C] [CommRing R] [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R), (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) → r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  first | exact @GlobalTheory.flat_comap_map_of_one_tmul_mem | exact GlobalTheory.flat_comap_map_of_one_tmul_mem | (intros; apply GlobalTheory.flat_comap_map_of_one_tmul_mem <;> assumption)
