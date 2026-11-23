import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitComponentMulMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (η[G]).left (G.hom y) ∈ U → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.mem_unitComponent_mul_mem | exact GlobalTheory.mem_unitComponent_mul_mem | (intros; apply GlobalTheory.mem_unitComponent_mul_mem <;> assumption)
