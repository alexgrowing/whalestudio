import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_mem_identity_component_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left), y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.inv_mem_connectedComponentIn_fibre | exact GlobalTheory.inv_mem_connectedComponentIn_fibre | (intros; apply GlobalTheory.inv_mem_connectedComponentIn_fibre <;> assumption)
