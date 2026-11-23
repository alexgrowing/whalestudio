import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyFun_mem_smooth_vectors : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  first | exact @GlobalTheory.CentralOps.polyFun_mem_smF | exact GlobalTheory.CentralOps.polyFun_mem_smF | (intros; apply GlobalTheory.CentralOps.polyFun_mem_smF <;> assumption)
