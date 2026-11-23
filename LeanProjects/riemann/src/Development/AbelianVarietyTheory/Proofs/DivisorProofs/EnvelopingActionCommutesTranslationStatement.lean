import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingActionCommutesTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_action_commutes_translation : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V), (∀ a ∈ GinfC V, ∀ (f : SmF θ V) (hfa : (fun x => f.1 (x * a)) ∈ SmF θ V), (envRepAll R u ⟨_, hfa⟩).1 = fun x => (envRepAll R u f).1 (x * a)) → ∀ x : GlobalTheory.AutFinLit.LieC V, envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) * envRepAll R u = envRepAll R u * envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) := by
  first | exact @GlobalTheory.EnvCommLie.envRepAll_comm_lie | exact GlobalTheory.EnvCommLie.envRepAll_comm_lie | (intros; apply GlobalTheory.EnvCommLie.envRepAll_comm_lie <;> assumption)
