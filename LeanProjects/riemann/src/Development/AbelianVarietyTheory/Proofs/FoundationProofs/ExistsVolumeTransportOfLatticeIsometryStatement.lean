import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_volume_transport_of_lattice_isometry : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), (∀ x y, V'.hT (e x) (e y) = V.hT x y) → (∀ x, x ∈ V.L0 ↔ e x ∈ V'.L0) → ∃ φ : GA D V ≃* GA D V', Continuous φ ∧ Continuous φ.symm ∧ (∀ g, g ∈ GQ V ↔ φ g ∈ GQ V') ∧ ∀ (P Q : ℕ) (μ : Measure (GA D V)), IsVolMeas D V P Q μ → IsVolMeas D V' P Q (μ.map φ) := by
  first | exact @GlobalTheory.VolTransport.transport | exact GlobalTheory.VolTransport.transport | (intros; apply GlobalTheory.VolTransport.transport <;> assumption)
