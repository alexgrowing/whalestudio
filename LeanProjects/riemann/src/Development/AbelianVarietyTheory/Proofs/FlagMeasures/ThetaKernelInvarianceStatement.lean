import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaKernelInvariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_invariance : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → ∀ (Φ : X.Sch L A) (g : GA D A), ∀ n ∈ d.N, (∀ γ ∈ d.N, γ ∈ GQ B → d.theta Wl.ψ (omZ Wl L A Φ) (γ * n) g = d.theta Wl.ψ (omZ Wl L A Φ) n g) ∧ ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → d.theta Wl.ψ (omZ Wl L A Φ) (δ * n * δ⁻¹) (γ * g) = d.theta Wl.ψ (omZ Wl L A Φ) n g := by
  first | exact @GlobalTheory.Per.ThetaAut.theta_aut | exact GlobalTheory.Per.ThetaAut.theta_aut | (intros; apply GlobalTheory.Per.ThetaAut.theta_aut <;> assumption)
