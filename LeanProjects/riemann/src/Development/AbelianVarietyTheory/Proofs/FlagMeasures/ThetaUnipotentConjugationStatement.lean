import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentConjugation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_unipotent_conjugation : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), (∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ γ ∈ GQ B, d.chr ψ γ = 1 ∧ ∀ f, IsThetaFun ψ L A f → d.jac ψ γ f 0 = f 0) ∧ Continuous (d.chr ψ)) ∧ Continuous d.aCo ∧ Continuous d.tCo ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ d.N, g * n * g⁻¹ ∈ d.N ∧ d.aCo (g * n * g⁻¹) = (Formalism.L2.Theta.mt A h).mulVec (d.aCo n) ∧ d.tCo (g * n * g⁻¹) = d.tCo n ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (g * n * g⁻¹) = d.chr ψ n := by
  first | exact @GlobalTheory.HeisCoord.coords_laws | exact GlobalTheory.HeisCoord.coords_laws | (intros; apply GlobalTheory.HeisCoord.coords_laws <;> assumption)
