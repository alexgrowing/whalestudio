import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_determined_by_schrodingerThetaValues : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  first | exact @GlobalTheory.SchrodingerUniq.main | exact GlobalTheory.SchrodingerUniq.main | (intros; apply GlobalTheory.SchrodingerUniq.main <;> assumption)
