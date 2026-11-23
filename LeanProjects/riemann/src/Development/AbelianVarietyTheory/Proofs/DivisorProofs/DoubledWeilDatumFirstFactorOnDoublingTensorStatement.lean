import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumFirstFactorOnDoublingTensor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  first | exact @GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor | exact GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor | (intros; apply GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor <;> assumption)
