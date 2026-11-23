import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_thetaSum_heisenbergLine : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ u : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      (∀ x, HasDerivAt (fun t : ℝ => d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Φ x) (Φ' x) 0) →
      ∀ u' : W, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (d.rho ψ u' (d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Φ)))
        (GlobalTheory.WeilM.thetaSum F (d.rho ψ u' Φ')) 0 := by
  first | exact @GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line | exact GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line | (intros; apply GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line <;> assumption)
