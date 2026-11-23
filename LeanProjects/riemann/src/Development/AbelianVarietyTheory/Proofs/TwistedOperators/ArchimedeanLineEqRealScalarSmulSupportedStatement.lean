import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineEqRealScalarSmulSupported
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
theorem _root_.GlobalTheory.T.archimedeanLine_eq_realScalar_smul_supported : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ),
    (∀ t : ℝ, lineAt θ τ z t = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (lineAt θ τ z 1) := by
  first | exact @GlobalTheory.LineRealAd.lineAt_realAd_smul | exact GlobalTheory.LineRealAd.lineAt_realAd_smul | (intros; apply GlobalTheory.LineRealAd.lineAt_realAd_smul <;> assumption)
