import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomials
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  first | exact @GlobalTheory.CenFockGen.cenFock_fin | exact GlobalTheory.CenFockGen.cenFock_fin | (intros; apply GlobalTheory.CenFockGen.cenFock_fin <;> assumption)
