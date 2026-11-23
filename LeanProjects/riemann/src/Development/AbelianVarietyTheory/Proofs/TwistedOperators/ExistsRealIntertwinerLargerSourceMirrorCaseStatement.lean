import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_largerSource_mirrorCase : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  first | exact @GlobalTheory.Chain.RealItLarge.itLarge | exact GlobalTheory.Chain.RealItLarge.itLarge | (intros; apply GlobalTheory.Chain.RealItLarge.itLarge <;> assumption)
