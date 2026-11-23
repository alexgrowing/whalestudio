import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridColumnParametersNegatedDataARPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridColumnParameters_negated_dataAR_pair : ∀ (D : D7) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ al be ga de : List ℚ,
    Formalism.MainNotions.SchurIrreducible.DataAR (GlobalTheory.Grid.sLen D - 1) al be ga de ∧
    GlobalTheory.Grid.parP D i τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
    GlobalTheory.Grid.parP D (i + 1) τ =
      dualPar (signed (al ++ block (GlobalTheory.Grid.sLen D - 1) ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) := by
  first | exact @GlobalTheory.NegPair.params | exact GlobalTheory.NegPair.params | (intros; apply GlobalTheory.NegPair.params <;> assumption)
