import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFiniteRepresentationChain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.given_finite_representation_chain : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  first | exact @GlobalTheory.FlipStart.startFin | exact GlobalTheory.FlipStart.startFin | (intros; apply GlobalTheory.FlipStart.startFin <;> assumption)
