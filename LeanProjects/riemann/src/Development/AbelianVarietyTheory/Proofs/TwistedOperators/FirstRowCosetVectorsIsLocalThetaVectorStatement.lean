import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVector
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
theorem _root_.GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {_} ch => ∀ (t : T) (i : Fin D.R.m) (κ : ch.G.CosAt i), ∃ e, IsIdemSum e (locPl ch.G t) ∧ ∃ φ, IsLocVec ch.W (.chi (i : ℕ) 0) e (ch.W.vac i) φ (ch.W.cosVec i κ) := by
  first | exact @GlobalTheory.RowLocVec.cosVec_isLocVec | exact GlobalTheory.RowLocVec.cosVec_isLocVec | (intros; apply GlobalTheory.RowLocVec.cosVec_isLocVec <;> assumption)
