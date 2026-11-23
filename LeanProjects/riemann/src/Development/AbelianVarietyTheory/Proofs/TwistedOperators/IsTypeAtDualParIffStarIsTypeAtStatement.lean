import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTypeAtDualParIffStarIsTypeAt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTypeAt_dualPar_iff_star_isTypeAt : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ), IsTypeAt θ V τ (Formalism.IndefR.Mult.dualPar P) φ ↔ IsTypeAt θ V τ P fun g => star (φ g) := by
  first | exact @GlobalTheory.TypeConj.isTypeAt_dualPar_iff | exact GlobalTheory.TypeConj.isTypeAt_dualPar_iff | (intros; apply GlobalTheory.TypeConj.isTypeAt_dualPar_iff <;> assumption)
